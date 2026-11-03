import DogeLib.Cryptography.Hash.Sha256
import DogeLib.Cryptography.Hash.Sha256d
import DogeLib.Serialization
import DogeLib.Work

/-!
# `KnownAnswers`

The driver of `lake test`: known answers from independent sources, run through the compiled specification.
Lake allows one test driver per package, so each operation with known answers adds a section here and a call in `main`.

## SHA-256

Runs the NIST CAVP SHA-256 vectors through the compiled `hash`.

`hash_eq_spec` proves that the definitions agree with a model of FIPS 180-4.
That theorem says nothing about the code that the Lean compiler produces from them.
This test checks the compiled code on the 129 byte-oriented vectors of CAVS 11.0.

Each file must contain the expected number of vectors.
A parser that reads none would otherwise pass.
-/

namespace KnownAnswers.Sha256Cavp

/-- One vector: the message length in bits, the message and the expected digest. -/
structure Vector where
  bits : Nat
  message : ByteArray
  digest : ByteArray

/-- The value of one hexadecimal digit, or `none` for another character. -/
def hexDigit? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- The bytes that a string of hexadecimal digits encodes, two digits per byte. -/
def parseHex (s : String) : Except String ByteArray := do
  let cs := s.toList
  if cs.length % 2 != 0 then throw s!"odd number of hex digits: {s}"
  let rec go : List Char → ByteArray → Except String ByteArray
    | hi :: lo :: rest, acc => do
      let some h := hexDigit? hi | throw s!"not a hex digit: {hi}"
      let some l := hexDigit? lo | throw s!"not a hex digit: {lo}"
      go rest (acc.push (h * 16 + l))
    | _, acc => pure acc
  go cs .empty

/-- Lowercase hexadecimal digits of `bytes`. -/
def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun acc b =>
    let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
    acc.push (digit (b / 16)) |>.push (digit (b % 16))

/-- The value after `key = ` on a line, if the line starts with that key. -/
def field? (key : String) (line : String) : Option String :=
  let pre := key ++ " = "
  if line.startsWith pre then some (line.drop pre.length).toString else none

/-- The vectors of an `.rsp` file, in order.
`Len = 0` comes with `Msg = 00`, so the message is the first `Len / 8` bytes of `Msg`. -/
def parse (text : String) : Except String (Array Vector) := do
  let lines := (text.splitOn "\n").map fun l => String.ofList (l.toList.filter (· != '\r'))
  let mut out := #[]
  let mut bits : Option Nat := none
  let mut msg : Option ByteArray := none
  for line in lines do
    if let some v := field? "Len" line then
      bits := v.toNat?
      if bits.isNone then throw s!"bad Len: {v}"
    else if let some v := field? "Msg" line then
      msg := some (← parseHex v)
    else if let some v := field? "MD" line then
      let some b := bits | throw "MD without Len"
      let some m := msg | throw "MD without Msg"
      if b % 8 != 0 then throw s!"Len {b} is not a whole number of bytes"
      if m.size < b / 8 then throw s!"Msg shorter than Len {b}"
      out := out.push { bits := b, message := m.extract 0 (b / 8), digest := ← parseHex v }
      bits := none
      msg := none
  return out

/-- Checks every vector of one file, and that the file holds `expected` vectors.
Returns the number of failures. -/
def checkFile (path : System.FilePath) (expected : Nat) : IO Nat := do
  let vectors ← match parse (← IO.FS.readFile path) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  if vectors.size != expected then
    IO.eprintln s!"FAIL {path}: {vectors.size} vectors, expected {expected}"
    failures := failures + 1
  for v in vectors do
    let got := DogeLib.Cryptography.Hash.Sha256.hash v.message
    if got.toList != v.digest.toList then
      IO.eprintln s!"FAIL {path}: Len = {v.bits}: got {toHex got}, expected {toHex v.digest}"
      failures := failures + 1
  IO.println s!"{path}: {vectors.size} vectors, {failures} failures"
  return failures

end KnownAnswers.Sha256Cavp

/-!
## Double SHA-256: Dogecoin's genesis blocks

Dogecoin Core asserts the hash of each network's genesis block, and the merkle root they share, in `src/chainparams.cpp` (SOURCES.md, D9).
Those asserted values are the known answers.

The bytes to hash are derived here by hand from the same file, because DogeLib does not define block or transaction serialization yet:

- A block hash is `CHash256` of the 80-byte pure header (D10): `nVersion`, `hashPrevBlock`, `hashMerkleRoot`, `nTime`, `nBits`, `nNonce`, each integer in little-endian order.
- The merkle root of a block with one transaction is that transaction's ID, the `CHash256` of its serialization.
  The genesis coinbase is built by `CreateGenesisBlock`.
- Core displays a hash with its bytes reversed (D11), so each displayed value is reversed before the comparison.

A wrong derivation makes the test fail, never pass: the expected digests come from Core, not from DogeLib.
-/

namespace KnownAnswers.Genesis

open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- `n` as four little-endian bytes. -/
def le32 (n : UInt32) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩

/-- `n` as eight little-endian bytes. -/
def le64 (n : UInt64) : ByteArray :=
  ⟨(Array.range 8).map fun i => (n >>> (8 * i.toUInt64)).toUInt8⟩

/-- The bytes of a displayed hash, in the order they are hashed: the display order reversed. -/
def ofDisplay (hex : String) : Except String ByteArray := do
  return ⟨(← parseHex hex).toList.reverse.toArray⟩

/-- The genesis coinbase transaction of `CreateGenesisBlock`, serialized by hand.
`486604799` is pushed as the four bytes `ff ff 00 1d`, `CScriptNum(4)` as the one byte `04`, and the timestamp `Nintondo` as eight bytes. -/
def coinbase : Except String ByteArray := do
  let scriptSig ← parseHex "04ffff001d0104084e696e746f6e646f"
  let key ← parseHex "040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9"
  let scriptPubKey := (ByteArray.mk #[0x41]) ++ key ++ ByteArray.mk #[0xac]
  return le32 1                                   -- nVersion
    ++ ByteArray.mk #[0x01]                       -- one input
    ++ ByteArray.mk (Array.replicate 32 0)        -- null outpoint hash
    ++ le32 0xffffffff                            -- null outpoint index
    ++ ByteArray.mk #[scriptSig.size.toUInt8] ++ scriptSig
    ++ le32 0xffffffff                            -- nSequence
    ++ ByteArray.mk #[0x01]                       -- one output
    ++ le64 (88 * 100000000)                      -- 88 * COIN
    ++ ByteArray.mk #[scriptPubKey.size.toUInt8] ++ scriptPubKey
    ++ le32 0                                     -- nLockTime

/-- The shared genesis merkle root, as Core displays it. -/
def merkleRoot : String := "5b2a3f53f605d62c53e62932dac6925e3d74afa5a4b459745c36d42d0ed26a69"

/-- The 80-byte pure header of a genesis block. -/
def header (time nonce bits : UInt32) : Except String ByteArray := do
  return le32 1 ++ ByteArray.mk (Array.replicate 32 0) ++ (← ofDisplay merkleRoot)
    ++ le32 time ++ le32 bits ++ le32 nonce

/-- Compares `Sha256d.hash bytes` with a digest that Core displays. Returns the number of failures. -/
def expect (name : String) (bytes : Except String ByteArray) (display : String) : IO Nat := do
  match bytes, ofDisplay display with
  | .ok b, .ok want =>
    let got := DogeLib.Cryptography.Hash.Sha256d.hash b
    if got.toList == want.toList then
      IO.println s!"genesis {name}: ok"
      return 0
    IO.eprintln s!"FAIL genesis {name}: got {toHex got}, expected {toHex want} (hashing order)"
    return 1
  | .error e, _ | _, .error e =>
    IO.eprintln s!"FAIL genesis {name}: {e}"
    return 1

/-- Every genesis known answer. Returns the number of failures. -/
def check : IO Nat := do
  let checks := [
    expect "coinbase txid = merkle root" coinbase merkleRoot,
    expect "main" (header 1386325540 99943 0x1e0ffff0)
      "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691",
    expect "testnet" (header 1391503289 997879 0x1e0ffff0)
      "bb0a78264637406b6360aad926284d544d7049f45189db5664f3c4d07350559e",
    expect "regtest" (header 1296688602 2 0x207fffff)
      "3d2160a3b5dc4a9d62e7e66a295f70313ac808440ef7400d6c0772171ce973a5"]
  checks.foldlM (init := 0) fun acc c => return acc + (← c)

end KnownAnswers.Genesis

/-!
## Codecs: fixed-width integers in Dogecoin's genesis data

Known answers for the list codecs and the packed codecs of the fixed-width integers.

The inputs are two hexadecimal literals: the 80-byte pure header of the main-network genesis block, and the genesis coinbase transaction.
The test first checks that the double SHA-256 of each literal is the digest that Core asserts in `src/chainparams.cpp` (SOURCES.md, D9).
So the literals are Core's bytes, independently of the codecs.

The expected integers are the arguments of `CreateGenesisBlock(1386325540, 99943, 0x1e0ffff0, 1, 88 * COIN)` in the same file.
Each field is at its offset in the serialization order of the header (D10) and of the transaction (D4):

```text
header    0..4    nVersion = 1
header   68..72   nTime    = 1386325540
header   72..76   nBits    = 0x1e0ffff0
header   76..80   nNonce   = 99943
coinbase 63..71   nValue   = 88 * COIN = 8800000000
```

Two 32-byte hashes check the codec of `Hash256`, which is `Bytes 32`:

```text
header   36..68   hashMerkleRoot = 5b2a3f…6a69 in display order (D9)
coinbase  5..37   prevout hash   = 32 zero bytes, COutPoint::SetNull (D4)
```

Each decoder check compares the full result: the value and the remainder, or the rejection.
The packed decoder checks read slices that start at a nonzero offset of the array.
-/

namespace KnownAnswers.Codec

open DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex toHex)
open KnownAnswers.Genesis (ofDisplay merkleRoot)

/-- The pure header of the main-network genesis block. -/
def headerHex : String :=
  "01000000" ++ "0000000000000000000000000000000000000000000000000000000000000000"
    ++ "696ad20e2dd4365c7459b4a4a5af743d5e92c6da3229e6532cd605f6533f2a5b"
    ++ "24a6a152" ++ "f0ff0f1e" ++ "67860100"

/-- The genesis coinbase transaction. -/
def coinbaseHex : String :=
  "01000000" ++ "01" ++ "0000000000000000000000000000000000000000000000000000000000000000"
    ++ "ffffffff" ++ "10" ++ "04ffff001d0104084e696e746f6e646f" ++ "ffffffff" ++ "01"
    ++ "0058850c02000000" ++ "43"
    ++ "41040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9ac"
    ++ "00000000"

/-- A packed decoder result with its remaining slice read as a list, for comparison. -/
def viewPacked {α : Type} (r : Option (α × ByteSlice)) : Option (α × List UInt8) :=
  r.map fun p => (p.1, p.2.toList)

/-- The checks on the two literals, each with its name and whether it holds. -/
def cases (header coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let h := header.toList
  let c := coinbase.toList
  let mainHash ← ofDisplay "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
  let root ← ofDisplay merkleRoot
  let hs := ByteSlice.ofByteArray header
  let cs := ByteSlice.ofByteArray coinbase
  return [
    ("header literal hashes to the main genesis hash",
      (DogeLib.Cryptography.Hash.Sha256d.hash header).toList == mainHash.toList),
    ("coinbase literal hashes to the genesis merkle root",
      (DogeLib.Cryptography.Hash.Sha256d.hash coinbase).toList == root.toList),
    -- List codecs: decoding.
    ("UInt8 reads the first byte of nVersion", Codec.decode h == some ((1 : UInt8), h.drop 1)),
    ("UInt16 reads the first two bytes of nVersion", Codec.decode h == some ((1 : UInt16), h.drop 2)),
    ("UInt32 reads nVersion", Codec.decode h == some ((1 : UInt32), h.drop 4)),
    ("UInt32 reads nTime", Codec.decode (h.drop 68) == some ((1386325540 : UInt32), h.drop 72)),
    ("UInt32 reads nBits", Codec.decode (h.drop 72) == some ((0x1e0ffff0 : UInt32), h.drop 76)),
    ("UInt32 reads nNonce and leaves nothing", Codec.decode (h.drop 76) == some ((99943 : UInt32), [])),
    ("UInt64 reads nValue", Codec.decode (c.drop 63) == some ((8800000000 : UInt64), c.drop 71)),
    ("pair reads nTime then nBits",
      Codec.decode (h.drop 68) == some (((1386325540 : UInt32), (0x1e0ffff0 : UInt32)), h.drop 76)),
    ("UInt32 rejects the last 3 bytes", (Codec.decode (h.drop 77) : Option (UInt32 × List UInt8)) == none),
    ("UInt64 rejects the last 7 bytes", (Codec.decode (c.drop 136) : Option (UInt64 × List UInt8)) == none),
    ("UInt8 rejects no bytes", (Codec.decode [] : Option (UInt8 × List UInt8)) == none),
    -- Fixed-length bytes: the merkle root and the null prevout hash.
    ("Hash256 reads hashMerkleRoot",
      (Codec.decode (α := DogeLib.Hash256) (h.drop 36)).map (fun p => (p.1.val, p.2))
        == some (root.toList, h.drop 68)),
    ("Hash256 reads hashMerkleRoot in display order",
      ((Codec.decode (α := DogeLib.Hash256) (h.drop 36)).map (·.1.displayBytes))
        == some root.toList.reverse),
    ("Hash256 of the display bytes of the merkle root",
      ((DogeLib.Hash256.ofDisplayBytes? root.toList.reverse).map (·.val)) == some root.toList),
    ("Hash256 reads the null prevout hash",
      (Codec.decode (α := DogeLib.Hash256) (c.drop 5)).map (fun p => (p.1.val, p.2))
        == some (DogeLib.Hash256.zero.val, c.drop 37)),
    ("Hash256 rejects 31 bytes", (Codec.decode (α := DogeLib.Hash256) ((h.drop 36).take 31)).isNone),
    ("Hash256 writes the null prevout hash",
      Codec.encode DogeLib.Hash256.zero == (c.drop 5).take 32),
    ("packed Hash256 reads hashMerkleRoot at offset 36",
      viewPacked ((PackedCodec.decodeSlice (α := DogeLib.Hash256) (hs.drop 36)).map
        fun p => (p.1.val, p.2)) == some (root.toList, h.drop 68)),
    ("packed Hash256 rejects 31 bytes",
      (PackedCodec.decodeSlice (α := DogeLib.Hash256) ((hs.drop 36).take 31)).isNone),
    ("packed Hash256 appends the null prevout hash",
      (PackedCodec.encodeInto DogeLib.Hash256.zero (coinbase.extract 0 5)).toList == c.take 37),
    -- List codecs: encoding.
    ("UInt32 writes nTime", Codec.encode (1386325540 : UInt32) == (h.drop 68).take 4),
    ("UInt64 writes nValue", Codec.encode (8800000000 : UInt64) == (c.drop 63).take 8),
    ("pairs write nTime, nBits and nNonce",
      Codec.encode (((1386325540 : UInt32), (0x1e0ffff0 : UInt32)), (99943 : UInt32)) == h.drop 68),
    -- Packed codecs: decoding from slices at a nonzero offset.
    ("packed UInt32 reads nTime",
      viewPacked (PackedCodec.decodeSlice (hs.drop 68)) == some ((1386325540 : UInt32), h.drop 72)),
    ("packed UInt32 reads nNonce and leaves nothing",
      viewPacked (PackedCodec.decodeSlice (hs.drop 76)) == some ((99943 : UInt32), [])),
    ("packed UInt64 reads nValue",
      viewPacked (PackedCodec.decodeSlice (cs.drop 63)) == some ((8800000000 : UInt64), c.drop 71)),
    ("packed pair reads nTime then nBits",
      viewPacked (PackedCodec.decodeSlice (hs.drop 68))
        == some (((1386325540 : UInt32), (0x1e0ffff0 : UInt32)), h.drop 76)),
    ("packed UInt32 reads nVersion from the whole array",
      viewPacked (PackedCodec.decode header) == some ((1 : UInt32), h.drop 4)),
    ("packed UInt32 rejects the last 3 bytes",
      (viewPacked (PackedCodec.decodeSlice (hs.drop 77)) : Option (UInt32 × List UInt8)) == none),
    ("packed UInt64 rejects the last 7 bytes",
      (viewPacked (PackedCodec.decodeSlice (cs.drop 136)) : Option (UInt64 × List UInt8)) == none),
    -- Packed codecs: encoding.
    ("packed UInt32 writes nTime", (PackedCodec.encode (1386325540 : UInt32)).toList == (h.drop 68).take 4),
    ("packed UInt64 writes nValue", (PackedCodec.encode (8800000000 : UInt64)).toList == (c.drop 63).take 8),
    ("packed UInt32 appends nNonce to the first 76 bytes",
      (PackedCodec.encodeInto (99943 : UInt32) (header.extract 0 76)).toList == h)]

/-- Every codec known answer. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let header ← parseHex headerHex
    let coinbase ← parseHex coinbaseHex
    if header.size != 80 then throw s!"header literal has {header.size} bytes, expected 80"
    if coinbase.size != 143 then throw s!"coinbase literal has {coinbase.size} bytes, expected 143"
    cases header coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL codec: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL codec {name}"
        failures := failures + 1
    IO.println s!"codec: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.Codec

/-!
## CompactSize: Core's `compactsize` and `noncanonical` tests

Known answers for the generic CompactSize codec and for Core's bounded reader, `decodeBounded`.
Each expected result comes from an assertion of Dogecoin Core's `src/test/serialize_tests.cpp` (SOURCES.md, D20), or from a reading of `src/serialize.h` (D1) and `src/streams.h` (D21).
None comes from the decoders under test.

- Boundary sweep, `compactsize` test, lines 231 to 242.
  Core writes `i - 1` and `i` for `i = 1, 2, 4, …, MAX_SIZE` into one stream, and asserts that `ReadCompactSize` reads them back in order.
  Here `encode` writes the same 52 values into one byte list.
  `decodeBounded` must read each value back in order, with the rest of the list as the remainder, and leave nothing at the end.
- Encoder bytes at the boundaries of the forms, derived from `WriteCompactSize`, `src/serialize.h` lines 219 to 242, and from the little-endian `ser_writedata16` to `ser_writedata64`.
- Non-canonical encodings, `noncanonical` test, lines 264 to 291.
  Core asserts the failure "non-canonical ReadCompactSize()" for six inputs, and the value `0xfd` for `fd fd 00`.
- Truncation. `ReadCompactSize` reads the marker and the payload through the stream (lines 247, 255, 261 and 267).
  `CDataStream::read` throws "end of data" when fewer bytes remain than it reads (`src/streams.h` lines 348 to 352).
- Values above `MAX_SIZE = 0x02000000` (`src/serialize.h` line 26).
  `ReadCompactSize` throws "size too large" at lines 271 and 272, after the check for a canonical encoding at lines 256, 262 and 268.
  So a non-canonical encoding of a value above `MAX_SIZE` is reported as non-canonical.

The generic decoder `decode` must accept the canonical encodings above `MAX_SIZE` that the bounded reader rejects.
The packed generic codec is checked on the same bytes, at a nonzero offset of the array.
-/

namespace KnownAnswers.CompactSize

open DogeLib.Serialization DogeLib.Serialization.CompactSize

/-- An expected result of `decodeBounded`: a value with its remainder, or an error. -/
inductive Expected where
  | ok (value : UInt64) (rest : List UInt8)
  | error (e : ReadError)

/-- Whether a result of `decodeBounded` is the expected result. -/
def Expected.matches : Expected → Except ReadError (UInt64 × List UInt8) → Bool
  | .ok v r, .ok (v', r') => v == v' && r == r'
  | .error e, .error e' => e == e'
  | _, _ => false

/-- The values of the boundary sweep of Core's `compactsize` test: `i - 1` and `i` for `i = 2 ^ 0, …, 2 ^ 25 = MAX_SIZE`, in Core's order. -/
def sweepValues : List UInt64 :=
  (List.range 26).flatMap fun k => [2 ^ k - 1, 2 ^ k]

/-- Reads `values.length` values from `bytes` with `decodeBounded`, as Core's loop does, and checks each value and remainder. Returns the names of the failed checks. -/
def readSweep (values : List UInt64) (bytes : List UInt8) : List String :=
  match values with
  | [] => if bytes.isEmpty then [] else ["sweep leaves bytes after the last value"]
  | v :: vs =>
    match decodeBounded bytes with
    | .ok (v', rest) =>
      (if v' == v then [] else [s!"sweep reads {v'}, expected {v}"]) ++ readSweep vs rest
    | .error _ => [s!"sweep rejects the encoding of {v}"]

/-- The checks on `decodeBounded`, each with its name, input and expected result. -/
def boundedCases : List (String × List UInt8 × Expected) := [
  -- noncanonical, lines 264 to 291.
  ("line 265: zero in three bytes", [0xfd, 0x00, 0x00], .error .nonCanonical),
  ("line 269: 0xfc in three bytes", [0xfd, 0xfc, 0x00], .error .nonCanonical),
  ("line 273: 0xfd in three bytes is OK", [0xfd, 0xfd, 0x00], .ok 0xfd []),
  ("line 278: zero in five bytes", [0xfe, 0x00, 0x00, 0x00, 0x00], .error .nonCanonical),
  ("line 282: 0xffff in five bytes", [0xfe, 0xff, 0xff, 0x00, 0x00], .error .nonCanonical),
  ("line 286: zero in nine bytes",
    [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], .error .nonCanonical),
  ("line 290: 0x01ffffff in nine bytes",
    [0xff, 0xff, 0xff, 0xff, 0x01, 0x00, 0x00, 0x00, 0x00], .error .nonCanonical),
  -- Remainder: the reader consumes only the encoding.
  ("0xfd in three bytes, then one more byte", [0xfd, 0xfd, 0x00, 0xab], .ok 0xfd [0xab]),
  ("252 in one byte, then one more byte", [0xfc, 0xfd], .ok 252 [0xfd]),
  -- Truncation: the stream ends before the marker or the payload.
  ("no bytes", [], .error .truncated),
  ("marker fd with no payload", [0xfd], .error .truncated),
  ("marker fd with 1 of 2 payload bytes", [0xfd, 0xfd], .error .truncated),
  ("marker fe with 3 of 4 payload bytes", [0xfe, 0x00, 0x00, 0x01], .error .truncated),
  ("marker ff with 7 of 8 payload bytes",
    [0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00], .error .truncated),
  -- MAX_SIZE, lines 26, 271 and 272.
  ("MAX_SIZE = 0x02000000 is accepted", [0xfe, 0x00, 0x00, 0x00, 0x02], .ok 0x02000000 []),
  ("0x02000001 is too large", [0xfe, 0x01, 0x00, 0x00, 0x02], .error .tooLarge),
  ("0xffffffff is too large", [0xfe, 0xff, 0xff, 0xff, 0xff], .error .tooLarge),
  ("0x100000000 is too large",
    [0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00], .error .tooLarge),
  ("0xffffffffffffffff is too large",
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], .error .tooLarge),
  ("0xffffffff in nine bytes is non-canonical, not too large",
    [0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00], .error .nonCanonical)]

/-- The checks on `encode`: a value and its bytes by `WriteCompactSize`. -/
def encodeCases : List (UInt64 × List UInt8) := [
  (0, [0x00]),
  (252, [0xfc]),
  (253, [0xfd, 0xfd, 0x00]),
  (0xffff, [0xfd, 0xff, 0xff]),
  (0x10000, [0xfe, 0x00, 0x00, 0x01, 0x00]),
  (0x02000000, [0xfe, 0x00, 0x00, 0x00, 0x02]),
  (0x02000001, [0xfe, 0x01, 0x00, 0x00, 0x02]),
  (0xffffffff, [0xfe, 0xff, 0xff, 0xff, 0xff]),
  (0x100000000, [0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]),
  (0xffffffffffffffff, [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff])]

/-- The checks on the generic decoders, each with its name and whether it holds. -/
def genericCases : List (String × Bool) :=
  let big := [0xfe, 0x01, 0x00, 0x00, 0x02, 0xab]
  let arr : ByteArray := ⟨#[0x00, 0x00] ++ big.toArray⟩
  [("generic decode accepts 0x02000001",
      decode big == some (0x02000001, [0xab])),
    ("generic decode accepts 0xffffffffffffffff",
      decode [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] == some (0xffffffffffffffff, [])),
    ("generic decode rejects zero in three bytes", decode [0xfd, 0x00, 0x00] == none),
    ("generic decode rejects marker fd with 1 of 2 payload bytes", decode [0xfd, 0xfd] == none),
    ("packed decode accepts 0x02000001 at offset 2",
      ((decodeSlice ((ByteSlice.ofByteArray arr).drop 2)).map fun p => (p.1, p.2.toList))
        == some (0x02000001, [0xab])),
    ("packed encode appends 0x02000001",
      (encodeInto 0x02000001 ⟨#[0x00, 0x00]⟩).toList == [0x00, 0x00, 0xfe, 0x01, 0x00, 0x00, 0x02])]

/-- Every CompactSize known answer. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  let mut count := 0
  -- The boundary sweep.
  if sweepValues.length != 52 then
    IO.eprintln s!"FAIL compactsize: the sweep has {sweepValues.length} values, expected 52"
    failures := failures + 1
  for name in readSweep sweepValues (sweepValues.flatMap encode) do
    IO.eprintln s!"FAIL compactsize {name}"
    failures := failures + 1
  count := count + 1
  for (name, input, expected) in boundedCases do
    count := count + 1
    if !expected.matches (decodeBounded input) then
      IO.eprintln s!"FAIL compactsize {name}"
      failures := failures + 1
  for (value, bytes) in encodeCases do
    count := count + 1
    if encode value != bytes then
      IO.eprintln s!"FAIL compactsize encode {value}: got {encode value}, expected {bytes}"
      failures := failures + 1
  for (name, ok) in genericCases do
    count := count + 1
    if !ok then
      IO.eprintln s!"FAIL compactsize {name}"
      failures := failures + 1
  IO.println s!"compactsize: {count} checks, {failures} failures"
  return failures

end KnownAnswers.CompactSize

/-!
## Counted lists: the scripts of the genesis coinbase, and Core's vector reader

Known answers for the generic counted-list codec, its packed forms, and Core's bounded reader `decodeBounded`.

The two scripts of the genesis coinbase are counted lists of bytes.
The input is the coinbase literal of the codec section, which that section checks against the merkle root that Core asserts (SOURCES.md, D9).
Each script is at its offset in the serialization order of a transaction (D4):

```text
coinbase  41        scriptSig count     = 0x10
coinbase  42..58    scriptSig           = 04ffff001d0104084e696e746f6e646f
coinbase  71        scriptPubKey count  = 0x43
coinbase  72..139   scriptPubKey        = 41 04…a9 ac
```

The other expected results come from a reading of `Unserialize_impl` and `ReadCompactSize` in `src/serialize.h` (D1), and of `CDataStream::read` in `src/streams.h` (D21):

- A count above `MAX_SIZE` is `tooLarge`, and no element is read (`ReadCompactSize`, lines 271 and 272).
- A non-canonical count is `nonCanonical` (lines 256, 262 and 268).
- A count of `MAX_SIZE` with no bytes after it is `truncated`, because the first block read fails (lines 667 to 673, and `CDataStream::read`).
- Too few elements is `truncated`.

The list of `UInt16` values `[1, 0x0302]` encodes as `02 01 00 02 03`, by `WriteCompactSize` (lines 219 to 242) and `ser_writedata16`.
-/

namespace KnownAnswers.CountedList

open DogeLib.Serialization DogeLib.Serialization.CountedList
open DogeLib.Serialization.CompactSize (ReadError)
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Codec (coinbaseHex)

/-- A decoder result with the counted list read as a list, for comparison. -/
def view {α : Type} (r : Option (CountedList α × List UInt8)) : Option (List α × List UInt8) :=
  r.map fun p => (p.1.val, p.2)

/-- A packed decoder result with the counted list and the remaining slice read as lists, for comparison. -/
def viewPacked {α : Type} (r : Option (CountedList α × ByteSlice)) : Option (List α × List UInt8) :=
  r.map fun p => (p.1.val, p.2.toList)

/-- A bounded reader result with the counted list read as a list, or `none` for any error, for comparison with an accepted result. -/
def viewBounded {α : Type} (r : Except ReadError (CountedList α × List UInt8)) :
    Option (List α × List UInt8) :=
  r.toOption.map fun p => (p.1.val, p.2)

/-- Whether a bounded result is the error `e`. -/
def isError {α : Type} (r : Except ReadError α) (e : ReadError) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

/-- A list of bytes as a counted list. The lists here are short, so the check never fails. -/
def counted (l : List UInt8) : CountedList UInt8 :=
  match CountedList.ofList? l with
  | some cl => cl
  | none => ⟨[], by decide⟩

/-- The checks on the coinbase literal and on short inputs, each with its name and whether it holds. -/
def cases (coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let c := coinbase.toList
  let cs := ByteSlice.ofByteArray coinbase
  let scriptSig := (← parseHex "04ffff001d0104084e696e746f6e646f").toList
  let scriptPubKey := (c.drop 72).take 67
  let readUInt16 : List UInt8 → Except ReadError (UInt16 × List UInt8) := fun bs =>
    match (Codec.decode bs : Option (UInt16 × List UInt8)) with
    | some p => .ok p
    | none => .error .truncated
  let maxSizeCount : List UInt8 := [0xfe, 0x00, 0x00, 0x00, 0x02]
  return [
    ("scriptSig count byte is 0x10", c[41]? == some 0x10),
    ("scriptPubKey count byte is 0x43 and ends with OP_CHECKSIG",
      c[71]? == some 0x43 && scriptPubKey.length == 67 && scriptPubKey.getLast? == some 0xac),
    -- The generic codec.
    ("generic decode reads scriptSig",
      view (Codec.decode (α := CountedList UInt8) (c.drop 41)) == some (scriptSig, c.drop 58)),
    ("generic decode reads scriptPubKey",
      view (Codec.decode (α := CountedList UInt8) (c.drop 71)) == some (scriptPubKey, c.drop 139)),
    ("generic encode writes scriptSig",
      Codec.encode (counted scriptSig) == (c.drop 41).take 17),
    ("generic encode writes scriptPubKey",
      Codec.encode (counted scriptPubKey) == (c.drop 71).take 68),
    ("generic decode reads scriptSig when it ends the input",
      view (Codec.decode (α := CountedList UInt8) ((c.drop 41).take 17)) == some (scriptSig, [])),
    ("generic decode rejects scriptSig without its last byte",
      view (Codec.decode (α := CountedList UInt8) ((c.drop 41).take 16)) == none),
    ("UInt16 list [1, 0x0302] encodes as 02 01 00 02 03",
      Codec.encode (α := CountedList UInt16) ⟨[1, 0x0302], by decide⟩ == [0x02, 0x01, 0x00, 0x02, 0x03]),
    ("UInt16 list decodes with a remainder",
      view (Codec.decode (α := CountedList UInt16) [0x02, 0x01, 0x00, 0x02, 0x03, 0xff])
        == some ([1, 0x0302], [0xff])),
    ("UInt16 list rejects a missing byte",
      view (Codec.decode (α := CountedList UInt16) [0x02, 0x01, 0x00, 0x02]) == none),
    ("generic decode reads count 0x02000001 and rejects the missing elements",
      view (Codec.decode (α := CountedList UInt8) [0xfe, 0x01, 0x00, 0x00, 0x02]) == none),
    -- The packed codecs, at nonzero offsets.
    ("packed byte decode reads scriptSig",
      viewPacked (PackedCodec.decodeSlice (α := CountedList UInt8) (cs.drop 41))
        == some (scriptSig, c.drop 58)),
    ("packed generic decode reads scriptPubKey",
      viewPacked (CountedList.decodeSlice (α := UInt8) (cs.drop 71)) == some (scriptPubKey, c.drop 139)),
    ("packed byte decode reads scriptPubKey when it ends the slice",
      viewPacked (PackedCodec.decodeSlice (α := CountedList UInt8) ((cs.drop 71).take 68))
        == some (scriptPubKey, [])),
    ("packed byte decode rejects scriptPubKey without its last byte",
      viewPacked (PackedCodec.decodeSlice (α := CountedList UInt8) ((cs.drop 71).take 67)) == none),
    ("packed byte encode appends scriptSig",
      (PackedCodec.encodeInto (counted scriptSig) (coinbase.extract 0 41)).toList == c.take 58),
    ("packed generic encode appends scriptPubKey",
      (CountedList.encodeInto (counted scriptPubKey) (coinbase.extract 0 71)).toList == c.take 139),
    -- Core's bounded reader.
    ("bounded reader reads scriptSig",
      viewBounded (decodeBoundedBytes (c.drop 41)) == some (scriptSig, c.drop 58)),
    ("bounded reader, one byte at a time, reads scriptPubKey",
      viewBounded (decodeBounded readByte (c.drop 71)) == some (scriptPubKey, c.drop 139)),
    ("bounded reader reads an empty list", viewBounded (decodeBoundedBytes [0x00, 0xab]) == some ([], [0xab])),
    ("bounded reader reads a list that ends the input",
      viewBounded (decodeBoundedBytes [0x03, 0x01, 0x02, 0x03]) == some ([0x01, 0x02, 0x03], [])),
    ("bounded reader reads scriptSig when it ends the input",
      viewBounded (decodeBoundedBytes ((c.drop 41).take 17)) == some (scriptSig, [])),
    ("bounded reader reads a UInt16 list",
      viewBounded (decodeBounded readUInt16 [0x02, 0x01, 0x00, 0x02, 0x03]) == some ([1, 0x0302], [])),
    ("count 0x02000001 is too large",
      isError (decodeBoundedBytes [0xfe, 0x01, 0x00, 0x00, 0x02]) .tooLarge),
    ("count 0x02000001 is too large for a UInt16 list",
      isError (decodeBounded readUInt16 [0xfe, 0x01, 0x00, 0x00, 0x02, 0x01, 0x00]) .tooLarge),
    ("count MAX_SIZE with no bytes is truncated", isError (decodeBoundedBytes maxSizeCount) .truncated),
    ("count MAX_SIZE with no bytes is truncated, one byte at a time",
      isError (decodeBounded readByte maxSizeCount) .truncated),
    ("non-canonical count 3 in three bytes",
      isError (decodeBoundedBytes [0xfd, 0x03, 0x00, 0x01, 0x02, 0x03]) .nonCanonical),
    ("count 3 with 2 bytes is truncated", isError (decodeBoundedBytes [0x03, 0x01, 0x02]) .truncated),
    ("scriptSig without its last byte is truncated",
      isError (decodeBoundedBytes ((c.drop 41).take 16)) .truncated),
    ("no bytes is truncated", isError (decodeBoundedBytes []) .truncated)]

/-- Every counted-list known answer. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let coinbase ← parseHex coinbaseHex
    if coinbase.size != 143 then throw s!"coinbase literal has {coinbase.size} bytes, expected 143"
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL countedlist: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL countedlist {name}"
        failures := failures + 1
    IO.println s!"countedlist: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.CountedList

/-!
## Difficulty retarget

Runs every `get_next_work_*` case of Dogecoin Core's `src/test/dogecoin_tests.cpp` at commit `e0a1c15` (SOURCES.md, D7) through the compiled `calculateDogecoinNextWorkRequired`.
Each case gives the last block's height, time and `nBits`, the first block time, the parameter set, and the expected `nBits`.
The inputs and the expected values are copied from the test file, with the line of each value.

## Compact encoding

Runs Core's `bignum_SetCompact` test of `src/test/arith_uint256_tests.cpp` at the same commit (SOURCES.md, D16) through the compiled `setCompact` and `getCompact`.
Each case gives the compact input, the value that `GetHex` shows, the expected `GetCompact` result and the two flags.
-/

namespace KnownAnswers.Work

open DogeLib.Work

/-- Eight lowercase hexadecimal digits of a 32-bit value. -/
def hex32 (n : UInt32) : String :=
  let digits := Nat.toDigits 16 n.toNat
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- One `get_next_work_*` case of `dogecoin_tests.cpp`. -/
structure RetargetCase where
  /-- The name of the Boost test case. -/
  name : String
  /-- The line of the `BOOST_CHECK_EQUAL` that states the expected value. -/
  line : Nat
  /-- The parameters that `Params().GetConsensus(h)` returns in the test. -/
  params : RetargetParams
  /-- `pindexLast.nHeight + 1`, the height of the next block. -/
  nHeight : Int32
  /-- `pindexLast.nTime`. -/
  nLastBlockTime : Int64
  /-- `nLastRetargetTime`, the time of the first block. -/
  nFirstBlockTime : Int64
  /-- `pindexLast.nBits`. -/
  nBits : UInt32
  /-- The expected result. -/
  expected : UInt32

/-- The six `get_next_work_*` cases of `src/test/dogecoin_tests.cpp` at `e0a1c15`.
`GetConsensus(0)` is `mainnetParams`, and `GetConsensus(145000)` is `mainnetDigishieldParams`. -/
def retargetCases : Array RetargetCase := #[
  -- Lines 123-135: GetConsensus(0), nLastRetargetTime 1386474927, nHeight 239.
  { name := "get_next_work_difficulty_limit", line := 134, params := mainnetParams,
    nHeight := 239 + 1, nLastBlockTime := 1386475638, nFirstBlockTime := 1386474927,
    nBits := 0x1e0ffff0, expected := 0x1e00ffff },
  -- Lines 137-149: GetConsensus(0), nLastRetargetTime 1386942008, nHeight 9599.
  { name := "get_next_work_pre_digishield", line := 148, params := mainnetParams,
    nHeight := 9599 + 1, nLastBlockTime := 1386954113, nFirstBlockTime := 1386942008,
    nBits := 0x1c1a1206, expected := 0x1c15ea59 },
  -- Lines 151-164: GetConsensus(145000), nLastRetargetTime 1395094427, nHeight 145000.
  { name := "get_next_work_digishield", line := 163, params := mainnetDigishieldParams,
    nHeight := 145000 + 1, nLastBlockTime := 1395094679, nFirstBlockTime := 1395094427,
    nBits := 0x1b499dfd, expected := 0x1b671062 },
  -- Lines 166-179: GetConsensus(145000), nLastRetargetTime 1395100835, nHeight 145107.
  { name := "get_next_work_digishield_modulated_upper", line := 178, params := mainnetDigishieldParams,
    nHeight := 145107 + 1, nLastBlockTime := 1395101360, nFirstBlockTime := 1395100835,
    nBits := 0x1b3439cd, expected := 0x1b4e56b3 },
  -- Lines 181-194: GetConsensus(145000), nLastRetargetTime 1395380517, nHeight 149423.
  -- The first block time is after the last, so the actual timespan is negative.
  { name := "get_next_work_digishield_modulated_lower", line := 193, params := mainnetDigishieldParams,
    nHeight := 149423 + 1, nLastBlockTime := 1395380447, nFirstBlockTime := 1395380517,
    nBits := 0x1b446f21, expected := 0x1b335358 },
  -- Lines 196-210: GetConsensus(145000), nLastRetargetTime 1395094679, nHeight 145001.
  { name := "get_next_work_digishield_rounding", line := 209, params := mainnetDigishieldParams,
    nHeight := 145001 + 1, nLastBlockTime := 1395094727, nFirstBlockTime := 1395094679,
    nBits := 0x1b671062, expected := 0x1b6558a4 }
]

/-- Runs every retarget case, and checks that there are six.
Returns the number of failures. -/
def checkRetarget : IO Nat := do
  let mut failures := 0
  if retargetCases.size != 6 then
    IO.eprintln s!"FAIL dogecoin_tests.cpp: {retargetCases.size} retarget cases, expected 6"
    failures := failures + 1
  for c in retargetCases do
    let got := calculateDogecoinNextWorkRequired c.params c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    if got != c.expected then
      IO.eprintln s!"FAIL dogecoin_tests.cpp:{c.line} {c.name}: got {hex32 got}, expected {hex32 c.expected}"
      failures := failures + 1
  IO.println s!"dogecoin_tests.cpp get_next_work_*: {retargetCases.size} cases, {failures} failures"
  return failures

/-- One step of `bignum_SetCompact` in `arith_uint256_tests.cpp`. -/
structure CompactCase where
  /-- The line of the `SetCompact` call, or of the assignment for the case without one. -/
  line : Nat
  /-- The input: a compact for `SetCompact`, or `none` when the test assigns `value` directly. -/
  nCompact : Option UInt32
  /-- The value that `GetHex` shows, or `none` when the test does not check it. -/
  value : Option Nat
  /-- The argument that the test passes to `GetCompact`. -/
  negativeArgument : Bool
  /-- The expected `GetCompact` result, or `none` when the test does not check it. -/
  compact : Option UInt32
  /-- The expected `*pfNegative`, or `none` without a `SetCompact` call. -/
  fNegative : Option Bool
  /-- The expected `*pfOverflow`, or `none` without a `SetCompact` call. -/
  fOverflow : Option Bool

/-- Every step of `bignum_SetCompact`, lines 412-538 of `src/test/arith_uint256_tests.cpp` at `e0a1c15`. -/
def compactCases : Array CompactCase := #[
  ⟨417, some 0x00000000, some 0, false, some 0, some false, some false⟩,
  ⟨423, some 0x00123456, some 0, false, some 0, some false, some false⟩,
  ⟨429, some 0x01003456, some 0, false, some 0, some false, some false⟩,
  ⟨435, some 0x02000056, some 0, false, some 0, some false, some false⟩,
  ⟨441, some 0x03000000, some 0, false, some 0, some false, some false⟩,
  ⟨447, some 0x04000000, some 0, false, some 0, some false, some false⟩,
  ⟨453, some 0x00923456, some 0, false, some 0, some false, some false⟩,
  ⟨459, some 0x01803456, some 0, false, some 0, some false, some false⟩,
  ⟨465, some 0x02800056, some 0, false, some 0, some false, some false⟩,
  ⟨471, some 0x03800000, some 0, false, some 0, some false, some false⟩,
  ⟨477, some 0x04800000, some 0, false, some 0, some false, some false⟩,
  ⟨483, some 0x01123456, some 0x12, false, some 0x01120000, some false, some false⟩,
  -- Line 490 assigns `num = 0x80` with no `SetCompact` call.
  ⟨490, none, some 0x80, false, some 0x02008000, none, none⟩,
  ⟨493, some 0x01fedcba, some 0x7e, true, some 0x01fe0000, some true, some false⟩,
  ⟨499, some 0x02123456, some 0x1234, false, some 0x02123400, some false, some false⟩,
  ⟨505, some 0x03123456, some 0x123456, false, some 0x03123456, some false, some false⟩,
  ⟨511, some 0x04123456, some 0x12345600, false, some 0x04123456, some false, some false⟩,
  ⟨517, some 0x04923456, some 0x12345600, true, some 0x04923456, some true, some false⟩,
  ⟨523, some 0x05009234, some 0x92340000, false, some 0x05009234, some false, some false⟩,
  ⟨529, some 0x20123456,
    some 0x1234560000000000000000000000000000000000000000000000000000000000, false,
    some 0x20123456, some false, some false⟩,
  ⟨535, some 0xff123456, none, false, none, some false, some true⟩
]

/-- Runs every compact case, and checks that there are twenty-one.
Returns the number of failures. -/
def checkCompact : IO Nat := do
  let mut failures := 0
  if compactCases.size != 21 then
    IO.eprintln s!"FAIL arith_uint256_tests.cpp: {compactCases.size} compact cases, expected 21"
    failures := failures + 1
  for c in compactCases do
    let (value, flags) := match c.nCompact with
      | some n =>
        let r := ArithUint256.setCompact n
        (r.value, some (r.fNegative, r.fOverflow))
      | none => (ArithUint256.ofNat (c.value.getD 0), none)
    let mut ok := true
    if let some v := c.value then
      if value.val != v then ok := false
    if let some e := c.compact then
      if ArithUint256.getCompact value c.negativeArgument != e then ok := false
    if let some (neg, ovf) := flags then
      if c.fNegative != some neg || c.fOverflow != some ovf then ok := false
    if !ok then
      IO.eprintln s!"FAIL arith_uint256_tests.cpp:{c.line}: value {value.val}, flags {flags}"
      failures := failures + 1
  IO.println s!"arith_uint256_tests.cpp bignum_SetCompact: {compactCases.size} cases, {failures} failures"
  return failures

end KnownAnswers.Work

/-- Entry point of `lake test`. -/
def main : IO UInt32 := do
  let dir : System.FilePath := "tests/cryptography/sha256/cavp"
  let short ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256ShortMsg.rsp") 65
  let long ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256LongMsg.rsp") 64
  let genesis ← KnownAnswers.Genesis.check
  let codec ← KnownAnswers.Codec.check
  let compactSize ← KnownAnswers.CompactSize.check
  let countedList ← KnownAnswers.CountedList.check
  let compact ← KnownAnswers.Work.checkCompact
  let retarget ← KnownAnswers.Work.checkRetarget
  return if short + long + genesis + codec + compactSize + countedList + compact + retarget == 0 then 0 else 1
