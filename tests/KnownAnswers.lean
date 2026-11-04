import DogeLib.Cryptography.Hash.Sha256
import DogeLib.Cryptography.Hash.Sha256d
import DogeLib.Serialization
import DogeLib.Transaction
import DogeLib.Work
import Lean.Data.Json

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
  -- The same cases through the packed reader, at offset 3 of a buffer.
  for (name, input, expected) in boundedCases do
    count := count + 1
    let buf : ByteArray := ⟨#[0xaa, 0xbb, 0xcc] ++ input.toArray⟩
    let got := (decodeBoundedSlice ((ByteSlice.ofByteArray buf).drop 3)).map fun p => (p.1, p.2.toList)
    if !expected.matches got then
      IO.eprintln s!"FAIL compactsize packed {name}"
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

Long lists (issue #19): a count of `longCount` elements, read by the three readers that read one element at a time.
Each must return that many elements with no remainder.
With one byte fewer, each must fail as a short list fails: `none`, or `truncated` from `decodeBounded`.

These checks test the results of the loop forms on long lists. They do not detect a return to the recursive forms.
In this compiled driver, the recursive forms read 8,000,000 elements and overflowed the stack at 16,000,000, where the loop forms passed.
A count that large needs about 4 GB, more than CI should spend, and `MAX_SIZE` itself is not tested.
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

/-- The count of the long-list checks. It keeps the memory of `lake test` near 1 GB. -/
def longCount : Nat := 3000000

/-- The long-list checks, each with its name and whether it holds. They run one at a time. -/
def longCases : List (String × (Unit → Bool)) := [
  ("generic codec reads a long list", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate longCount 7
    match Codec.decode (α := CountedList UInt8) bs with
    | some (cl, []) => cl.val.length == longCount
    | _ => false),
  ("generic codec rejects a long list one byte short", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate (longCount - 1) 7
    (Codec.decode (α := CountedList UInt8) bs).isNone),
  ("decodeBounded readByte reads a long list", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate longCount 7
    match decodeBounded readByte bs with
    | .ok (cl, []) => cl.val.length == longCount
    | _ => false),
  ("decodeBounded readByte: a long list one byte short is truncated", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate (longCount - 1) 7
    isError (decodeBounded readByte bs) .truncated),
  ("packed codec reads a long UInt16 list", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate (2 * longCount) 7
    match PackedCodec.decodeSlice (α := CountedList UInt16) (ByteSlice.ofByteArray ⟨bs.toArray⟩) with
    | some (cl, rest) => cl.val.length == longCount && rest.toList.isEmpty
    | none => false),
  ("packed codec rejects a long UInt16 list one byte short", fun _ =>
    let bs := CompactSize.encode (UInt64.ofNat longCount) ++ List.replicate (2 * longCount - 1) 7
    (PackedCodec.decodeSlice (α := CountedList UInt16) (ByteSlice.ofByteArray ⟨bs.toArray⟩)).isNone)]

/-- Every counted-list known answer. Returns the number of failures. -/
def check : IO Nat := do
  let mut longFailures := 0
  for (name, run) in longCases do
    if !run () then
      IO.eprintln s!"FAIL countedlist {name}"
      longFailures := longFailures + 1
  IO.println s!"countedlist: {longCases.length} long-list checks of {longCount} elements, {longFailures} failures"
  let result := do
    let coinbase ← parseHex coinbaseHex
    if coinbase.size != 143 then throw s!"coinbase literal has {coinbase.size} bytes, expected 143"
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL countedlist: {e}"
    return 1 + longFailures
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL countedlist {name}"
        failures := failures + 1
    IO.println s!"countedlist: {cs.length} checks, {failures} failures"
    return failures + longFailures

end KnownAnswers.CountedList

/-!
## Transactions: the genesis coinbase, and Core's base-mode reader

Known answers for the base serialization of a transaction, its packed codec, Core's base-mode reader `readBase`, the complete reader, and the transaction ID.

The genesis coinbase is the literal of the codec section, which that section checks against the merkle root that Core asserts (SOURCES.md, D9).
Its expected fields are the arguments of `CreateGenesisBlock` in `src/chainparams.cpp` (D9):

- Version 1 and lock time 0.
- One input with the null outpoint (`COutPoint::SetNull`, D4), the scriptSig of the coinbase, and sequence `0xffffffff`.
- One output of `88 * COIN` with the scriptPubKey.

Its transaction ID must be the merkle root, because a block with one transaction has that transaction's ID as its merkle root.

The short inputs are built by hand.
Their expected results come from a reading of `UnserializeTransaction` and the `SerializationOp` methods in `src/primitives/transaction.h` (D4), with `ReadCompactSize` (D1) and `CDataStream::read` (D21).
In base mode Core reads `nVersion`, `vin`, `vout` and `nLockTime` in this order, and stops at the first failure:

- A transaction with no inputs is read as such. In base mode there is no flags byte.
- Counts above `MAX_SIZE` are `tooLarge`, and non-canonical counts are `nonCanonical`, for the inputs, the outputs and both scripts.
- When a script count is non-canonical and the output count after it is too large, the error is `nonCanonical`, the first in read order.
- Input that ends inside the outpoint, or before the lock time, is `truncated`.
- Versions and amounts with the high bit set are read and written again without change. Their signed values are the two's-complement values.
-/

namespace KnownAnswers.Transactions

open DogeLib DogeLib.Serialization DogeLib.Transaction
open DogeLib.Serialization.CompactSize (ReadError)
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Codec (coinbaseHex)
open KnownAnswers.Genesis (ofDisplay merkleRoot)
open KnownAnswers.CountedList (isError)

/-- A list as a counted list. The lists here are short, so the check never fails. -/
def countedOf {α : Type} (l : List α) : CountedList α :=
  match CountedList.ofList? l with
  | some cl => cl
  | none => ⟨[], by simp⟩

/-- A script with these bytes. -/
def script (bs : List UInt8) : Script := ⟨countedOf bs⟩

/-- `n` as `w` little-endian bytes. -/
def le (w : Nat) (n : Nat) : List UInt8 := (List.range w).map fun i => (n >>> (8 * i)).toUInt8

/-- The 36 bytes of an outpoint with hash bytes `1, 2, …, 32` and index 7. -/
def outpointBytes : List UInt8 := (List.range 32).map (fun i => (i + 1).toUInt8) ++ le 4 7

/-- Version 1. -/
def ver : List UInt8 := le 4 1

/-- The count `0x02000001`, one above `MAX_SIZE`. -/
def tooBig : List UInt8 := [0xfe, 0x01, 0x00, 0x00, 0x02]

/-- A transaction with version bits `v`, no inputs, one output of value bits `value` with an empty script, and lock time 0. -/
def noInputs (v : Nat) (value : Nat) : List UInt8 :=
  le 4 v ++ [0x00] ++ [0x01] ++ le 8 value ++ [0x00] ++ le 4 0

/-- Whether `readBase` reads all of `bs` as a transaction that `check` accepts, and the codec writes `bs` again. -/
def readsBack (bs : List UInt8) (check : Transaction → Bool) : Bool :=
  match Transaction.readBase bs with
  | .ok (tx, []) => check tx && Codec.encode tx == bs
  | _ => false

/-- The checks on the genesis coinbase and on short inputs, each with its name and whether it holds. -/
def cases (coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let c := coinbase.toList
  let root ← ofDisplay merkleRoot
  let scriptSig := (← parseHex "04ffff001d0104084e696e746f6e646f").toList
  let key ← parseHex "040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9"
  let scriptPubKey := [0x41] ++ key.toList ++ [0xac]
  let genesis : Transaction := {
    version := 1
    inputs := countedOf [{ prevout := OutPoint.null, scriptSig := script scriptSig, sequence := 0xffffffff }]
    outputs := countedOf [{ value := 8800000000, scriptPubKey := script scriptPubKey }]
    lockTime := 0 }
  let padded : ByteArray := ⟨#[0xaa, 0xbb, 0xcc]⟩ ++ coinbase
  return [
    -- The genesis coinbase.
    ("generic codec reads the genesis coinbase", Codec.decode c == some (genesis, [])),
    ("generic codec writes the genesis coinbase", Codec.encode genesis == c),
    ("readBase reads the genesis coinbase", (Transaction.readBase c).toOption == some (genesis, [])),
    ("complete reader reads the genesis coinbase", (Transaction.decodeBaseComplete c).toOption == some genesis),
    ("packed codec reads the genesis coinbase at offset 3",
      ((PackedCodec.decodeSlice (α := Transaction) ((ByteSlice.ofByteArray padded).drop 3)).map
        fun p => (p.1, p.2.toList)) == some (genesis, [])),
    ("packed codec writes the genesis coinbase", (PackedCodec.encode genesis).toList == c),
    ("txid of the genesis coinbase is the merkle root", genesis.txid.val == root.toList),
    ("txid in display order", genesis.txid.displayBytes == root.toList.reverse),
    ("genesis amount is 88 * COIN", genesis.outputs.val.map (·.amount) == [8800000000]),
    ("complete reader reports one trailing byte",
      match Transaction.decodeBaseComplete (c ++ [0x00]) with
      | .error (.trailingBytes 1) => true
      | _ => false),
    ("readBase keeps one trailing byte", (Transaction.readBase (c ++ [0x00])).toOption == some (genesis, [0x00])),
    ("genesis coinbase without its last byte is truncated", isError (Transaction.readBase (c.take 142)) .truncated),
    -- No inputs, base mode.
    ("a transaction with no inputs is read in base mode",
      readsBack (noInputs 1 0) fun tx => tx.inputs.val.isEmpty && tx.outputs.val.length == 1),
    -- Counts, in read order.
    ("input count above MAX_SIZE is tooLarge", isError (Transaction.readBase (ver ++ tooBig)) .tooLarge),
    ("input count non-canonical", isError (Transaction.readBase (ver ++ [0xfd, 0x01, 0x00])) .nonCanonical),
    ("scriptSig count above MAX_SIZE is tooLarge",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes ++ tooBig)) .tooLarge),
    ("scriptSig count non-canonical",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes ++ [0xfd, 0x00, 0x00])) .nonCanonical),
    ("output count above MAX_SIZE is tooLarge", isError (Transaction.readBase (ver ++ [0x00] ++ tooBig)) .tooLarge),
    ("output count non-canonical",
      isError (Transaction.readBase (ver ++ [0x00] ++ [0xfd, 0x02, 0x00])) .nonCanonical),
    ("scriptPubKey count above MAX_SIZE is tooLarge",
      isError (Transaction.readBase (ver ++ [0x00, 0x01] ++ le 8 0 ++ tooBig)) .tooLarge),
    ("scriptPubKey count non-canonical",
      isError (Transaction.readBase (ver ++ [0x00, 0x01] ++ le 8 0 ++ [0xfd, 0x00, 0x00])) .nonCanonical),
    ("non-canonical scriptSig before a too-large output count is nonCanonical",
      isError (Transaction.readBase
        (ver ++ [0x01] ++ outpointBytes ++ [0xfd, 0x00, 0x00] ++ le 4 0 ++ tooBig)) .nonCanonical),
    ("input that ends inside the outpoint is truncated",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes.take 20)) .truncated),
    ("missing lock time is truncated", isError (Transaction.readBase ((noInputs 1 0).take 15)) .truncated),
    ("three bytes of lock time is truncated", isError (Transaction.readBase ((noInputs 1 0).take 18)) .truncated),
    -- Signed fields: the bits are kept.
    ("version 0xffffffff is read and written again, signed -1",
      readsBack (noInputs 0xffffffff 0) fun tx => tx.signedVersion == -1),
    ("version 0x80000000 is read and written again, signed -2^31",
      readsBack (noInputs 0x80000000 0) fun tx => tx.signedVersion.toInt == -2147483648),
    ("amount 0xffffffffffffffff is read and written again, signed -1",
      readsBack (noInputs 1 0xffffffffffffffff) fun tx => tx.outputs.val.map (·.amount) == [-1]),
    ("amount 0x8000000000000000 is read and written again, signed -2^63",
      readsBack (noInputs 1 0x8000000000000000) fun tx =>
        tx.outputs.val.map (·.amount.toInt) == [-9223372036854775808])]

/-- Every transaction known answer. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let coinbase ← parseHex coinbaseHex
    if coinbase.size != 143 then throw s!"coinbase literal has {coinbase.size} bytes, expected 143"
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL transactions: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL transactions {name}"
        failures := failures + 1
    IO.println s!"transactions: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.Transactions

/-!
## Transactions: the witness-allowed format

Known answers for `Transaction.readAllowWitness`, the complete reader, the writer and the witness hash.
They model a serialization format only. Segregated witness is not active on Dogecoin's main or test network at the pin.

The inputs are built by hand.
Their expected results come from a reading of `UnserializeTransaction` and `SerializeTransaction` in `src/primitives/transaction.h`, lines 211 to 272 (D4), with `ReadCompactSize` (D1) and `CDataStream::read` (D21):

- After the version, an input count of zero is followed by a flags byte. Flags zero end the transaction before the lock time, with no outputs.
- With flags that are not zero, Core reads the inputs and the outputs. If bit 0 is set, it reads one stack per input.
- Only then does it reject any other flag bit, before it reads the lock time.
  So a read error in the lists or the stacks comes first, and a missing lock time does not hide the flags error.
- A stack with one empty item counts as witness data. A section of empty stacks does not, and the writer then uses the base form.

The witness hash of the genesis coinbase, which has no witness data, is its transaction ID, the merkle root that Core asserts (D9).
-/

namespace KnownAnswers.Witness

open DogeLib DogeLib.Serialization DogeLib.Transaction
open DogeLib.Serialization.CompactSize (ReadError)
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Codec (coinbaseHex)
open KnownAnswers.Genesis (ofDisplay merkleRoot)
open KnownAnswers.Transactions (le outpointBytes ver tooBig)

/-- An input with the outpoint of `outpointBytes`, an empty script and sequence `0xffffffff`. -/
def input0 : List UInt8 := outpointBytes ++ [0x00] ++ le 4 0xffffffff

/-- An output of value 0 with an empty script. -/
def output0 : List UInt8 := le 8 0 ++ [0x00]

/-- A stack with one item of one byte, `ab`. -/
def stack1 : List UInt8 := [0x01, 0x01, 0xab]

/-- Lock time 0. -/
def lock : List UInt8 := le 4 0

/-- The extended form with these flags, one input, one output and these stack bytes, without the lock time. -/
def extended (flags : UInt8) (stacks : List UInt8) : List UInt8 :=
  ver ++ [0x00, flags] ++ [0x01] ++ input0 ++ [0x01] ++ output0 ++ stacks

/-- The base form of the transaction with one input and one output. -/
def base : List UInt8 := ver ++ [0x01] ++ input0 ++ [0x01] ++ output0 ++ lock

/-- Whether the reader fails on `bs` with error `e`. -/
def isError (bs : List UInt8) (e : WitnessReadError) : Bool :=
  match Transaction.readAllowWitness bs with
  | .error e' => e' == e
  | .ok _ => false

/-- Whether the reader reads `bs` as a transaction and remainder that `check` accepts. -/
def reads (bs : List UInt8) (check : WitnessTransaction → List UInt8 → Bool) : Bool :=
  match Transaction.readAllowWitness bs with
  | .ok (w, rest) => check w rest
  | .error _ => false

/-- The checks, each with its name and whether it holds. -/
def cases (coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let root ← ofDisplay merkleRoot
  return [
    -- Zero flags.
    ("zero count, zero flags and a lock time: no inputs, no outputs",
      reads (ver ++ [0x00, 0x00] ++ lock) fun w rest =>
        w.tx.inputs.val.isEmpty && w.tx.outputs.val.isEmpty && w.witnesses.isEmpty && rest.isEmpty),
    ("zero count, zero flags, no lock time: truncated", isError (ver ++ [0x00, 0x00]) (.read .truncated)),
    ("zero count and no flags byte: truncated", isError (ver ++ [0x00]) (.read .truncated)),
    -- Flag bit 0.
    ("flags 01 with one stack: read, witness data, written again",
      reads (extended 0x01 stack1 ++ lock) fun w rest =>
        w.hasWitness && rest.isEmpty && w.encode == extended 0x01 stack1 ++ lock),
    ("flags 01 with zero inputs: no stacks, written in the base form",
      reads (ver ++ [0x00, 0x01, 0x00, 0x01] ++ output0 ++ lock) fun w rest =>
        !w.hasWitness && w.witnesses.isEmpty && rest.isEmpty &&
          w.encode == ver ++ [0x00, 0x01] ++ output0 ++ lock),
    ("a stack with one empty item is witness data",
      reads (extended 0x01 [0x01, 0x00] ++ lock) fun w _ =>
        w.hasWitness && w.encode == extended 0x01 [0x01, 0x00] ++ lock),
    ("a section of empty stacks is read, and written in the base form",
      reads (extended 0x01 [0x00] ++ lock) fun w _ => !w.hasWitness && w.encode == base),
    ("flags 01, lock time missing: truncated", isError (extended 0x01 stack1) (.read .truncated)),
    ("flags 01, stack truncated: truncated", isError (extended 0x01 [0x01, 0x05, 0xab]) (.read .truncated)),
    ("flags 01, stack count non-canonical",
      isError (extended 0x01 [0xfd, 0x01, 0x00, 0x01, 0xab] ++ lock) (.read .nonCanonical)),
    ("flags 01, stack count above MAX_SIZE: tooLarge", isError (extended 0x01 tooBig) (.read .tooLarge)),
    ("flags 01, item length above MAX_SIZE: tooLarge", isError (extended 0x01 ([0x01] ++ tooBig)) (.read .tooLarge)),
    -- Other flag bits.
    ("flags 02, complete: unknownOptionalData", isError (extended 0x02 [] ++ lock) .unknownOptionalData),
    ("flags 02, lock time missing: unknownOptionalData", isError (extended 0x02 []) .unknownOptionalData),
    ("flags 02, outputs truncated: truncated, before the flags",
      isError (ver ++ [0x00, 0x02, 0x01] ++ input0 ++ [0x01] ++ output0.take 4) (.read .truncated)),
    ("flags 03, complete with a stack: unknownOptionalData", isError (extended 0x03 stack1 ++ lock) .unknownOptionalData),
    ("flags 03, a stack, lock time missing: unknownOptionalData", isError (extended 0x03 stack1) .unknownOptionalData),
    ("flags ff, complete with a stack: unknownOptionalData", isError (extended 0xff stack1 ++ lock) .unknownOptionalData),
    ("flags 03, stack truncated: truncated, before the flags",
      isError (extended 0x03 [0x01, 0x05, 0xab]) (.read .truncated)),
    ("flags 03, stack count non-canonical: nonCanonical, before the flags",
      isError (extended 0x03 [0xfd, 0x01, 0x00, 0x01, 0xab] ++ lock) (.read .nonCanonical)),
    ("flags 03, item length above MAX_SIZE: tooLarge, before the flags",
      isError (extended 0x03 ([0x01] ++ tooBig)) (.read .tooLarge)),
    -- Remainders.
    ("one trailing byte: the prefix reader keeps it",
      reads (extended 0x01 stack1 ++ lock ++ [0x00]) fun _ rest => rest == [0x00]),
    ("one trailing byte: the complete reader reports it",
      match Transaction.decodeAllowWitnessComplete (extended 0x01 stack1 ++ lock ++ [0x00]) with
      | .error (.trailingBytes 1) => true
      | _ => false),
    -- The witness hash.
    ("the genesis coinbase has no witness data, and its witness hash is its ID",
      match Transaction.decodeAllowWitnessComplete coinbase.toList with
      | .ok w => !w.hasWitness && w.wtxid.val == root.toList
      | .error _ => false)]

/-- Every known answer of the witness-allowed format. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let coinbase ← parseHex coinbaseHex
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL witness format: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL witness format {name}"
        failures := failures + 1
    IO.println s!"witness format: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.Witness

/-!
## Core's transaction corpus

Runs the serialized transactions of Core's `src/test/data/tx_valid.json` and `tx_invalid.json` at commit `e0a1c15` (SOURCES.md, D28 and D29), vendored in `tests/transaction/corpus/`, through the compiled base-mode reader and codec.

Core's `transaction_tests.cpp` (D30, lines 151 and 236) reads each one with witness data allowed, and then checks the scripts.
So a record of `tx_invalid.json` is a transaction that Core reads and then rejects for another reason. It is not a parser rejection.
Script validity is not checked here.

A record is in base mode when byte 4 of its transaction, the first byte of the input count, is not `00`.
`UnserializeTransaction` (D4, lines 219 to 230) reads a flags byte only after an empty input list.
So for these records, Core's reading with witness data allowed is the base reading.
The rule reads raw bytes, not DogeLib's reader. The other records use the witness-allowed format.

For each base-mode record, the test checks five things. `readBase` reads the whole transaction, `decodeBaseComplete` accepts it, the codec writes the same bytes again, and the packed codec reads the same transaction.
`readAllowWitness` reads the same transaction, with an empty stack for each input.

For each record in the witness-allowed format, `decodeAllowWitnessComplete` must read the whole transaction, and `WitnessTransaction.encode` must write the same bytes again.
Each of these records has a stack that is not empty, so the writer uses the extended form. The test checks that too.
The format is only a serialization format here. Segregated witness is not active on Dogecoin's main or test network at the pin.

Core's harness checks none of these directly. They are DogeLib's checks on Core's bytes, not a comparison with a running Core.
-/

namespace KnownAnswers.TxCorpus

open DogeLib DogeLib.Serialization DogeLib.Transaction
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- The serialized transactions of the records of a corpus file. Fails on a record of another shape or on bad hexadecimal digits. -/
def parseCorpus (text : String) : Except String (Array (List UInt8)) := do
  let json ← Lean.Json.parse text
  let rows ← json.getArr?
  let mut out := #[]
  for row in rows do
    let fields ← row.getArr?
    if fields.size == 1 then
      let _ ← fields[0]!.getStr?
      continue
    if fields.size != 3 then throw s!"record with {fields.size} fields: {row.compress}"
    let _ ← fields[0]!.getArr?
    let _ ← fields[2]!.getStr?
    out := out.push (← parseHex (← fields[1]!.getStr?)).toList
  return out

/-- Checks one corpus file, which must hold `base` base-mode records and `witness` other records. Returns the number of failures. -/
def checkFile (path : System.FilePath) (base witness : Nat) : IO Nat := do
  let txs ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  let mut nBase := 0
  let mut nWitness := 0
  for bs in txs do
    if bs.length < 5 then
      IO.eprintln s!"FAIL {path}: transaction shorter than 5 bytes: {toHex ⟨bs.toArray⟩}"
      failures := failures + 1
    else if bs[4]! == 0x00 then
      nWitness := nWitness + 1
      match Transaction.decodeAllowWitnessComplete bs with
      | .ok w =>
        if !w.hasWitness || w.encode != bs then
          IO.eprintln s!"FAIL {path}: witness record not written again in the extended form: {toHex ⟨bs.toArray⟩}"
          failures := failures + 1
      | .error _ =>
        IO.eprintln s!"FAIL {path}: decodeAllowWitnessComplete does not read the witness record {toHex ⟨bs.toArray⟩}"
        failures := failures + 1
    else
      nBase := nBase + 1
      let read := match Transaction.readBase bs with
        | .ok (tx, []) => some tx
        | _ => none
      match read with
      | none =>
        IO.eprintln s!"FAIL {path}: readBase does not read the whole transaction {toHex ⟨bs.toArray⟩}"
        failures := failures + 1
      | some tx =>
        let complete := match Transaction.decodeBaseComplete bs with
          | .ok tx' => tx' == tx
          | .error _ => false
        let packed := (PackedCodec.decodeSlice (α := Transaction) (ByteSlice.ofByteArray ⟨bs.toArray⟩)).map
          fun p => (p.1, p.2.toList)
        let allowWitness := match Transaction.readAllowWitness bs with
          | .ok (w, []) => w == WitnessTransaction.ofBase tx
          | _ => false
        if !complete || Codec.encode tx != bs || packed != some (tx, []) || !allowWitness then
          IO.eprintln s!"FAIL {path}: complete reader, codec, packed codec or witness-allowed reader disagrees on {toHex ⟨bs.toArray⟩}"
          failures := failures + 1
  if nBase != base || nWitness != witness then
    IO.eprintln s!"FAIL {path}: {nBase} base-mode and {nWitness} witness records, expected {base} and {witness}"
    failures := failures + 1
  IO.println s!"{path}: {nBase} base-mode and {nWitness} witness-format records read and written again, {failures} failures"
  return failures

/-- Both corpus files. Returns the number of failures. -/
def check : IO Nat := do
  let valid ← checkFile "tests/transaction/corpus/tx_valid.json" 91 27
  let invalid ← checkFile "tests/transaction/corpus/tx_invalid.json" 68 12
  return valid + invalid

end KnownAnswers.TxCorpus

/-!
## Legacy signature hash

Two kinds of known answer, both run through the compiled `legacySignatureHash` and `legacyPreimage`.

The first is Core's corpus `src/test/data/sighash.json` at commit `e0a1c15` (SOURCES.md, D26), vendored in `tests/transaction/sighash/`.
Core's `sighash_from_data` reads each transaction with witness data allowed.
Every record's transaction has at least one input, and then that reader reads what the base reader reads (D4, lines 218 to 241).
The test checks that each transaction has an input and is read whole by `decodeBaseComplete`.
The corpus gives digests only, so it does not check preimages.

The second is a set of preimages derived by hand from `CTransactionSignatureSerializer` and `SignatureHash` (D3, lines 1054 to 1246) and `GetOp2` (D24).
Each expected byte string is written out field by field below, not computed with DogeLib's functions.

Both kinds also run through `legacyReferencePlan`, the transformation of `SignatureHashOld` (D2, lines 28 to 88).
The two plans must give the same answers, except on a script that ends in a short push.
There `SignatureHashOld` keeps the whole push, and its expected preimage is derived by hand from `FindAndDelete` (D24, lines 570 to 596).
-/

namespace KnownAnswers.LegacySighash

open DogeLib DogeLib.Serialization DogeLib.Transaction
open KnownAnswers.Sha256Cavp (parseHex toHex)
open KnownAnswers.Transactions (countedOf script le)

/-- One record of the corpus. -/
structure Record where
  tx : List UInt8
  script : List UInt8
  nIn : Int
  hashType : Int
  display : List UInt8

/-- The 32 bits of an `int` value, as Core stores them. -/
def bits32 (i : Int) : UInt32 := (i % 2 ^ 32).toNat.toUInt32

/-- The records of the corpus, after its comment. Fails on a record that is not a comment or a five-field record. -/
def parseCorpus (text : String) : Except String (Array Record) := do
  let json ← Lean.Json.parse text
  let rows ← json.getArr?
  let mut out := #[]
  for row in rows do
    let fields ← row.getArr?
    if fields.size == 1 then continue
    if fields.size != 5 then throw s!"record with {fields.size} fields: {row.compress}"
    out := out.push {
      tx := (← parseHex (← fields[0]!.getStr?)).toList
      script := (← parseHex (← fields[1]!.getStr?)).toList
      nIn := ← fields[2]!.getInt?
      hashType := ← fields[3]!.getInt?
      display := (← parseHex (← fields[4]!.getStr?)).toList }
  return out

/-- Runs every corpus record. Returns the number of failures. -/
def checkCorpus (path : System.FilePath) : IO Nat := do
  let records ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  let mut fixed := 0
  let mut unparsed := 0
  if records.size != 500 then
    IO.eprintln s!"FAIL {path}: {records.size} records, expected 500"
    failures := failures + 1
  for r in records do
    match Transaction.decodeBaseComplete r.tx, CountedList.ofList? r.script with
    | .ok tx, some sc =>
      if tx.inputs.val.isEmpty || r.nIn < 0 || r.nIn ≥ 2 ^ 32 then
        IO.eprintln s!"FAIL {path}: record outside the tested domain: {toHex ⟨r.tx.toArray⟩}"
        failures := failures + 1
      else
        let plan := legacySignatureHashPlan ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)
        if plan matches .fixedDigest _ then fixed := fixed + 1
        let got := (legacySignatureHash ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)).displayBytes
        if got != r.display then
          IO.eprintln s!"FAIL {path}: nIn {r.nIn}, hashType {r.hashType}: got {toHex ⟨got.toArray⟩}, expected {toHex ⟨r.display.toArray⟩}"
          failures := failures + 1
        -- The transformation reference, SignatureHashOld.
        if !(scanOps r.script).2.isEmpty then unparsed := unparsed + 1
        let ref := (legacyReferencePlan ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)).digest.displayBytes
        if ref != r.display then
          IO.eprintln s!"FAIL {path} reference: nIn {r.nIn}, hashType {r.hashType}: got {toHex ⟨ref.toArray⟩}, expected {toHex ⟨r.display.toArray⟩}"
          failures := failures + 1
    | _, _ =>
      IO.eprintln s!"FAIL {path}: transaction not read whole: {toHex ⟨r.tx.toArray⟩}"
      failures := failures + 1
  IO.println s!"{path}: {records.size} records, {fixed} with the fixed digest, {unparsed} with a script that does not parse, {failures} failures (production and reference)"
  return failures

/-! ### Hand-derived preimages -/

/-- The transaction of the hand-derived cases, before its outputs. -/
def txIn0 : TxIn :=
  { prevout := ⟨⟨List.replicate 32 0x11, by simp⟩, 0⟩, scriptSig := script [0x51], sequence := 0xfffffffe }

def txIn1 : TxIn :=
  { prevout := ⟨⟨List.replicate 32 0x22, by simp⟩, 1⟩, scriptSig := script [0x52, 0x53], sequence := 0x01020304 }

def txOut0 : TxOut := { value := 5, scriptPubKey := script [0x76] }

def txOut1 : TxOut := { value := 0x0102, scriptPubKey := script [0xac] }

/-- Version 2, inputs 0 and 1, the given outputs, lock time `0x11223344`. -/
def tx (outs : List TxOut) : Transaction :=
  { version := 2, inputs := countedOf [txIn0, txIn1], outputs := countedOf outs, lockTime := 0x11223344 }

/-! Wire fields of the cases, written out byte by byte. -/

def version : List UInt8 := [0x02, 0x00, 0x00, 0x00]
def lockTime : List UInt8 := [0x44, 0x33, 0x22, 0x11]
def prevout0 : List UInt8 := List.replicate 32 0x11 ++ [0x00, 0x00, 0x00, 0x00]
def prevout1 : List UInt8 := List.replicate 32 0x22 ++ [0x01, 0x00, 0x00, 0x00]
def seq0 : List UInt8 := [0xfe, 0xff, 0xff, 0xff]
def seq1 : List UInt8 := [0x04, 0x03, 0x02, 0x01]
def zeroSeq : List UInt8 := [0x00, 0x00, 0x00, 0x00]
def emptyScript : List UInt8 := [0x00]
def out0 : List UInt8 := [0x05, 0, 0, 0, 0, 0, 0, 0] ++ [0x01, 0x76]
def out1 : List UInt8 := [0x02, 0x01, 0, 0, 0, 0, 0, 0] ++ [0x01, 0xac]
/-- `CTxOut()`: amount −1, empty script. -/
def nullOut : List UInt8 := List.replicate 8 0xff ++ [0x00]

/-- The script code `OP_DUP OP_CODESEPARATOR OP_CHECKSIG`. -/
def codeSep : List UInt8 := [0x76, 0xab, 0xac]
/-- It is written without the separator: count 2, then `76 ac`. -/
def codeSepBytes : List UInt8 := [0x02, 0x76, 0xac]

/-- Whether the production plan hashes exactly `expected`. -/
def hashesProduction (sc : List UInt8) (t : Transaction) (nIn h : UInt32) (expected : List UInt8) : Bool :=
  legacySignatureHashPlan (script sc) t nIn h == .hashBytes expected

/-- Whether the production plan and the transformation reference both hash exactly `expected`. -/
def hashes (sc : List UInt8) (t : Transaction) (nIn h : UInt32) (expected : List UInt8) : Bool :=
  hashesProduction sc t nIn h expected && legacyReferencePlan (script sc) t nIn h == .hashBytes expected

/-- Whether both plans are the fixed digest `one`. -/
def fixedBoth (sc : List UInt8) (t : Transaction) (nIn h : UInt32) : Bool :=
  legacySignatureHashPlan (script sc) t nIn h == .fixedDigest legacyOne &&
    legacyReferencePlan (script sc) t nIn h == .fixedDigest legacyOne

/--
The `FindAndDelete` cases: the script, the pattern, and the script and count that `CScript::FindAndDelete` returns (D24, lines 570 to 596).
Copies are removed only at instruction boundaries, and the bytes of a failed instruction are kept.
-/
def findAndDeleteCases : List (String × List UInt8 × List UInt8 × List UInt8 × Nat) := [
  ("empty pattern changes nothing", [0xab, 0x51], [], [0xab, 0x51], 0),
  ("no copy changes nothing", [0x51, 0x52], [0xab], [0x51, 0x52], 0),
  ("separator instructions are removed", [0x76, 0xab, 0xab, 0xac, 0xab], [0xab], [0x76, 0xac], 3),
  ("0xab inside push data is not an instruction", [0x02, 0xab, 0xab, 0x51], [0xab], [0x02, 0xab, 0xab, 0x51], 0),
  ("0xab after push data is removed", [0x02, 0xab, 0xab, 0xab, 0x51], [0xab], [0x02, 0xab, 0xab, 0x51], 1),
  ("a pattern inside push data is not at a boundary", [0x51, 0x01, 0xab], [0xab], [0x51, 0x01, 0xab], 0),
  ("repeated three-byte copies at one boundary and at a later one",
    [0x02, 0xaa, 0xbb, 0x02, 0xaa, 0xbb, 0x51, 0x02, 0xaa, 0xbb], [0x02, 0xaa, 0xbb], [0x51], 3),
  ("a copy, then a short push: the whole short push is kept",
    [0xab, 0x4c, 0x05, 0xaa], [0xab], [0x4c, 0x05, 0xaa], 1),
  ("a short push alone: unchanged", [0x4c, 0x05, 0xaa], [0xab], [0x4c, 0x05, 0xaa], 0)]

/-- The script-code cases: the script, and its bytes as `SerializeScriptCode` writes them. -/
def scriptCodeCases : List (String × List UInt8 × List UInt8) := [
  ("empty script", [], [0x00]),
  ("separator instruction is removed and not counted", codeSep, codeSepBytes),
  ("separator alone", [0xab], [0x00]),
  ("0xab inside push data is kept", [0x02, 0xab, 0xab, 0xab], [0x03, 0x02, 0xab, 0xab]),
  ("empty PUSHDATA1, then a separator", [0x4c, 0x00, 0xab], [0x02, 0x4c, 0x00]),
  ("whole PUSHDATA4 of one byte", [0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa],
    [0x06, 0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa]),
  -- Short pushes: the count is of the whole script, the bytes stop at GetOp's cursor.
  ("push of 1 with no data stops after the opcode", [0x01], [0x01, 0x01]),
  ("push of 2 with 1 byte stops after the opcode", [0x02, 0xaa], [0x02, 0x02]),
  ("PUSHDATA1 with no length stops after the opcode", [0x4c], [0x01, 0x4c]),
  ("PUSHDATA1 of 5 with 1 byte stops after the length", [0x4c, 0x05, 0xaa], [0x03, 0x4c, 0x05]),
  ("PUSHDATA2 with 1 length byte stops after the opcode", [0x4d, 0x01], [0x02, 0x4d]),
  ("PUSHDATA4 of 2 with 1 byte stops after the length", [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa],
    [0x06, 0x4e, 0x02, 0x00, 0x00, 0x00]),
  ("separator, then a short PUSHDATA1", [0xab, 0x4c], [0x01, 0x4c])]

/-- The checks on hand-derived preimages, each with its name and whether it holds. -/
def cases : Except String (List (String × Bool)) := do
  let one ← parseHex "0000000000000000000000000000000000000000000000000000000000000001"
  let both := tx [txOut0, txOut1]
  let allOutputs := [0x02] ++ out0 ++ out1
  let inputsWithCode1 (otherSeq : List UInt8) :=
    [0x02] ++ prevout0 ++ emptyScript ++ otherSeq ++ prevout1 ++ codeSepBytes ++ seq1
  let scriptCodeChecks := scriptCodeCases.map fun (name, sc, expected) =>
    (s!"script code: {name}", scriptCodeBytes (script sc) == expected)
  let findAndDeleteChecks := findAndDeleteCases.map fun (name, s, b, out, n) =>
    (s!"FindAndDelete: {name}", findAndDelete s b == (out, n))
  return scriptCodeChecks ++ findAndDeleteChecks ++ [
    ("one displays as 00…01", legacyOne.displayBytes == one.toList),
    ("ALL, nIn 1",
      hashes codeSep both 1 1 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("ALL, nIn 0",
      hashes codeSep both 0 1 (version ++ [0x02] ++ prevout0 ++ codeSepBytes ++ seq0 ++ prevout1 ++ emptyScript ++
        seq1 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("NONE, nIn 1: no outputs, other sequence 0",
      hashes codeSep both 1 2 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x02, 0, 0, 0])),
    ("SINGLE, nIn 1: null output 0, other sequence 0",
      hashes codeSep both 1 3
        (version ++ inputsWithCode1 zeroSeq ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++ [0x03, 0, 0, 0])),
    ("SINGLE, nIn 0: output 0 only",
      hashes codeSep both 0 3
        (version ++ [0x02] ++ prevout0 ++ codeSepBytes ++ seq0 ++ prevout1 ++ emptyScript ++ zeroSeq ++
          [0x01] ++ out0 ++ lockTime ++ [0x03, 0, 0, 0])),
    ("SINGLE|ANYONECANPAY, nIn 1: input 1 alone with its sequence, null output 0",
      hashes codeSep both 1 0x83
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++
          [0x83, 0, 0, 0])),
    ("ALL|ANYONECANPAY, nIn 0: input 0 alone, all outputs",
      hashes codeSep both 0 0x81
        (version ++ [0x01] ++ prevout0 ++ codeSepBytes ++ seq0 ++ allOutputs ++ lockTime ++ [0x81, 0, 0, 0])),
    ("NONE|ANYONECANPAY, nIn 1: input 1 alone with its sequence, no outputs",
      hashes codeSep both 1 0x82
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ [0x00] ++ lockTime ++ [0x82, 0, 0, 0])),
    -- Other raw hash types: low 5 bits other than 2 and 3 serialize as ALL.
    ("hash type 0 serializes as ALL",
      hashes codeSep both 1 0 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x00, 0, 0, 0])),
    ("hash type 4 serializes as ALL",
      hashes codeSep both 1 4 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x04, 0, 0, 0])),
    ("hash type 0x21 serializes as ALL",
      hashes codeSep both 1 0x21 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x21, 0, 0, 0])),
    ("hash type 0x22 serializes as NONE",
      hashes codeSep both 1 0x22 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x22, 0, 0, 0])),
    ("hash type -1 serializes as ALL|ANYONECANPAY",
      hashes codeSep both 1 (bits32 (-1))
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ allOutputs ++ lockTime ++ [0xff, 0xff, 0xff, 0xff])),
    ("hash type 0x103 serializes as SINGLE",
      hashes codeSep both 1 0x103
        (version ++ inputsWithCode1 zeroSeq ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++ [0x03, 0x01, 0, 0])),
    -- A short push in the script code.
    ("short PUSHDATA1 in the script code of input 1",
      hashesProduction [0x4c, 0x05, 0xaa] both 1 1
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    -- SignatureHashOld keeps the whole short push, so its plan differs.
    ("reference keeps the whole short PUSHDATA1",
      legacyReferencePlan (script [0x4c, 0x05, 0xaa]) both 1 1 == .hashBytes
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05, 0xaa] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("reference keeps a short push after a separator",
      legacyReferencePlan (script [0xab, 0x4c, 0x05, 0xaa]) both 1 1 == .hashBytes
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05, 0xaa] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    -- The fixed digest.
    ("nIn equal to the input count gives one",
      fixedBoth codeSep both 2 1),
    ("nIn 0xffffffff gives one",
      fixedBoth codeSep both 0xffffffff 1),
    ("SINGLE with no output at nIn gives one",
      fixedBoth codeSep (tx [txOut0]) 1 3),
    ("SINGLE|ANYONECANPAY with no output at nIn gives one",
      fixedBoth codeSep (tx [txOut0]) 1 0x83),
    ("ALL with no output at nIn hashes",
      hashes codeSep (tx [txOut0]) 1 1
        (version ++ inputsWithCode1 seq0 ++ [0x01] ++ out0 ++ lockTime ++ [0x01, 0, 0, 0])),
    ("NONE with no outputs hashes",
      hashes codeSep (tx []) 1 2 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x02, 0, 0, 0])),
    ("the digest of the fixed plan is one",
      (legacySignatureHash (script codeSep) both 2 1).val == one.toList.reverse)]

/-- Every legacy signature-hash known answer. Returns the number of failures. -/
def check : IO Nat := do
  let corpus ← checkCorpus "tests/transaction/sighash/sighash.json"
  match cases with
  | .error e =>
    IO.eprintln s!"FAIL legacy sighash: {e}"
    return corpus + 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL legacy sighash {name}"
        failures := failures + 1
    IO.println s!"legacy sighash: {cs.length} hand-derived checks, {failures} failures"
    return corpus + failures

end KnownAnswers.LegacySighash

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


/-!
### Operators: `multiply`, `divide` and `GetLow64`

The cases of `arith_uint256_tests.cpp` (D16) that use the operators the retarget uses: `operator*` by a 32-bit value, `operator/` and `GetLow64`.
The inputs and expected values are copied from the test file, with the line of each case.
Two `divide` cases, lines 362 and 368, expect an exception for a zero divisor. `ArithUint256.div` takes a proof that the divisor is not zero, so it has no such case.
The multiply and `GetLow64` cases also run through the word models.
The division cases run through the arithmetic definition only (issue #16).
-/

/-- The value of a string of hexadecimal digits, or `none` for another character. -/
def hexNat? (s : String) : Option Nat :=
  s.toList.foldlM (init := 0) fun acc c => (KnownAnswers.Sha256Cavp.hexDigit? c).map (acc * 16 + ·.toNat)

/-- `R1L` of `arith_uint256_tests.cpp` lines 25 to 30: `R1Array` read as a little-endian number, which is `R1ArrayHex`. -/
def r1Hex : String := "7d1de5eaf9b156d53208f033b5aa8122d2d2355d5e12292b121156cfdb4a529c"

/-- `R2L`, lines 33 to 36: `R2Array` read as a little-endian number. The digits are the bytes of `R2Array` from last to first. -/
def r2Hex : String := "d781cab4f072134971da2d19a3473013bfb69ca6c30a7e26406ba5477c1d3270"

/-- `MaxL`, lines 50 to 53: every bit set. -/
def maxHex : String := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-- `D1L` and `D2L` of the `divide` test, lines 355 and 356. -/
def d1Hex : String := "ad7133ac1977fa2b7"
def d2Hex : String := "ecd751716"

/-- The value of `a / b` by `ArithUint256.div`, or `none` for a zero divisor. -/
def divide? (a b : ArithUint256) : Option ArithUint256 :=
  if h : b.val ≠ 0 then some (ArithUint256.div a b h) else none

/-- The operator cases, each with its line in `arith_uint256_tests.cpp` and whether it holds. -/
def operatorCases : Except String (List (Nat × Bool)) := do
  let num (s : String) : Except String ArithUint256 :=
    match hexNat? s with
    | some n => pure (ArithUint256.ofNat n)
    | none => throw s!"bad hex {s}"
  let r1 ← num r1Hex
  let r2 ← num r2Hex
  let mx ← num maxHex
  let d1 ← num d1Hex
  let d2 ← num d2Hex
  let one := ArithUint256.ofNat 1
  let zero := ArithUint256.ofNat 0
  let is (a : ArithUint256) (s : String) : Except String Bool := do return a == (← num s)
  let divIs (a b : ArithUint256) (c : ArithUint256) : Bool := divide? a b == some c
  return [
    (347, ArithUint256.mulUInt32 r1 0 == zero),
    (348, ArithUint256.mulUInt32 r1 1 == r1),
    (349, ← is (ArithUint256.mulUInt32 r1 3) "7759b1c0ed14047f961ad09b20ff83687876a0181a367b813634046f91def7d4"),
    (350, ← is (ArithUint256.mulUInt32 r2 0x87654321) "23f7816e30c4ae2017257b7a0fa64d60402f5234d46e746b61c960d09a26d070"),
    (357, divIs r1 d1 (← num "00000000000000000b8ac01106981635d9ed112290f8895545a7654dde28fb3a")),
    (358, divIs r1 d2 (← num "000000000873ce8efec5b67150bad3aa8c5fcb70e947586153bf2cec7c37c57a")),
    (359, divIs r1 one r1),
    (360, divIs r1 mx zero),
    (361, divIs mx r1 (ArithUint256.ofNat 2)),
    (363, divIs r2 d1 (← num "000000000000000013e1665895a1cc981de6d93670105a6b3ec3b73141b3a3c5")),
    (364, divIs r2 d2 (← num "000000000e8f0abe753bb0afe2e9437ee85d280be60882cf0bd1aaf7fa3cc2c4")),
    (365, divIs r2 one r2),
    (366, divIs r2 mx zero),
    (367, divIs mx r2 one),
    (394, ArithUint256.getLow64 r1 == 0x121156cfdb4a529c),
    (395, ArithUint256.getLow64 (ArithUint256.shiftLeft one 255) == 0),
    (396, ArithUint256.getLow64 one == 1),
    (347, ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 0) == zero),
    (348, ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 1) == r1),
    (349, ← is (ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 3))
      "7759b1c0ed14047f961ad09b20ff83687876a0181a367b813634046f91def7d4"),
    (350, ← is (ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r2) 0x87654321))
      "23f7816e30c4ae2017257b7a0fa64d60402f5234d46e746b61c960d09a26d070"),
    (394, (ArithUint256.Words.getLow64 (ArithUint256.Words.ofArith r1)).toNat == 0x121156cfdb4a529c),
    (395, (ArithUint256.Words.getLow64
      (ArithUint256.Words.shiftLeft (ArithUint256.Words.ofArith one) 255)).toNat == 0),
    (396, (ArithUint256.Words.getLow64 (ArithUint256.Words.ofArith one)).toNat == 1)]

/-- Every operator case. Returns the number of failures. -/
def checkOperators : IO Nat := do
  match operatorCases with
  | .error e =>
    IO.eprintln s!"FAIL arith_uint256_tests.cpp operators: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (line, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL arith_uint256_tests.cpp:{line}"
        failures := failures + 1
    IO.println s!"arith_uint256_tests.cpp multiply, divide, GetLow64: {cs.length} cases, {failures} failures"
    return failures

/-!
### Next-work selection

Parameter expectations come from D14 at `e0a1c15`: mainnet lines 88-95 and 126-141,
testnet lines 233-251 and 282-306, regtest lines 392-397 and 425-437.
Synthetic branch fixtures follow D17 lines 32-88 and D6 lines 26-39.
They are source-derived examples, not observed historical headers or a Core comparison.
-/

/-- Compares the full result, including finite-view error categories. -/
private instance : BEq (Except NextWorkError UInt32) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => decide (x = y)
    | _, _ => false

/-- Synthetic view entry. Times and compact targets are supplied without header validation. -/
def workEntry (height : Nat) (time bits : UInt32) : BlockIndex := ⟨height, time, bits⟩

/-- Parameter fields fixed independently by Core's network records (D14).
The tuple is timespan, spacing, DigiShield calculation flag, minimum-difficulty permission and compact limit. -/
def workFields (network : WorkNetwork) (height : UInt32) : Int × Nat × Bool × Bool × UInt32 :=
  let p := getConsensus network height
  (p.nPowTargetTimespan.toInt, p.nPowTargetSpacing, p.fDigishieldDifficultyCalculation,
    p.fPowAllowMinDifficultyBlocks, ArithUint256.getCompact p.powLimit)

/-- Boundary examples from the effective heights in D14, including records whose work fields repeat. -/
def parameterCases : List (String × Bool) :=
  let mainLegacy := (14400, 60, false, false, 0x1e0fffff)
  let mainDigi := (60, 60, true, false, 0x1e0fffff)
  let testLegacy := (14400, 60, false, true, 0x1e0fffff)
  let testMin := (60, 60, true, true, 0x1e0fffff)
  let regLegacy := (14400, 1, false, true, 0x207fffff)
  let regDigi := (1, 1, true, true, 0x207fffff)
  [("main genesis fields", workFields .mainnet 0 == mainLegacy),
   ("main 144999", workFields .mainnet 144999 == mainLegacy),
   ("main 145000", workFields .mainnet 145000 == mainDigi),
   ("main 145001", workFields .mainnet 145001 == mainDigi),
   ("main 371336", workFields .mainnet 371336 == mainDigi),
   ("main 371337", workFields .mainnet 371337 == mainDigi),
   ("main 371338", workFields .mainnet 371338 == mainDigi),
   ("test 144999", workFields .testnet 144999 == testLegacy),
   ("test 145000", workFields .testnet 145000 == mainDigi),
   ("test 145001", workFields .testnet 145001 == mainDigi),
   ("test 157499", workFields .testnet 157499 == mainDigi),
   ("test 157500", workFields .testnet 157500 == testMin),
   ("test 157501", workFields .testnet 157501 == testMin),
   ("test 158099", workFields .testnet 158099 == testMin),
   ("test 158100", workFields .testnet 158100 == testMin),
   ("test 158101", workFields .testnet 158101 == testMin),
   ("regtest 9", workFields .regtest 9 == regLegacy),
   ("regtest 10", workFields .regtest 10 == regDigi),
   ("regtest 11", workFields .regtest 11 == regDigi),
   ("regtest 19", workFields .regtest 19 == regDigi),
   ("regtest 20", workFields .regtest 20 == regDigi),
   ("regtest 21", workFields .regtest 21 == regDigi),
   ("main UInt32 maximum", workFields .mainnet 0xffffffff == mainDigi),
   ("test UInt32 maximum", workFields .testnet 0xffffffff == testMin),
   ("regtest UInt32 maximum", workFields .regtest 0xffffffff == regDigi)]

/-- Synthetic inputs fixed by the return statements and strict comparisons of D17 and D6.
Malformed and truncated inputs check the finite-view adapter, not Core rejection codes. -/
def nextWorkCases : List (String × Bool) :=
  let legacy := testnetWorkParams
  let minParams := testnetMinDifficultyWorkParams
  let e := workEntry
  [("main genesis", nextWorkRequired .mainnet [] 0 == .ok 0x1e0fffff),
   ("test genesis", nextWorkRequired .testnet [] 0 == .ok 0x1e0fffff),
   ("regtest genesis", nextWorkRequired .regtest [] 0 == .ok 0x207fffff),
   -- D17 lines 50-53: threshold uses previous height.
   ("local interval 144999", retargetInterval mainnetWorkParams 144999 == 240),
   ("local interval 145000", retargetInterval mainnetWorkParams 145000 == 1),
   ("local interval 145001", retargetInterval mainnetWorkParams 145001 == 1),
   ("record interval stays 240", mainnetWorkParams.difficultyAdjustmentInterval == 240),
   ("first interval lookback", blocksToGoBack 240 239 == 239),
   ("later interval lookback", blocksToGoBack 240 479 == 240),
   ("main copies compact verbatim", nextWorkRequired .mainnet [e 1 100 0x04923456] 101 == .ok 0x04923456),
   -- D17 lines 54-73: equality is not a delay, and boundary stops recovery.
   ("legacy equal delay", nextWorkRequired .testnet [e 1 100 0x1c123456] 220 == .ok 0x1c123456),
   ("legacy delayed", nextWorkRequired .testnet [e 1 100 0x1c123456] 221 == .ok 0x1e0fffff),
   ("recovery nonminimum", nextWorkRequired .testnet
      [e 3 100 0x1e0fffff, e 2 90 0x1e0fffff, e 1 80 0x1c123456] 101 == .ok 0x1c123456),
   ("recovery interval boundary", nextWorkRequired .testnet
      [e 241 100 0x1e0fffff, e 240 90 0x1e0fffff, e 239 80 0x1c123456] 101 == .ok 0x1e0fffff),
   ("recovery genesis", nextWorkRequired .testnet
      [e 1 100 0x1e0fffff, e 0 90 0x1e0fffff] 101 == .ok 0x1e0fffff),
   ("recovery missing history", nextWorkRequired .testnet [e 1 100 0x1e0fffff] 101 == .error .missingAncestor),
   -- D6 lines 29-38: independent previous-height and permission checks.
   ("DigiShield previous 157499", !allowDigishieldMinDifficultyForBlock minParams (e 157499 100 0) 221),
   ("DigiShield previous 157500", allowDigishieldMinDifficultyForBlock minParams (e 157500 100 0) 221),
   ("DigiShield previous 157501", allowDigishieldMinDifficultyForBlock minParams (e 157501 100 0) 221),
   ("DigiShield equal delay", !allowDigishieldMinDifficultyForBlock minParams (e 157500 100 0) 220),
   ("DigiShield permission false", !allowDigishieldMinDifficultyForBlock testnetDigishieldWorkParams (e 157500 100 0) 221),
   ("test candidate 157500 still retargets", nextWorkRequired .testnet [e 157499 100 0x1c123456] 221 == .error .missingAncestor),
   ("test candidate 157501 minimum", nextWorkRequired .testnet [e 157500 100 0x1c123456] 221 == .ok 0x1e0fffff),
   ("DigiShield equality needs ancestor", nextWorkRequired .testnet [e 157500 100 0x1c123456] 220 == .error .missingAncestor),
   ("activation candidate 145000 needs ancestor", nextWorkRequired .mainnet [e 144999 100 0] 101 == .error .missingAncestor),
   ("main missing retarget ancestor", nextWorkRequired .mainnet [e 239 100 0] 101 == .error .missingAncestor),
   -- Regtest's fPowNoRetargeting is true, but this caller ignores it (D17 line 87).
   -- With T=1 and actual timespan=1, D6 returns the old compact.
   ("regtest retarget at 10", nextWorkRequired .regtest [e 9 100 0x1c123456, e 8 99 0] 101 == .ok 0x1c123456),
   -- D16 bignum_SetCompact lines 511-521: the signed and unsigned forms
   -- decode to the same value, whose unsigned GetCompact is 0x04123456.
   ("regtest ignores no-retarget flag and normalizes compact", nextWorkRequired .regtest
      [e 9 100 0x04923456, e 8 99 0] 101 == .ok 0x04123456),
   ("regtest delayed before retarget", nextWorkRequired .regtest [e 1 100 0x1c123456] 103 == .ok 0x207fffff),
   ("regtest maximum widened time", nextWorkRequired .regtest [e 1 0xffffffff 0x1c123456] 0xffffffff == .ok 0x1c123456),
   ("inconsistent view", nextWorkRequired .mainnet [e 2 100 0, e 0 90 0] 101 == .error .inconsistentHeights),
   ("maximum accepted previous height", nextWorkRequired .mainnet
      [e 2147483646 100 0x1c123456, e 2147483645 40 0] 0 == .ok 0x1c123456),
   ("height overflow", nextWorkRequired .mainnet [e 2147483647 100 0] 101 == .error .heightOutOfRange),
   ("genesis with predecessor", nextWorkRequired .mainnet [e 0 100 0, e 0 90 0] 101 == .error .inconsistentHeights),
   ("zero custom interval", getNextWorkRequired { legacy with nPowTargetSpacing := 20000 }
      [e 1 100 0] 101 == .error .zeroInterval)]

/-- Synthetic contiguous windows with the six pinned D7 arithmetic inputs.
The first and last timestamps and expected compact are from the cited test.
Intermediate timestamps and heights provide context for the caller and make no historical claim. -/
def callerRetargetCases : List (String × Bool) :=
  retargetCases.toList.map fun c =>
    let height := c.nHeight.toInt.toNat - 1
    let back := if height = 239 then 239 else if height < 145000 then 240 else 1
    let view := (List.range (back + 1)).map fun i =>
      workEntry (height - i)
        (UInt32.ofNat (if i = back then c.nFirstBlockTime.toInt.toNat else c.nLastBlockTime.toInt.toNat)) c.nBits
    (s!"caller {c.name}", nextWorkRequired .mainnet view 0 == .ok c.expected)

/-- Runs the source-derived next-work examples and pinned retarget answers through the caller. -/
def checkNextWork : IO Nat := do
  let cases := parameterCases ++ nextWorkCases ++ callerRetargetCases
  let mut failures := 0
  for (name, ok) in cases do
    if !ok then
      IO.eprintln s!"FAIL next work: {name}"
      failures := failures + 1
  IO.println s!"next-work selection: {cases.length} cases, {failures} failures"
  return failures

/-!
### Shifts

The byte helpers and cases below adapt `src/test/arith_uint256_tests.cpp` lines 125-197 at Core `e0a1c15` (D16).
The adaptation uses total byte lookup and natural shifts before truncation to a byte.
The expected bytes come from Core's byte helpers, independently of the arithmetic and word models.
This adapted section is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notice:

Copyright (c) 2011-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

/-- Core's byte-array left shift, lines 139-154, with zero for an absent byte. -/
def coreBytesLeft (bytes : List UInt8) (shift : Nat) : List UInt8 :=
  (List.range 32).map fun t =>
    if t ≥ shift / 8 then
      let f := t - shift / 8
      UInt8.ofNat (((bytes[f]?.getD 0).toNat <<< (shift % 8)) |||
        (if t ≥ shift / 8 + 1 then (bytes[f - 1]?.getD 0).toNat >>> (8 - shift % 8) else 0))
    else 0

/-- Core's byte-array right shift, lines 125-137, with zero for an absent byte. -/
def coreBytesRight (bytes : List UInt8) (shift : Nat) : List UInt8 :=
  (List.range 32).map fun t =>
    let f := t + shift / 8
    UInt8.ofNat (((bytes[f]?.getD 0).toNat >>> (shift % 8)) |||
      ((bytes[f + 1]?.getD 0).toNat <<< (8 - shift % 8)))

/-- Interpret Core's little-endian byte array as a natural number. -/
def coreBytesValue (bytes : List UInt8) : Nat := bytes.foldr (fun byte acc => byte.toNat + 256 * acc) 0

/-- Run Core's shift cases, lines 159-196, against the arithmetic and word models.
Extra word-loop cases at shifts of at least 256 expect zero from Core's index guards (D13 lines 30-33 and 47-50). -/
def checkShifts : IO Nat := do
  let some r1 := hexNat? r1Hex | throw (IO.userError "bad R1 hex")
  let some mx := hexNat? maxHex | throw (IO.userError "bad Max hex")
  let .ok r1Bytes := KnownAnswers.Sha256Cavp.parseHex r1Hex | throw (IO.userError "bad R1 bytes")
  let inputs := [(1, (1 : UInt8) :: List.replicate 31 0),
    (r1, r1Bytes.toList.reverse), (mx, List.replicate 32 (255 : UInt8))]
  let mut failures := 0
  let mut count := 0
  for shift in [:256] do
    for (input, bytes) in inputs do
      let a := ArithUint256.ofNat input
      let w := ArithUint256.Words.ofArith a
      let left := coreBytesValue (coreBytesLeft bytes shift)
      let right := coreBytesValue (coreBytesRight bytes shift)
      -- Core lines 162, 170, 175, 180 and 185 use the byte-array helpers.
      -- Core lines 165-167 use HalfL >> (255-i) = OneL << i.
      let checks := if input == 1 then
        [(162, (ArithUint256.shiftLeft a shift).val == left &&
          (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == left),
         (165, (ArithUint256.Words.toArith
            (ArithUint256.Words.shiftRight (ArithUint256.Words.ofArith (ArithUint256.ofNat (2 ^ 255))) (255 - shift))).val == left &&
          (ArithUint256.shiftRight (ArithUint256.ofNat (2 ^ 255)) (255 - shift)).val == left)]
        else
          [(if input == r1 then 170 else 180,
            (ArithUint256.shiftLeft a shift).val == left &&
              (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == left),
           (if input == r1 then 175 else 185,
            (ArithUint256.shiftRight a shift).val == right &&
              (ArithUint256.Words.toArith (ArithUint256.Words.shiftRight w shift)).val == right)]
      for (line, ok) in checks do
        count := count + 1
        unless ok do
          failures := failures + 1
          IO.eprintln s!"FAIL arith_uint256_tests.cpp:{line}, shift {shift}"
    -- Core lines 189-196 fix c1L and place c2L 128 bits higher.
    let c1 := ArithUint256.Words.ofArith (ArithUint256.ofNat 0x0123456789abcdef)
    let c2 := ArithUint256.Words.ofArith (ArithUint256.ofNat (0x0123456789abcdef * 2 ^ 128))
    let lhs := ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft c1 shift)
    let rhs := ArithUint256.Words.toArith (if shift < 128 then ArithUint256.Words.shiftRight c2 (128 - shift)
      else ArithUint256.Words.shiftLeft c2 (shift - 128))
    count := count + 1
    unless lhs == rhs do
      failures := failures + 1
      IO.eprintln s!"FAIL arith_uint256_tests.cpp:192/195, shift {shift}"
  for shift in [256, 257, 511, 512, 0xffffffff] do
    for (input, _) in inputs do
      let w := ArithUint256.Words.ofArith (ArithUint256.ofNat input)
      count := count + 2
      unless (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == 0 &&
          (ArithUint256.Words.toArith (ArithUint256.Words.shiftRight w shift)).val == 0 do
        failures := failures + 1
        IO.eprintln s!"FAIL word shift at {shift}, expected zero"
  IO.println s!"arith_uint256_tests.cpp shifts and zero boundaries: {count} cases, {failures} failures"
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
  let transactions ← KnownAnswers.Transactions.check
  let witness ← KnownAnswers.Witness.check
  let txCorpus ← KnownAnswers.TxCorpus.check
  let sighash ← KnownAnswers.LegacySighash.check
  let compact ← KnownAnswers.Work.checkCompact
  let retarget ← KnownAnswers.Work.checkRetarget
  let nextWork ← KnownAnswers.Work.checkNextWork
  let operators ← KnownAnswers.Work.checkOperators
  let shifts ← KnownAnswers.Work.checkShifts
  return if short + long + genesis + codec + compactSize + countedList + transactions + witness + txCorpus + sighash + compact + retarget + nextWork + operators + shifts == 0 then 0 else 1
