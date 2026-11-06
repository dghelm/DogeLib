import DogeLib.Cryptography.Secp256k1.Ecdsa
import DogeLib.Cryptography.Hash.Hash160
import DogeLib.Cryptography.Hash.Hmac
import DogeLib.Cryptography.Hash.Pbkdf2
import DogeLib.Cryptography.Proofs.Hash.ScryptSpec
import DogeLib.Cryptography.Hash.Sha1
import DogeLib.Cryptography.Hash.Sha256
import DogeLib.Cryptography.Hash.Sha256d
import DogeLib.Serialization
import DogeLib.Transaction
import DogeLib.Work
import DogeLib.Block
import DogeLib.Script
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
## SHA-1

NIST CAVS 11.0 supplies the byte-oriented short and long answers, and CAVS 11.1 supplies the Monte Carlo checkpoints.
`tests/cryptography/sha1/cavp/README.md` records the files and SHAVS §6.4 procedure.
Core supplies ten further answers in `sha1_testvectors`, including two million-byte inputs.
-/

namespace KnownAnswers.Sha1

open Sha256Cavp
open DogeLib.Cryptography.Hash (sha1)

/-- Checks every SHA-1 vector in a short or long NIST file, including the expected vector count. -/
def checkFile (path : System.FilePath) (expected : Nat) : IO Nat := do
  let vectors ← match parse (← IO.FS.readFile path) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  if vectors.size != expected then
    IO.eprintln s!"FAIL {path}: {vectors.size} vectors, expected {expected}"
    failures := failures + 1
  for v in vectors do
    let got := sha1 v.message
    unless v.digest.size == 20 && got.toList == v.digest.toList do
      IO.eprintln s!"FAIL {path}: Len = {v.bits}: got {toHex got}, expected {toHex v.digest}"
      failures := failures + 1
  IO.println s!"{path}: {vectors.size} vectors, {failures} failures"
  return failures

/-- Reads one 20-byte seed and all 100 sequential Monte Carlo checkpoints, or reports a malformed fixture. -/
def parseMonte (text : String) : Except String (ByteArray × Array ByteArray) := do
  let mut seed : Option ByteArray := none
  let mut pending : Option Nat := none
  let mut checkpoints := #[]
  for raw in text.splitOn "\n" do
    let line := String.ofList (raw.toList.filter (· != '\r'))
    if let some value := field? "Seed" line then
      unless seed.isNone && checkpoints.isEmpty && pending.isNone do throw "unexpected Seed"
      let bytes ← parseHex value
      unless bytes.size == 20 do throw "SHA-1 seed must have twenty bytes"
      seed := some bytes
    else if let some value := field? "COUNT" line then
      unless seed.isSome && pending.isNone do throw "unexpected COUNT"
      let some index := value.toNat? | throw "bad COUNT"
      unless index == checkpoints.size do throw "COUNT out of order"
      pending := some index
    else if let some value := field? "MD" line then
      unless pending.isSome do throw "MD without COUNT"
      let bytes ← parseHex value
      unless bytes.size == 20 do throw "SHA-1 digest must have twenty bytes"
      checkpoints := checkpoints.push bytes
      pending := none
  let some initial := seed | throw "missing Seed"
  unless pending.isNone && checkpoints.size == 100 do throw "expected 100 complete checkpoints"
  return (initial, checkpoints)

/-- Performs 1,000 hashes of the three prior digests, as SHAVS §6.4, Figure 1 prescribes. -/
def monteCheckpoint (seed : ByteArray) : ByteArray := Id.run do
  let mut a := seed
  let mut b := seed
  let mut c := seed
  for _ in [:1000] do
    let next := sha1 (a ++ b ++ c)
    a := b
    b := c
    c := next
  return c

/-- Checks all 100 NIST checkpoints in sequence, with 100,000 SHA-1 calls. -/
def checkMonte (path : System.FilePath) : IO Nat := do
  let (initial, checkpoints) ← match parseMonte (← IO.FS.readFile path) with
    | .ok value => pure value
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut seed := initial
  let mut failures := 0
  for i in [:checkpoints.size] do
    seed := monteCheckpoint seed
    unless seed.toList == checkpoints[i]!.toList do
      IO.eprintln s!"FAIL {path}: COUNT = {i}: got {toHex seed}, expected {toHex checkpoints[i]!}"
      failures := failures + 1
  IO.println s!"{path}: {checkpoints.size} checkpoints, {failures} failures"
  return failures

/-!
The message construction and cases below adapt `src/test/crypto_tests.cpp`, lines 190 to 202 and 220 to 233,
at Dogecoin Core `e0a1c157791544e818c901bd9341896965afbf9d`, under MIT.
`LICENSES/dogecoin-core-MIT.txt` preserves its licence and copyright notice.
The adaptation uses Lean byte arrays instead of C++ strings and omits the incremental-write harness.
The quoted SHA-1 safety sentence is fixture data, not a claim by DogeLib.
-/

/-- Core's million-byte `LongTestString`, with each integer's five low bytes at four-bit offsets. -/
def longTestString : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity 1000000
  for i in [:200000] do
    for shift in [0, 4, 8, 12, 16] do
      bytes := bytes.push (UInt8.ofNat (i >>> shift))
  return bytes

/-- Core's ten SHA-1 messages and expected digest literals. -/
def coreCases : List (ByteArray × String) := [
  ("".toUTF8, "da39a3ee5e6b4b0d3255bfef95601890afd80709"),
  ("abc".toUTF8, "a9993e364706816aba3e25717850c26c9cd0d89d"),
  ("message digest".toUTF8, "c12252ceda8be8994d5fa0290a47231c1d16aae3"),
  ("secure hash algorithm".toUTF8, "d4d6d2f0ebe317513bbd8d967d89bac5819c2f60"),
  ("SHA1 is considered to be safe".toUTF8, "f2b6650569ad3a8720348dd6ea6c497dee3a842a"),
  ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8, "84983e441c3bd26ebaae4aa1f95129e5e54670f1"),
  ("For this sample, this 63-byte string will be used as input data".toUTF8, "4f0ea5cd0585a23d028abdc1a6684e5a8094dc49"),
  ("This is exactly 64 bytes long, not counting the terminating byte".toUTF8, "fb679f23e7d1ce053313e66e127ab1b444397057"),
  (⟨Array.replicate 1000000 0x61⟩, "34aa973cd4c4daa4f61eeb2bdbad27316534016f"),
  (longTestString, "b7755760681cbfd971451668f32af5774f4656b5") ]

/-- Checks Core's ten SHA-1 expected digests through the compiled function. -/
def checkCore : IO Nat := do
  let mut failures := 0
  for (message, expected) in coreCases do
    let got := toHex (sha1 message)
    unless got == expected do
      IO.eprintln s!"FAIL Core SHA-1 ({message.size} bytes): got {got}, expected {expected}"
      failures := failures + 1
  IO.println s!"crypto_tests.cpp SHA-1: {coreCases.length} cases, {failures} failures"
  return failures

/-- Checks the NIST SHA-1 files and Core cases. -/
def check : IO Nat := do
  let dir : System.FilePath := "tests/cryptography/sha1/cavp"
  let short ← checkFile (dir / "SHA1ShortMsg.rsp") 65
  let long ← checkFile (dir / "SHA1LongMsg.rsp") 64
  let monte ← checkMonte (dir / "SHA1Monte.rsp")
  let core ← checkCore
  return short + long + monte + core

end KnownAnswers.Sha1

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

/-- The complete base-mode result of the slice reader, with the remainder as bytes. -/
def readSlice (s : ByteSlice) : Except CompactSize.ReadError (Transaction × List UInt8) :=
  (Transaction.readBaseSlice s).map fun (tx, rest) => (tx, rest.toList)

/-- Compare prefix and complete base-mode readers at a nonzero offset, with bytes outside both slice bounds. -/
def sliceAgrees (bs : List UInt8) : Bool :=
  let bytes : ByteArray := ⟨(0xaa :: 0xbb :: bs ++ [0xcc]).toArray⟩
  let s := (ByteSlice.ofByteArray bytes).drop 2 |>.take bs.length
  let complete := match Transaction.decodeBaseCompleteSlice s, Transaction.decodeBaseComplete bs with
    | .error e, .error e' => decide (e = e')
    | .ok a, .ok b => a == b
    | _, _ => false
  complete && match readSlice s, Transaction.readBase bs with
  | .error e, .error e' => decide (e = e')
  | .ok a, .ok b => a == b
  | _, _ => false

/-- Whether `readBase` reads all of `bs` as a transaction that `check` accepts, and the codec writes `bs` again. -/
def readsBack (bs : List UInt8) (check : Transaction → Bool) : Bool :=
  match Transaction.readBase bs with
  | .ok (tx, []) => check tx && Codec.encode tx == bs && sliceAgrees bs
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
    ("slice reader reads the genesis coinbase at offset 3",
      (readSlice ((ByteSlice.ofByteArray padded).drop 3)).toOption == some (genesis, [])),
    ("slice reader keeps one trailing byte",
      (readSlice (ByteSlice.ofByteArray ⟨(c ++ [0x00]).toArray⟩)).toOption == some (genesis, [0x00])),
    ("slice reader agrees on every truncated genesis prefix",
      (List.range c.length).all fun n => sliceAgrees (c.take n)),
    ("slice reader preserves count errors at every field",
      [ver ++ tooBig, ver ++ [0xfd, 0x01, 0x00],
        ver ++ [1] ++ outpointBytes ++ tooBig,
        ver ++ [1] ++ outpointBytes ++ [0xfd, 0, 0],
        ver ++ [0] ++ tooBig, ver ++ [0, 0xfd, 2, 0],
        ver ++ [0, 1] ++ le 8 0 ++ tooBig,
        ver ++ [0, 1] ++ le 8 0 ++ [0xfd, 0, 0],
        ver ++ [1] ++ outpointBytes ++ [0xfd, 0, 0] ++ le 4 0 ++ tooBig].all sliceAgrees),
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
The format models serialization only.
Core rejects blocks with witness data on main and test at the pin (D9, D36).
The module documentation of `DogeLib.Transaction.Witness` records the separate consensus mechanisms.

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
The format models serialization only.
Core rejects blocks with witness data on main and test at the pin (D9, D36).
The module documentation of `DogeLib.Transaction.Witness` records the separate consensus mechanisms.

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
    if !KnownAnswers.Transactions.sliceAgrees bs then
      IO.eprintln s!"FAIL {path}: slice base reader disagrees on {toHex ⟨bs.toArray⟩}"
      failures := failures + 1
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

/-! ### Mutations of the corpus records

These checks test DogeLib against itself, not against Core.
Each takes a record of Core's `sighash.json`, changes one field of its transaction, and recomputes the production digest.
The expected result, the same digest or a different one, comes from the theorems of `DogeLib.Transaction.Proofs.LegacySighashCommitment` and from the definition, not from Core.
An expected difference assumes that double SHA-256 has no collision on these inputs.
-/

/-- `t` with input `i` changed by `f`. -/
def mapInput (t : Transaction) (i : Nat) (f : TxIn → TxIn) : Transaction :=
  { t with inputs := countedOf (t.inputs.val.modify i f) }

/-- `t` with output `i` changed by `f`. -/
def mapOutput (t : Transaction) (i : Nat) (f : TxOut → TxOut) : Transaction :=
  { t with outputs := countedOf (t.outputs.val.modify i f) }

/-- A script with one more byte, `0x51`, so a different script. -/
def extendScript (s : Script) : Script := script (s.bytes.val ++ [0x51])

/-- The kinds of mutation, each with its name and whether the digest should stay the same. -/
def mutationKinds : List (String × Bool) := [
  ("ALL: lock time changes the digest", false),
  ("ALL: every scriptSig leaves it", true),
  ("ALL|ANYONECANPAY: another input's outpoint leaves it", true),
  ("ALL|ANYONECANPAY: input nIn's sequence changes it", false),
  ("NONE: removing the outputs leaves it", true),
  ("NONE: input nIn's sequence changes it", false),
  ("NONE: another input's sequence leaves it", true),
  ("SINGLE: another output's value leaves it", true),
  ("SINGLE: output nIn's value changes it", false)]

/-- The mutations of one record that apply to it: the index of the kind in `mutationKinds`, and the mutated transaction. -/
def mutations (t : Transaction) (n : Nat) (h : UInt32) : List (Nat × Transaction) :=
  let acp := HashType.anyoneCanPay h
  let none := HashType.isNone h
  let single := HashType.isSingle h
  let other := if n = 0 then 1 else 0
  let nIns := t.inputs.val.length
  let nOuts := t.outputs.val.length
  let allClass := !none && !single
  let bumpSeq := fun (i : TxIn) => { i with sequence := i.sequence + 1 }
  (if allClass && !acp then
    [(0, { t with lockTime := t.lockTime + 1 }),
     (1, { t with inputs := countedOf (t.inputs.val.map fun i => { i with scriptSig := extendScript i.scriptSig }) })]
   else []) ++
  (if allClass && acp then
    (if other < nIns then
      [(2, mapInput t other fun i => { i with prevout := { i.prevout with n := i.prevout.n + 1 } })] else []) ++
    [(3, mapInput t n bumpSeq)]
   else []) ++
  (if none && !acp then
    [(4, { t with outputs := countedOf [] }), (5, mapInput t n bumpSeq)] ++
    (if other < nIns then [(6, mapInput t other bumpSeq)] else [])
   else []) ++
  (if single && !acp && n < nOuts then
    (if other < nOuts then [(7, mapOutput t other fun o => { o with value := o.value + 1 })] else []) ++
    [(8, mapOutput t n fun o => { o with value := o.value + 1 })]
   else [])

/-- Runs every mutation on every corpus record whose plan hashes. Returns the number of failures. -/
def checkMutations (path : System.FilePath) : IO Nat := do
  let records ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut counts := Array.replicate mutationKinds.length 0
  let mut failures := 0
  for r in records do
    match Transaction.decodeBaseComplete r.tx, CountedList.ofList? r.script with
    | .ok t, some sc =>
      let n := bits32 r.nIn
      let h := bits32 r.hashType
      if legacySignatureHashPlan ⟨sc⟩ t n h matches .hashBytes _ then
        let d := legacySignatureHash ⟨sc⟩ t n h
        for (k, t') in mutations t n.toNat h do
          let (name, same) := mutationKinds[k]!
          counts := counts.modify k (· + 1)
          if (legacySignatureHash ⟨sc⟩ t' n h == d) != same then
            IO.eprintln s!"FAIL {path} mutation {name}: nIn {r.nIn}, hashType {r.hashType}"
            failures := failures + 1
    | _, _ => pure ()
  for ((name, _), c) in mutationKinds.zip counts.toList do
    if c == 0 then
      IO.eprintln s!"FAIL {path} mutation {name}: no record"
      failures := failures + 1
  let summary := ", ".intercalate ((mutationKinds.zip counts.toList).map fun ((name, _), c) => s!"{name} {c}")
  IO.println s!"{path} mutations (DogeLib against itself): {summary}; {failures} failures"
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
    -- The signed input's position (`legacyReferencePlan_allOnly_index_eq`).
    -- With an empty script code, every input of the copy has the empty script, so indices 0 and 1 give one preimage.
    ("ALL, empty script code: nIn 0 and nIn 1 hash the same bytes",
      legacySignatureHashPlan (script []) both 0 1 == legacySignatureHashPlan (script []) both 1 1 &&
        hashes [] both 0 1 (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ emptyScript ++
          seq1 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("ALL, script code 76 ab ac: nIn 0 and nIn 1 hash different bytes",
      legacySignatureHashPlan (script codeSep) both 0 1 != legacySignatureHashPlan (script codeSep) both 1 1),
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
  let corpus := corpus + (← checkMutations "tests/transaction/sighash/sighash.json")
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

The six `get_next_work_*` cases come from Dogecoin Core `e0a1c15`, `src/test/dogecoin_tests.cpp` (SOURCES.md, D7).
They run through the arithmetic retarget and both word entry points.
Each case gives the last block's height, time and `nBits`, the first block time, the parameter set, and the expected `nBits`.
The inputs and the expected values are copied from the test file, with the line of each value.

## Compact encoding

The `bignum_SetCompact` cases come from `src/test/arith_uint256_tests.cpp` at the same commit (SOURCES.md, D16).
They run through the arithmetic and word compact models.
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
    let wordGot := calculateDogecoinNextWorkRequiredWords c.params c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    let byteGot := (ArithUint256.targetBytesOfHex ArithUint256.mainnetPowLimitHex).bind fun limit =>
      calculateDogecoinNextWorkRequiredBytes c.params limit c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    if got != c.expected || wordGot != some c.expected || byteGot != some c.expected then
      IO.eprintln s!"FAIL dogecoin_tests.cpp:{c.line} {c.name}: got {hex32 got}, words {wordGot}, bytes {byteGot}, expected {hex32 c.expected}"
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
    let (wordValue, wordFlags) := match c.nCompact with
      | some n =>
        let r := ArithUint256.Words.setCompact n
        (r.value, some (r.fNegative, r.fOverflow))
      | none => (ArithUint256.Words.ofUInt64 (UInt64.ofNat (c.value.getD 0)), none)
    let mut ok := true
    if let some v := c.value then
      if value.val != v || ArithUint256.Words.value wordValue != v then ok := false
    if let some e := c.compact then
      if ArithUint256.getCompact value c.negativeArgument != e ||
          ArithUint256.Words.getCompact wordValue c.negativeArgument != e then ok := false
    if let some (neg, ovf) := flags then
      if c.fNegative != some neg || c.fOverflow != some ovf then ok := false
    if let some (neg, ovf) := wordFlags then
      if c.fNegative != some neg || c.fOverflow != some ovf then ok := false
    if !ok then
      IO.eprintln s!"FAIL arith_uint256_tests.cpp:{c.line}: value {value.val}, flags {flags}, word value {ArithUint256.Words.value wordValue}, word flags {wordFlags}"
      failures := failures + 1
  IO.println s!"arith_uint256_tests.cpp bignum_SetCompact: {compactCases.size} cases, {failures} failures"
  return failures


/-!
### Operators: `multiply`, `divide` and `GetLow64`

The cases of `arith_uint256_tests.cpp` (D16) that use the operators the retarget uses: `operator*` by a 32-bit value, `operator/` and `GetLow64`.
The inputs and expected values are copied from the test file, with the line of each case.
The multiply, nonzero divide and `GetLow64` cases run through both the arithmetic and word models.
Two `divide` cases, lines 362 and 368, expect `uint_error` for a zero divisor.
The word model returns `none` for these `BOOST_CHECK_THROW` expectations.
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
  let wordDivide (a b : ArithUint256) : Option ArithUint256 :=
    (ArithUint256.Words.divide (ArithUint256.Words.ofArith a) (ArithUint256.Words.ofArith b)).map ArithUint256.Words.toArith
  let divIs (a b : ArithUint256) (c : ArithUint256) : Bool :=
    divide? a b == some c && wordDivide a b == some c
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
    (362, wordDivide r1 zero == none),
    (363, divIs r2 d1 (← num "000000000000000013e1665895a1cc981de6d93670105a6b3ec3b73141b3a3c5")),
    (364, divIs r2 d2 (← num "000000000e8f0abe753bb0afe2e9437ee85d280be60882cf0bd1aaf7fa3cc2c4")),
    (365, divIs r2 one r2),
    (366, divIs r2 mx zero),
    (367, divIs mx r2 one),
    (368, wordDivide r2 zero == none),
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
### Supplied-hash proof of work

These synthetic known answers derive from D17, `src/pow.cpp` lines 124-129 at `e0a1c15`.
`0x03000100` decodes to 256, so little-endian hashes 255 and 256 pass and 257 fails.
`0x04000001` also decodes to 256, despite its noncanonical encoding.

The custom limit of 256 isolates equality and the above-limit branch.
The full 256-bit limit isolates overflow even when the wrapped target is nonzero and below the limit.
`0x22000101` encodes `257 * 2^248`, which wraps to `2^248` and reports overflow.
These expectations follow from the source's arithmetic and comparisons, not this implementation's output.

Core's `src/test/pow_tests.cpp` has no direct `CheckProofOfWork` cases at this pin.
`src/test/auxpow_tests.cpp` lines 333-355 mines both passing and failing scrypt digests at runtime.
Those tests supply no fixed digest to copy here.
The cases below do not compute scrypt or run Core.
-/

/-- Synthetic internal-order hash with two explicit low bytes and thirty zero bytes. -/
def lowHash (lo hi : UInt8) : DogeLib.Hash256 :=
  ⟨[lo, hi] ++ List.replicate 30 0, by simp⟩

/-- Source-derived branch and boundary cases for the supplied-hash check. -/
def proofOfWorkCases : List (String × Bool) :=
  let params := mainnetParams
  let exactLimit := { params with powLimit := ArithUint256.ofNat 256 }
  let fullLimit := { params with powLimit := ArithUint256.ofNat (2 ^ 256 - 1) }
  [("zero target", !validProofOfWorkTarget 0 params),
   ("shifted zero mantissa", !validProofOfWorkTarget 0x01000001 params),
   ("signed shifted zero", !validProofOfWorkTarget 0x01800001 params),
   ("negative target", !validProofOfWorkTarget 0x03800100 params),
   ("overflow with zero wrapped target", !validProofOfWorkTarget 0x23000001 params),
   ("overflow with nonzero wrapped target", !validProofOfWorkTarget 0x22000101 fullLimit),
   ("above mainnet limit", !validProofOfWorkTarget 0x1f00ffff params),
   ("target equals custom limit", validProofOfWorkTarget 0x03000100 exactLimit),
   ("target exceeds custom limit", !validProofOfWorkTarget 0x03000100
      { params with powLimit := ArithUint256.ofNat 255 }),
   ("zero hash accepted", checkProofOfWork DogeLib.Hash256.zero 0x03000100 params),
   ("hash below target", checkProofOfWork (lowHash 255 0) 0x03000100 params),
   ("hash equals target", checkProofOfWork (lowHash 0 1) 0x03000100 params),
   ("hash above target", !checkProofOfWork (lowHash 1 1) 0x03000100 params),
   ("reversed equality bytes fail", !checkProofOfWork
      ⟨List.replicate 30 0 ++ [1, 0], by decide⟩ 0x03000100 params),
   ("noncanonical positive target accepted", checkProofOfWork (lowHash 0 1) 0x04000001 params),
   ("zero hash cannot rescue negative target", !checkProofOfWork DogeLib.Hash256.zero 0x03800100 params),
   ("zero hash cannot rescue overflow", !checkProofOfWork DogeLib.Hash256.zero 0x22000101 fullLimit),
   ("zero hash cannot rescue zero target", !checkProofOfWork DogeLib.Hash256.zero 0 params),
   ("zero hash cannot rescue above-limit target", !checkProofOfWork DogeLib.Hash256.zero 0x1f00ffff params),
   ("mainnet genesis target in range", validProofOfWorkTarget 0x1e0ffff0 params)]

/-- Runs the supplied-hash check on source-derived known answers and returns the failure count. -/
def checkProofOfWorkCases : IO Nat := do
  let mut failures := 0
  for (name, ok) in proofOfWorkCases do
    if !ok then
      IO.eprintln s!"FAIL proof of work: {name}"
      failures := failures + 1
  IO.println s!"proof-of-work check: {proofOfWorkCases.length} cases, {failures} failures"
  return failures

/-!
### Mainnet headers

The raw fixture and its Electrum provenance are in `tests/work/mainnet-headers/README.md`.
D10 fixes the 80-byte layout.
D9 fixes checkpoint 145000 at Core `e0a1c15`.
The checkpoint anchors its ancestors, but does not authenticate later headers.
These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.
-/

namespace MainnetHeaders

open DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- One pure header, with the int32 version's bits preserved as UInt32.
The fixture height is separate from the 80 serialized bytes (D10). -/
structure Header where
  height : Nat
  versionBits : UInt32
  prev : DogeLib.Hash256
  merkleRoot : DogeLib.Hash256
  time : UInt32
  bits : UInt32
  nonce : UInt32
  digest : ByteArray

/-- Parses all six D10 fields, consumes exactly 80 bytes and hashes those bytes with Sha256d. -/
def parseHeader (height : Nat) (hex : String) : Except String Header := do
  let bytes ← parseHex hex
  if bytes.size != 80 then throw s!"height {height}: expected 80 bytes, got {bytes.size}"
  let some ((version, prev, merkle, time, bits, nonce), rest) :=
      Codec.decode (α := UInt32 × DogeLib.Hash256 × DogeLib.Hash256 × UInt32 × UInt32 × UInt32) bytes.toList
    | throw s!"height {height}: cannot decode header"
  if !rest.isEmpty then throw s!"height {height}: trailing header bytes"
  return ⟨height, version, prev, merkle, time, bits, nonce,
    DogeLib.Cryptography.Hash.Sha256d.hash bytes⟩

/-- Requires exactly the fixture's 312 consecutive heights, so missing records cannot reduce the checks. -/
def parseHeaders (text : String) : Except String (Array Header) := do
  let mut headers := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [heightText, hex] := line.splitOn " " | throw "expected height and header hex"
    let some height := heightText.toNat? | throw s!"bad height: {heightText}"
    if height != 144719 + headers.size then throw s!"unexpected height: {height}"
    headers := headers.push (← parseHeader height hex)
  if headers.size != 312 then throw s!"expected 312 headers, got {headers.size}"
  return headers

/-- Checks every target range, hash link, checkpoint 145000 and next-work result with sufficient prior history.
Only the initial context header and the incomplete retarget at 144720 lack known answers. -/
def check : IO Nat := do
  let headers ← match parseHeaders (← IO.FS.readFile "tests/work/mainnet-headers/headers.txt") with
    | .ok headers => pure headers
    | .error e =>
      IO.eprintln s!"FAIL mainnet headers: {e}"
      return 1
  let mut failures := 0
  let mut previous : Option Header := none
  let mut view : List BlockIndex := []
  let mut copies := 0
  let mut legacyRetargets := 0
  let mut digiRetargets := 0
  for header in headers do
    unless validProofOfWorkTarget header.bits (getConsensus .mainnet (UInt32.ofNat header.height)).toRetargetParams do
      IO.eprintln s!"FAIL mainnet target range {header.height}"
      failures := failures + 1
    if let some prev := previous then
      unless header.prev.val == prev.digest.toList do
        IO.eprintln s!"FAIL mainnet header {header.height}: predecessor hash"
        failures := failures + 1
    if header.height == 145000 then
      let display := toHex ⟨header.digest.toList.reverse.toArray⟩
      unless display == "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72" do
        IO.eprintln s!"FAIL mainnet checkpoint 145000: {display}"
        failures := failures + 1
    if header.height > 144719 then
      let got := nextWorkRequired .mainnet view header.time
      if header.height == 144720 then
        unless got == .error .missingAncestor do
          IO.eprintln s!"FAIL mainnet header 144720: expected missingAncestor, got {repr got}"
          failures := failures + 1
      else
        unless got == .ok header.bits do
          IO.eprintln s!"FAIL mainnet next work {header.height}: got {repr got}, expected {header.bits}"
          failures := failures + 1
        if header.height >= 145000 then digiRetargets := digiRetargets + 1
        else if header.height % 240 == 0 then legacyRetargets := legacyRetargets + 1
        else copies := copies + 1
    view := ⟨header.height, header.time, header.bits⟩ :: view
    previous := some header
  unless copies == 278 && legacyRetargets == 1 && digiRetargets == 31 do
    IO.eprintln "FAIL mainnet headers: unexpected branch counts"
    failures := failures + 1
  IO.println s!"mainnet headers: {headers.size} hashes, 311 links, checkpoint 145000; {failures} failures"
  IO.println s!"mainnet target validity: {headers.size} targets checked"
  IO.println s!"mainnet next work: {copies} legacy copies, {legacyRetargets} interval-240 retarget, {digiRetargets} DigiShield retargets"
  return failures

end MainnetHeaders

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

/-!
## Pure headers and Merkle roots

`tests/block/README.md` records fixture provenance and the limits of the independent expectations.
Header hashes use successor fields or independent Python hashlib expectations.
The Merkle vectors transcribe Core's deterministic transaction lists at the pinned revision.
-/
namespace KnownAnswers.Block
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- Parse a display-order hash without padding or truncation. -/
def parseHash (s : String) : Except String Hash256 := do
  let some h := Hash256.ofDisplayBytes? (← parseHex s).toList | throw "expected 32-byte hash"
  return h

/-- Check a proposition and report its fixture label on failure. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL block: {label}"
  return 1

/-- Read fixture JSON, with a failure on malformed or absent input. -/
def jsonFile (path : System.FilePath) : IO Lean.Json := do
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw (IO.userError e)

/-- Whether `BlockHeader.read mode bs` returns exactly `h` and `rest`. -/
def readsAs (mode : TxReadMode) (bs : List UInt8) (h : BlockHeader) (rest : List UInt8) : Bool :=
  match BlockHeader.read mode bs with
  | .ok (h', rest') => h' == h && rest' == rest
  | .error _ => false

/-- Whether `BlockHeader.read mode bs` fails with `e`. -/
def readFails (mode : TxReadMode) (bs : List UInt8) (e : Transaction.WitnessReadError) : Bool :=
  match BlockHeader.read mode bs with
  | .ok _ => false
  | .error e' => e' == e

/-- Whether `BlockHeader.read mode bs` fails. -/
def readRejects (mode : TxReadMode) (bs : List UInt8) : Bool :=
  match BlockHeader.read mode bs with
  | .ok _ => false
  | .error _ => true

/-- Check pure-header decoding, encoding, hash bytes, all truncated prefixes and an arbitrary suffix. -/
def checkHeader (label : String) (raw : List UInt8) (expected : Hash256) : IO Nat := do
  let some (h, rest) := Codec.decode (α := PureBlockHeader) raw
    | return ← require s!"{label}: decode" false
  let mut failures ← require s!"{label}: exact encoding" (rest.isEmpty && Codec.encode h == raw)
  failures := failures + (← require s!"{label}: 80 bytes" (raw.length == 80))
  failures := failures + (← require s!"{label}: hash" (h.getHash == expected))
  failures := failures + (← require s!"{label}: suffix"
    (Codec.decode (raw ++ [0x42, 0xff]) == some (h, [0x42, 0xff])))
  for n in [:80] do
    failures := failures + (← require s!"{label}: truncated at {n}"
      ((Codec.decode (α := PureBlockHeader) (raw.take n)).isNone))
  if !h.isAuxpow then
    for mode in [TxReadMode.allowWitness, .base] do
      failures := failures + (← require s!"{label}: full header without payload, {repr mode}"
        (readsAs mode (raw ++ [0x42, 0xff]) ⟨h, none⟩ [0x42, 0xff]))
  return failures

/-- Check all 312 recorded mainnet headers against recorded links and the independent final digest. -/
def checkHeaders : IO Nat := do
  let text ← IO.FS.readFile "tests/work/mainnet-headers/headers.txt"
  let records ← match KnownAnswers.Work.MainnetHeaders.parseHeaders text with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let last ← match parseHash (← IO.FS.readFile "tests/block/last-header-hash.txt").trimAscii.toString with
    | .ok h => pure h
    | .error e => throw (IO.userError e)
  let lines := (text.splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  for i in [:records.size] do
    let some record := records[i]? | throw (IO.userError "missing header")
    let expected := match records[i+1]? with
      | some next => next.prev
      | none => last
    let some line := lines[i]? | throw (IO.userError s!"missing raw header at index {i}")
    let some hex := (line.splitOn " ")[1]? | throw (IO.userError "bad header line")
    let raw ← match parseHex hex with
      | .ok b => pure b.toList
      | .error e => throw (IO.userError e)
    failures := failures + (← checkHeader s!"height {record.height}" raw expected)
  IO.println s!"pure headers: {records.size} records, 24960 truncated prefixes; {failures} failures"
  return failures

/-- Check real transaction lists against Merkle roots in the fetched raw headers. -/
def checkMainnet : IO Nat := do
  let rows ← match (← jsonFile "tests/block/mainnet.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "three mainnet block fixtures" (rows.size == 3)
  for row in rows do
    let parsed : Except String (Nat × List UInt8 × Hash256 × List Transaction.Transaction × List Hash256) := do
      let height ← (← row.getObjVal? "height").getNat?
      let raw := (← parseHex (← row.getObjValAs? String "header")).toList
      let expected ← parseHash (← row.getObjValAs? String "blockHash")
      let txs ← (← row.getObjVal? "transactions").getArr?
      let ids ← (← row.getObjVal? "txids").getArr?
      let transactions ← txs.toList.mapM fun j => do
        let bytes := (← parseHex (← j.getStr?)).toList
        match Transaction.Transaction.decodeBaseComplete bytes with
        | .ok tx => pure tx
        | .error _ => throw "transaction decode failed"
      let hashes ← ids.toList.mapM fun j => do parseHash (← j.getStr?)
      return (height, raw, expected, transactions, hashes)
    let (height, raw, expected, txs, ids) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    failures := failures + (← checkHeader s!"block {height}" raw expected)
    let some (h, _) := Codec.decode (α := PureBlockHeader) raw
      | throw (IO.userError "pure header decode failed")
    failures := failures + (← require s!"block {height}: transaction IDs" (txs.map (·.txid) == ids))
    failures := failures + (← require s!"block {height}: Merkle root"
      (blockMerkleRoot txs == (⟨h.hashMerkleRoot, false⟩ : MerkleResult)))
  return failures

/-- Check independently computed roots and mutation flags for deterministic Core transaction lists. -/
def checkMerkleVectors : IO Nat := do
  let rows ← match (← jsonFile "tests/block/merkle.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "34 deterministic Merkle vectors" (rows.size == 34)
  for row in rows do
    let parsed : Except String (Nat × Nat × List Hash256 × MerkleResult) := do
      let count ← (← row.getObjVal? "count").getNat?
      let mutation ← (← row.getObjVal? "mutation").getNat?
      let leaves ← (← (← row.getObjVal? "leaves").getArr?).toList.mapM fun j => do
        parseHash (← j.getStr?)
      let root ← parseHash (← row.getObjValAs? String "root")
      let mutated ← row.getObjValAs? Bool "mutated"
      return (count, mutation, leaves, ⟨root, mutated⟩)
    let (count, mutation, leaves, expected) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    failures := failures + (← require s!"Merkle size {count}, mutation {mutation}"
      (computeMerkleRoot leaves == expected))
    let base : List Transaction.Transaction := (List.range count).map fun j =>
      ⟨1, ⟨[], by decide⟩, ⟨[], by decide⟩, j.toUInt32⟩
    let baseHashes := base.map (·.txid)
    let baseRoot := (computeMerkleRoot baseHashes).root
    failures := failures + (← require s!"Merkle size {count}: root unchanged"
      (expected.root == baseRoot))
    failures := failures + (← require s!"Merkle size {count}: mutation flag"
      (expected.mutated == (mutation != 0)))
    let mut rebuilt := baseHashes
    for _ in [:mutation] do
      let mut n := rebuilt.length
      let mut duplicate := 1
      while n > 0 && n % 2 == 0 do
        duplicate := duplicate * 2
        n := n / 2
      if duplicate >= rebuilt.length then
        throw (IO.userError s!"Merkle size {count}: duplication would add a whole tree level")
      rebuilt := rebuilt ++ rebuilt.drop (rebuilt.length - duplicate)
    failures := failures + (← require s!"Merkle size {count}, mutation {mutation}: reconstructed leaves"
      (rebuilt == leaves))
  return failures

/-- One recorded AuxPoW payload: the fields that the independent importer parsed and checked against Blockchair's decoded JSON. -/
structure PayloadRecord where
  txHex : List UInt8
  txid : Hash256
  hashBlock : List UInt8
  merkleBranch : List (List UInt8)
  index : Int
  chainMerkleBranch : List (List UInt8)
  chainIndex : Int
  parentBlock : List UInt8

/-- Parse the `payload` object of an AuxPoW header record. -/
def parsePayload (j : Lean.Json) : Except String PayloadRecord := do
  let hexField (k : String) : Except String (List UInt8) := do
    return (← parseHex (← j.getObjValAs? String k)).toList
  let hexList (k : String) : Except String (List (List UInt8)) := do
    (← (← j.getObjVal? k).getArr?).toList.mapM fun e => do return (← parseHex (← e.getStr?)).toList
  return {
    txHex := ← hexField "txHex", txid := ← parseHash (← j.getObjValAs? String "txid"),
    hashBlock := ← hexField "hashBlock", merkleBranch := ← hexList "merkleBranch",
    index := ← (← j.getObjVal? "index").getInt?, chainMerkleBranch := ← hexList "chainMerkleBranch",
    chainIndex := ← (← j.getObjVal? "chainIndex").getInt?, parentBlock := ← hexField "parentBlock" }

/--
Check the full mainnet headers of `tests/block/auxpow-headers.json` in both read modes.
Each record is a whole raw block. The test checks the consumed length, the remainder and the payload fields.
It also checks the re-encoding, the checkpoint hash, every proper prefix and the transaction list in the remainder.
-/
def checkAuxPowHeaders : IO Nat := do
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "six AuxPoW header fixtures" (rows.size == 6)
  let mut prefixes := 0
  for row in rows do
    let parsed : Except String (Nat × Hash256 × Bool × Nat × Nat × List UInt8 × PayloadRecord) := do
      let height ← (← row.getObjVal? "height").getNat?
      let hash ← parseHash (← row.getObjValAs? String "blockHash")
      let flag ← row.getObjValAs? Bool "auxpowFlag"
      let len ← (← row.getObjVal? "headerLength").getNat?
      let txCount ← (← row.getObjVal? "txCount").getNat?
      let block := (← parseHex (← row.getObjValAs? String "block")).toList
      let payload ← parsePayload (← row.getObjVal? "payload")
      return (height, hash, flag, len, txCount, block, payload)
    let (height, hash, flag, len, txCount, block, p) ← match parsed with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    let label := s!"AuxPoW header {height}"
    let header := block.take len
    let remainder := block.drop len
    for mode in [TxReadMode.allowWitness, .base] do
      let ml := s!"{label}, {repr mode}"
      match BlockHeader.read mode block with
      | .error _ => failures := failures + (← require s!"{ml}: read" false)
      | .ok (h, rest) =>
        failures := failures + (← require s!"{ml}: remainder" (rest == remainder))
        failures := failures + (← require s!"{ml}: checkpoint hash" (h.pure.getHash == hash))
        failures := failures + (← require s!"{ml}: flag" (h.pure.isAuxpow == flag))
        failures := failures + (← require s!"{ml}: re-encoding" (BlockHeader.encode mode h == header))
        failures := failures + (← require s!"{ml}: complete read"
          (match BlockHeader.decodeComplete mode header with
           | .ok h' => h' == h
           | .error _ => false))
        match h.auxpow with
        | none => failures := failures + (← require s!"{ml}: payload" false)
        | some a =>
          failures := failures + (← require s!"{ml}: transaction bytes"
            (encodeTx .allowWitness a.tx == p.txHex))
          failures := failures + (← require s!"{ml}: no witness data" (!a.tx.hasWitness))
          failures := failures + (← require s!"{ml}: transaction ID" (a.tx.tx.txid == p.txid))
          failures := failures + (← require s!"{ml}: hashBlock" (a.hashBlock.val == p.hashBlock))
          failures := failures + (← require s!"{ml}: coinbase branch"
            (a.merkleBranch.val.map (·.val) == p.merkleBranch))
          failures := failures + (← require s!"{ml}: nIndex" (a.signedIndex.toInt == p.index))
          failures := failures + (← require s!"{ml}: chain branch"
            (a.chainMerkleBranch.val.map (·.val) == p.chainMerkleBranch))
          failures := failures + (← require s!"{ml}: nChainIndex" (a.signedChainIndex.toInt == p.chainIndex))
          failures := failures + (← require s!"{ml}: parent header" (Codec.encode a.parentBlock == p.parentBlock))
        match CountedList.decodeBounded Transaction.Transaction.readBase rest with
        | .ok (txs, []) =>
          failures := failures + (← require s!"{ml}: transaction count" (txs.val.length == txCount))
          failures := failures + (← require s!"{ml}: Merkle root"
            (blockMerkleRoot txs.val == (⟨h.pure.hashMerkleRoot, false⟩ : MerkleResult)))
        | _ => failures := failures + (← require s!"{ml}: transaction list" false)
      for k in [:len] do
        failures := failures + (← require s!"{ml}: truncated at {k}" (readRejects mode (header.take k)))
      prefixes := prefixes + len
  IO.println s!"AuxPoW headers: {rows.size} records, {prefixes} truncated prefixes across both modes"
  return failures

/-- A pure header with only the AuxPoW flag set: version `0x00000100`, every other field zero. -/
def flaggedPure : List UInt8 := [0x00, 0x01, 0x00, 0x00] ++ List.replicate 76 0

/-- A coinbase-shaped transaction in base form: one input with a zero outpoint, an empty script, sequence `0xffffffff`, no outputs. -/
def oneInputTx : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x00] ++ [0, 0, 0, 0]

/-- The same transaction in the extended form, flags `01`, with one empty witness stack. -/
def oneInputTxExtended : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x00, 0x01] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++
    [0x00] ++ [0x00] ++ [0, 0, 0, 0]

/-- The payload fields after the transaction, all zero, with empty branches. -/
def zeroTail : List UInt8 :=
  List.replicate 32 0 ++ [0x00] ++ [0, 0, 0, 0] ++ [0x00] ++ [0, 0, 0, 0] ++ List.replicate 80 0

/--
Hand-written full headers, from Core's format (D41, D54, D4): the read mode of the embedded transaction, errors and truncation.
The bytes are written here from the format, not produced by the encoder under test.
-/
def checkAuxPowCases : IO Nat := do
  let base := flaggedPure ++ oneInputTx ++ zeroTail
  let ext := flaggedPure ++ oneInputTxExtended ++ zeroTail
  let mut failures := 0
  -- Both encodings read as one header in the witness-allowed mode, with nothing left over.
  match BlockHeader.read .allowWitness base, BlockHeader.read .allowWitness ext with
  | .ok (h1, []), .ok (h2, []) =>
    failures := failures + (← require "empty stacks: same header" (h1 == h2))
    failures := failures + (← require "empty stacks: writer emits base form"
      (BlockHeader.encode .allowWitness h2 == base))
  | _, _ => failures := failures + (← require "empty stacks: both encodings read" false)
  -- Base mode reads the extended form as a different transaction and leaves 35 bytes.
  failures := failures + (← require "empty stacks: base mode"
    (match BlockHeader.read .base ext with
     | .ok (h, rest) => rest.length == 35 &&
        h.auxpow.map (fun (a : AuxPow) => (a.tx.tx.inputs.val.length, a.tx.tx.outputs.val.length)) == some (0, 1)
     | .error _ => false))
  failures := failures + (← require "base form: base mode" (readsAs .base base
    (match BlockHeader.read .allowWitness base with | .ok (h, _) => h | .error _ => ⟨⟨0, Hash256.zero, Hash256.zero, 0, 0, 0⟩, none⟩) []))
  -- A flag set with only the pure header: the payload read is truncated.
  for mode in [TxReadMode.allowWitness, .base] do
    failures := failures + (← require s!"flag set, no payload, {repr mode}"
      (readFails mode flaggedPure (.read .truncated)))
  -- Flags 02 in the embedded transaction.
  let flags2 := flaggedPure ++ ([0x01, 0, 0, 0, 0x00, 0x02] ++ [0x01] ++ List.replicate 36 0 ++
    [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x00] ++ [0, 0, 0, 0]) ++ zeroTail
  failures := failures + (← require "flags 02" (readFails .allowWitness flags2 .unknownOptionalData))
  -- A coinbase branch count of MAX_SIZE + 1 (0x02000001), before any hash.
  let tooLarge := flaggedPure ++ oneInputTx ++ List.replicate 32 0 ++ [0xfe, 0x01, 0x00, 0x00, 0x02]
  for mode in [TxReadMode.allowWitness, .base] do
    failures := failures + (← require s!"branch count above MAX_SIZE, {repr mode}"
      (readFails mode tooLarge (.read .tooLarge)))
  -- Every proper prefix of the hand-written headers.
  for (label, bytes, mode) in [("base form", base, TxReadMode.allowWitness), ("base form", base, .base),
      ("extended form", ext, .allowWitness)] do
    for k in [:bytes.length] do
      failures := failures + (← require s!"{label}, {repr mode}: truncated at {k}"
        (readRejects mode (bytes.take k)))
  IO.println s!"AuxPoW hand-written cases: {failures} failures"
  return failures

/-- Check genesis commitments, the AuxPoW bit predicate, and all block fixtures. -/
def check : IO Nat := do
  let mut failures ← checkHeaders
  failures := failures + (← checkMainnet)
  failures := failures + (← checkMerkleVectors)
  failures := failures + (← checkAuxPowHeaders)
  failures := failures + (← checkAuxPowCases)
  let parsed : Except String (PureBlockHeader × Transaction.Transaction × Hash256) := do
    let raw := (← parseHex KnownAnswers.Codec.headerHex).toList
    let some (h, []) := Codec.decode (α := PureBlockHeader) raw | throw "genesis header"
    let tx ← match Transaction.Transaction.decodeBaseComplete (← KnownAnswers.Genesis.coinbase).toList with
      | .ok tx => pure tx
      | .error _ => throw "genesis transaction"
    return (h, tx, ← parseHash "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691")
  let (h, tx, expected) ← match parsed with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  failures := failures + (← require "genesis header hash" (h.getHash == expected))
  failures := failures + (← require "genesis block Merkle root"
    (blockMerkleRoot [tx] == (⟨h.hashMerkleRoot, false⟩ : MerkleResult)))
  for version in ([0, 1, 255, 256, 257, 511, 512, 0x80000100, 0xffffffff] : List UInt32) do
    failures := failures + (← require s!"AuxPoW flag {version}"
      (({h with nVersion := version}).isAuxpow == (version.toNat / 256 % 2 == 1)))
  failures := failures + (← require "signed version high bit"
    (({h with nVersion := 0x80000100}).signedVersion.toInt == -2147483392))
  failures := failures + (← require "signed version minus one"
    (({h with nVersion := 0xffffffff}).signedVersion.toInt == -1))
  IO.println s!"block known answers: {failures} failures"
  return failures
end KnownAnswers.Block

/-!
## `CAuxPow::check`

`tests/block/check-auxpow.json` holds the 26 deterministic cases of Core's `check_auxpow` and the boundary cases of design record 0004, stage 3.
`tests/block/import_check_auxpow.py` built their bytes with Python, independently of DogeLib.
The expected Boolean of a Core case is its `BOOST_CHECK`.
The expected Boolean of a boundary case is argued from the source.

`error_line` names the `return error` of `src/auxpow.cpp` that the case reaches, worked out by reading the source.
The test compares it with the Lean diagnostic. That comparison checks the Lean error order. It is not evidence from Core.

The six mainnet headers of `tests/block/auxpow-headers.json` are checked with their own hash and chain ID and the mainnet value of `fStrictChainId`.
-/

namespace KnownAnswers.AuxPowCheck
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Block (require jsonFile)

/-- The line of `src/auxpow.cpp` whose `return error` each error stands for (D55). -/
def errorLine : AuxPowCheckError → Nat
  | .notCoinbase => 85
  | .parentHasChainId => 88
  | .chainBranchTooLong => 91
  | .merkleRootIncorrect => 102
  | .noInputs => 106
  | .missingChainRoot => 120
  | .multipleMarkers => 127
  | .markerNotBeforeRoot => 129
  | .rootTooLate => 137
  | .missingSizeAndNonce => 145
  | .sizeMismatch => 152
  | .wrongIndex => 158

/-- One record: a label, the payload bytes, the arguments of `check`, the expected result and the expected error line. -/
structure Case where
  label : String
  payload : List UInt8
  hashAux : Hash256
  chainId : Int32
  strict : Bool
  expected : Bool
  errorLine : Option Nat

/-- Parse one record of `check-auxpow.json`. -/
def parseCase (j : Lean.Json) : Except String Case := do
  let kind ← j.getObjValAs? String "kind"
  let label ← if kind == "check_auxpow" then do
      pure s!"check_auxpow line {(← (← j.getObjVal? "line").getNat?)}"
    else do pure s!"boundary {(← j.getObjValAs? String "name")}"
  let payload := (← parseHex (← j.getObjValAs? String "payload_hex")).toList
  let some hashAux := Hash256.ofBytes? (← parseHex (← j.getObjValAs? String "hash_aux_block_hex")).toList
    | throw s!"{label}: hash_aux_block_hex is not 32 bytes"
  let chainId ← (← j.getObjVal? "chain_id").getInt?
  let errorLine ← match (← j.getObjVal? "error_line") with
    | .null => pure none
    | v => some <$> v.getNat?
  let strict ← j.getObjValAs? Bool "strict_chain_id"
  let expected ← j.getObjValAs? Bool "expected"
  return { label, payload, hashAux, chainId := Int32.ofInt chainId, strict, expected, errorLine }

/-- Check every record of `tests/block/check-auxpow.json`. -/
def checkCases : IO Nat := do
  let doc ← jsonFile "tests/block/check-auxpow.json"
  let rows ← match doc.getObjValAs? (Array Lean.Json) "cases" with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "check-auxpow: 42 records" (rows.size == 42)
  let mut core := 0
  for row in rows do
    let c ← match parseCase row with
      | .ok c => pure c
      | .error e => throw (IO.userError e)
    if c.label.startsWith "check_auxpow" then core := core + 1
    match AuxPow.read .allowWitness c.payload with
    | .ok (a, []) =>
      let result := a.check c.hashAux c.chainId c.strict
      let accepted := match result with | .ok () => true | .error _ => false
      failures := failures + (← require s!"{c.label}: result" (accepted == c.expected))
      let line := match result with | .ok () => none | .error e => some (errorLine e)
      failures := failures + (← require s!"{c.label}: Lean diagnostic line {line}, expected {c.errorLine}"
        (line == c.errorLine))
    | _ => failures := failures + (← require s!"{c.label}: payload reads completely" false)
  failures := failures + (← require "check-auxpow: 26 Core cases" (core == 26))
  IO.println s!"AuxPoW check: {rows.size} records, {core} from check_auxpow"
  return failures

/-- Check the six mainnet AuxPoW headers with their own hash, their own chain ID and `fStrictChainId` true (D14 lines 120 to 121). -/
def checkMainnet : IO Nat := do
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "AuxPoW check: six mainnet headers" (rows.size == 6)
  for row in rows do
    let parsed : Except String (Nat × List UInt8) := do
      return (← (← row.getObjVal? "height").getNat?, (← parseHex (← row.getObjValAs? String "block")).toList)
    let (height, block) ← match parsed with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    match BlockHeader.read .allowWitness block with
    | .ok (⟨pure, some a⟩, _) =>
      failures := failures + (← require s!"AuxPoW check: mainnet {height} chain ID 98" (pure.chainId == 98))
      failures := failures + (← require s!"AuxPoW check: mainnet {height}"
        (match a.check pure.getHash pure.chainId true with | .ok () => true | .error _ => false))
    | _ => failures := failures + (← require s!"AuxPoW check: mainnet {height} reads with a payload" false)
  IO.println s!"AuxPoW check: {rows.size} mainnet headers"
  return failures

/-- Small known answers of the helpers, from Core's definitions (D55). -/
def checkHelpers : IO Nat := do
  let mut failures := 0
  -- `GetChainId` of version 0x00620104, and the arithmetic shift of a negative version.
  failures := failures + (← require "chain ID of 0x00620104"
    ((⟨0x00620104, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == 98))
  failures := failures + (← require "chain ID of 0xffff0104"
    ((⟨0xffff0104, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == -1))
  failures := failures + (← require "chain ID of 0x80000000"
    ((⟨0x80000000, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == -32768))
  -- The marker and the first-occurrence search.
  failures := failures + (← require "marker bytes" (mergedMiningMarker == [0xfa, 0xbe, 0x6d, 0x6d]))
  failures := failures + (← require "first occurrence" (findSubseq? [1, 2] [0, 1, 2, 1, 2] == some 1))
  failures := failures + (← require "no occurrence" (findSubseq? [1, 2] [0, 1, 3, 2] == none))
  failures := failures + (← require "occurrence at the end" (findSubseq? [1, 2] [0, 1, 2] == some 1))
  failures := failures + (← require "needle longer than input" (findSubseq? [1, 2, 3] [1, 2] == none))
  return failures

/-- Run every `CAuxPow::check` known answer. -/
def check : IO Nat := do
  let mut failures ← checkHelpers
  failures := failures + (← checkCases)
  failures := failures + (← checkMainnet)
  IO.println s!"AuxPoW check known answers: {failures} failures"
  return failures
end KnownAnswers.AuxPowCheck

/-!
## RIPEMD-160 and Hash160

The checks read immutable expectations from `tests/cryptography/ripemd160/vectors.json`.
Its README records the authors' vectors, pinned Core vectors and independently compared Hash160 digests.
-/

namespace KnownAnswers.Ripemd160

open KnownAnswers.Sha256Cavp (parseHex toHex)
open DogeLib.Cryptography.Hash

/-- One independent expectation, with its algorithm and source label. -/
structure Fixture where
  algorithm : String
  source : String
  message : ByteArray
  digest : ByteArray

/-- Decode the fixture formats, including Core's million-byte `LongTestString`. -/
def parseFixtures (text : String) : Except String (Array Fixture) := do
  let rows ← (← Lean.Json.parse text).getArr?
  rows.mapM fun row => do
    let algorithm ← (← row.getObjVal? "algorithm").getStr?
    let source ← (← row.getObjVal? "source").getStr?
    let encoding ← (← row.getObjVal? "encoding").getStr?
    let messageText ← (← row.getObjVal? "message").getStr?
    let message ← match encoding with
      | "hex" => parseHex messageText
      | "repeat_a" => do
        unless messageText == "1000000" do throw "unexpected repeat count"
        pure ⟨Array.replicate 1000000 0x61⟩
      | "core_long" => do
        unless messageText.isEmpty do throw "unexpected core_long payload"
        pure ⟨Array.ofFn fun j : Fin 1000000 =>
          ((j.val / 5) >>> (4 * (j.val % 5))).toUInt8⟩
      | _ => throw s!"unknown message encoding: {encoding}"
    let digest ← parseHex (← (← row.getObjVal? "digest").getStr?)
    unless digest.size == 20 do throw "expected a twenty-byte digest"
    unless (algorithm == "ripemd160" && (source == "authors" || source == "core_crypto_tests")) ||
        (algorithm == "hash160" && source == "hashlib_and_core_chash160") do
      throw s!"unexpected algorithm or source: {algorithm}, {source}"
    pure { algorithm, source, message, digest }

/-- Check all 31 expectations and the count from each independent source. -/
def check : IO Nat := do
  let text ← IO.FS.readFile "tests/cryptography/ripemd160/vectors.json"
  let fixtures ← match parseFixtures text with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures := 0
  for (source, expected) in [("authors", 9), ("core_crypto_tests", 10), ("hashlib_and_core_chash160", 12)] do
    let count := (fixtures.filter (·.source == source)).size
    unless count == expected do
      IO.eprintln s!"FAIL {source}: {count} fixtures, expected {expected}"
      failures := failures + 1
  for v in fixtures do
    let got := if v.algorithm == "ripemd160" then Ripemd160.hash v.message else Hash160.hash v.message
    let wrapped := if v.algorithm == "ripemd160" then ripemd160 v.message else hash160 v.message
    unless got == v.digest && wrapped == v.digest do
      IO.eprintln s!"FAIL {v.algorithm} fixture ({v.source}, {v.message.size} bytes): got {toHex got}, expected {toHex v.digest}"
      failures := failures + 1
  IO.println s!"ripemd160/hash160: {fixtures.size} fixtures, {failures} failures"
  return failures

end KnownAnswers.Ripemd160

/-!
## Script instruction reader

Runs `readInstruction` on cases from Dogecoin Core's `script_tests.json` and on cases derived from `GetOp2`, through the compiled code.

Every expected result is written by hand.
A case from `script_tests.json` (SOURCES.md, D24 for the reader) names its line at commit `e0a1c15`.
The asm of the fixture is written here as its bytes, and the expected result follows from `GetOp2`, `src/script/script.h` lines 502 to 552.
A case marked `GetOp2` comes from that function alone.

The `OP_0`, high-length-byte and state reset cases are adapted from an independent implementation of this stage (branch `feat/script-state-codex`), with citations to Core added here.
Each case fixes a script, a cursor and the full `ReadResult`.
That result is the opcode, the instruction bytes, the pushed bytes and the next cursor, or the failure, its part and its cursor.
A loop case fixes the results of `readInstruction` calls from cursor 0.
The loop stops after the first result that is not an instruction.

The cases cover direct pushes, `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4`, and every short length field.
They also cover short data for each push kind, nonminimal pushes and code separator bytes inside pushed data.
Some cases read at cursors after 0, and some read opcodes that push nothing.
-/

namespace KnownAnswers.Script

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- A successful read with opcode `o`, instruction bytes `bytes`, pushed bytes `pushed` and next cursor `next`. -/
def ins (o : UInt8) (bytes pushed : List UInt8) (next : Nat) : ReadResult :=
  .instruction ⟨o, bytes, pushed, next⟩

/-- One case: a label with its source, a script, a cursor and the expected result. -/
structure Case where
  label : String
  script : List UInt8
  pc : Nat
  expected : ReadResult

/-- One loop case: a label with its source, a script and the expected results of the loop from cursor 0. -/
structure LoopCase where
  label : String
  script : List UInt8
  expected : List ReadResult

/-- The payload of `script_tests.json` line 25: `A` and then 74 bytes `z`. -/
def az75 : List UInt8 := 0x41 :: rep 74 0x7a

/-- The single-read cases. -/
def cases : List Case := [
  -- script_tests.json: direct pushes, PUSHDATA forms, nonminimal pushes, short pushes.
  ⟨"script_tests.json:23 0x01 0x0b", [0x01, 0x0b], 0, ins 0x01 [0x01, 0x0b] [0x0b] 2⟩,
  ⟨"script_tests.json:24 0x02 0x417a", [0x02, 0x41, 0x7a], 0, ins 0x02 [0x02, 0x41, 0x7a] [0x41, 0x7a] 3⟩,
  ⟨"script_tests.json:25 0x4b and 75 bytes", 0x4b :: az75, 0, ins 0x4b (0x4b :: az75) az75 76⟩,
  ⟨"script_tests.json:28 0x4c 0x01 0x07", [0x4c, 0x01, 0x07], 0, ins 0x4c [0x4c, 0x01, 0x07] [0x07] 3⟩,
  ⟨"script_tests.json:29 0x4d 0x0100 0x08", [0x4d, 0x01, 0x00, 0x08], 0,
    ins 0x4d [0x4d, 0x01, 0x00, 0x08] [0x08] 4⟩,
  ⟨"script_tests.json:30 0x4e 0x01000000 0x09", [0x4e, 0x01, 0x00, 0x00, 0x00, 0x09], 0,
    ins 0x4e [0x4e, 0x01, 0x00, 0x00, 0x00, 0x09] [0x09] 6⟩,
  ⟨"script_tests.json:32 0x4c 0x00", [0x4c, 0x00], 0, ins 0x4c [0x4c, 0x00] [] 2⟩,
  ⟨"script_tests.json:33 0x4d 0x0000", [0x4d, 0x00, 0x00], 0, ins 0x4d [0x4d, 0x00, 0x00] [] 3⟩,
  ⟨"script_tests.json:34 0x4e 0x00000000", [0x4e, 0x00, 0x00, 0x00, 0x00], 0,
    ins 0x4e [0x4e, 0x00, 0x00, 0x00, 0x00] [] 5⟩,
  ⟨"script_tests.json:538 0x4c 0x4b and 75 bytes", [0x4c, 0x4b] ++ rep 75 0x11, 0,
    ins 0x4c ([0x4c, 0x4b] ++ rep 75 0x11) (rep 75 0x11) 77⟩,
  ⟨"script_tests.json:721 0x4c01", [0x4c, 0x01], 0, .truncated 0x4c .payload 2⟩,
  ⟨"script_tests.json:722 0x4d0200ff", [0x4d, 0x02, 0x00, 0xff], 0, .truncated 0x4d .payload 3⟩,
  ⟨"script_tests.json:723 0x4e03000000ffff", [0x4e, 0x03, 0x00, 0x00, 0x00, 0xff, 0xff], 0,
    .truncated 0x4e .payload 5⟩,
  -- GetOp2: OP_0 pushes an empty byte string.
  ⟨"GetOp2: OP_0", [0x00], 0, ins 0x00 [0x00] [] 1⟩,
  -- GetOp2: lengths with a nonzero high byte, read in little-endian order.
  ⟨"GetOp2: 4d 0001 and 256 bytes", [0x4d, 0x00, 0x01] ++ rep 256 0xab, 0,
    ins 0x4d ([0x4d, 0x00, 0x01] ++ rep 256 0xab) (rep 256 0xab) 259⟩,
  ⟨"GetOp2: 4e 00010000 and 256 bytes", [0x4e, 0x00, 0x01, 0x00, 0x00] ++ rep 256 0xab, 0,
    ins 0x4e ([0x4e, 0x00, 0x01, 0x00, 0x00] ++ rep 256 0xab) (rep 256 0xab) 261⟩,
  ⟨"GetOp2: 4d 0001, no data", [0x4d, 0x00, 0x01], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4e 00000100, no data", [0x4e, 0x00, 0x00, 0x01, 0x00], 0, .truncated 0x4e .payload 5⟩,
  ⟨"GetOp2: 4e 00000001, no data", [0x4e, 0x00, 0x00, 0x00, 0x01], 0, .truncated 0x4e .payload 5⟩,
  -- GetOp2: the end of the script.
  ⟨"GetOp2: empty script", [], 0, .atEnd⟩,
  ⟨"GetOp2: cursor at the end", [0x61], 1, .atEnd⟩,
  ⟨"GetOp2: cursor after the end", [0x61], 5, .atEnd⟩,
  -- GetOp2: every short length field. The cursor stops after the opcode.
  ⟨"GetOp2: 4c, no length byte", [0x4c], 0, .truncated 0x4c .lengthField 1⟩,
  ⟨"GetOp2: 4d, no length byte", [0x4d], 0, .truncated 0x4d .lengthField 1⟩,
  ⟨"GetOp2: 4d, one length byte", [0x4d, 0x00], 0, .truncated 0x4d .lengthField 1⟩,
  ⟨"GetOp2: 4e, no length byte", [0x4e], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, one length byte", [0x4e, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, two length bytes", [0x4e, 0x00, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, three length bytes", [0x4e, 0x00, 0x00, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  -- GetOp2: short data. The cursor stops after the length field, or after a direct push opcode.
  ⟨"GetOp2: 01, no data", [0x01], 0, .truncated 0x01 .payload 1⟩,
  ⟨"GetOp2: 02, one data byte", [0x02, 0xaa], 0, .truncated 0x02 .payload 1⟩,
  ⟨"GetOp2: 4b, 74 data bytes", 0x4b :: rep 74 0xaa, 0, .truncated 0x4b .payload 1⟩,
  ⟨"GetOp2: 4c ff, 254 data bytes", [0x4c, 0xff] ++ rep 254 0xaa, 0, .truncated 0x4c .payload 2⟩,
  ⟨"GetOp2: 4d 0100, no data", [0x4d, 0x01, 0x00], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4d ffff, 3 data bytes", [0x4d, 0xff, 0xff, 0xaa, 0xaa, 0xaa], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4e 01000000, no data", [0x4e, 0x01, 0x00, 0x00, 0x00], 0, .truncated 0x4e .payload 5⟩,
  ⟨"GetOp2: 4e ffffffff, 1 data byte", [0x4e, 0xff, 0xff, 0xff, 0xff, 0xaa], 0,
    .truncated 0x4e .payload 5⟩,
  -- GetOp2: nonminimal pushes with data keep their own bytes.
  ⟨"GetOp2: 4d 0100 aa", [0x4d, 0x01, 0x00, 0xaa], 0, ins 0x4d [0x4d, 0x01, 0x00, 0xaa] [0xaa] 4⟩,
  ⟨"GetOp2: 4e 02000000 aabb", [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa, 0xbb], 0,
    ins 0x4e [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa, 0xbb] [0xaa, 0xbb] 7⟩,
  ⟨"GetOp2: 4c ff and 255 bytes", [0x4c, 0xff] ++ rep 255 0xaa, 0,
    ins 0x4c ([0x4c, 0xff] ++ rep 255 0xaa) (rep 255 0xaa) 257⟩,
  -- GetOp2: reads at cursors after 0, including one inside pushed data.
  ⟨"GetOp2: 51 02aabb ab at 1", [0x51, 0x02, 0xaa, 0xbb, 0xab], 1,
    ins 0x02 [0x02, 0xaa, 0xbb] [0xaa, 0xbb] 4⟩,
  ⟨"GetOp2: 51 02aabb ab at 2, inside the push", [0x51, 0x02, 0xaa, 0xbb, 0xab], 2,
    ins 0xaa [0xaa] [] 3⟩,
  ⟨"GetOp2: 51 02aabb ab at 4", [0x51, 0x02, 0xaa, 0xbb, 0xab], 4, ins 0xab [0xab] [] 5⟩,
  ⟨"GetOp2: 51 4d01 at 1", [0x51, 0x4d, 0x01], 1, .truncated 0x4d .lengthField 2⟩,
  ⟨"GetOp2: 51 4c02aa at 1", [0x51, 0x4c, 0x02, 0xaa], 1, .truncated 0x4c .payload 3⟩,
  -- GetOp2: opcodes above OP_PUSHDATA4 are one byte and push nothing.
  ⟨"GetOp2: OP_1NEGATE", [0x4f, 0x01], 0, ins 0x4f [0x4f] [] 1⟩,
  ⟨"GetOp2: OP_RESERVED", [0x50, 0x01], 0, ins 0x50 [0x50] [] 1⟩,
  ⟨"GetOp2: OP_NOP", [0x61], 0, ins 0x61 [0x61] [] 1⟩,
  ⟨"GetOp2: OP_CODESEPARATOR", [0xab, 0x01], 0, ins 0xab [0xab] [] 1⟩,
  ⟨"GetOp2: OP_INVALIDOPCODE", [0xff], 0, ins 0xff [0xff] [] 1⟩
]

/-- The loop cases. -/
def loopCases : List LoopCase := [
  ⟨"script_tests.json:442 CODESEPARATOR 1", [0xab, 0x51],
    [ins 0xab [0xab] [] 1, ins 0x51 [0x51] [] 2, .atEnd]⟩,
  ⟨"script_tests.json:721 0x4c01", [0x4c, 0x01], [.truncated 0x4c .payload 2]⟩,
  ⟨"GetOp2: 01 ab, a separator byte as data", [0x01, 0xab], [ins 0x01 [0x01, 0xab] [0xab] 2, .atEnd]⟩,
  ⟨"GetOp2: 02 abab ab, data then a separator", [0x02, 0xab, 0xab, 0xab],
    [ins 0x02 [0x02, 0xab, 0xab] [0xab, 0xab] 3, ins 0xab [0xab] [] 4, .atEnd]⟩,
  ⟨"GetOp2: 4c ab and 171 bytes ab, a separator byte as the length", [0x4c, 0xab] ++ rep 171 0xab,
    [ins 0x4c ([0x4c, 0xab] ++ rep 171 0xab) (rep 171 0xab) 173, .atEnd]⟩,
  ⟨"GetOp2: 4d 0100 ab ab", [0x4d, 0x01, 0x00, 0xab, 0xab],
    [ins 0x4d [0x4d, 0x01, 0x00, 0xab] [0xab] 4, ins 0xab [0xab] [] 5, .atEnd]⟩,
  ⟨"GetOp2: 51 02aabb ab, the loop never reads cursor 2", [0x51, 0x02, 0xaa, 0xbb, 0xab],
    [ins 0x51 [0x51] [] 1, ins 0x02 [0x02, 0xaa, 0xbb] [0xaa, 0xbb] 4, ins 0xab [0xab] [] 5, .atEnd]⟩,
  ⟨"GetOp2: 61 4e000000, a short length field after an instruction", [0x61, 0x4e, 0x00, 0x00, 0x00],
    [ins 0x61 [0x61] [] 1, .truncated 0x4e .lengthField 2]⟩
]

/-- The results of the loop of `readInstruction` calls from cursor 0, up to and including the first result that is not an instruction. Each instruction moves the cursor forward, so `script.length + 1` calls are enough. -/
def loop (script : List UInt8) : List ReadResult :=
  go (script.length + 1) 0
where
  go : Nat → Nat → List ReadResult
    | 0, _ => []
    | fuel + 1, pc =>
      match readInstruction script pc with
      | .instruction i => .instruction i :: go fuel i.next
      | r => [r]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  if cases.length != 50 || loopCases.length != 8 then
    IO.eprintln s!"FAIL script reader: {cases.length} cases and {loopCases.length} loop cases, expected 50 and 8"
    failures := failures + 1
  for c in cases do
    let got := readInstruction c.script c.pc
    unless got == c.expected do
      IO.eprintln s!"FAIL {c.label}: got {repr got}, expected {repr c.expected}"
      failures := failures + 1
  for c in loopCases do
    let got := loop c.script
    unless got == c.expected do
      IO.eprintln s!"FAIL {c.label}: got {repr got}, expected {repr c.expected}"
      failures := failures + 1
  -- EvalScript resets every local at the start of a call (interpreter.cpp lines 258 to 268).
  -- VerifyScript passes only `stack` to the next call (lines 1424 and 1429).
  -- The prior state has a nonempty altstack, cursors, conditional stack and count.
  -- Its stack holds an empty item, negative zero and a two-byte zero, which stay raw.
  let prior : ExecState :=
    { stack := [[], [0x80], [0, 0]], altstack := [[0xff]], pc := 99, beginCodeHash := 80,
      vfExec := [true, false], opCount := 201 }
  let reset : ExecState :=
    { stack := [[], [0x80], [0, 0]], altstack := [], pc := 0, beginCodeHash := 0,
      vfExec := [], opCount := 0 }
  unless prior.handOff == reset && ExecState.init prior.stack == reset && reset.fExec &&
      !prior.fExec do
    IO.eprintln s!"FAIL script state reset and hand-off: got {repr prior.handOff}, expected {repr reset}"
    failures := failures + 1
  IO.println s!"script reader: {cases.length} cases, {loopCases.length} loop cases, state reset and hand-off, {failures} failures"
  return failures

end KnownAnswers.Script

/-!
## Script numbers and truth values

Runs `ScriptNum.encode`, `decode`, `getint` and `castToBool` through the compiled code.

Every expected byte string and value is written by hand from the byte layout of `CScriptNum` (SOURCES.md, D24, lines 198 to 371) and `CastToBool` (D3, lines 38 to 51).
None is computed by the definitions under test.
Each encoding case also fixes the result of decoding its expected bytes at sizes 4 and 5, with and without the minimal requirement.
The expected result is `overflow` when the expected bytes are longer than the size, and the value otherwise.

The sweep takes the integers of the `creation` test of `scriptnum_tests.cpp` (D44): every `values[i]` and `values[i] ± offsets[j]`.
That test compares `CScriptNum` with a copy of the 0.10.0 code and has no literal expected bytes.
Within ±(2^31 − 1), the operand range of the comment at D24 lines 200 to 207, each integer must survive the round trip.
The round trip is `encode`, then a default-size `decode`.
Outside that range the default-size decode must overflow.
`getint` must match a clamp written out below.
-/

namespace KnownAnswers.ScriptNum

open DogeLib.Script DogeLib.Script.ScriptNum

/-- An expected decode result. `Except` has no equality test, so the cases compare through this type. -/
inductive Expected where
  | ok (n : Int)
  | overflow
  | nonMinimal

/-- Whether a decode result is the expected one. -/
def Expected.matches : Expected → Except DecodeError Int → Bool
  | .ok n, .ok m => n == m
  | .overflow, .error .overflow => true
  | .nonMinimal, .error .nonMinimal => true
  | _, _ => false

/-- The expected decode of the encoding `bytes` of `n` at size `size`, from the length of the expected bytes. -/
def expectedAt (n : Int) (bytes : List UInt8) (size : Nat) : Expected :=
  if bytes.length ≤ size then .ok n else .overflow

/-- Integers and their encodings, hand-derived: magnitude little-endian, sign in the top bit of the last byte. -/
def encodeCases : List (Int × List UInt8) := [
  (0, []),
  (1, [0x01]), (-1, [0x81]),
  (127, [0x7f]), (-127, [0xff]),
  (128, [0x80, 0x00]), (-128, [0x80, 0x80]),
  (255, [0xff, 0x00]), (-255, [0xff, 0x80]),
  (256, [0x00, 0x01]), (-256, [0x00, 0x81]),
  (2147483647, [0xff, 0xff, 0xff, 0x7f]), (-2147483647, [0xff, 0xff, 0xff, 0xff]),
  -- Five-byte results: the magnitude fills the top bit, so one more byte carries the sign.
  (2147483648, [0x00, 0x00, 0x00, 0x80, 0x00]), (-2147483648, [0x00, 0x00, 0x00, 0x80, 0x80]),
  (4294967295, [0xff, 0xff, 0xff, 0xff, 0x00]), (-4294967295, [0xff, 0xff, 0xff, 0xff, 0x80]),
  (4294967296, [0x00, 0x00, 0x00, 0x00, 0x01]),
  (549755813887, [0xff, 0xff, 0xff, 0xff, 0x7f]), (-549755813887, [0xff, 0xff, 0xff, 0xff, 0xff]),
  -- 2^39: six bytes, beyond the size 5 of CHECKLOCKTIMEVERIFY.
  (549755813888, [0x00, 0x00, 0x00, 0x00, 0x80, 0x00])]

/-- Decode cases: a label, the bytes, the minimal requirement, the size and the expected result. -/
def decodeCases : List (String × List UInt8 × Bool × Nat × Expected) := [
  ("empty", [], true, 4, .ok 0),
  ("empty at size 0", [], true, 0, .ok 0),
  ("01 at size 0", [0x01], false, 0, .overflow),
  ("negative zero 80", [0x80], false, 4, .ok 0),
  ("negative zero 80, minimal", [0x80], true, 4, .nonMinimal),
  ("00", [0x00], false, 4, .ok 0),
  ("00, minimal", [0x00], true, 4, .nonMinimal),
  ("0000", [0x00, 0x00], false, 4, .ok 0),
  ("0000, minimal", [0x00, 0x00], true, 4, .nonMinimal),
  ("0080", [0x00, 0x80], false, 4, .ok 0),
  ("0080, minimal", [0x00, 0x80], true, 4, .nonMinimal),
  ("7f00", [0x7f, 0x00], false, 4, .ok 127),
  ("7f00, minimal", [0x7f, 0x00], true, 4, .nonMinimal),
  ("8000, minimal: the top bit of 80 needs the sign byte", [0x80, 0x00], true, 4, .ok 128),
  ("ff00, minimal", [0xff, 0x00], true, 4, .ok 255),
  ("ff80, minimal", [0xff, 0x80], true, 4, .ok (-255)),
  ("ffffff7f, minimal", [0xff, 0xff, 0xff, 0x7f], true, 4, .ok 2147483647),
  ("0000000000 at size 4, minimal: overflow first", [0x00, 0x00, 0x00, 0x00, 0x00], true, 4, .overflow),
  ("0000000000 at size 5, minimal", [0x00, 0x00, 0x00, 0x00, 0x00], true, 5, .nonMinimal),
  ("ffffffffff at size 4", [0xff, 0xff, 0xff, 0xff, 0xff], false, 4, .overflow),
  ("ffffffffff at size 5", [0xff, 0xff, 0xff, 0xff, 0xff], true, 5, .ok (-549755813887)),
  ("0000008080 at size 4", [0x00, 0x00, 0x00, 0x80, 0x80], true, 4, .overflow),
  ("0000008080 at size 5", [0x00, 0x00, 0x00, 0x80, 0x80], true, 5, .ok (-2147483648)),
  ("ffffffff00 at size 5", [0xff, 0xff, 0xff, 0xff, 0x00], true, 5, .ok 4294967295)]

/-- `getint` cases: an integer and its value saturated to `[-2^31, 2^31 - 1]`. -/
def getintCases : List (Int × Int) := [
  (0, 0), (-1, -1),
  (2147483647, 2147483647), (-2147483647, -2147483647),
  (2147483648, 2147483647), (-2147483648, -2147483648), (-2147483649, -2147483648),
  (1099511627776, 2147483647), (-1099511627776, -2147483648)]

/-- `castToBool` cases: a label, the bytes and the expected truth value. -/
def castCases : List (String × List UInt8 × Bool) := [
  ("empty", [], false),
  ("00", [0x00], false),
  ("negative zero 80", [0x80], false),
  ("0080", [0x00, 0x80], false),
  ("000080", [0x00, 0x00, 0x80], false),
  ("600 zero bytes", List.replicate 600 0x00, false),
  ("600 zero bytes and 80", List.replicate 600 0x00 ++ [0x80], false),
  ("01", [0x01], true),
  ("81", [0x81], true),
  ("8000: 80 is not the last byte", [0x80, 0x00], true),
  ("008000", [0x00, 0x80, 0x00], true),
  ("0001", [0x00, 0x01], true),
  ("600 zero bytes and 01", List.replicate 600 0x00 ++ [0x01], true)]

/-- `values` of `scriptnum_tests.cpp` (D44, line 17). -/
def sweepValues : List Int :=
  [0, 1, -2, 127, 128, -255, 256, 2 ^ 15 - 1, -(2 ^ 16), 2 ^ 24 - 1, 2 ^ 31, 1 - 2 ^ 32, 2 ^ 40]

/-- `offsets` of `scriptnum_tests.cpp` (D44, line 19). -/
def sweepOffsets : List Int := [1, 0x79, 0x80, 0x81, 0xFF, 0x7FFF, 0x8000, 0xFFFF, 0x10000]

/-- The integers of the `creation` test (D44, lines 169 to 180). Core runs `values[i]` once for each offset, and here it appears once. -/
def sweep : List Int :=
  sweepValues.flatMap fun v => v :: sweepOffsets.flatMap fun o => [v + o, v - o]

/-- The clamp of `getint`, written out: `INT_MAX` above, `INT_MIN` below. -/
def clamp (n : Int) : Int :=
  if n > 2147483647 then 2147483647 else if n < -2147483648 then -2147483648 else n

/-- Every Script number and truth-value known answer. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  let mut count := 0
  for (n, bytes) in encodeCases do
    count := count + 1
    if encode n != bytes then
      IO.eprintln s!"FAIL scriptnum encode {n}: got {encode n}, expected {bytes}"
      failures := failures + 1
    for size in [4, 5] do
      for req in [false, true] do
        count := count + 1
        if !(expectedAt n bytes size).matches (decode bytes req size) then
          IO.eprintln s!"FAIL scriptnum decode of the encoding of {n} at size {size}, minimal {req}"
          failures := failures + 1
  for (name, bytes, req, size, expected) in decodeCases do
    count := count + 1
    if !expected.matches (decode bytes req size) then
      IO.eprintln s!"FAIL scriptnum decode {name}"
      failures := failures + 1
  for (n, expected) in getintCases do
    count := count + 1
    if getint n != expected then
      IO.eprintln s!"FAIL scriptnum getint {n}: got {getint n}, expected {expected}"
      failures := failures + 1
  for (name, bytes, expected) in castCases do
    count := count + 1
    if castToBool bytes != expected then
      IO.eprintln s!"FAIL castToBool {name}"
      failures := failures + 1
  if sweep.length != 247 then
    IO.eprintln s!"FAIL scriptnum: the sweep has {sweep.length} integers, expected 247"
    failures := failures + 1
  for n in sweep do
    count := count + 1
    let inRange := -2147483647 ≤ n && n ≤ 2147483647
    let ok :=
      if inRange then
        (Expected.ok n).matches (decode (encode n) false) && (Expected.ok n).matches (decode (encode n) true)
      else
        Expected.overflow.matches (decode (encode n) false)
    if !ok || getint n != clamp n then
      IO.eprintln s!"FAIL scriptnum sweep {n}"
      failures := failures + 1
  IO.println s!"scriptnum/castToBool: {count} checks, {failures} failures"
  return failures

end KnownAnswers.ScriptNum


/-!
## Script evaluation

Runs `evalScript`, one `EvalScript` call, through the compiled code.

### Core's script corpus

Each record of `tests/script/corpus/script_tests.jsonl` is a `VerifyScript` call (SOURCES.md, D45 and D46), not one `EvalScript` call.
This test composes two calls of `evalScript` as `VerifyScript` does without its P2SH branch (D3, lines 1409 to 1435).
It runs `scriptSig` on an empty stack, and then `scriptPubKey` on the resulting main stack.
Both calls use `transactionChecker` over the record's spending transaction and input index, with `coreVerifier`.
So every record whose verdict needs an elliptic-curve check is compared, and the count of `signature verifier` results must be zero.
An empty final stack or a false top item gives `EVAL_FALSE`.
The composition is test code. DogeLib does not specify `VerifyScript` yet.

Three cases give an unsupported result instead of a comparison:

- A nonempty witness stack, which design record 0003 reports as unsupported.
- An unsupported result of either call. With `coreVerifier`, a signature opcode never gives one.
- Both calls succeed with a true top item, the P2SH flag is set and `scriptPubKey` is the exact P2SH template (D48, `CScript::IsPayToScriptHash`, lines 204 to 211). Core's verdict then depends on the P2SH branch.

The flags are the record's `effective_flags_mask`.
Every other record must give exactly the record's `expected_error`, where `OK` is acceptance.
The test fails on any disagreement, on a record outside the milestone that does not give unsupported, and when no record is compared.

### Hand cases

Each hand case fixes a script, flags, a caller stack and the expected result: the final main stack, Core's error, or the unsupported reason.
Every expected result is written by hand from `EvalScript` (D3, lines 248 to 1046), the limits of D24 lines 22 to 31, and the encoding of `CScriptNum` (D24, lines 198 to 371).
The expected digests of the hash cases come from Core's `script_tests.json` (D45), not from DogeLib's hash definitions.
The cases cover the limit boundaries, short pushes, unbalanced conditionals, and disabled and reserved opcodes in skipped branches.
They also cover stack underflow, negative zero, the operands of `OP_PICK` and `OP_ROLL`, and unsupported capabilities.
For the numeric opcodes they cover operand order, five-byte results, negative zero and non-minimal operands, `OP_NUMEQUALVERIFY` failure and the bounds of `OP_WITHIN`.
Each hand case runs without a checker, as in stage 2, and again with `baseChecker`.
The two runs expect the same result, except for a case that expects an unsupported signature opcode, which runs only without a checker.
-/

namespace KnownAnswers.ScriptEval

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- The outcome of one corpus record. -/
inductive Outcome where
  | accepted
  | rejected (e : ScriptError)
  | unsupported (reason : String)
  deriving BEq, Repr

/-- The label of an unsupported reason, for the counts. With `transactionChecker`, a signature opcode is unsupported only when it reaches the verifier. -/
def reasonLabel : Unsupported → String
  | .flags _ => "flags"
  | .signatureOpcode _ => "signature verifier"
  | .checkLockTimeVerify => "CHECKLOCKTIMEVERIFY"
  | .checkSequenceVerify => "CHECKSEQUENCEVERIFY"

/-- A `VerifyResult` as a corpus outcome. -/
def outcomeOf : VerifyResult → Outcome
  | .accepted => .accepted
  | .rejected e => .rejected e
  | .unsupported u => .unsupported (reasonLabel u)

/-- The fields of one corpus record that this test reads. -/
structure Record where
  line : Nat
  scriptSig : List UInt8
  scriptPubKey : List UInt8
  flags : UInt32
  expected : String
  witness : Bool
  inside : Bool
  /-- The spending transaction of the record's context, decoded in base mode. -/
  spendTx : DogeLib.Transaction.Transaction
  inputIndex : Nat

/-- Reads one line of `script_tests.jsonl`. -/
def parseRecord (text : String) : Except String Record := do
  let j ← Lean.Json.parse text
  let hex (k : String) : Except String (List UInt8) := do
    return (← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? k).getStr?)).toList
  let classification ← j.getObjVal? "classification"
  let context ← j.getObjVal? "context"
  let spendBytes ← KnownAnswers.Sha256Cavp.parseHex (← (← context.getObjVal? "spending_tx_base_hex").getStr?)
  let spendTx ← match DogeLib.Transaction.Transaction.decodeBaseComplete spendBytes.toList with
    | .ok tx => pure tx
    | .error _ => throw "spending_tx_base_hex does not decode"
  return {
    line := ← (← j.getObjVal? "source_line").getNat?
    scriptSig := ← hex "scriptSig_hex"
    scriptPubKey := ← hex "scriptPubKey_hex"
    flags := (← (← j.getObjVal? "effective_flags_mask").getNat?).toUInt32
    expected := ← (← j.getObjVal? "expected_error").getStr?
    witness := (← (← j.getObjVal? "witness").getArr?).size != 0
    inside := (← (← classification.getObjVal? "milestone").getStr?) == "inside"
    spendTx
    inputIndex := ← (← context.getObjVal? "input_index").getNat? }

/-- The name of an outcome in the corpus's terms. -/
def outcomeName : Outcome → String
  | .accepted => "OK"
  | .rejected e => e.name
  | .unsupported r => s!"unsupported ({r})"

/-- Runs every corpus record. Returns the number of failures. -/
def checkCorpus : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/script_tests.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut agree := 0
  let mut agreeAccepted := 0
  let mut unsupported : List (String × Nat) := [("signature verifier", 0)]
  -- Records with P2SH set and the template as `scriptPubKey`.
  let mut p2shAgree := 0
  let mut p2shVerifier := 0
  -- Records with a lock-time flag set and its opcode in a script.
  let mut lockAgree := 0
  let mut lockUnsupported := 0
  if lines.length != 1193 then
    IO.eprintln s!"FAIL {path}: {lines.length} records, expected 1193"
    failures := failures + 1
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    let got :=
      if r.witness then Outcome.unsupported "witness"
      else
        let checker := transactionChecker r.spendTx r.inputIndex.toUInt32 coreVerifier
        outcomeOf (verifyScript checker r.flags r.scriptSig r.scriptPubKey)
    let p2sh := !r.witness && hasFlag r.flags ScriptFlags.p2sh && isPayToScriptHash r.scriptPubKey
    let lock := !r.witness && unsupportedFlagBits r.flags == 0 &&
      ((hasFlag r.flags ScriptFlags.checkLockTimeVerify && (r.scriptSig.contains 0xb1 || r.scriptPubKey.contains 0xb1)) ||
        (hasFlag r.flags ScriptFlags.checkSequenceVerify && (r.scriptSig.contains 0xb2 || r.scriptPubKey.contains 0xb2)))
    match got with
    | .unsupported reason =>
      if p2sh && reason == "signature verifier" then p2shVerifier := p2shVerifier + 1
      if lock then lockUnsupported := lockUnsupported + 1
      unsupported :=
        if unsupported.any (·.1 == reason) then unsupported.map fun (k, n) => (k, if k == reason then n + 1 else n)
        else unsupported ++ [(reason, 1)]
    | _ =>
      if !r.inside then
        IO.eprintln s!"FAIL script_tests.json:{r.line}: outside the milestone, got {outcomeName got}"
        failures := failures + 1
      else if outcomeName got == r.expected then
        agree := agree + 1
        if p2sh then p2shAgree := p2shAgree + 1
        if lock then lockAgree := lockAgree + 1
        if r.expected == "OK" then agreeAccepted := agreeAccepted + 1
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: got {outcomeName got}, expected {r.expected}"
        failures := failures + 1
  if agree == 0 then
    IO.eprintln "FAIL script corpus: no record compared"
    failures := failures + 1
  if unsupported.any fun (k, n) => k == "signature verifier" && n != 0 then
    IO.eprintln "FAIL script corpus: a record reaches an unavailable verifier"
    failures := failures + 1
  let total := unsupported.foldl (fun acc (_, n) => acc + n) 0
  let detail := ", ".intercalate (unsupported.map fun (k, n) => s!"{k} {n}")
  IO.println s!"script corpus: {lines.length} records, {agree} agree with Core ({agreeAccepted} accepted, {agree - agreeAccepted} rejected), {failures} failures, {total} unsupported: {detail}"
  IO.println s!"script corpus: P2SH template with its flag {p2shAgree} agree, {p2shVerifier} reach the verifier; lock-time opcodes with their flags {lockAgree} agree, {lockUnsupported} unsupported"
  return failures

/-- The expected result of a hand case. -/
inductive Expect where
  /-- Success with this final main stack. -/
  | ok (stack : List (List UInt8))
  /-- Success with this final main stack and separator cursor. -/
  | okSeparator (stack : List (List UInt8)) (beginCodeHash : Nat)
  /-- Core's error. -/
  | rejected (e : ScriptError)
  /-- An unsupported capability. -/
  | unsupported (u : Unsupported)

/-- Whether `r` is the expected result `e`. -/
def Expect.matches : Expect → EvalResult → Bool
  | .ok stack, .ok s => s.stack == stack
  | .okSeparator stack b, .ok s => s.stack == stack && s.beginCodeHash == b
  | .rejected e, .rejected e' => e == e'
  | .unsupported u, .unsupported u' => u == u'
  | _, _ => false

/-- One hand case: a label, flags, a script, a caller stack and the expected result. -/
structure Case where
  label : String
  flags : UInt32
  script : List UInt8
  stack : List (List UInt8)
  expected : Expect

/-- `OP_PUSHDATA2` of `n` bytes `0x01`, for `n < 65536`. -/
def push2 (n : Nat) : List UInt8 := [0x4d, (n % 256).toUInt8, (n / 256).toUInt8] ++ rep n 0x01

/-- A script of exactly 10,000 bytes: 19 pushes of 520 bytes, each dropped, a 41-byte push, dropped, and `OP_1`. -/
def script10000 : List UInt8 :=
  (List.replicate 19 (push2 520 ++ [0x75])).flatten ++ [0x29] ++ rep 41 0x02 ++ [0x75, 0x51]

/-- The stack, numeric and hash opcodes on an empty stack, which give `INVALID_STACK_OPERATION` (D3, lines 478 to 871). -/
def underflowOps : List UInt8 :=
  [0x69, 0x6b, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d,
    0x82, 0x87, 0x88, 0x8b, 0x8c, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f, 0xa0,
    0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa]

/-- The bytes of a hexadecimal string. A bad digit gives no bytes, which no hash case expects. -/
def hex (s : String) : List UInt8 :=
  match KnownAnswers.Sha256Cavp.parseHex s with
  | .ok b => b.toList
  | .error _ => []

/-- The hand cases. -/
def cases : List Case := [
  -- MAX_OPS_PER_SCRIPT (D24 line 25, D3 lines 286 and 287).
  ⟨"201 counted NOPs", 0, rep 201 0x61, [], .ok []⟩,
  ⟨"202 counted NOPs", 0, rep 202 0x61, [], .rejected .opCount⟩,
  ⟨"201 counted, 199 of them skipped", 0, [0x00, 0x63] ++ rep 199 0x61 ++ [0x68], [], .ok []⟩,
  ⟨"202 counted, 200 of them skipped", 0, [0x00, 0x63] ++ rep 200 0x61 ++ [0x68], [], .rejected .opCount⟩,
  ⟨"OP_RESERVED does not count", 0, [0x00, 0x63, 0x50] ++ rep 199 0x61 ++ [0x68], [], .ok []⟩,
  ⟨"pushes and OP_1 to OP_16 do not count", 0, rep 201 0x61 ++ [0x00, 0x51, 0x60, 0x01, 0x07], [],
    .ok [[], [1], [16], [7]]⟩,
  -- MAX_SCRIPT_ELEMENT_SIZE (D24 line 22, D3 lines 282 and 283).
  ⟨"520-byte push", 0, push2 520, [], .ok [rep 520 0x01]⟩,
  ⟨"521-byte push", 0, push2 521, [], .rejected .pushSize⟩,
  ⟨"521-byte push in a skipped branch", 0, [0x00, 0x63] ++ push2 521 ++ [0x68], [], .rejected .pushSize⟩,
  -- The combined stack size (D3 line 1033).
  ⟨"1,000 items", 0, rep 1000 0x51, [], .ok (List.replicate 1000 [1])⟩,
  ⟨"1,001 items", 0, rep 1001 0x51, [], .rejected .stackSize⟩,
  ⟨"1,000 items on both stacks", 0, rep 1000 0x51 ++ [0x6b], [], .ok (List.replicate 999 [1])⟩,
  ⟨"1,001 items on both stacks", 0, rep 1000 0x51 ++ [0x6b, 0x51], [], .rejected .stackSize⟩,
  ⟨"1,001-item caller stack, empty script", 0, [], List.replicate 1001 [], .ok (List.replicate 1001 [])⟩,
  ⟨"1,001-item caller stack, OP_NOP", 0, [0x61], List.replicate 1001 [], .rejected .stackSize⟩,
  -- MAX_SCRIPT_SIZE (D24 line 31, D3 lines 266 and 267), checked before the opcode count.
  ⟨"10,000-byte script", 0, script10000, [], .ok [[1]]⟩,
  ⟨"10,001-byte script", 0, script10000 ++ [0x61], [], .rejected .scriptSize⟩,
  ⟨"10,001 NOPs", 0, rep 10001 0x61, [], .rejected .scriptSize⟩,
  -- Short pushes (D3 lines 280 and 281).
  ⟨"short OP_PUSHDATA1 length", 0, [0x4c], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA1 data", 0, [0x4c, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA2 length", 0, [0x4d, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA4 length", 0, [0x4e, 0x01, 0x00, 0x00], [], .rejected .badOpcode⟩,
  ⟨"short direct push", 0, [0x02, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short push in a skipped branch", 0, [0x00, 0x63, 0x02, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short push after OP_RETURN is not read", 0, [0x6a, 0x02, 0x01], [], .rejected .opReturn⟩,
  -- Conditionals (D3 lines 437 to 476 and 1042 to 1043).
  ⟨"OP_IF without OP_ENDIF", 0, [0x51, 0x63], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_ELSE alone", 0, [0x67], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_ENDIF alone", 0, [0x68], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_IF on an empty stack", 0, [0x63, 0x68], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_IF on an empty stack in a skipped branch", 0, [0x00, 0x63, 0x63, 0x68, 0x68], [], .ok []⟩,
  ⟨"two OP_ELSE", 0, [0x51, 0x63, 0x52, 0x67, 0x53, 0x67, 0x54, 0x68], [], .ok [[2], [4]]⟩,
  ⟨"OP_NOTIF", 0, [0x00, 0x64, 0x52, 0x67, 0x53, 0x68], [], .ok [[2]]⟩,
  ⟨"nested skipped OP_ELSE", 0, [0x00, 0x63, 0x00, 0x63, 0x67, 0x52, 0x68, 0x68], [], .ok []⟩,
  -- Disabled, reserved and invalid opcodes (D3 lines 289 to 304, 311 and 1028 to 1029).
  ⟨"OP_CAT in a skipped branch", 0, [0x00, 0x63, 0x7e, 0x68], [], .rejected .disabledOpcode⟩,
  ⟨"OP_RSHIFT in a skipped branch", 0, [0x00, 0x63, 0x99, 0x68], [], .rejected .disabledOpcode⟩,
  ⟨"OP_2MUL executed", 0, [0x51, 0x8d], [], .rejected .disabledOpcode⟩,
  ⟨"reserved and invalid opcodes in a skipped branch", 0,
    [0x00, 0x63, 0x50, 0x62, 0x89, 0x8a, 0xba, 0xff, 0x68, 0x51], [], .ok [[1]]⟩,
  ⟨"OP_VERIF in a skipped branch", 0, [0x00, 0x63, 0x65, 0x68], [], .rejected .badOpcode⟩,
  ⟨"OP_VERNOTIF in a skipped branch", 0, [0x00, 0x63, 0x66, 0x68], [], .rejected .badOpcode⟩,
  ⟨"OP_RESERVED executed", 0, [0x50], [], .rejected .badOpcode⟩,
  ⟨"OP_VER executed", 0, [0x62], [], .rejected .badOpcode⟩,
  ⟨"OP_RESERVED1 executed", 0, [0x89], [], .rejected .badOpcode⟩,
  ⟨"0xba executed", 0, [0xba], [], .rejected .badOpcode⟩,
  ⟨"0xff executed", 0, [0xff], [], .rejected .badOpcode⟩,
  ⟨"OP_RETURN in a skipped branch", 0, [0x00, 0x63, 0x6a, 0x68], [], .ok []⟩,
  ⟨"OP_RETURN executed", 0, [0x6a], [], .rejected .opReturn⟩,
  -- Underflow (D3 lines 478 to 738).
  ⟨"OP_FROMALTSTACK on an empty altstack", 0, [0x51, 0x6c], [], .rejected .invalidAltstackOperation⟩,
  ⟨"OP_SWAP on one item", 0, [0x51, 0x7c], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_2ROT on five items", 0, rep 5 0x51 ++ [0x71], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK on one item", 0, [0x00, 0x79], [], .rejected .invalidStackOperation⟩,
  -- Negative zero (D3 lines 38 to 51).
  ⟨"negative zero is false for OP_IF", 0, [0x01, 0x80, 0x63, 0x51, 0x67, 0x52, 0x68], [], .ok [[2]]⟩,
  ⟨"negative zero is false for OP_VERIFY", 0, [0x01, 0x80, 0x69], [], .rejected .verify⟩,
  ⟨"negative zero is false for OP_IFDUP", 0, [0x01, 0x80, 0x73], [], .ok [[0x80]]⟩,
  ⟨"0x0080 is false", 0, [0x02, 0x00, 0x80, 0x73], [], .ok [[0x00, 0x80]]⟩,
  ⟨"0x8000 is true", 0, [0x02, 0x80, 0x00, 0x73], [], .ok [[0x80, 0x00], [0x80, 0x00]]⟩,
  ⟨"negative zero and the empty string differ for OP_EQUAL", 0, [0x00, 0x01, 0x80, 0x87], [], .ok [[]]⟩,
  -- OP_PICK and OP_ROLL (D3 lines 648 to 664).
  ⟨"OP_PICK 1", 0, [0x52, 0x53, 0x51, 0x79], [], .ok [[2], [3], [2]]⟩,
  ⟨"OP_ROLL 1", 0, [0x52, 0x53, 0x51, 0x7a], [], .ok [[3], [2]]⟩,
  ⟨"OP_PICK 0", 0, [0x52, 0x53, 0x00, 0x79], [], .ok [[2], [3], [3]]⟩,
  ⟨"OP_PICK past the bottom", 0, [0x51, 0x51, 0x79], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK -1", 0, [0x51, 0x4f, 0x79], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK with a five-byte operand", 0, [0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x79], [],
    .rejected .unknownError⟩,
  ⟨"OP_ROLL with a nonminimal operand", 0, [0x52, 0x53, 0x02, 0x01, 0x00, 0x7a], [], .ok [[3], [2]]⟩,
  ⟨"OP_PICK with the five-byte operand 2^31", 0, [0x51, 0x51, 0x05, 0x00, 0x00, 0x00, 0x80, 0x00, 0x79], [],
    .rejected .unknownError⟩,
  ⟨"OP_PICK with 2^31 - 1", 0, [0x51, 0x51, 0x04, 0xff, 0xff, 0xff, 0x7f, 0x79], [],
    .rejected .invalidStackOperation⟩,
  -- Other stack operations (D3 lines 502 to 706).
  ⟨"OP_2ROT", 0, [0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x71], [], .ok [[3], [4], [5], [6], [1], [2]]⟩,
  ⟨"OP_2SWAP", 0, [0x51, 0x52, 0x53, 0x54, 0x72], [], .ok [[3], [4], [1], [2]]⟩,
  ⟨"OP_ROT", 0, [0x51, 0x52, 0x53, 0x7b], [], .ok [[2], [3], [1]]⟩,
  ⟨"OP_TUCK", 0, [0x51, 0x52, 0x7d], [], .ok [[2], [1], [2]]⟩,
  ⟨"OP_DEPTH", 0, [0x51, 0x74], [], .ok [[1], [1]]⟩,
  ⟨"OP_DEPTH of an empty stack", 0, [0x74], [], .ok [[]]⟩,
  ⟨"OP_SIZE", 0, [0x02, 0x01, 0x02, 0x82], [], .ok [[1, 2], [2]]⟩,
  ⟨"OP_SIZE of 128 bytes", 0, [0x4c, 0x80] ++ rep 128 0x00 ++ [0x82], [], .ok [rep 128 0x00, [0x80, 0x00]]⟩,
  ⟨"OP_1NEGATE", 0, [0x4f], [], .ok [[0x81]]⟩,
  ⟨"altstack round trip", 0, [0x51, 0x52, 0x6b, 0x53, 0x6c], [], .ok [[1], [3], [2]]⟩,
  ⟨"OP_EQUALVERIFY", 0, [0x51, 0x51, 0x88], [], .ok []⟩,
  ⟨"OP_EQUALVERIFY fails", 0, [0x51, 0x52, 0x88], [], .rejected .equalVerify⟩,
  ⟨"OP_CODESEPARATOR", 0, [0x51, 0xab, 0x51], [], .okSeparator [[1], [1]] 2⟩,
  ⟨"OP_CODESEPARATOR in a skipped branch", 0, [0x00, 0x63, 0xab, 0x68], [], .okSeparator [] 0⟩,
  -- NOPs and flags (D3 lines 347 to 435).
  ⟨"OP_NOP1 to OP_NOP10 without their flags", 0, [0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9], [],
    .ok []⟩,
  ⟨"OP_CHECKLOCKTIMEVERIFY with its flag", ScriptFlags.checkLockTimeVerify, [0x51, 0xb1], [],
    .unsupported .checkLockTimeVerify⟩,
  ⟨"OP_CHECKSEQUENCEVERIFY with its flag", ScriptFlags.checkSequenceVerify, [0x51, 0xb2], [],
    .unsupported .checkSequenceVerify⟩,
  ⟨"OP_CHECKLOCKTIMEVERIFY with its flag, skipped", ScriptFlags.checkLockTimeVerify, [0x00, 0x63, 0xb1, 0x68], [],
    .ok []⟩,
  ⟨"all seven supported flags", 0x061f, [0x51], [], .ok [[1]]⟩,
  ⟨"MINIMALDATA is unsupported", ScriptFlags.minimalData, [0x51], [], .unsupported (.flags 0x0040)⟩,
  ⟨"unsupported flags before the script size", ScriptFlags.p2sh ||| ScriptFlags.cleanStack ||| 0x10000,
    rep 10001 0x61, [], .unsupported (.flags 0x10100)⟩,
  -- Numeric opcodes (D3, lines 744 to 841, and D24, lines 198 to 371).
  ⟨"OP_ADD", 0, [0x51, 0x52, 0x93], [], .ok [[3]]⟩,
  ⟨"OP_SUB subtracts the top item", 0, [0x51, 0x52, 0x94], [], .ok [[0x81]]⟩,
  ⟨"OP_LESSTHAN 1 2", 0, [0x51, 0x52, 0x9f], [], .ok [[1]]⟩,
  ⟨"OP_LESSTHAN 2 1", 0, [0x52, 0x51, 0x9f], [], .ok [[]]⟩,
  ⟨"OP_GREATERTHAN -1 1", 0, [0x4f, 0x51, 0xa0], [], .ok [[]]⟩,
  ⟨"OP_LESSTHANOREQUAL 2 2", 0, [0x52, 0x52, 0xa1], [], .ok [[1]]⟩,
  ⟨"OP_GREATERTHANOREQUAL 1 2", 0, [0x51, 0x52, 0xa2], [], .ok [[]]⟩,
  ⟨"OP_MIN", 0, [0x51, 0x52, 0xa3], [], .ok [[1]]⟩,
  ⟨"OP_MAX", 0, [0x51, 0x52, 0xa4], [], .ok [[2]]⟩,
  ⟨"OP_NUMNOTEQUAL", 0, [0x51, 0x52, 0x9e], [], .ok [[1]]⟩,
  ⟨"OP_NEGATE", 0, [0x52, 0x8f], [], .ok [[0x82]]⟩,
  ⟨"OP_ABS -2", 0, [0x01, 0x82, 0x90], [], .ok [[2]]⟩,
  ⟨"OP_NOT 2", 0, [0x52, 0x91], [], .ok [[]]⟩,
  ⟨"OP_0NOTEQUAL 2", 0, [0x52, 0x92], [], .ok [[1]]⟩,
  ⟨"OP_1SUB 1", 0, [0x51, 0x8c], [], .ok [[]]⟩,
  -- Five-byte results are pushed, and a later numeric use gives UNKNOWN_ERROR.
  ⟨"OP_1ADD of 2^31 - 1", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b], [], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"OP_ADD of 2^31 - 1 twice", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x76, 0x93], [],
    .ok [[0xfe, 0xff, 0xff, 0xff, 0x00]]⟩,
  ⟨"OP_1SUB of -(2^31 - 1)", 0, [0x04, 0xff, 0xff, 0xff, 0xff, 0x8c], [], .ok [[0x00, 0x00, 0x00, 0x80, 0x80]]⟩,
  ⟨"OP_SUB of -(2^31 - 1) and 2^31 - 1", 0, [0x04, 0xff, 0xff, 0xff, 0xff, 0x04, 0xff, 0xff, 0xff, 0x7f, 0x94], [],
    .ok [[0xfe, 0xff, 0xff, 0xff, 0x80]]⟩,
  ⟨"a five-byte result fails a later OP_1ADD", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b, 0x8b], [],
    .rejected .unknownError⟩,
  ⟨"a five-byte result passes OP_SIZE", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b, 0x82], [],
    .ok [[0x00, 0x00, 0x00, 0x80, 0x00], [5]]⟩,
  ⟨"OP_1ADD on a five-byte operand", 0, [0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8b], [], .rejected .unknownError⟩,
  ⟨"OP_ADD on a five-byte top operand", 0, [0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x93], [],
    .rejected .unknownError⟩,
  ⟨"OP_ADD on a five-byte second operand", 0, [0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x51, 0x93], [],
    .rejected .unknownError⟩,
  ⟨"OP_ADD on one item", 0, [0x51, 0x93], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_1ADD on a five-byte operand in a skipped branch", 0, [0x00, 0x63, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x68],
    [], .ok []⟩,
  -- Negative zero and non-minimal operands, accepted without MINIMALDATA.
  ⟨"OP_1ADD of negative zero", 0, [0x01, 0x80, 0x8b], [], .ok [[1]]⟩,
  ⟨"OP_NOT of negative zero", 0, [0x01, 0x80, 0x91], [], .ok [[1]]⟩,
  ⟨"OP_ABS of negative zero", 0, [0x01, 0x80, 0x90], [], .ok [[]]⟩,
  ⟨"OP_NEGATE of negative zero", 0, [0x01, 0x80, 0x8f], [], .ok [[]]⟩,
  ⟨"OP_0NOTEQUAL of 0x0080", 0, [0x02, 0x00, 0x80, 0x92], [], .ok [[]]⟩,
  ⟨"OP_NUMEQUAL of negative zero and 0", 0, [0x01, 0x80, 0x00, 0x9c], [], .ok [[1]]⟩,
  ⟨"OP_BOOLAND of negative zero and 1", 0, [0x01, 0x80, 0x51, 0x9a], [], .ok [[]]⟩,
  ⟨"OP_BOOLOR of negative zero and 1", 0, [0x01, 0x80, 0x51, 0x9b], [], .ok [[1]]⟩,
  ⟨"OP_NUMEQUAL of 2 and 0x0200", 0, [0x52, 0x02, 0x02, 0x00, 0x9c], [], .ok [[1]]⟩,
  -- OP_NUMEQUALVERIFY (D3, lines 803 and 817 to 823).
  ⟨"OP_NUMEQUALVERIFY of 2 and 0x0200", 0, [0x52, 0x02, 0x02, 0x00, 0x9d], [], .ok []⟩,
  ⟨"OP_NUMEQUALVERIFY fails", 0, [0x51, 0x52, 0x9d], [], .rejected .numEqualVerify⟩,
  ⟨"OP_NUMEQUALVERIFY of 0 and negative zero", 0, [0x51, 0x00, 0x01, 0x80, 0x9d], [], .ok [[1]]⟩,
  -- OP_WITHIN (D3, lines 827 to 841): x lo hi gives lo <= x < hi.
  ⟨"OP_WITHIN at the lower bound", 0, [0x00, 0x00, 0x51, 0xa5], [], .ok [[1]]⟩,
  ⟨"OP_WITHIN at the upper bound", 0, [0x51, 0x00, 0x51, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN with lo above hi", 0, [0x51, 0x52, 0x00, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN with negative bounds", 0, [0x4f, 0x4f, 0x00, 0xa5], [], .ok [[1]]⟩,
  ⟨"OP_WITHIN below the lower bound", 0, [0x4f, 0x00, 0x51, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN on two items", 0, [0x51, 0x51, 0xa5], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_WITHIN on a five-byte bound", 0, [0x51, 0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa5], [],
    .rejected .unknownError⟩,
  -- Hash opcodes on the empty input (D3, lines 847 to 871). The digests are those of Core's script_tests.json (D45),
  -- lines 216, 219, 222, 227 and 230.
  ⟨"OP_RIPEMD160 of the empty input", 0, [0x00, 0xa6], [], .ok [hex "9c1185a5c5e9fc54612808977ee8f548b2258d31"]⟩,
  ⟨"OP_SHA1 of the empty input", 0, [0x00, 0xa7], [], .ok [hex "da39a3ee5e6b4b0d3255bfef95601890afd80709"]⟩,
  ⟨"OP_SHA256 of the empty input", 0, [0x00, 0xa8], [],
    .ok [hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"]⟩,
  ⟨"OP_HASH160 of the empty input", 0, [0x00, 0xa9], [], .ok [hex "b472a266d0bd89c13706a4132ccfb16f7c3b9fcb"]⟩,
  ⟨"OP_HASH256 of the empty input", 0, [0x00, 0xaa], [],
    .ok [hex "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"]⟩,
  ⟨"OP_HASH160 is OP_RIPEMD160 of OP_SHA256", 0, [0x01, 0x61, 0x76, 0xa9, 0x7c, 0xa8, 0xa6, 0x87], [], .ok [[1]]⟩,
  ⟨"OP_HASH256 is OP_SHA256 twice", 0, [0x01, 0x61, 0x76, 0xaa, 0x7c, 0xa8, 0xa8, 0x87], [], .ok [[1]]⟩,
  -- Capabilities of later stages.
  ⟨"OP_CHECKSIG executed", 0, [0xac], [], .unsupported (.signatureOpcode 0xac)⟩,
  ⟨"later-stage opcodes in a skipped branch", 0, [0x00, 0x63, 0x93, 0xa5, 0xa9, 0xac, 0xaf, 0x68], [], .ok []⟩
]

/-- Runs every hand case. Returns the number of failures. -/
def checkCases : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript none c.flags c.script c.stack
    unless c.expected.matches got do
      IO.eprintln s!"FAIL script eval {c.label}: got {repr got}"
      failures := failures + 1
    -- Without a checker these opcodes are unsupported. `KnownAnswers.ScriptVerify` covers them with `baseChecker`.
    let needsChecker := match c.expected with
      | .unsupported (.signatureOpcode _) | .unsupported .checkLockTimeVerify | .unsupported .checkSequenceVerify => true
      | _ => false
    unless needsChecker do
      let got := evalScript (some baseChecker) c.flags c.script c.stack
      unless c.expected.matches got do
        IO.eprintln s!"FAIL script eval {c.label} with baseChecker: got {repr got}"
        failures := failures + 1
  for op in underflowOps do
    for checker in [none, some baseChecker] do
      let got := evalScript checker 0 [op] []
      unless got == .rejected .invalidStackOperation do
        IO.eprintln s!"FAIL script eval underflow of {op}: got {repr got}"
        failures := failures + 1
  unless script10000.length == 10000 do
    IO.eprintln s!"FAIL script eval: the 10,000-byte script has {script10000.length} bytes"
    failures := failures + 1
  let table ← IO.FS.readFile "harness/core/script_error_names.inc"
  let names := table.splitOn "\n" |>.filterMap fun line =>
    if line.startsWith "SCRIPT_ERROR(" then (line.splitOn "\"")[1]? else none
  unless names == "OK" :: ScriptError.all.map ScriptError.name do
    IO.eprintln "FAIL Script error names: the Core table and Lean names differ"
    failures := failures + 1
  IO.println s!"script eval: {cases.length} hand cases, {underflowOps.length} underflow cases, {failures} failures"
  return failures

/-- Runs the corpus and the hand cases. Returns the number of failures. -/
def check : IO Nat := do
  return (← checkCases) + (← checkCorpus)

end KnownAnswers.ScriptEval

namespace KnownAnswers.SignatureCode

open DogeLib.Script

/--
All sixteen cases of Core's `script_FindAndDelete` (D46), in source order, as input, pattern, output and count.
Copied from Dogecoin Core `e0a1c157791544e818c901bd9341896965afbf9d`, `src/test/script_tests.cpp`, under the MIT licence.
The opcode constructors are expanded to their exact bytes.
The upstream licence is in `LICENSES/dogecoin-core-MIT.txt`.
-/
def coreCases : List (String × String × String × Nat) := [
  ("5152", "", "5152", 0),
  ("515253", "52", "5153", 1),
  ("535153535453", "53", "5154", 4),
  ("0302ff03", "0302ff03", "", 1),
  ("0302ff030302ff03", "0302ff03", "", 2),
  ("0302ff030302ff03", "02", "0302ff030302ff03", 0),
  ("0302ff030302ff03", "ff", "0302ff030302ff03", 0),
  ("0302ff030302ff03", "03", "02ff0302ff03", 2),
  ("02feed5169", "feed51", "02feed5169", 0),
  ("02feed5169", "02feed51", "69", 1),
  ("516902feed5169", "feed51", "516902feed5169", 0),
  ("516902feed5169", "02feed51", "516969", 1),
  ("00005151", "0051", "0051", 1),
  ("000051005151", "0051", "0051", 2),
  ("0003feed", "03feed", "00", 1),
  ("0003feed", "00", "03feed", 1)]

/-- Malformed suffix cases derived from D24's deletion loop and failed `GetOp2` reads. -/
def tailCases : List (String × String × String × Nat) := [
  ("514c", "51", "4c", 1),
  ("514d01", "51", "4d01", 1),
  ("514e010203", "51", "4e010203", 1),
  ("514c02aa", "51", "4c02aa", 1),
  ("514d0200aa", "51", "4d0200aa", 1),
  ("514e02000000aa", "51", "4e02000000aa", 1),
  ("4c02aa51", "51", "4c02aa51", 0),
  ("4c03aa51", "51", "4c03aa51", 0)]

/-- Push headers at every size transition, derived from Core's vector overload (D24, lines 437 to 464). -/
def pushCases : List (Nat × List UInt8) := [
  (0, [0x00]), (1, [0x01]), (75, [0x4b]), (76, [0x4c, 0x4c]),
  (255, [0x4c, 0xff]), (256, [0x4d, 0x00, 0x01]),
  (65535, [0x4d, 0xff, 0xff]), (65536, [0x4e, 0x00, 0x00, 0x01, 0x00])]

/-- Run Core's complete deletion test, malformed suffix cases, push boundaries and signature-code preparation. -/
def check : IO Nat := do
  let mut failures := 0
  unless coreCases.length == 16 do
    throw (IO.userError "FindAndDelete corpus must contain sixteen cases")
  for (s, b, out, count) in coreCases ++ tailCases do
    let .ok sBytes := Sha256Cavp.parseHex s | throw (IO.userError "invalid input hex")
    let .ok bBytes := Sha256Cavp.parseHex b | throw (IO.userError "invalid pattern hex")
    let .ok outBytes := Sha256Cavp.parseHex out | throw (IO.userError "invalid output hex")
    let got := DogeLib.Transaction.findAndDelete sBytes.toList bBytes.toList
    unless got == (outBytes.toList, count) do
      IO.eprintln s!"FAIL FindAndDelete {s} / {b}: {repr got}"
      failures := failures + 1
  for (n, header) in pushCases do
    let data := List.replicate n (0xab : UInt8)
    let expected := header ++ data
    unless pushEncoding data == expected do
      IO.eprintln s!"FAIL push encoding at {n} bytes"
      failures := failures + 1
    let got := readInstruction (pushEncoding data ++ [0x61]) 0
    let expectedRead := ReadResult.instruction ⟨header.head!, expected, data, expected.length⟩
    unless got == expectedRead do
      IO.eprintln s!"FAIL push reader at {n} bytes"
      failures := failures + 1
  -- Vector construction never substitutes OP_1 or OP_1NEGATE (D24).
  unless pushEncoding [0x01] == [0x01, 0x01] && pushEncoding [0x81] == [0x01, 0x81] do
    IO.eprintln "FAIL single-byte vector push"
    failures := failures + 1
  -- Stack signature suffix [01, 02] has 02 nearest the top (D3, stacktop(-isig-k)).
  -- The script prefix before cursor 2 stays outside the selected code.
  let script := [0x61, 0xab, 0x01, 0x01, 0xab, 0x02, 0x01, 0x02, 0x01, 0x02, 0x4c]
  let first := effectiveScriptCode script 2 [[0x02]]
  let both := effectiveScriptCode script 2 [[0x02], [0x01]]
  unless first == [0x01, 0x01, 0xab, 0x02, 0x01, 0x02, 0x4c] &&
      both == [0xab, 0x02, 0x01, 0x02, 0x4c] &&
      both == effectiveScriptCode first 0 [[0x01]] do
    IO.eprintln "FAIL multisig signature visitation, retained payload or malformed suffix"
    failures := failures + 1
  unless effectiveScriptCode [0x00, 0x61, 0x00] 0 [[]] == [0x61] &&
      effectiveScriptCode script 2 [] == script.drop 2 &&
      effectiveScriptCode script 99 [[0x01]] == [] do
    IO.eprintln "FAIL empty signature or suffix selection"
    failures := failures + 1
  IO.println s!"signature code: 16 Core deletion cases, 8 malformed tails, 8 push boundaries, preparation cases, {failures} failures"
  return failures

end KnownAnswers.SignatureCode

/-!
## Signature and public-key encoding

Runs the encoding checks of `DogeLib.Script.SignatureEncoding` through the compiled code.

### Core's script corpus

The test selects every record of `tests/script/corpus/script_tests.jsonl` (SOURCES.md, D45 and D46) with these properties:

- The record is inside the milestone, and its witness stack is empty.
- Its `scriptPubKey` is one direct push, opcode `0x00` to `0x4b`, then `OP_CHECKSIG` (`0xac`), optionally followed by `OP_NOT` (`0x91`).

The selected records are the P2PK and P2PK NOT records.
The test runs the record's `scriptSig` with `evalScript` and the record's `effective_flags_mask`, and takes the top stack item as the signature.
The pushed bytes of `scriptPubKey` are the public key.
`OP_CHECKSIG` runs `CheckSignatureEncoding` and then `CheckPubKeyEncoding` before it verifies anything (D3, line 898).
So each selected record expects one of these outcomes:

- `SIG_DER`, `SIG_HIGH_S`, `SIG_HASHTYPE` or `PUBKEYTYPE`: the two checks, in Core's order, give exactly that error.
- `OK` or `EVAL_FALSE`: both checks pass.

The test skips and counts a selected record with any other expected error, and one whose `scriptSig` does not give a nonempty stack.
The expected outcome is the record's, never a DogeLib result.
The test fails on any disagreement, and when no record of one of the four errors is compared.
Multisig records are not selected here. The script corpus test compares them through the evaluator.

### Hand cases

Every expected result is written by hand from `IsValidSignatureEncoding` and the other checks (D3, lines 66 to 223), the lax parser (D50, lines 27 to 166) and the order constants (D53, lines 13 to 27).
None is computed by the definitions under test.
The cases cover each strict-DER rule, and the lax parser's length forms, trailing bytes and overflows.
They also cover the LOW_S bound and the overflow case of design record 0003, section 5.
The rest cover the order of the three signature errors, the hash types and the public-key shapes.
-/

namespace KnownAnswers.SignatureEncoding

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- The bytes of a hexadecimal string. A bad digit gives no bytes, which no case expects. -/
def hex (s : String) : List UInt8 := KnownAnswers.ScriptEval.hex s

/-- The name of a check result: `OK`, or Core's error name. -/
def resultName : Except ScriptError Unit → String
  | .ok () => "OK"
  | .error e => e.name

/-- The public key of a P2PK or P2PK NOT `scriptPubKey`: one push of opcode `0x00` to `0x4b`, then `OP_CHECKSIG`, optionally then `OP_NOT`. -/
def p2pkKey : List UInt8 → Option (List UInt8)
  | [] => none
  | op :: rest =>
    let n := op.toNat
    let key := rest.take n
    let tail := rest.drop n
    if n ≤ 0x4b && key.length == n && (tail == [0xac] || tail == [0xac, 0x91]) then some key else none

/-- The result of `CheckSignatureEncoding` and then `CheckPubKeyEncoding`, as `OP_CHECKSIG` runs them (D3, line 898). -/
def checkBoth (sig key : List UInt8) (flags : UInt32) : String :=
  match checkSignatureEncoding sig flags with
  | .error e => e.name
  | .ok () => resultName (checkPubKeyEncoding key flags)

/-- The four encoding errors. -/
def encodingErrors : List String := ["SIG_DER", "SIG_HIGH_S", "SIG_HASHTYPE", "PUBKEYTYPE"]

/-- Runs the selected corpus records. Returns the number of failures. -/
def checkCorpus : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/script_tests.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut selected := 0
  let mut passes := 0
  let mut skipped := 0
  let mut errors : List (String × Nat) := encodingErrors.map (·, 0)
  for text in lines do
    let r ← match KnownAnswers.ScriptEval.parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if !r.inside || r.witness then continue
    let some key := p2pkKey r.scriptPubKey | continue
    selected := selected + 1
    let sig? := match evalScript none r.flags r.scriptSig [] with
      | .ok s => s.stack.getLast?
      | _ => none
    let some sig := sig? | skipped := skipped + 1; continue
    let got := checkBoth sig key r.flags
    if encodingErrors.contains r.expected then
      if got == r.expected then
        errors := errors.map fun (k, n) => (k, if k == r.expected then n + 1 else n)
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: encoding checks give {got}, expected {r.expected}"
        failures := failures + 1
    else if r.expected == "OK" || r.expected == "EVAL_FALSE" then
      if got == "OK" then passes := passes + 1
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: encoding checks give {got}, expected both to pass ({r.expected})"
        failures := failures + 1
    else skipped := skipped + 1
  for (k, n) in errors do
    if n == 0 then
      IO.eprintln s!"FAIL signature encoding corpus: no {k} record compared"
      failures := failures + 1
  let detail := ", ".intercalate (errors.map fun (k, n) => s!"{k} {n}")
  IO.println s!"signature encoding corpus: {selected} P2PK records, {passes} pass both checks, {detail}, {skipped} skipped, {failures} failures"
  return failures

/-- The secp256k1 group order `n`, written out from D53 lines 13 to 16. -/
def orderBytes : List UInt8 := hex "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
/-- `n − 1`. -/
def orderMinusOneBytes : List UInt8 := hex "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140"
/-- Half the order, `⌊n/2⌋`, written out from D53 lines 24 to 27. -/
def halfBytes : List UInt8 := hex "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0"
/-- `⌊n/2⌋ + 1`. -/
def halfPlusOneBytes : List UInt8 := hex "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A1"

/-- A strict-DER signature with R = 1, S = 1 and hash type `0x01`. -/
def basic : List UInt8 := hex "300602010102010101"
/-- Strict DER with R = 1, S = `⌊n/2⌋ + 1`, a high S, and hash type `0x01`. -/
def highS : List UInt8 := hex "30250201010220" ++ halfPlusOneBytes ++ [0x01]

/-- The `isValidSignatureEncoding` cases: label, bytes, expected result. -/
def derCases : List (String × List UInt8 × Bool) := [
  ("R = 1, S = 1, 9 bytes", basic, true),
  ("8 bytes", hex "3005020101020001", false),
  ("73 bytes, R and S of 33 bytes", hex "3046022100" ++ rep 32 0xff ++ hex "02210080" ++ rep 31 0x00 ++ [0x01], true),
  ("74 bytes", hex "3047022200" ++ rep 33 0xff ++ hex "02210080" ++ rep 31 0x00 ++ [0x01], false),
  ("compound tag 0x31", hex "310602010102010101", false),
  ("total length one more", hex "300702010102010101", false),
  ("total length one less", hex "300502010102010101", false),
  ("R length past the end", hex "300602040102010101", false),
  ("trailing byte: lengths do not add up", hex "30070201010201010101", false),
  ("R tag 0x03", hex "300603010102010101", false),
  ("S tag 0x03", hex "300602010103010101", false),
  ("zero-length R", hex "300602000202010101", false),
  ("zero-length S", hex "300602020101020001", false),
  ("negative R", hex "300602018102010101", false),
  ("negative S", hex "300602010102018101", false),
  ("excess R padding", hex "30070202000102010101", false),
  ("required R padding", hex "30070202008002010101", true),
  ("R = 0, one zero byte", hex "300602010002010101", true),
  ("excess S padding", hex "30070201010202000101", false),
  ("required S padding", hex "30070201010202008001", true),
  ("empty", [], false)]

/-- The `parseDerLax` cases, on bytes without a hash type: label, bytes, expected result. -/
def laxCases : List (String × List UInt8 × Option (Nat × Nat)) := [
  ("R = 1, S = 2", hex "3006020101020102", some (1, 2)),
  ("empty", [], none),
  ("sequence tag 0x31", hex "3106020101020102", none),
  ("sequence length ignored", hex "3000020101020102", some (1, 2)),
  ("long-form sequence length", hex "308106020101020102", some (1, 2)),
  ("long-form sequence length 0x80, no bytes", hex "3080020101020102", some (1, 2)),
  ("long-form sequence length past the end", hex "30850201", none),
  ("long-form R length with leading zeros", hex "30000282000105020107", some (5, 7)),
  ("long-form R length of 8 bytes", hex "3000028801" ++ rep 7 0x00 ++ hex "0101020102", none),
  ("R length past the end", hex "3006020501020102", none),
  ("missing S", hex "3003020101", none),
  ("S tag 0x03", hex "3006020101030102", none),
  ("trailing bytes ignored", hex "3006020101020102ffff", some (1, 2)),
  ("negative R, unsigned value", hex "3006020181020102", some (0x81, 2)),
  ("excess R padding", hex "300702020001020102", some (1, 2)),
  ("zero-length R", hex "30050200020102", some (0, 2)),
  ("R = n − 1 with a leading zero", hex "3026022100" ++ orderMinusOneBytes ++ hex "020101",
    some (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140, 1)),
  ("R = n overflows", hex "30250220" ++ orderBytes ++ hex "020101", some (0, 0)),
  ("S = n overflows", hex "3025020101" ++ [0x02, 0x20] ++ orderBytes, some (0, 0)),
  ("R of 33 significant bytes overflows", hex "3026022101" ++ rep 32 0x00 ++ hex "020101", some (0, 0)),
  ("R of 32 bytes 0xff and a leading zero overflows", hex "3026022100" ++ rep 32 0xff ++ hex "020101", some (0, 0))]

/-- The `laxIntegerLength` cases at position 0 with an 8-byte `size_t`: label, bytes, expected length and next position.
They test the count of significant bytes and the skipped leading zeros of D50, lines 72 to 77. -/
def lengthCases : List (String × List UInt8 × Option (Nat × Nat)) := [
  ("seven significant bytes", hex "8701" ++ rep 6 0x00, some (0x1000000000000, 8)),
  ("eight significant bytes", hex "8801" ++ rep 7 0x00, none),
  ("eight bytes, seven of them leading zeros", hex "88" ++ rep 7 0x00 ++ [0x01], some (1, 9))]

/-- The `checkLowS` cases, on bytes without a hash type: label, bytes, expected result. -/
def lowSCases : List (String × List UInt8 × Bool) := [
  ("S = ⌊n/2⌋", hex "30250201010220" ++ halfBytes, true),
  ("S = ⌊n/2⌋ + 1", hex "30250201010220" ++ halfPlusOneBytes, false),
  ("S = 1", hex "3006020101020101", true),
  ("not parseable", hex "3106020101020101", false),
  ("overflow: R = 2^256 − 1 and S = 2^255 − 1",
    hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff, true)]

/-- The flag sets of the cases. -/
def derSig := ScriptFlags.derSig
def lowS := ScriptFlags.lowS
def strictEnc := ScriptFlags.strictEnc
def allEnc := ScriptFlags.derSig ||| ScriptFlags.lowS ||| ScriptFlags.strictEnc

/-- The `checkSignatureEncoding` cases: label, signature, flags, expected result. -/
def sigCases : List (String × List UInt8 × UInt32 × String) := [
  ("empty, no flags", [], 0, "OK"),
  ("empty, all encoding flags", [], allEnc, "OK"),
  ("not DER, no flags", hex "300603010102010101", 0, "OK"),
  ("not DER, DERSIG", hex "300603010102010101", derSig, "SIG_DER"),
  ("not DER, LOW_S", hex "300603010102010101", lowS, "SIG_DER"),
  ("not DER, STRICTENC", hex "300603010102010101", strictEnc, "SIG_DER"),
  ("high S, LOW_S", highS, lowS, "SIG_HIGH_S"),
  ("high S, DERSIG", highS, derSig, "OK"),
  ("high S, STRICTENC", highS, strictEnc, "OK"),
  ("hash type 0x00, STRICTENC", hex "300602010102010100", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x00, DERSIG", hex "300602010102010100", derSig, "OK"),
  ("hash type 0x00, LOW_S", hex "300602010102010100", lowS, "OK"),
  ("not DER and hash type 0x00, STRICTENC", hex "300603010102010100", strictEnc, "SIG_DER"),
  ("high S and hash type 0x00, LOW_S and STRICTENC",
    hex "30250201010220" ++ halfPlusOneBytes ++ [0x00], lowS ||| strictEnc, "SIG_HIGH_S"),
  ("overflow example, all encoding flags",
    hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff ++ [0x01], allEnc, "OK"),
  ("hash type 0x01", basic, strictEnc, "OK"),
  ("hash type 0x02", hex "300602010102010102", strictEnc, "OK"),
  ("hash type 0x03", hex "300602010102010103", strictEnc, "OK"),
  ("hash type 0x04", hex "300602010102010104", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x81", hex "300602010102010181", strictEnc, "OK"),
  ("hash type 0x83", hex "300602010102010183", strictEnc, "OK"),
  ("hash type 0x84", hex "300602010102010184", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x80", hex "300602010102010180", strictEnc, "SIG_HASHTYPE")]

/-- The public-key cases: label, key, flags, expected `checkPubKeyEncoding` result, expected `isValidPubKey`. -/
def keyCases : List (String × List UInt8 × UInt32 × String × Bool) := [
  ("compressed 0x02", 0x02 :: rep 32 0x11, strictEnc, "OK", true),
  ("compressed 0x03", 0x03 :: rep 32 0x11, strictEnc, "OK", true),
  ("uncompressed 0x04", 0x04 :: rep 64 0x11, strictEnc, "OK", true),
  ("hybrid 0x06", 0x06 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", true),
  ("hybrid 0x07", 0x07 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", true),
  ("hybrid 0x06, no flags", 0x06 :: rep 64 0x11, 0, "OK", true),
  ("header 0x05", 0x05 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x02 with 32 bytes", 0x02 :: rep 31 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x02 with 65 bytes", 0x02 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x04 with 33 bytes", 0x04 :: rep 32 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x04 with 64 bytes", 0x04 :: rep 63 0x11, strictEnc, "PUBKEYTYPE", false),
  ("empty", [], strictEnc, "PUBKEYTYPE", false),
  ("empty, no flags", [], 0, "OK", false)]

/-- Every encoding known answer. Returns the number of failures. -/
def check : IO Nat := do
  let corpusFailures ← checkCorpus
  let mut failures := 0
  let mut count := 0
  for (label, bytes, expected) in derCases do
    count := count + 1
    if isValidSignatureEncoding bytes != expected then
      IO.eprintln s!"FAIL isValidSignatureEncoding {label}: expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in laxCases do
    count := count + 1
    if parseDerLax bytes != expected then
      IO.eprintln s!"FAIL parseDerLax {label}: got {parseDerLax bytes}, expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in lengthCases do
    count := count + 1
    if laxIntegerLength 8 bytes 0 != expected then
      IO.eprintln s!"FAIL laxIntegerLength {label}: got {laxIntegerLength 8 bytes 0}, expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in lowSCases do
    count := count + 1
    if checkLowS bytes != expected then
      IO.eprintln s!"FAIL checkLowS {label}: expected {expected}"
      failures := failures + 1
  for (label, sig, flags, expected) in sigCases do
    count := count + 1
    let got := resultName (checkSignatureEncoding sig flags)
    if got != expected then
      IO.eprintln s!"FAIL checkSignatureEncoding {label}: got {got}, expected {expected}"
      failures := failures + 1
  for (label, key, flags, expected, valid) in keyCases do
    count := count + 1
    let got := resultName (checkPubKeyEncoding key flags)
    if got != expected || isValidPubKey key != valid then
      IO.eprintln s!"FAIL public key {label}: got {got} and {isValidPubKey key}, expected {expected} and {valid}"
      failures := failures + 1
  IO.println s!"signature encoding hand cases: {count} cases, {failures} failures"
  return corpusFailures + failures

end KnownAnswers.SignatureEncoding

/-!
## Signature opcodes

Runs `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` through `evalScript` with a test checker.

The test checker is a lookup table, a test backend that says nothing about consensus validity.
It answers `some true` for the listed signature and key pairs and `some false` for every other pair.
It answers only for the script code that the case expects, and `none` for any other script code.
So a wrong script code gives an unsupported result, and the case fails.

Every expected result is written by hand from `EvalScript` (D3, lines 880 to 1026) and `CScript::FindAndDelete` (D24, lines 570 to 596).
The expected script codes are written out byte for byte.
The cases cover each error of the two opcodes in Core's order.
They cover 0-of-0, 1-of-1, 2-of-3 with signatures in and out of order, and early exit.
They cover the dummy with and without `NULLDUMMY`, a key count of 21 and an opcode count raised past 201 by keys.
They also cover a code separator before the opcode, a signature push inside the script code, and the order-dependent encoding check of D3 line 969.

The `transactionChecker` cases fix a transaction and use a verifier that answers only for the expected request.
The verifier ignores the digest, which `transactionChecker_verify` in `DogeLib.Script.Proofs.Signature` characterizes.
-/

namespace KnownAnswers.ScriptSignature

open DogeLib.Script
open KnownAnswers.ScriptEval (Expect hex rep)

/-- The test checker: `some true` for a listed pair, `some false` for another pair, and `none` unless the script code is `code`. -/
def tableChecker (code : List UInt8) (valid : List (List UInt8 × List UInt8)) : SignatureChecker where
  checkSig sig key c := if c == code then some (valid.contains (sig, key)) else none
  checkLockTime _ := none
  checkSequence _ := none

/-- Three test signatures and three test keys, of arbitrary bytes. With flags 0 no encoding check reads them. -/
def s1 : List UInt8 := [0xa1, 0x01]
def s2 : List UInt8 := [0xa2, 0x01]
def s3 : List UInt8 := [0xa3, 0x01]
def k1 : List UInt8 := [0xb1]
def k2 : List UInt8 := [0xb2]
def k3 : List UInt8 := [0xb3]

/-- The valid pairs of the table. -/
def table : List (List UInt8 × List UInt8) := [(s1, k1), (s2, k2), (s3, k3)]

/-- A strict-DER signature with R = 1, S = 1 and hash type `0x01`, which passes `STRICTENC`. -/
def derSig : List UInt8 := hex "300602010102010101"
/-- A compressed public key: `0x02` and 32 bytes. -/
def goodKey : List UInt8 := 0x02 :: rep 32 0x11
/-- A key that fails `STRICTENC`: `0x02` and 31 bytes. -/
def badKey : List UInt8 := 0x02 :: rep 31 0x11

/-- `OP_PUSHBYTES_n` of a short item. -/
def push (b : List UInt8) : List UInt8 := b.length.toUInt8 :: b

/-- One case: a label, flags, a checker, a script, a caller stack and the expected result. -/
structure Case where
  label : String
  flags : UInt32
  checker : SignatureChecker
  script : List UInt8
  stack : List (List UInt8)
  expected : Expect

/-- `OP_2 <k1> <k2> <k3> OP_3 OP_CHECKMULTISIG`. -/
def twoOfThree : List UInt8 := [0x52, 0x01, 0xb1, 0x01, 0xb2, 0x01, 0xb3, 0x53, 0xae]

/-- 180 or 181 counted NOPs, 20 empty keys, a key count of 20 and `OP_CHECKMULTISIG`, after a signature count of 0. -/
def twentyKeys (nops : Nat) : List UInt8 := rep nops 0x61 ++ [0x00] ++ rep 20 0x00 ++ [0x01, 0x14, 0xae]

/-- `OP_1 <badKey> <goodKey> OP_2 OP_CHECKMULTISIG`: the loop visits `goodKey` first. -/
def badKeyBelow : List UInt8 := [0x51, 0x20] ++ badKey ++ [0x21] ++ goodKey ++ [0x52, 0xae]

/-- The hand cases. -/
def cases : List Case := [
  -- OP_CHECKSIG and OP_CHECKSIGVERIFY (D3, lines 880 to 918).
  ⟨"CHECKSIG on one item", 0, tableChecker [0xac] table, [0xac], [s1], .rejected .invalidStackOperation⟩,
  ⟨"CHECKSIG valid pair", 0, tableChecker [0xac] table, [0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG invalid pair", 0, tableChecker [0xac] table, [0xac], [s1, k2], .ok [[]]⟩,
  ⟨"CHECKSIGVERIFY valid pair", 0, tableChecker [0xad] table, [0xad], [[7], s1, k1], .ok [[7]]⟩,
  ⟨"CHECKSIGVERIFY invalid pair", 0, tableChecker [0xad] table, [0xad], [s1, k2], .rejected .checkSigVerify⟩,
  ⟨"CHECKSIG empty signature reaches the checker", 0, tableChecker [0xac] table, [0xac], [[], k1], .ok [[]]⟩,
  ⟨"CHECKSIG signature encoding before key encoding", 0x02, tableChecker [0xac] table, [0xac], [s1, badKey],
    .rejected .sigDer⟩,
  ⟨"CHECKSIG key encoding", 0x02, tableChecker [0xac] [], [0xac], [derSig, badKey], .rejected .pubkeyType⟩,
  ⟨"CHECKSIG encoding passes", 0x02, tableChecker [0xac] [(derSig, goodKey)], [0xac], [derSig, goodKey], .ok [[1]]⟩,
  ⟨"CHECKSIG unavailable checker", 0, ⟨fun _ _ _ => none, fun _ => none, fun _ => none⟩, [0xac], [s1, k1],
    .unsupported (.signatureOpcode 0xac)⟩,
  ⟨"CHECKSIG script code from the start", 0, tableChecker [0x61, 0xac] table, [0x61, 0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG after a code separator", 0, tableChecker [0xac] table, [0x61, 0xab, 0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG deletes its signature push", 0, tableChecker [0x01, 0xb1, 0xac] table,
    [0x02, 0xa1, 0x01, 0x01, 0xb1, 0xac], [], .ok [[1]]⟩,
  ⟨"CHECKSIG keeps a push of other bytes", 0, tableChecker [0x02, 0xa2, 0x01, 0x75, 0xac] table,
    [0x02, 0xa2, 0x01, 0x75, 0xac], [s1, k1], .ok [[1]]⟩,
  -- OP_CHECKMULTISIG and OP_CHECKMULTISIGVERIFY (D3, lines 920 to 1026), errors in Core's order.
  ⟨"CHECKMULTISIG on an empty stack", 0, tableChecker [0xae] table, [0xae], [], .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG key count of five bytes", 0, tableChecker [] table, [0x05, 0x01, 0x00, 0x00, 0x00, 0x00, 0xae],
    [], .rejected .unknownError⟩,
  ⟨"CHECKMULTISIG key count -1", 0, tableChecker [] table, [0x4f, 0xae], [], .rejected .pubkeyCount⟩,
  ⟨"CHECKMULTISIG key count 21", 0, tableChecker [] table, [0x01, 0x15, 0xae], [], .rejected .pubkeyCount⟩,
  ⟨"CHECKMULTISIG 201 counted opcodes with 20 keys", 0, tableChecker [] table, twentyKeys 180, [[]], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 202 counted opcodes with 20 keys", 0, tableChecker [] table, twentyKeys 181, [[]],
    .rejected .opCount⟩,
  ⟨"CHECKMULTISIG key count before keys", 0, tableChecker [] table, [0x52, 0xae], [], .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG missing signature count", 0, tableChecker [] table, [0x01, 0xb1, 0x51, 0xae], [],
    .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG signature count of five bytes", 0, tableChecker [] table,
    [0x05, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0xb1, 0x51, 0xae], [], .rejected .unknownError⟩,
  ⟨"CHECKMULTISIG signature count above key count", 0, tableChecker [] table, [0x52, 0x01, 0xb1, 0x51, 0xae], [],
    .rejected .sigCount⟩,
  ⟨"CHECKMULTISIG signature count -1", 0, tableChecker [] table, [0x4f, 0x01, 0xb1, 0x51, 0xae], [],
    .rejected .sigCount⟩,
  ⟨"CHECKMULTISIG missing signature", 0, tableChecker [] table, [0x51, 0x01, 0xb1, 0x51, 0xae], [[]],
    .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG missing dummy", 0, tableChecker [] table, [0x51, 0x01, 0xb1, 0x51, 0xae], [s1],
    .rejected .invalidStackOperation⟩,
  -- Matching.
  ⟨"CHECKMULTISIG 0-of-0", 0, tableChecker [] table, [0x00, 0x00, 0xae], [[]], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 0-of-0 keeps the item below the dummy", 0, tableChecker [] table, [0x00, 0x00, 0xae], [[9], []],
    .ok [[9], [1]]⟩,
  ⟨"CHECKMULTISIG 1-of-1", 0, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table, [0x51, 0x01, 0xb1, 0x51, 0xae],
    [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 1-of-1 wrong key", 0, tableChecker [0x51, 0x01, 0xb2, 0x51, 0xae] table,
    [0x51, 0x01, 0xb2, 0x51, 0xae], [[], s1], .ok [[]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 in order", 0, tableChecker twoOfThree table, twoOfThree, [[], s1, s2], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 skipping a key", 0, tableChecker twoOfThree table, twoOfThree, [[], s1, s3], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 out of order", 0, tableChecker twoOfThree table, twoOfThree, [[], s2, s1], .ok [[]]⟩,
  ⟨"CHECKMULTISIGVERIFY 2-of-3 in order", 0, tableChecker (twoOfThree.dropLast ++ [0xaf]) table,
    twoOfThree.dropLast ++ [0xaf], [[], s2, s3], .ok []⟩,
  ⟨"CHECKMULTISIGVERIFY 2-of-3 out of order", 0, tableChecker (twoOfThree.dropLast ++ [0xaf]) table,
    twoOfThree.dropLast ++ [0xaf], [[], s3, s2], .rejected .checkMultisigVerify⟩,
  -- Early exit (D3, lines 987 to 991): after s1 fails against k3 and k2, two signatures remain for one key.
  -- The pair (s1, k1) would be unavailable, so a visit would give an unsupported result.
  ⟨"CHECKMULTISIG early exit", 0,
    ⟨fun sig key code =>
      if code != twoOfThree then none
      else if sig == s1 && key == k1 then none
      else some (table.contains (sig, key)), fun _ => none, fun _ => none⟩,
    twoOfThree, [[], s2, s1], .ok [[]]⟩,
  -- The order-dependent encoding check (D3, line 969), with STRICTENC.
  ⟨"CHECKMULTISIG never visits a bad key below a match", 0x02, tableChecker badKeyBelow [(derSig, goodKey)],
    badKeyBelow, [[], derSig], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG visits a bad key first", 0x02, tableChecker [] [(derSig, goodKey)],
    [0x51, 0x21] ++ goodKey ++ [0x20] ++ badKey ++ [0x52, 0xae], [[], derSig], .rejected .pubkeyType⟩,
  -- The dummy (D3, lines 1004 to 1014).
  ⟨"CHECKMULTISIG nonempty dummy without NULLDUMMY", 0, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[0x01], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG nonempty dummy with NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[0x01], s1], .rejected .sigNullDummy⟩,
  ⟨"CHECKMULTISIG empty dummy with NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG failure with nonempty dummy and NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb2, 0x51, 0xae] table,
    [0x51, 0x01, 0xb2, 0x51, 0xae], [[0x01], s1], .rejected .sigNullDummy⟩,
  -- Script code.
  ⟨"CHECKMULTISIG after a code separator", 0, tableChecker [0xae] table, [0x51, 0x01, 0xb1, 0x51, 0xab, 0xae],
    [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG deletes its signature push", 0, tableChecker [0x00, 0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x00, 0x02, 0xa1, 0x01, 0x51, 0x01, 0xb1, 0x51, 0xae], [], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG deletes every signature push before the loop", 0, tableChecker (rep 1 0x00 ++ twoOfThree) table,
    [0x00, 0x02, 0xa1, 0x01, 0x02, 0xa2, 0x01] ++ twoOfThree, [], .ok [[1]]⟩,
  -- Skipped branches: no checker call and no key count.
  ⟨"signature opcodes in a skipped branch", 0, ⟨fun _ _ _ => none, fun _ => none, fun _ => none⟩, [0x00, 0x63, 0xac, 0xad, 0xae, 0xaf, 0x68],
    [], .ok []⟩,
  ⟨"CHECKMULTISIG in a skipped branch counts once", 0, tableChecker [] table,
    [0x00, 0x63, 0x01, 0x14, 0xae, 0x68] ++ rep 198 0x61, [], .ok []⟩
]

/-- A transaction with one input and one output, from the context of record 9 of `script_tests.json`. -/
def spendTx? : Option DogeLib.Transaction.Transaction :=
  match DogeLib.Transaction.Transaction.decodeBaseComplete
      (hex "0100000001dc3e1270bc983b5fc117d86201475c85dbac7647c663e275f730cc87200f7a920000000000ffffffff0100000000000000000000000000") with
  | .ok tx => some tx
  | .error _ => none

/-- A verifier that answers `some true` only for the signature `sig` without its hash type and the key `key`, and `none` for every other request. -/
def strictVerifier (sig key : List UInt8) : SignatureVerifier :=
  fun s k _ => if s == sig && k == key then some true else none

/-- The `transactionChecker` cases: label, signature, key and expected answer. -/
def checkerCases : List (String × List UInt8 × List UInt8 × Option Bool) := [
  ("invalid key, verifier not called", derSig, [0x05], some false),
  ("empty key, verifier not called", derSig, [], some false),
  ("empty signature, verifier not called", [], goodKey, some false),
  ("hash type removed", derSig, goodKey, some true),
  ("hybrid key of 65 bytes reaches the verifier", derSig, 0x06 :: rep 64 0x11, none)
]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript (some c.checker) c.flags c.script c.stack
    unless c.expected.matches got do
      IO.eprintln s!"FAIL signature opcode {c.label}: got {repr got}"
      failures := failures + 1
  let stripped := derSig.dropLast
  let some spendTx := spendTx? | throw (IO.userError "the transaction of record 9 does not decode")
  for (label, sig, key, expected) in checkerCases do
    let got := (transactionChecker spendTx 0 (strictVerifier stripped goodKey)).checkSig sig key [0xac]
    unless got == expected do
      IO.eprintln s!"FAIL transactionChecker {label}: got {repr got}"
      failures := failures + 1
  let base := baseChecker.checkSig derSig goodKey [0xac]
  unless base == some false do
    IO.eprintln s!"FAIL baseChecker: got {repr base}"
    failures := failures + 1
  IO.println s!"signature opcodes: {cases.length} hand cases, {checkerCases.length + 1} checker cases, {failures} failures"
  return failures

end KnownAnswers.ScriptSignature

/-!
## `VerifyScript` and the lock-time opcodes

Hand cases for stage 4, each at a boundary that Core's source states:
`OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` (D3, lines 350 to 427), `CheckLockTime` and `CheckSequence` (D3, lines 1274 to 1353), `VerifyScript` (D3, lines 1409 to 1526) and `IsPushOnly` (D48, lines 239 to 259).
Each expected result is read from those lines, not computed by DogeLib.
The P2SH cases build the template from the HASH160 digest of the redeem script, and `lake test` checks HASH160 against its own vectors.
-/

namespace KnownAnswers.ScriptVerify

open DogeLib.Script
open KnownAnswers.ScriptEval (Expect hex rep)

/-- A transaction with one input of sequence `sequence`, no outputs, version bits `version` and lock time `lockTime`. -/
def mkTx (version lockTime sequence : UInt32) : DogeLib.Transaction.Transaction :=
  { version
    inputs := ⟨[{ prevout := DogeLib.Transaction.OutPoint.null, scriptSig := ⟨⟨[], by decide⟩⟩, sequence }], by simp⟩
    outputs := ⟨[], by decide⟩
    lockTime }

/-- `transactionChecker` for input 0 of `mkTx`, with a verifier that is always unavailable. -/
def txChecker (version lockTime sequence : UInt32) : SignatureChecker :=
  transactionChecker (mkTx version lockTime sequence) 0 fun _ _ _ => none

/-- A push of the bytes `b`, for at most 75 bytes. -/
def push (b : List UInt8) : List UInt8 := b.length.toUInt8 :: b

def cltv : UInt32 := ScriptFlags.checkLockTimeVerify
def csv : UInt32 := ScriptFlags.checkSequenceVerify

/-- One hand case of an evaluation: a label, flags, a checker, a script and the expected result on the empty stack. -/
structure Case where
  label : String
  flags : UInt32
  checker : Option SignatureChecker
  script : List UInt8
  expected : Expect

/-- 499,999,999, 500,000,000 and 500,000,001 as script numbers. -/
def n499999999 : List UInt8 := [0xff, 0x64, 0xcd, 0x1d]
def n500000000 : List UInt8 := [0x00, 0x65, 0xcd, 0x1d]
def n500000001 : List UInt8 := [0x01, 0x65, 0xcd, 0x1d]

/-- The lock-time cases. Each operand stays on the stack, because neither opcode pops. -/
def cases : List Case := [
  -- CHECKLOCKTIMEVERIFY: the threshold (D24 line 35, D3 lines 1283 to 1287).
  ⟨"CLTV 499,999,999 against 500,000,000", cltv, txChecker 1 500000000 0, push n499999999 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 500,000,000 against 500,000,000", cltv, txChecker 1 500000000 0, push n500000000 ++ [0xb1],
    .ok [n500000000]⟩,
  ⟨"CLTV 499,999,999 against 499,999,999", cltv, txChecker 1 499999999 0, push n499999999 ++ [0xb1],
    .ok [n499999999]⟩,
  ⟨"CLTV 500,000,001 against 500,000,000", cltv, txChecker 1 500000000 0, push n500000001 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 500,000,000 against 499,999,999", cltv, txChecker 1 499999999 0, push n500000000 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  -- The comparison (D3 lines 1291 and 1292).
  ⟨"CLTV 6 against 5", cltv, txChecker 1 5 0, [0x56, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 0 against 0", cltv, txChecker 1 0 0, [0x00, 0xb1], .ok [[]]⟩,
  -- The final sequence (D4 line 76, D3 lines 1304 and 1305).
  ⟨"CLTV with sequence 0xffffffff", cltv, txChecker 1 0 0xffffffff, [0x00, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV with sequence 0xfffffffe", cltv, txChecker 1 0 0xfffffffe, [0x00, 0xb1], .ok [[]]⟩,
  -- The five-byte operand (D3 line 377).
  ⟨"CLTV five-byte 0xffffffff against 0xffffffff", cltv, txChecker 1 0xffffffff 0,
    push [0xff, 0xff, 0xff, 0xff, 0x00] ++ [0xb1], .ok [[0xff, 0xff, 0xff, 0xff, 0x00]]⟩,
  ⟨"CLTV five-byte 2^32 against 0xffffffff", cltv, txChecker 1 0xffffffff 0,
    push [0x00, 0x00, 0x00, 0x00, 0x01] ++ [0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV six-byte operand", cltv, txChecker 1 0xffffffff 0, push [0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ [0xb1],
    .rejected .unknownError⟩,
  -- The negative operand and the empty stack (D3 lines 360, 361, 382 and 383).
  ⟨"CLTV -1", cltv, txChecker 1 0 0, [0x4f, 0xb1], .rejected .negativeLocktime⟩,
  ⟨"CLTV negative zero is not negative", cltv, txChecker 1 0 0, push [0x80] ++ [0xb1], .ok [[0x80]]⟩,
  ⟨"CLTV on an empty stack", cltv, txChecker 1 0 0, [0xb1], .rejected .invalidStackOperation⟩,
  ⟨"CLTV with BaseSignatureChecker", cltv, some baseChecker, [0x00, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV without a checker", cltv, none, [0x00, 0xb1], .unsupported .checkLockTimeVerify⟩,
  -- Flag off: NOP2 and NOP3 (D3 lines 352 to 358 and 394 to 400).
  ⟨"NOP2 on an empty stack", 0, txChecker 1 0 0xffffffff, [0xb1], .ok []⟩,
  ⟨"NOP3 on an empty stack", 0, txChecker 1 0 0xffffffff, [0xb2], .ok []⟩,
  ⟨"NOP2 without a checker", csv, none, [0xb1], .ok []⟩,
  -- CHECKSEQUENCEVERIFY: the version as uint32_t (D3 lines 1318 and 1319).
  ⟨"CSV with version 1", csv, txChecker 1 0 10, [0x55, 0xb2], .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV with version 2", csv, txChecker 2 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  ⟨"CSV with version 0xffffffff", csv, txChecker 0xffffffff 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  ⟨"CSV with version 0x80000000", csv, txChecker 0x80000000 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  -- The disable bit in the operand (D4 line 81, D3 lines 418 and 419).
  ⟨"CSV operand with bit 31, version 1", csv, txChecker 1 0 10,
    push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"CSV operand with bit 31, BaseSignatureChecker", csv, some baseChecker,
    push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"CSV operand with bit 31, no checker", csv, none, push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2],
    .unsupported .checkSequenceVerify⟩,
  -- The disable bit in the sequence (D3 lines 1325 and 1326).
  ⟨"CSV with sequence bit 31", csv, txChecker 2 0 0x8000000a, [0x55, 0xb2], .rejected .unsatisfiedLocktime⟩,
  -- The type bit (D4 line 86, D3 lines 1341 to 1346).
  ⟨"CSV time operand against height sequence", csv, txChecker 2 0 10, push [0x00, 0x00, 0x40] ++ [0xb2],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV height operand against time sequence", csv, txChecker 2 0 0x40000a, [0x55, 0xb2],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV time operand against time sequence", csv, txChecker 2 0 0x40000a, push [0x05, 0x00, 0x40] ++ [0xb2],
    .ok [[0x05, 0x00, 0x40]]⟩,
  -- The masked comparison (D4 line 90, D3 lines 1330 to 1332 and 1350 and 1351).
  ⟨"CSV 11 against 10", csv, txChecker 2 0 10, [0x5b, 0xb2], .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV 10 against 10", csv, txChecker 2 0 10, [0x5a, 0xb2], .ok [[10]]⟩,
  ⟨"CSV operand bits outside the mask", csv, txChecker 2 0 10, push [0x05, 0x00, 0x01] ++ [0xb2],
    .ok [[0x05, 0x00, 0x01]]⟩,
  ⟨"CSV sequence bits outside the mask", csv, txChecker 2 0 0x0001000a, [0x5a, 0xb2], .ok [[10]]⟩,
  ⟨"CSV six-byte operand", csv, txChecker 2 0 10, push [0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ [0xb2],
    .rejected .unknownError⟩,
  ⟨"CSV -1", csv, txChecker 2 0 10, [0x4f, 0xb2], .rejected .negativeLocktime⟩,
  ⟨"CSV on an empty stack", csv, txChecker 2 0 10, [0xb2], .rejected .invalidStackOperation⟩
]

/-- The P2SH template for the redeem script `redeem`: `OP_HASH160`, its HASH160 digest, `OP_EQUAL`. -/
def p2shOf (redeem : List UInt8) : List UInt8 :=
  [0xa9, 0x14] ++ (DogeLib.Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList ++ [0x87]

/-- The expected result of a `VerifyScript` case. -/
inductive VExpect where
  | accepted
  | rejected (e : ScriptError)
  | unsupported (u : Unsupported)
  deriving BEq, Repr

def VExpect.matches : VExpect → VerifyResult → Bool
  | .accepted, .accepted => true
  | .rejected e, .rejected e' => e == e'
  | .unsupported u, .unsupported u' => u == u'
  | _, _ => false

def p2sh : UInt32 := ScriptFlags.p2sh

/-- `VerifyScript` cases: label, flags, scriptSig, scriptPubKey and the expected result. -/
def verifyCases : List (String × UInt32 × List UInt8 × List UInt8 × VExpect) := [
  ("P2SH, redeem script OP_1", p2sh, push [0x51], p2shOf [0x51], .accepted),
  ("P2SH, redeem script leaves false", p2sh, push [0x00], p2shOf [0x00], .rejected .evalFalse),
  ("P2SH, redeem script OP_RETURN", p2sh, push [0x6a], p2shOf [0x6a], .rejected .opReturn),
  ("P2SH, redeem script reads the item below", p2sh, [0x51] ++ push [0x75, 0x51], p2shOf [0x75, 0x51], .accepted),
  ("P2SH, empty redeem script leaves nothing", p2sh, [0x00], p2shOf [], .rejected .evalFalse),
  ("P2SH, scriptSig not push-only", p2sh, [0x61] ++ push [0x51], p2shOf [0x51], .rejected .sigPushOnly),
  ("P2SH flag off, scriptSig not push-only", 0, [0x61] ++ push [0x51], p2shOf [0x51], .accepted),
  ("P2SH flag off, redeem script leaves false", 0, push [0x00], p2shOf [0x00], .accepted),
  ("P2SH, wrong redeem script", p2sh, push [0x52], p2shOf [0x51], .rejected .evalFalse),
  ("P2SH, empty scriptSig", p2sh, [], p2shOf [0x51], .rejected .invalidStackOperation),
  ("P2SH, OP_RESERVED in scriptSig", p2sh, [0x50] ++ push [0x51], p2shOf [0x51], .rejected .badOpcode),
  ("P2SH, OP_RESERVED in a skipped branch is not push-only", p2sh, [0x00, 0x63, 0x50, 0x68] ++ push [0x51],
    p2shOf [0x51], .rejected .sigPushOnly),
  ("P2SH, extra items are not checked", p2sh, [0x51, 0x52] ++ push [0x51], p2shOf [0x51], .accepted),
  ("not P2SH: the template and OP_NOP", p2sh, [0x61] ++ push [0x51], p2shOf [0x51] ++ [0x61], .accepted),
  ("bare scripts, true top", p2sh, [0x51], [], .accepted),
  ("bare scripts, false top", p2sh, [0x51], [0x00], .rejected .evalFalse),
  ("bare scripts, empty stack", 0, [], [], .rejected .evalFalse),
  ("scriptSig fails first", p2sh, [0x6a], p2shOf [0x51], .rejected .opReturn),
  ("SIGPUSHONLY is unsupported", ScriptFlags.sigPushOnly, [0x61], [0x51], .unsupported (.flags 0x20)),
  ("CLEANSTACK is unsupported", p2sh ||| ScriptFlags.cleanStack, push [0x51], p2shOf [0x51],
    .unsupported (.flags 0x100))
]

/-- `isPushOnly` cases (D48, lines 239 to 259). -/
def pushOnlyCases : List (List UInt8 × Bool) := [
  ([], true), ([0x00], true), ([0x50], true), ([0x60], true), ([0x4f], true), ([0x4c, 0x01, 0x07], true),
  ([0x61], false), ([0x51, 0x61], false), ([0x02, 0x01], false), ([0x4c], false), ([0xb1], false)
]

/-- The bytes as a transaction script. Every script here is far below 2^64 bytes. -/
def toScript (b : List UInt8) : DogeLib.Transaction.Script :=
  if h : b.length < 2 ^ 64 then ⟨⟨b, h⟩⟩ else ⟨⟨[], by decide⟩⟩

/-- An input context over input 0 of `mkTx`. -/
def ctx (version lockTime sequence : UInt32) : InputContext :=
  ⟨mkTx version lockTime sequence, 0, by simp [mkTx], by simp [mkTx], by simp [mkTx]⟩

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript c.checker c.flags c.script []
    unless c.expected.matches got do
      IO.eprintln s!"FAIL lock time {c.label}: got {repr got}"
      failures := failures + 1
  for (label, flags, ss, spk, expected) in verifyCases do
    let got := verifyScript (txChecker 2 0 0) flags ss spk
    unless expected.matches got do
      IO.eprintln s!"FAIL verifyScript {label}: got {repr got}"
      failures := failures + 1
  for (script, expected) in pushOnlyCases do
    unless isPushOnly script == expected do
      IO.eprintln s!"FAIL isPushOnly {script}: expected {expected}"
      failures := failures + 1
  -- A spend whose P2SH redeem script checks the lock time of the input.
  let redeem : List UInt8 := [0x55, 0xb1]
  let prev := toScript (p2shOf redeem)
  let mkSpend (lockTime sequence : UInt32) : InputContext :=
    let base := ctx 1 lockTime sequence
    let input := { base.input with scriptSig := toScript (push redeem) }
    ⟨{ base.tx with inputs := ⟨[input], by simp⟩ }, 0, by simp, by simp, by simp [base, ctx, mkTx]⟩
  let flags := p2sh ||| cltv
  let spends : List (String × InputContext × VExpect) := [
    ("spend, lock time 5", mkSpend 5 0, .accepted),
    ("spend, lock time 4", mkSpend 4 0, .rejected .unsatisfiedLocktime),
    ("spend, final sequence", mkSpend 5 0xffffffff, .rejected .unsatisfiedLocktime)
  ]
  for (label, c, expected) in spends do
    let got := verifyLegacySpend c prev flags fun _ _ _ => none
    unless expected.matches got do
      IO.eprintln s!"FAIL verifyLegacySpend {label}: got {repr got}"
      failures := failures + 1
  let total := cases.length + verifyCases.length + pushOnlyCases.length + spends.length
  IO.println s!"verify and lock time: {total} hand cases, {failures} failures"
  return failures

end KnownAnswers.ScriptVerify

/-!
## The worked property: multisig with recovery

Spends of the 2-of-3 template of design record 0003, section 7, through `verifyLegacySpend` and so through `verifyScript`.
The redeem script is written byte for byte from section 7, and one case checks that `multisigRecoveryScript` builds the same bytes.
Each expected result is read from section 7 and from `EvalScript` (D3, lines 437 to 476, 880 to 1026 and 1274 to 1308), not computed by DogeLib.

The verifier is a lookup table, a test backend that says nothing about consensus validity.
It answers `some true` for the listed pairs of stripped signature and key, and `some false` for every other request.
It ignores the digest, which `transactionChecker_verify` in `DogeLib.Script.Proofs.Signature` characterizes.
The keys are 33 bytes with the prefix `02`, which every encoding flag accepts.

`checkSighash` compares, for three script codes of the template and six hash types, the production digest with the digest of the transformation reference.
Both sides are DogeLib definitions, so that check is a consistency check, not independent evidence.
-/

namespace KnownAnswers.MultisigRecovery

open DogeLib.Script
open KnownAnswers.ScriptEval (hex rep)
open KnownAnswers.ScriptVerify (VExpect mkTx toScript p2shOf)

def P1 : List UInt8 := 0x02 :: rep 32 0x11
def P2 : List UInt8 := 0x02 :: rep 32 0x22
def P3 : List UInt8 := 0x02 :: rep 32 0x33
def R : List UInt8 := 0x02 :: rep 32 0x44

/-- The 2-of-3 redeem script of section 7, written out: 149 bytes. -/
def redeem : List UInt8 :=
  [0x63, 0x52, 0x21] ++ P1 ++ [0x21] ++ P2 ++ [0x21] ++ P3 ++
    [0x53, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75, 0x21] ++ R ++ [0xac, 0x68]

/-- A push of `b` as `CScript() << b` writes it, for at most 255 bytes. -/
def push (b : List UInt8) : List UInt8 :=
  if b.length < 76 then b.length.toUInt8 :: b else 0x4c :: b.length.toUInt8 :: b

/-- Test signatures of arbitrary bytes, each with the hash type `01`. With no encoding flag no check reads them. -/
def sig1 : List UInt8 := [0xa1, 0x01]
def sig2 : List UInt8 := [0xa2, 0x01]
def sigR : List UInt8 := [0xa4, 0x01]
/-- A strict DER signature: R = 1, S = 1, hash type `01`. -/
def derSigR : List UInt8 := hex "300602010102010101"
/-- The same signature with the undefined hash type `00`. -/
def derSigR0 : List UInt8 := hex "300602010102010100"
/-- A strict DER signature with R = 1 and S = ⌊n/2⌋ + 1, one above the LOW_S bound, and the hash type `01`. -/
def highSigR : List UInt8 := hex "30250201010220" ++ KnownAnswers.SignatureEncoding.halfPlusOneBytes ++ [0x01]
/-- The LOW_S overflow case: R = 2^256 − 1 and S = 2^255 − 1, which `CheckLowS` accepts after lax parsing sets both to zero. -/
def overflowSigR : List UInt8 := hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff ++ [0x01]

/-- The table verifier, a test backend: `some true` for a listed pair of stripped signature and key. -/
def tableVerifier : SignatureVerifier := fun s k _ =>
  some ([([0xa1], P1), ([0xa2], P2), ([0xa4], R), (derSigR.dropLast, R), (overflowSigR.dropLast, R),
    ([0xa1], [0x06] ++ rep 32 0x44)].contains (s, k))

/-- An input context for input 0 of `mkTx 1 lockTime sequence`, with the `scriptSig` bytes `ss`. -/
def spendCtx (ss : List UInt8) (lockTime sequence : UInt32) : InputContext :=
  let base := KnownAnswers.ScriptVerify.ctx 1 lockTime sequence
  let input := { base.input with scriptSig := toScript ss }
  ⟨{ base.tx with inputs := ⟨[input], by simp⟩ }, 0, by simp, by simp, by simp [base, KnownAnswers.ScriptVerify.ctx, mkTx]⟩

def p2sh : UInt32 := ScriptFlags.p2sh
def cltv : UInt32 := ScriptFlags.checkLockTimeVerify
def base : UInt32 := p2sh ||| cltv

/-- The ordinary unlocking script: a dummy, two signatures in push order and a selector, then the redeem script. -/
def ordinary (dummy a b sel : List UInt8) (red : List UInt8 := redeem) : List UInt8 :=
  push dummy ++ push a ++ push b ++ push sel ++ push red

/-- The recovery unlocking script: a signature and a selector, then the redeem script. -/
def recovery (s sel : List UInt8) (red : List UInt8 := redeem) : List UInt8 := push s ++ push sel ++ push red

/-- A redeem script with the recovery key `r`, for the key-encoding case. -/
def redeemWith (r : List UInt8) : List UInt8 :=
  [0x63, 0x52, 0x21] ++ P1 ++ [0x21] ++ P2 ++ [0x21] ++ P3 ++
    [0x53, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75, 0x21] ++ r ++ [0xac, 0x68]

/-- Cases: label, flags, scriptSig, redeem script, lock time, sequence and expected result. -/
def cases : List (String × UInt32 × List UInt8 × List UInt8 × UInt32 × UInt32 × VExpect) := [
  ("ordinary branch, signatures in key order", base, ordinary [] sig1 sig2 [1], redeem, 0, 0xffffffff, .accepted),
  ("ordinary branch, signatures in the wrong order", base, ordinary [] sig2 sig1 [1], redeem, 0, 0xffffffff,
    .rejected .evalFalse),
  ("ordinary branch, one signature missing", base, push [] ++ push sig1 ++ push [1] ++ push redeem, redeem, 0, 0,
    .rejected .invalidStackOperation),
  ("recovery, lock time 1,000,000", base, recovery sigR [], redeem, 1000000, 0, .accepted),
  ("recovery, lock time 999,999", base, recovery sigR [], redeem, 999999, 0, .rejected .unsatisfiedLocktime),
  ("recovery, lock time 500,000,000 is a time", base, recovery sigR [], redeem, 500000000, 0,
    .rejected .unsatisfiedLocktime),
  ("recovery, final sequence", base, recovery sigR [], redeem, 1000000, 0xffffffff, .rejected .unsatisfiedLocktime),
  ("recovery, wrong signature", base, recovery sig1 [], redeem, 1000000, 0, .rejected .evalFalse),
  ("recovery, empty signature", base, recovery [] [], redeem, 1000000, 0, .rejected .evalFalse),
  ("selector negative zero takes the recovery branch", base, recovery sigR [0x80], redeem, 1000000, 0, .accepted),
  ("selector negative zero, ordinary signatures", base, ordinary [] sig1 sig2 [0x80], redeem, 1000000, 0,
    .rejected .evalFalse),
  ("nonminimal selector 01 00 takes the ordinary branch", base, ordinary [] sig1 sig2 [0x01, 0x00], redeem, 0, 0,
    .accepted),
  ("nonempty dummy without NULLDUMMY", base, ordinary [0x07] sig1 sig2 [1], redeem, 0, 0, .accepted),
  ("nonempty dummy with NULLDUMMY", base ||| ScriptFlags.nullDummy, ordinary [0x07] sig1 sig2 [1], redeem, 0, 0,
    .rejected .sigNullDummy),
  ("empty dummy with NULLDUMMY", base ||| ScriptFlags.nullDummy, ordinary [] sig1 sig2 [1], redeem, 0, 0, .accepted),
  ("CLTV clear, lock time 0", p2sh, recovery sigR [], redeem, 0, 0xffffffff, .accepted),
  ("empty stack below the redeem script", base, push redeem, redeem, 0, 0, .rejected .unbalancedConditional),
  ("DER signature, all encoding flags", base ||| ScriptFlags.derSig ||| ScriptFlags.lowS ||| ScriptFlags.strictEnc,
    recovery derSigR [], redeem, 1000000, 0, .accepted),
  ("undefined hash type 00 under STRICTENC", base ||| ScriptFlags.strictEnc, recovery derSigR0 [], redeem, 1000000, 0,
    .rejected .sigHashtype),
  ("LOW_S overflow case passes the encoding check", base ||| ScriptFlags.lowS, recovery overflowSigR [], redeem,
    1000000, 0, .accepted),
  ("S one above the half order under LOW_S", base ||| ScriptFlags.lowS, recovery highSigR [], redeem, 1000000, 0,
    .rejected .sigHighS),
  ("arbitrary signature bytes under DERSIG", base ||| ScriptFlags.derSig, recovery sigR [], redeem, 1000000, 0,
    .rejected .sigDer),
  ("33-byte key with prefix 06 under STRICTENC", base ||| ScriptFlags.strictEnc,
    recovery [] [] (redeemWith ([0x06] ++ rep 32 0x44)), redeemWith ([0x06] ++ rep 32 0x44), 1000000, 0,
    .rejected .pubkeyType),
  ("33-byte key with prefix 06 without STRICTENC", base,
    recovery sig1 [] (redeemWith ([0x06] ++ rep 32 0x44)), redeemWith ([0x06] ++ rep 32 0x44), 1000000, 0,
    .rejected .evalFalse)
]

/-- A transaction with two inputs and two outputs, so that every hash type below hashes a preimage for input 0. -/
def sighashTx : DogeLib.Transaction.Transaction :=
  { version := 1
    inputs := ⟨[{ prevout := DogeLib.Transaction.OutPoint.null, scriptSig := toScript (recovery sigR []), sequence := 0 },
      { prevout := DogeLib.Transaction.OutPoint.null, scriptSig := toScript [], sequence := 0xfffffffe }], by simp⟩
    outputs := ⟨[⟨100000, toScript (p2shOf redeem)⟩, ⟨5000, toScript [0x51]⟩], by simp⟩
    lockTime := 1000000 }

/--
Three script codes of the template, with their expected lengths:

- the ordinary code, with `sig2` and then `sig1` removed, nearest the stack top first
- the recovery code, with `sigR` removed
- a code with the push of `P1` removed, so that FindAndDelete deletes 34 bytes
-/
def sighashCodes : List (String × List UInt8 × Nat) := [
  ("ordinary", effectiveScriptCode redeem 0 [sig2, sig1], 149),
  ("recovery", effectiveScriptCode redeem 0 [sigR], 149),
  ("P1 removed", effectiveScriptCode redeem 0 [P1], 115)
]

/-- SIGHASH_ALL, NONE and SINGLE, each with and without ANYONECANPAY. -/
def sighashTypes : List UInt32 := [1, 2, 3, 0x81, 0x82, 0x83]

/--
For each template code and hash type, the production digest `legacySignatureHash` equals the digest of `legacyReferencePlan`, and the code parses completely.
This compares two DogeLib definitions with each other: a consistency check of the template corollaries, not an expected value from an independent source.
The independent evidence for `legacySignatureHash` is Core's `sighash.json`.
-/
def checkSighash : IO Nat := do
  let mut failures := 0
  for (label, code, len) in sighashCodes do
    unless code.length == len && (DogeLib.Transaction.scanOps code).2 == [] do
      IO.eprintln s!"FAIL multisig recovery digest {label}: length {code.length} or the parse differs"
      failures := failures + 1
    for h in sighashTypes do
      let prod := DogeLib.Transaction.legacySignatureHash (toScript code) sighashTx 0 h
      let ref := (DogeLib.Transaction.legacyReferencePlan (toScript code) sighashTx 0 h).digest
      unless prod.val == ref.val do
        IO.eprintln s!"FAIL multisig recovery digest {label}, hash type {h}: production and reference differ"
        failures := failures + 1
  return failures

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  failures := failures + (← checkSighash)
  unless redeem.length == 149 && multisigRecoveryScript 2 [P1, P2, P3] R == redeem do
    IO.eprintln "FAIL multisig recovery: the template bytes differ from section 7"
    failures := failures + 1
  for (label, flags, ss, red, lockTime, sequence, expected) in cases do
    let got := verifyLegacySpend (spendCtx ss lockTime sequence) (toScript (p2shOf red)) flags tableVerifier
    unless expected.matches got do
      IO.eprintln s!"FAIL multisig recovery {label}: got {repr got}"
      failures := failures + 1
  IO.println s!"multisig recovery: {cases.length + 1} hand cases, {sighashCodes.length * sighashTypes.length} digest comparisons, {failures} failures"
  return failures

end KnownAnswers.MultisigRecovery

/-!
## Transaction spend corpus

Run the inside-milestone inputs of `tx_spends.jsonl` through `verifyLegacySpend` with `coreVerifier`.
Every eligible input must give a verdict: an unsupported result fails the test.
D28 and D29 supply the transactions, and D30 supplies the per-input acceptance requirement for `tx_valid`.
An invalid transaction supplies no individual Script expectation.
The witness-allowed prefix reader follows D30, while a separate complete base decode checks the oracle input domain.
-/

namespace KnownAnswers.TxSpends

open DogeLib.Script DogeLib.Transaction

/-- The fields needed to check one transaction input against the corpus requirement. -/
structure Record where
  source : String
  line : Nat
  inputIndex : UInt32
  bytes : List UInt8
  prevScript : DogeLib.Transaction.Script
  flags : UInt32
  accept : Bool
  inside : Bool

/-- Read a spend record without deriving an expectation from transaction rejection. -/
def parseRecord (text : String) : Except String Record := do
  let j ← Lean.Json.parse text
  let bytes ← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? "tx_hex").getStr?)
  let prev ← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? "prevout_scriptPubKey_hex").getStr?)
  let some prevScript := DogeLib.Serialization.CountedList.ofList? prev.toList
    | throw "previous-output script exceeds the counted-list bound"
  let index ← (← j.getObjVal? "input_index").getNat?
  if index ≥ 2 ^ 32 then throw "input index exceeds uint32"
  let expectation ← j.getObjVal? "per_input_expectation"
  let accept ← match expectation with
    | .null => pure false
    | .str "accept" => pure true
    | _ => throw "unknown per-input expectation"
  return {
    source := ← (← j.getObjVal? "source_file").getStr?
    line := ← (← j.getObjVal? "source_line").getNat?
    inputIndex := index.toUInt32
    bytes := bytes.toList
    prevScript := ⟨prevScript⟩
    flags := (← (← j.getObjVal? "flags_mask").getNat?).toUInt32
    accept
    inside := (← (← (← j.getObjVal? "classification").getObjVal? "milestone").getStr?) == "inside" }

/-- Check every eligible input. Unknown expectations contribute outcome counts only. -/
def check : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/tx_spends.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut excluded := 0
  let mut baseDecoded := 0
  let mut accepted := 0
  let mut verifier := 0
  let mut required := 0
  let mut unknownAccepted := 0
  let mut unknownRejected := 0
  let mut unknownVerifier := 0
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if !r.inside then
      excluded := excluded + 1
      continue
    if r.accept then required := required + 1
    match Transaction.decodeBaseComplete r.bytes with
    | .ok _ => baseDecoded := baseDecoded + 1
    | .error _ =>
      IO.eprintln s!"FAIL {r.source}:{r.line}: eligible input does not decode as complete base bytes"
      failures := failures + 1
    let w ← match Transaction.readAllowWitness r.bytes with
      | .ok (w, _) => pure w
      | .error _ => throw (IO.userError s!"{r.source}:{r.line}: transaction prefix does not decode")
    if w.hasWitness then throw (IO.userError "eligible spend has a witness")
    let tx := w.tx
    if hi : r.inputIndex.toNat < tx.inputs.val.length then
      if hn : tx.inputs.val.length < 2 ^ 32 then
        if ho : tx.outputs.val.length < 2 ^ 32 then
          let ctx : InputContext := ⟨tx, r.inputIndex, hi, hn, ho⟩
          let got := verifyLegacySpend ctx r.prevScript r.flags coreVerifier
          match got with
          | .accepted =>
            if r.accept then accepted := accepted + 1 else unknownAccepted := unknownAccepted + 1
          | .unsupported (.signatureOpcode _) =>
            if r.accept then verifier := verifier + 1 else unknownVerifier := unknownVerifier + 1
          | .rejected _ =>
            if r.accept then
              IO.eprintln s!"FAIL {r.source}:{r.line} input {r.inputIndex}: required accept, got {repr got}"
              failures := failures + 1
            else unknownRejected := unknownRejected + 1
          | .unsupported _ =>
            IO.eprintln s!"FAIL {r.source}:{r.line}: unexpected unsupported result {repr got}"
            failures := failures + 1
        else throw (IO.userError "output count exceeds context bound")
      else throw (IO.userError "input count exceeds context bound")
    else throw (IO.userError "spend index outside transaction")
  let unknown := unknownAccepted + unknownRejected + unknownVerifier
  unless lines.length == 267 && excluded == 108 && baseDecoded == 159 && required == 91 && unknown == 68 &&
      verifier == 0 && unknownVerifier == 0 do
    IO.eprintln "FAIL transaction spend corpus counts"
    failures := failures + 1
  IO.println s!"transaction spends: {lines.length} records, {excluded} excluded, {baseDecoded} complete base decodes, {failures} failures"
  IO.println s!"transaction spends required accept: {required} inputs, {accepted} accepted, {verifier} unsupported at a signature opcode"
  IO.println s!"transaction spends unknown expectation: {unknown} inputs, {unknownAccepted} accepted, {unknownRejected} rejected, {unknownVerifier} unsupported at a signature opcode (no agreement claim)"
  return failures

end KnownAnswers.TxSpends


namespace KnownAnswers.Hmac

/-- RFC 4231 §§4.2–4.8: key, message and HMAC-SHA-256 tag in hexadecimal.
Case 5 supplies only the first 16 bytes.
Cases 6 and 7 use 131-byte keys.
The RFC Editor errata search was read on 2026-11-06.
Erratum 3853 adds an equals sign to case 3's key label and changes no bytes. -/
def vectors : Array (String × String × String) := #[
  ("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
    "4869205468657265",
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
  ("4a656665",
    "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
  ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
  ("0102030405060708090a0b0c0d0e0f10111213141516171819",
    "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd",
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"),
  ("0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c",
    "546573742057697468205472756e636174696f6e",
    "a3b6167473100ee06e0c796c2955552b"),
  ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374",
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
  ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e",
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")
]

/-- Checks all seven RFC tags through compiled HMAC, including the case 5 prefix. -/
def check : IO Nat := do
  let mut failures := 0
  for i in [:vectors.size] do
    let (keyHex, messageHex, tagHex) := vectors[i]!
    let parse (s : String) : IO ByteArray :=
      match Sha256Cavp.parseHex s with
      | .ok b => pure b
      | .error e => throw (IO.userError e)
    let key ← parse keyHex
    let message ← parse messageHex
    let expected ← parse tagHex
    let got := DogeLib.Cryptography.Hash.Hmac.hmac key message
    let tagSize := if i == 4 then 16 else 32
    unless got.size == 32 && expected.size == tagSize && got.extract 0 tagSize == expected do
      IO.eprintln s!"FAIL RFC 4231 case {i + 1}: {Sha256Cavp.toHex got}"
      failures := failures + 1
  unless vectors.size == 7 do
    IO.eprintln "FAIL RFC 4231 case count"
    failures := failures + 1
  IO.println s!"HMAC-SHA-256: {vectors.size} RFC 4231 cases, {failures} failures"
  return failures

end KnownAnswers.Hmac

namespace KnownAnswers.Secp256k1

open DogeLib DogeLib.Cryptography.Secp256k1
open KnownAnswers.Sha256Cavp (parseHex)

/-- The value of one scalar or coordinate in big-endian bytes. -/
def readNat (bytes : ByteArray) : Nat := ofBytesBE bytes.toList

/-- One quoted hex field in the pinned Wycheproof YAML subset, without a general YAML parser. -/
def hexField (name text : String) : Except String ByteArray := do
  let pre := "  " ++ name ++ ": '0x"
  let some line := (text.splitOn "\n").find? (·.startsWith pre)
    | throw s!"missing {name}"
  if !line.endsWith "'" then throw s!"bad quote in {name}"
  parseHex ((line.drop pre.length).toString.dropEnd 1).toString

/-- Checks 252 pinned P1363 records on coordinates and scalars.
Eighteen records have no 64-byte signature and check the fixture boundary only.
Reports time spent in the 234 scalar verifications, apart from fixture IO and decoding. -/
def check : IO Nat := do
  let mut failures := 0
  let mut scalarCases := 0
  let mut excluded := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut nanos : Nat := 0
  for id in [1:253] do
    let path := s!"tests/cryptography/secp256k1/verify/verify_wycheproof_p1363_{id}/data.yaml"
    let text ← IO.FS.readFile path
    let parsed : Except String (Point × Hash256 × ByteArray) := do
      let key ← hexField "public_key" text
      let digest ← hexField "msg_hash" text
      let sig ← hexField "signature" text
      if key.size != 65 || key[0]! != 4 then throw "expected uncompressed key"
      let x := readNat (key.extract 1 33)
      let y := readNat (key.extract 33 65)
      if hx : x < Fp.modulus then
        if hy : y < Fp.modulus then
          let some hash := Hash256.ofBytes? digest.toList | throw "digest length"
          return (.affine ⟨x, hx⟩ ⟨y, hy⟩, hash, sig)
        else throw "Y out of range"
      else throw "X out of range"
    let (q, hash, sig) ← match parsed with
      | .ok value => pure value
      | .error msg => throw (IO.userError s!"{path}: {msg}")
    let some output := (text.splitOn "\n").find? (·.startsWith "output: ")
      | throw (IO.userError s!"{path}: no output")
    if output == "output: null" then
      unless sig.size != 64 do throw (IO.userError s!"{path}: null on a scalar pair")
      excluded := excluded + 1
    else
      unless sig.size == 64 do throw (IO.userError s!"{path}: signature length")
      unless output == "output: true" || output == "output: false" do
        throw (IO.userError s!"{path}: unknown expectation")
      let r := readNat (sig.extract 0 32)
      let s := readNat (sig.extract 32 64)
      let start ← IO.monoNanosNow
      let got ← IO.lazyPure (fun _ => Ecdsa.verify q hash r s)
      if got then accepted := accepted + 1 else rejected := rejected + 1
      let stop ← IO.monoNanosNow
      nanos := nanos + (stop - start)
      scalarCases := scalarCases + 1
      unless got == (output == "output: true") do
        IO.eprintln s!"FAIL Wycheproof P1363 {id}: got {got}, expected {output}"
        failures := failures + 1
  unless scalarCases == 234 && excluded == 18 && accepted == 167 && rejected == 67 do
    IO.eprintln "FAIL Wycheproof P1363 counts"
    failures := failures + 1
  -- A non-palindromic digest fixes the storage-byte interpretation independently of curve arithmetic.
  let orderHash : Hash256 := ⟨1 :: List.replicate 31 0, by decide⟩
  unless Ecdsa.hashToInt orderHash == 2 ^ 248 do
    IO.eprintln "FAIL ECDSA digest byte order"
    failures := failures + 1
  IO.println s!"secp256k1 P1363: {scalarCases} scalar cases, {excluded} non-64-byte records excluded, {failures} failures"
  IO.println s!"secp256k1 timing: {nanos} ns / {scalarCases} verifications, {nanos / scalarCases} ns per verification (design budget about 1150000 ns)"
  return failures

end KnownAnswers.Secp256k1

/-!
## Core's signature verifier

### Public-key parsing

libsecp256k1's own test of `secp256k1_ec_pubkey_parse` at the compatibility pin supplies the points and the expectations (SOURCES.md, D57).
`run_ec_pubkey_parse_test` lists 12 valid points, 4 points with a valid `x` only and 7 invalid points.
`ec_pubkey_parse_pointtest` tries each one with every first byte from 0 to 255 and every length from 3 to 65.
Its formulas `xpass` and `ypass` give the expectation, and this test copies them.
No expectation comes from DogeLib.

The 23 points are copied from libsecp256k1 as Dogecoin Core bundles it at `e0a1c157791544e818c901bd9341896965afbf9d`, under the MIT licence in `LICENSES/libsecp256k1-MIT.txt`.
When a key must parse, the test checks the `x` of the point and, for a compressed key, the parity of `y`.
When `ypass` holds, it also checks `y`, as the upstream test does when it serializes the point again.

The points cover every row of design record 0005, section 4.1, and each failure: `x ≥ p`, `y ≥ p`, no square root, the wrong hybrid parity and a point off the curve.

### `coreVerifier` hand cases

- The digest one: `tx_valid.json` (D30) requires the acceptance of input 1 of the `SIGHASH_SINGLE` bug transaction, whose only check signs the fixed digest `01` followed by 31 zero bytes.
  The test runs its signature and key through `coreVerifier` with `Transaction.legacyOne`, and expects `true`.
  With the digest bytes reversed, `e` is 1 instead of `2^248`, and the test expects `false`.
- A high S: the same signature with S replaced by `n − S`, encoded again in DER.
  Core normalizes S before it verifies (D50, line 184), so the test expects `true`.
- Overflow: the same signature with R replaced by `n`, and with S replaced by a 33-byte value.
  The lax parser stores zero for both scalars (D50, lines 132 to 164), and `secp256k1_ecdsa_sig_verify` rejects a zero R, so the test expects `false`.
- Steps 1 to 4 of `CPubKey::Verify`: each gives `false`. The cases are an invalid key length, a key off the curve, the empty signature and a signature that the lax parser rejects.
-/

namespace KnownAnswers.CoreVerifier

open DogeLib DogeLib.Script DogeLib.Cryptography.Secp256k1
open KnownAnswers.Sha256Cavp (parseHex)

/-- Hex to a byte list. Malformed hex gives the empty list, which the length check or the expected result then rejects. -/
def hex (s : String) : List UInt8 :=
  match parseHex s with
  | .ok b => b.toList
  | .error _ => []

/-- The 64-byte `x ‖ y` inputs of `run_ec_pubkey_parse_test` (D57, lines 5231 to 5398), with `xvalid` and `yvalid`. -/
def parsePoints : List (String × Bool × Bool) :=
  -- `valid`: lines 5231 to 5316.
  [ "0000000000000000000000000000425200000000000000000000000000000000000064efa17b7761e1e42706989fb483b8d2d49bf78fae9803f099b834edeb00",
    "7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee4218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2c0e994b14ea72f8c3eb95c71ef692575e775058332d7e52d0995cf8038871b67d",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2cf166b4eb158d073c146a38e1096da8a188afa7ccd281ad2f66a307fb778e45b2",
    "00000000000000000000000000000000000000000000000000000000000000014218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "0000000000000000000000000000000000000000000000000000000000000001bde70df51939b94c9c24979fa7dd04ebd9b3572da7802290438af2a681895441",
    "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff507fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f673fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b5fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff5070000000000000000000000000000000000000000000000000000000000000001",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f6730000000000000000000000000000000000000000000000000000000000000001",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b50000000000000000000000000000000000000000000000000000000000000001"
  ].map (·, true, true) ++
  -- `onlyxvalid`: lines 5317 to 5347.
  [ "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff507fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f673fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b5fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000003"
  ].map (·, true, false) ++
  -- `invalid`: lines 5348 to 5398.
  [ "0a2d2ba93507f1df233770c2a797962cc61f6d15da14ecd47d8d27ae1cd5f8530000000000000000000000000000000000000000000000000000000000000001",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc304218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30bde70df51939b94c9c24979fa7dd04ebd9b3572da7802290438af2a681895441",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2ef484145cb0149b825dff412fa052a83fcb72db61d56f3770ce066b7349a2aa28",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e0b7beba34feb647da200bed05fad57c0348d249e2a90c88f31f9948bb65d5207",
    "00000000000000000000000000000000000000000000000000000000000000008f537eefdfc1606a0727cd69b4a7333d38ed44e3932a7179eecb4b6fba9360dc",
    "000000000000000000000000000000000000000000000000000000000000000070ac8110203e9f95f8d832964b58ccc2c712bb1c6cd58e861134b48f456c9b53"
  ].map (·, false, false)

/--
`ec_pubkey_parse_pointtest` (D57, lines 5154 to 5225) for one input.
Returns the number of failures, and the numbers of keys that parsed by `xpass` and by `ypass`.
-/
def pointTest (input : List UInt8) (xvalid yvalid : Bool) : Nat × Nat × Nat := Id.run do
  let mut failures := 0
  let mut xCount := 0
  let mut yCount := 0
  let x := ofBytesBE (input.take 32)
  let y := ofBytesBE (input.drop 32)
  let ysign := (input.getD 63 0 &&& 1).toNat + 2
  for len in [3:66] do
    for i in [0:256] do
      let key := (i.toUInt8) :: input.take (len - 1)
      let xpass := xvalid && len == 33 && (i &&& 254) == 2
      let ypass := xvalid && yvalid && (i &&& 4) == (if len == 65 then 4 else 0) &&
        (i == 4 || (i &&& 251) == ysign) && (len == 33 || len == 65)
      match parsePubKey key with
      | some (.affine px py) =>
        let ok := (xpass || ypass) && px.val == x &&
          (len != 33 || (py.val % 2 == 1) == (i == 3)) &&
          (!ypass || (py.val % 2) + 2 == ysign && py.val == y)
        if ok then
          if xpass then xCount := xCount + 1
          if ypass then yCount := yCount + 1
        else failures := failures + 1
      | some .infinity => failures := failures + 1
      | none => if xpass || ypass then failures := failures + 1
  return (failures, xCount, yCount)

/-- The DER encoding of a nonnegative integer, with a zero byte before a set top bit. -/
def derInt (v : Nat) : List UInt8 :=
  let rec bytes (fuel v : Nat) (acc : List UInt8) : List UInt8 :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if v = 0 then acc else bytes fuel (v / 256) ((v % 256).toUInt8 :: acc)
  let b := bytes 64 v []
  let b := if b.isEmpty then [0] else b
  let b := if b.headD 0 &&& 0x80 != 0 then 0 :: b else b
  0x02 :: (b.length.toUInt8) :: b

/-- A DER signature of two integer encodings. -/
def derSig (r s : List UInt8) : List UInt8 := 0x30 :: (r.length + s.length).toUInt8 :: (r ++ s)

/-- Input 1 of the `SIGHASH_SINGLE` bug transaction of `tx_valid.json` (D30), lines 53 to 56: R, S and the key. -/
def oneR : Nat := 0xc9cdd08798a28af9d1baf44a6c77bcc7e279f47dc487c8c899911bc48feaffcc
def oneS : Nat := 0x503c5c50ae3998a733263c5c0f7061b483e2b56c4c41b456e7d2f5a78a74c077
def oneKey : List UInt8 := hex "02d5c25adb51b61339d2b05315791e21bbe80ea470a49db0135720983c905aace0"
/-- The signature bytes of that input, without the hash-type byte `03`. -/
def oneSig : List UInt8 :=
  hex "3045022100c9cdd08798a28af9d1baf44a6c77bcc7e279f47dc487c8c899911bc48feaffcc0220503c5c50ae3998a733263c5c0f7061b483e2b56c4c41b456e7d2f5a78a74c077"

/-- Runs the parse test and the hand cases. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  let mut xTotal := 0
  let mut yTotal := 0
  for (h, xvalid, yvalid) in parsePoints do
    let input := hex h
    unless input.length == 64 do throw (IO.userError "point length")
    let (f, xs, ys) := pointTest input xvalid yvalid
    if f != 0 then IO.eprintln s!"FAIL ec_pubkey_parse_pointtest {h}: {f} failures"
    failures := failures + f
    xTotal := xTotal + xs
    yTotal := yTotal + ys
  -- `xpass`: each of the 16 points with a valid `x` parses with 33 bytes and the first byte `02` or `03`.
  -- `ypass`: each of the 12 valid points parses with 33 bytes and its parity byte, with `04`, and with its hybrid byte.
  unless parsePoints.length == 23 && xTotal == 32 && yTotal == 36 do
    IO.eprintln s!"FAIL ec_pubkey_parse_pointtest counts: {xTotal} xpass, {yTotal} ypass"
    failures := failures + 1
  let reversed : Hash256 := ⟨Transaction.legacyOne.val.reverse, by simp [Transaction.legacyOne]⟩
  let n := secp256k1Order
  let cases : List (String × List UInt8 × List UInt8 × Hash256 × Bool) := [
    ("digest one", oneSig, oneKey, Transaction.legacyOne, true),
    ("digest one reversed", oneSig, oneKey, reversed, false),
    ("re-encoded signature", derSig (derInt oneR) (derInt oneS), oneKey, Transaction.legacyOne, true),
    ("high S", derSig (derInt oneR) (derInt (n - oneS)), oneKey, Transaction.legacyOne, true),
    ("high S, digest reversed", derSig (derInt oneR) (derInt (n - oneS)), oneKey, reversed, false),
    ("R overflow", derSig (derInt n) (derInt oneS), oneKey, Transaction.legacyOne, false),
    ("S of 33 bytes", derSig (derInt oneR) (0x02 :: 33 :: 0x01 :: List.replicate 32 0), oneKey,
      Transaction.legacyOne, false),
    ("invalid key length", oneSig, oneKey.dropLast, Transaction.legacyOne, false),
    ("key off the curve", oneSig, 0x04 :: hex (parsePoints[15]!.1), Transaction.legacyOne, false),
    ("empty signature", [], oneKey, Transaction.legacyOne, false),
    ("lax parser rejects", [0x31] ++ oneSig.drop 1, oneKey, Transaction.legacyOne, false)
  ]
  for (label, sig, key, digest, expected) in cases do
    let got := coreVerifier sig key digest
    unless got == some expected do
      IO.eprintln s!"FAIL coreVerifier {label}: got {got}"
      failures := failures + 1
  -- The re-encoded signature is the corpus signature, so the hand encodings start from Core's bytes.
  unless derSig (derInt oneR) (derInt oneS) == oneSig do
    IO.eprintln "FAIL coreVerifier: DER re-encoding differs from the corpus signature"
    failures := failures + 1
  IO.println s!"public-key parse test: {parsePoints.length} points, 256 first bytes, lengths 3 to 65, {xTotal} xpass and {yTotal} ypass parses, {failures} failures"
  IO.println s!"coreVerifier: {cases.length} hand cases"
  return failures

end KnownAnswers.CoreVerifier


namespace KnownAnswers.Pbkdf2

/-- Both RFC 7914 §11 cases: ASCII password, salt, count and complete 64-byte derived key.
The RFC Editor errata search was read on 2026-11-06.
Verified errata 5871 and 6972 concern ASN.1 and parameter advice.
Reported errata 5971, 5972, 5973 and 6452 concern scrypt parameters and Integerify.
None changes section 11. -/
def vectors : Array (String × String × Nat × String) := #[
  ("passwd", "salt", 1,
    "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc" ++
    "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"),
  ("Password", "NaCl", 80000,
    "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56" ++
    "a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d")
]

/-- Check both complete RFC outputs through compiled PBKDF2 and print each elapsed time.
The first vector also checks output prefixes and the model's zero-count extension.
Zero output and oversized output check the declared API boundaries. -/
def check : IO Nat := do
  let mut failures := 0
  for i in [:vectors.size] do
    let (password, salt, c, hex) := vectors[i]!
    let expected ← match Sha256Cavp.parseHex hex with
      | .ok b => pure b
      | .error e => throw (IO.userError e)
    let start ← IO.monoMsNow
    let got := DogeLib.Cryptography.Hash.Pbkdf2.pbkdf2 password.toUTF8 salt.toUTF8 c 64
    unless got == some expected && expected.size == 64 do
      IO.eprintln s!"FAIL RFC 7914 section 11 case {i + 1}"
      failures := failures + 1
    let stop ← IO.monoMsNow
    IO.println s!"PBKDF2-HMAC-SHA-256: RFC case {i + 1}, c={c}, {stop - start} ms"
    if i == 0 then
      for n in [0, 1, 31, 32, 33, 63, 64] do
        unless DogeLib.Cryptography.Hash.Pbkdf2.pbkdf2 password.toUTF8 salt.toUTF8 c n ==
            some (expected.extract 0 n) do
          IO.eprintln s!"FAIL PBKDF2 RFC prefix of {n} bytes"
          failures := failures + 1
      unless DogeLib.Cryptography.Hash.Pbkdf2.pbkdf2 password.toUTF8 salt.toUTF8 0 64 == some expected do
        IO.eprintln "FAIL PBKDF2 zero iterations"
        failures := failures + 1
  let empty := ByteArray.empty
  unless DogeLib.Cryptography.Hash.Pbkdf2.pbkdf2 empty empty 0 0 == some empty &&
      DogeLib.Cryptography.Hash.Pbkdf2.pbkdf2 empty empty 1 ((2 ^ 32 - 1) * 32 + 1) == none do
    IO.eprintln "FAIL PBKDF2 output length boundaries"
    failures := failures + 1
  unless vectors.size == 2 do
    IO.eprintln "FAIL RFC 7914 section 11 case count"
    failures := failures + 1
  IO.println s!"PBKDF2-HMAC-SHA-256: {vectors.size} RFC 7914 cases, {failures} failures"
  return failures

end KnownAnswers.Pbkdf2

namespace KnownAnswers.Scrypt

open DogeLib.Cryptography.Hash

/-- RFC 7914 §8: all 64 input bytes of the Salsa20/8 known answer. -/
def salsaInput : String :=
    "7e879a214f3ec9867ca940e641718f26" ++
    "baee555b8c61c1b50df846116dcd3b1d" ++
    "ee24f319df9b3d8514121e4b5ac5aa32" ++
    "76021d2909c74829edebc68db8b8c25e"

/-- RFC 7914 §8: all 64 expected bytes of the Salsa20/8 known answer. -/
def salsaOutput : String :=
    "a41f859c6608cc993b81cacb020cef05" ++
    "044b2181a2fd337dfd7b1c6396682f29" ++
    "b4393168e3c9e6bcfe6bc5b7a06d96ba" ++
    "e424cc102c91745c24ad673dc7618f81"

/-- RFC 7914 §§9–10: the shared 128-byte input, with `r = 1`. -/
def mixInput : String :=
    "f7ce0b653d2d72a4108cf5abe912ffdd" ++
    "777616dbbb27a70e8204f3ae2d0f6fad" ++
    "89f68f4811d1e87bcc3bd7400a9ffd29" ++
    "094f0184639574f39ae5a1315217bcd7" ++
    "894991447213bb226c25b54da86370fb" ++
    "cd984380374666bb8ffcb5bf40c254b0" ++
    "67d27c51ce4ad5fed829c90b505a571b" ++
    "7f4d1cad6a523cda770e67bceaaf7e89"

/-- RFC 7914 §9: the full BlockMix output, in even-then-odd block order. -/
def blockMixOutput : String :=
    "a41f859c6608cc993b81cacb020cef05" ++
    "044b2181a2fd337dfd7b1c6396682f29" ++
    "b4393168e3c9e6bcfe6bc5b7a06d96ba" ++
    "e424cc102c91745c24ad673dc7618f81" ++
    "20edc975323881a80540f64c162dcd3c" ++
    "21077cfe5f8d5fe2b1a4168f953678b7" ++
    "7d3b3d803b60e4ab920996e59b4d53b6" ++
    "5d2a225877d5edf5842cb9f14eefe425"

/-- RFC 7914 §10: the full ROMix output for `r = 1` and `N = 16`. -/
def roMixOutput : String :=
    "79ccc193629debca047f0b70604bf6b6" ++
    "2ce3dd4a9626e355fafc6198e6ea2b46" ++
    "d58413673b99b029d665c357601fb426" ++
    "a0b2f4bba200ee9f0a43d19b571a9c71" ++
    "ef1142e65d5a266fddca832ce59faa7c" ++
    "ac0b9cf1be2bffca300d01ee387619c4" ++
    "ae12fd4438f203a0e4e1c47ec314861f" ++
    "4e9087cb33396a6873e8f9d2539a4b8e"

/-- All four RFC 7914 §12 tuples: password, salt, `N`, `r`, `p`, and complete 64-byte output.
Only case 1 runs by default.
The optional cases support measured cost checks without changing the reference fill.
The RFC Editor errata were read on 2026-11-06, and none changes these vectors.
See `tests/cryptography/scrypt/README.md` for provenance and cost limits. -/
def vectors : Array (String × String × Nat × Nat × Nat × String) := #[
  ("", "", 16, 1, 1,
    "77d6576238657b203b19ca42c18a0497" ++
    "f16b4844e3074ae8dfdffa3fede21442" ++
    "fcd0069ded0948f8326a753a0fc81f17" ++
    "e8d3e0fb2e0d3628cf35e20c38d18906"),
  ("password", "NaCl", 1024, 8, 16,
    "fdbabe1c9d3472007856e7190d01e9fe" ++
    "7c6ad7cbc8237830e77376634b373162" ++
    "2eaf30d92e22a3886ff109279d9830da" ++
    "c727afb94a83ee6d8360cbdfa2cc0640"),
  ("pleaseletmein", "SodiumChloride", 16384, 8, 1,
    "7023bdcb3afd7348461c06cd81fd38eb" ++
    "fda8fbba904f8e3ea9b543f6545da1f2" ++
    "d5432955613f0fcf62d49705242a9af9" ++
    "e61e85dc0d651e40dfcf017b45575887"),
  ("pleaseletmein", "SodiumChloride", 1048576, 8, 1,
    "2101cb9b6a511aaeaddbbe09cf70f881" ++
    "ec568d574a2ffd4dabe5ee9820adaa47" ++
    "8e56fd8f4ba5d09ffa1c6d927c40f4c3" ++
    "37304049e8a952fbcbf45c6fa77a41a4")
]

/-- Parse the recorded hexadecimal bytes and retain their order in the list model. -/
def parse (hex : String) : IO (List (BitVec 8)) := do
  match Sha256Cavp.parseHex hex with
  | .ok b => return Hmac.Spec.toBytes b
  | .error e => throw (IO.userError e)

/-- Compare a complete section 12 output through the compiled reference model.
The case index is zero-based, and an absent case is an error. -/
def checkCase (i : Nat) : IO Nat := do
  let some (password, salt, n, r, p, hex) := vectors[i]?
    | throw (IO.userError "scrypt RFC case index out of range")
  let expected ← parse hex
  IO.println s!"scrypt: starting RFC 7914 section 12 case {i + 1}, N={n}, r={r}, p={p}"
  let start ← IO.monoMsNow
  let got := Scrypt.Spec.scrypt (Hmac.Spec.toBytes password.toUTF8) (Hmac.Spec.toBytes salt.toUTF8) n r p 64
  let ok := got == some expected && expected.length == 64
  unless ok do IO.eprintln s!"FAIL RFC 7914 section 12 case {i + 1}"
  let stop ← IO.monoMsNow
  IO.println s!"scrypt: RFC case {i + 1}, {stop - start} ms, {if ok then 0 else 1} failures"
  return if ok then 0 else 1

/-- Check RFC 7914 §§8–10 and the small section 12 case through the compiled model.
Check that invalid parameter tuples give `none`.
`valid` rejects every tuple except the excessive output length, which PBKDF2 rejects. -/
def check : IO Nat := do
  let mut failures := 0
  for (name, inputHex, outputHex, size, f) in [
      ("Salsa20/8", salsaInput, salsaOutput, 64, Scrypt.Spec.salsa),
      ("BlockMix", mixInput, blockMixOutput, 128, Scrypt.Spec.blockMix 1),
      ("ROMix", mixInput, roMixOutput, 128, Scrypt.Spec.roMix 1 16)] do
    let input ← parse inputHex
    let expected ← parse outputHex
    let start ← IO.monoMsNow
    unless input.length == size && expected.length == size && f input == expected do
      IO.eprintln s!"FAIL RFC 7914 {name}"
      failures := failures + 1
    let stop ← IO.monoMsNow
    IO.println s!"scrypt: RFC {name}, {stop - start} ms"
  failures := failures + (← checkCase 0)
  for (n, r, p, len) in [(0, 1, 1, 64), (1, 1, 1, 64), (3, 1, 1, 64),
      (65536, 1, 1, 64), (16, 0, 1, 64), (16, 1, 0, 64),
      (16, 1, 1073741824, 64), (16, 1, 1, 0),
      (16, 1, 1, (2 ^ 32 - 1) * 32 + 1)] do
    unless Scrypt.Spec.scrypt [] [] n r p len == none do
      IO.eprintln s!"FAIL scrypt rejection N={n}, r={r}, p={p}, dkLen={len}"
      failures := failures + 1
  IO.println s!"scrypt: four RFC known answers and parameter rejection checks, {failures} failures"
  return failures

end KnownAnswers.Scrypt

/-- Entry point of `lake test`.
`--scrypt-rfc n` runs only section 12 case `n` (one-based), including optional expensive cases. -/
def main (args : List String) : IO UInt32 := do
  if let ["--scrypt-rfc", index] := args then
    let some n := index.toNat? | throw (IO.userError "expected a case number from 1 to 4")
    unless 1 ≤ n && n ≤ 4 do throw (IO.userError "expected a case number from 1 to 4")
    return if (← KnownAnswers.Scrypt.checkCase (n - 1)) == 0 then 0 else 1
  unless args.isEmpty do throw (IO.userError "usage: known-answers [--scrypt-rfc 1|2|3|4]")
  let scrypt ← KnownAnswers.Scrypt.check
  let pbkdf2 ← KnownAnswers.Pbkdf2.check
  let hmac ← KnownAnswers.Hmac.check
  let secp256k1 ← KnownAnswers.Secp256k1.check
  let coreVerifier ← KnownAnswers.CoreVerifier.check
  let sha1 ← KnownAnswers.Sha1.check
  let dir : System.FilePath := "tests/cryptography/sha256/cavp"
  let short ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256ShortMsg.rsp") 65
  let long ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256LongMsg.rsp") 64
  let ripemd ← KnownAnswers.Ripemd160.check
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
  let blocks ← KnownAnswers.Block.check
  let auxpowCheck ← KnownAnswers.AuxPowCheck.check
  let mainnetHeaders ← KnownAnswers.Work.MainnetHeaders.check
  let proofOfWork ← KnownAnswers.Work.checkProofOfWorkCases
  let scriptReader ← KnownAnswers.Script.check
  let nextWork ← KnownAnswers.Work.checkNextWork
  let operators ← KnownAnswers.Work.checkOperators
  let shifts ← KnownAnswers.Work.checkShifts
  let scriptNum ← KnownAnswers.ScriptNum.check
  let scriptEval ← KnownAnswers.ScriptEval.check
  let signatureCode ← KnownAnswers.SignatureCode.check
  let signatureEncoding ← KnownAnswers.SignatureEncoding.check
  let scriptSignature ← KnownAnswers.ScriptSignature.check
  let scriptVerify ← KnownAnswers.ScriptVerify.check
  let multisigRecovery ← KnownAnswers.MultisigRecovery.check
  let txSpends ← KnownAnswers.TxSpends.check
  return if scrypt + pbkdf2 + hmac + secp256k1 + coreVerifier + sha1 + blocks + auxpowCheck + short + long + ripemd + genesis + codec + compactSize + countedList + transactions + witness + txCorpus + sighash + compact + retarget + nextWork + mainnetHeaders + operators + shifts + proofOfWork + scriptReader + scriptNum + scriptEval + signatureCode + signatureEncoding + scriptSignature + scriptVerify + multisigRecovery + txSpends == 0 then 0 else 1

