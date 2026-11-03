import DogeLib.Cryptography.Hash.Sha256
import DogeLib.Cryptography.Hash.Sha256d

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

/-- Entry point of `lake test`. -/
def main : IO UInt32 := do
  let dir : System.FilePath := "tests/cryptography/sha256/cavp"
  let short ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256ShortMsg.rsp") 65
  let long ← KnownAnswers.Sha256Cavp.checkFile (dir / "SHA256LongMsg.rsp") 64
  let genesis ← KnownAnswers.Genesis.check
  return if short + long + genesis == 0 then 0 else 1
