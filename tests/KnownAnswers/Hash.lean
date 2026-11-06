import DogeLib.Cryptography.Hash.Hash160
import DogeLib.Cryptography.Hash.Hmac
import DogeLib.Cryptography.Hash.Pbkdf2
import DogeLib.Cryptography.Hash.Sha1
import DogeLib.Cryptography.Hash.Sha256
import KnownAnswers.Common

/-!
## SHA-256

Runs the NIST CAVP SHA-256 vectors through the compiled `hash`.

`hash_eq_spec` proves that the definitions agree with a model of FIPS 180-4.
That theorem says nothing about the code that the Lean compiler produces from them.
This test checks the compiled code on the 129 byte-oriented vectors of CAVS 11.0.

Each file must contain the expected number of vectors.
A parser that reads none would otherwise pass.
-/

namespace KnownAnswers.Sha256Cavp

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

/-- Named checks for Hash known answers, in alphabetical order. -/
def KnownAnswers.Hash.checks : List (String × IO Nat) := [
  ("hmac", KnownAnswers.Hmac.check),
  ("pbkdf2", KnownAnswers.Pbkdf2.check),
  ("ripemd", KnownAnswers.Ripemd160.check),
  ("sha1", KnownAnswers.Sha1.check),
  ("sha256Long", KnownAnswers.Sha256Cavp.checkFile "tests/cryptography/sha256/cavp/SHA256LongMsg.rsp" 64),
  ("sha256Short", KnownAnswers.Sha256Cavp.checkFile "tests/cryptography/sha256/cavp/SHA256ShortMsg.rsp" 65),
]
