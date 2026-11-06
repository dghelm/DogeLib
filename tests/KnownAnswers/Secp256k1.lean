import DogeLib.Cryptography.Secp256k1.Ecdsa
import KnownAnswers.Common

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

/-- Named checks for Secp256k1 known answers, in alphabetical order. -/
def KnownAnswers.Secp256k1.checks : List (String × IO Nat) := [
  ("secp256k1", KnownAnswers.Secp256k1.check)
]
