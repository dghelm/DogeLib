import DogeLib.Cryptography.Proofs.Hash.ScryptSpec
import KnownAnswers.Common

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

/-- Named checks for Scrypt known answers, in alphabetical order. -/
def KnownAnswers.Scrypt.checks : List (String × IO Nat) := [
  ("scrypt", KnownAnswers.Scrypt.check)
]
