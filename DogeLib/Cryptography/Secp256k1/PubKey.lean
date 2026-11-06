module

public import DogeLib.Cryptography.Secp256k1.Ecdsa

/-!
# `Secp256k1.PubKey`

The public-key parser of Dogecoin Core's bundled libsecp256k1, `secp256k1_ec_pubkey_parse`.

It accepts exactly these encodings:

| Length | First byte | Condition |
| --- | --- | --- |
| 33 | `02` or `03` | `x` is below `p`, and `x^3 + 7` has a square root. The root with the parity of the first byte is `y`. |
| 65 | `04` | `x` and `y` are below `p`, and `(x, y)` is on the curve. |
| 65 | `06` or `07` | As for `04`, and `y` is even for `06` and odd for `07`. |

The hybrid encodings `06` and `07` are not in SEC 1 v2 §2.3.4.
Core accepts them, and Script reaches this parser with them when `STRICTENC` is clear.

## Source

Dogecoin Core at `e0a1c157791544e818c901bd9341896965afbf9d`, `src/secp256k1` (SOURCES.md D5, D52, D58 and D59):

| DogeLib | libsecp256k1 | File and lines |
| --- | --- | --- |
| `readCoordinate` | `secp256k1_fe_set_b32` | `src/field_5x52_impl.h`, lines 309 to 345 |
| `decompress` | `secp256k1_ge_set_xo_var` | `src/group_impl.h`, lines 214 to 229 |
| `parsePubKey` | `secp256k1_eckey_pubkey_parse` and `secp256k1_ec_pubkey_parse` | `src/eckey_impl.h`, lines 17 to 35, and `src/secp256k1.c`, lines 228 to 244 |

`secp256k1_ec_pubkey_parse` also runs `secp256k1_ge_is_in_correct_subgroup` (`src/group_impl.h`, lines 677 to 697).
Outside the exhaustive-test build, that test returns true, because the cofactor of secp256k1 is 1.
`parsePubKey` therefore omits it.

The parser is written from these sources. It is not adapted from EthLib, whose decoder rejects the hybrid encodings.
-/

@[expose] public section

namespace DogeLib.Cryptography.Secp256k1

/-- A coordinate from 32 big-endian bytes: `secp256k1_fe_set_b32`, which fails when the value is at least `p`. -/
def readCoordinate (bytes : List UInt8) : Option Fp :=
  let v := ofBytesBE bytes
  if h : v < Fp.modulus then some ⟨v, h⟩ else none

namespace Point

/-- Whether the `y` of a point is odd: `secp256k1_fe_is_odd` on a normalized coordinate.

The point at infinity has no `y`, and gives `false`. -/
def isOddY : Point → Bool
  | infinity => false
  | affine _ y => y.val % 2 == 1

end Point

/--
The point with this `x` and a `y` of the given parity: `secp256k1_ge_set_xo_var`.
It fails when `x^3 + 7` has no square root.
Otherwise it takes the root that `Fp.sqrt` finds, and negates it when its parity differs from `odd`.
-/
def decompress (x : Fp) (odd : Bool) : Option Point :=
  match Fp.sqrt (x * x * x + b) with
  | none => none
  | some y => some (.affine x (if (y.val % 2 == 1) != odd then -y else y))

/--
`secp256k1_ec_pubkey_parse` on a 64-bit build of Core at the compatibility pin.
`none` is Core's return value 0, and `some q` is the return value 1 with the point `q`.

1. With 33 bytes and the first byte `02` or `03`: `readCoordinate` of bytes 1 to 32, then `decompress` with the parity of the first byte.
2. With 65 bytes and the first byte `04`, `06` or `07`: `readCoordinate` of bytes 1 to 32 and 33 to 64.
   For `06` and `07`, the parity of `y` must be even and odd.
   Then `(x, y)` must satisfy the curve equation.
3. Any other input fails.
-/
def parsePubKey (key : List UInt8) : Option Point :=
  let header := key.getD 0 0
  if key.length = 33 ∧ (header = 0x02 ∨ header = 0x03) then
    match readCoordinate ((key.drop 1).take 32) with
    | none => none
    | some x => decompress x (header == 0x03)
  else if key.length = 65 ∧ (header = 0x04 ∨ header = 0x06 ∨ header = 0x07) then
    match readCoordinate ((key.drop 1).take 32), readCoordinate ((key.drop 33).take 32) with
    | some x, some y =>
      let q := Point.affine x y
      if (header = 0x06 ∨ header = 0x07) ∧ q.isOddY ≠ (header == 0x07) then none
      else if q.isOnCurve then some q else none
    | _, _ => none
  else none

end DogeLib.Cryptography.Secp256k1
