module

public import DogeLib.Cryptography.Proofs.Hash.Pbkdf2Spec

/-!
# RFC 7914 scrypt list model

Adapted from pyca/verified-garbage `lean/VerifiedGarbage/Spec/Scrypt.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes imports, namespaces and documentation, and spells VG's `Byte` as `BitVec 8`.
It retains the definitions, including the quadratic reference fill of ROMix.
PBKDF2 uses the existing list model with DogeLib's executable SHA-256 through HMAC.

Sections below refer to RFC 7914.
The RFC Editor errata were read on 2026-11-06.
Verified errata 5871 and 6972 concern ASN.1 and parameter advice, and do not change these definitions.

Reported errata 5971–5973 propose removing the published upper bound on `N`.
This model retains that bound, as the pinned VG definition does.
Reported erratum 6452 proposes different Integerify wording.
This model reads the final 64-byte block as a little-endian integer, as the published RFC and VG specify.
None of these errata changes the known answers in sections 8–12.

The component functions are total on arbitrary byte lists and natural parameters.
`wordLE` supplies zero for absent bytes, and XOR truncates to the shorter input.
Their RFC input domains are the lengths stated in their doc comments.
Only `scrypt` checks parameter validity and the PBKDF2 output limit.
No theorem here asserts cryptographic security or agreement with Dogecoin Core.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Scrypt.Spec

open Pbkdf2.Spec (xorBytes)

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-! ## The Salsa20/8 Core (§3) -/

/-- One line of the RFC's `salsa20_word_specification`,
`x[i] ^= R(x[j]+x[k], n)`, where `R(a,b)` is the rotation of `a` by `b`
bits towards the high bits. -/
def step (x : Vector Word 16) (i j k : Fin 16) (n : Nat) : Vector Word 16 :=
  x.set i (x[i] ^^^ (x[j] + x[k]).rotateLeft n)

/-- The body of the RFC's loop `for (i = 8;i > 0;i -= 2)`: a column round
and a row round, in the RFC's order. -/
def doubleRound (x : Vector Word 16) : Vector Word 16 :=
  let x := step x  4  0 12  7; let x := step x  8  4  0  9
  let x := step x 12  8  4 13; let x := step x  0 12  8 18
  let x := step x  9  5  1  7; let x := step x 13  9  5  9
  let x := step x  1 13  9 13; let x := step x  5  1 13 18
  let x := step x 14 10  6  7; let x := step x  2 14 10  9
  let x := step x  6  2 14 13; let x := step x 10  6  2 18
  let x := step x  3 15 11  7; let x := step x  7  3 15  9
  let x := step x 11  7  3 13; let x := step x 15 11  7 18
  let x := step x  1  0  3  7; let x := step x  2  1  0  9
  let x := step x  3  2  1 13; let x := step x  0  3  2 18
  let x := step x  6  5  4  7; let x := step x  7  6  5  9
  let x := step x  4  7  6 13; let x := step x  5  4  7 18
  let x := step x 11 10  9  7; let x := step x  8 11 10  9
  let x := step x  9  8 11 13; let x := step x 10  9  8 18
  let x := step x 12 15 14  7; let x := step x 13 12 15  9
  let x := step x 14 13 12 13
  step x 15 14 13 18

/-- `salsa20_word_specification`: four iterations of `doubleRound` (the loop
runs for `i = 8, 6, 4, 2`), then the input added word by word (modulo 2³²). -/
def core (b : Vector Word 16) : Vector Word 16 :=
  Vector.zipWith (· + ·) (Nat.repeat doubleRound 4 b) b

/-- Word `j` of a byte string read as little-endian 32-bit integers. -/
def wordLE (bs : List (BitVec 8)) (j : Nat) : Word :=
  (bs.getD (4 * j + 3) 0 ++ bs.getD (4 * j + 2) 0 ++ bs.getD (4 * j + 1) 0 ++ bs.getD (4 * j) 0 : Word)

/-- Sixteen words as 64 bytes, each little-endian. -/
def serialize (x : Vector Word 16) : List (BitVec 8) :=
  x.toList.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `Salsa (T)`: the Salsa20/8 Core on a 64-octet string. -/
def salsa (t : List (BitVec 8)) : List (BitVec 8) :=
  serialize (core (Vector.ofFn fun j => wordLE t j.1))

/-! ## scryptBlockMix (§4) -/

/-- `B[i]`: the `i`th 64-octet block of `b`. -/
def blk (b : List (BitVec 8)) (i : Nat) : List (BitVec 8) := (b.drop (64 * i)).take 64

/-- Step 2 of scryptBlockMix returns the `Y[i]` blocks for indices in `is`, in order.
Each step sets `T = X xor B[i]`, then `X = Salsa (T)` and `Y[i] = X`. -/
def blockMixYs (b : List (BitVec 8)) : List (BitVec 8) → List Nat → List (List (BitVec 8))
  | _, [] => []
  | x, i :: is => let x' := salsa (xorBytes x (blk b i)); x' :: blockMixYs b x' is

/-- scryptBlockMix with block size parameter `r`, on the `128 * r` octets
`B[0] ‖ … ‖ B[2 * r - 1]`: step 1 (`X = B[2 * r - 1]`), step 2 for
`i = 0 … 2 * r - 1`, and step 3,
`B' = (Y[0], Y[2], …, Y[2 * r - 2], Y[1], Y[3], …, Y[2 * r - 1])`. -/
def blockMix (r : Nat) (b : List (BitVec 8)) : List (BitVec 8) :=
  let y := blockMixYs b (blk b (2 * r - 1)) (List.range (2 * r))
  ((List.range r).flatMap fun i => y.getD (2 * i) []) ++
    ((List.range r).flatMap fun i => y.getD (2 * i + 1) [])

/-! ## scryptROMix (§5) -/

/-- An octet string as a little-endian integer. -/
def leNat (bs : List (BitVec 8)) : Nat := bs.foldr (fun b n => b.toNat + 256 * n) 0

/-- `Integerify (B[0] ‖ … ‖ B[2 * r - 1])`: `B[2 * r - 1]` as a
little-endian integer. -/
def integerify (r : Nat) (x : List (BitVec 8)) : Nat := leNat (blk x (2 * r - 1))

/-- Step 3 of scryptROMix, `n` more iterations from `X`, with the blocks `V`
written in step 2: `j = Integerify (X) mod N`, `T = X xor V[j]`,
`X = scryptBlockMix (T)`. Returns the final `X` and the indices `j`, in the
order they were computed. -/
def mixLoop (r N : Nat) (v : List (List (BitVec 8))) : Nat → List (BitVec 8) → List (BitVec 8) × List Nat
  | 0, x => (x, [])
  | n + 1, x =>
    let j := integerify r x % N
    let (x', js) := mixLoop r N v n (blockMix r (xorBytes x (v.getD j [])))
    (x', j :: js)

/-- Steps 1–3 of scryptROMix, with block size `r` and cost `N`, on `128 * r` bytes.
Step 2 computes `V[i] = scryptBlockMix^i (B)` separately for `i = 0 … N - 1`.
It leaves `X = scryptBlockMix^N (B)`, then step 3 performs `N` further iterations.
The result is the final `X` (step 4, `B'`) and the indices `j` read in step 3. -/
def roMixAux (r N : Nat) (b : List (BitVec 8)) : List (BitVec 8) × List Nat :=
  let v := (List.range N).map fun i => Nat.repeat (blockMix r) i b
  mixLoop r N v N (Nat.repeat (blockMix r) N b)

/-- scryptROMix (`B'`). -/
def roMix (r N : Nat) (b : List (BitVec 8)) : List (BitVec 8) := (roMixAux r N b).1

/-- The indices `j = Integerify (X) mod N` read by step 3 of scryptROMix, in order.
These indices depend on the input, so the model makes no constant-time claim. -/
def roMixIndices (r N : Nat) (b : List (BitVec 8)) : List Nat := (roMixAux r N b).2

/-! ## scrypt (§6) -/

/-- The published §6 parameter conditions, except the output upper bound checked by PBKDF2.
`N` must exceed 1, be a power of 2, and be less than `2^(128 * r / 8)`.
`p` must be positive and at most `((2^32 - 1) * 32) / (128 * r)`.
`dkLen` must be positive, and PBKDF2 separately checks `dkLen ≤ (2^32 - 1) * 32`.
The bound on `N` implies positive `r`. -/
def valid (N r p dkLen : Nat) : Prop :=
  1 < N ∧ N &&& (N - 1) = 0 ∧ N < 2 ^ (128 * r / 8) ∧
    0 < p ∧ p ≤ (2 ^ 32 - 1) * 32 / (128 * r) ∧ 0 < dkLen

instance (N r p dkLen : Nat) : Decidable (valid N r p dkLen) := by
  unfold valid; infer_instance

/-- `scrypt (P, S, N, r, p, dkLen)` returns `none` for invalid parameters or an excessive PBKDF2 output length.
Otherwise, it computes the following three steps:
1. `B[0] ‖ … ‖ B[p - 1] = PBKDF2-HMAC-SHA256 (P, S, 1, p * 128 * r)`,
2. `B[i] = scryptROMix (r, B[i], N)` for `i = 0 … p - 1`,
3. `DK = PBKDF2-HMAC-SHA256 (P, B[0] ‖ … ‖ B[p - 1], 1, dkLen)`. -/
def scrypt (pw s : List (BitVec 8)) (N r p dkLen : Nat) : Option (List (BitVec 8)) :=
  if valid N r p dkLen then do
    let b ← Pbkdf2.Spec.pbkdf2HmacSha256 pw s 1 (p * 128 * r)
    let b' := (List.range p).flatMap fun i => roMix r N ((b.drop (128 * r * i)).take (128 * r))
    Pbkdf2.Spec.pbkdf2HmacSha256 pw b' 1 dkLen
  else none

end DogeLib.Cryptography.Hash.Scrypt.Spec
