module

public import DogeLib.Base.Bytes
public import DogeLib.Cryptography.Hash.Pbkdf2

/-!
# `scrypt_1024_1_1_256`

Dogecoin's proof-of-work digest: scrypt with N = 1024, r = 1, p = 1 and a 32-byte output,
with the same 80 bytes as password and salt.

The definitions follow `scrypt_1024_1_1_256_sp_generic` and `xor_salsa8` in Dogecoin Core's
`src/crypto/scrypt.cpp`, lines 121–218 at the pin (SOURCES.md, C13 of design record 0004).
They follow its loops and index computation, but copy no code or comments from that file.

- PBKDF2-HMAC-SHA-256 with one iteration derives 128 bytes, which `le32dec` reads as 32 words.
- The state `X[0..31]` is held as its two halves, `X[0..15]` and `X[16..31]`.
- The first loop stores `X` in the flat scratchpad `V`, at words `32 * i` to `32 * i + 31`,
  then applies `xor_salsa8(&X[0], &X[16])` and `xor_salsa8(&X[16], &X[0])`.
- The second loop computes `j = 32 * (X[16] & 1023)`, XORs `V[j..j+31]` into `X`,
  and applies the same two calls.
- `le32enc` writes `X` back to 128 bytes, and PBKDF2 with one iteration derives the 32-byte digest.

Each double round runs Core's statements in Core's order.
`powHash_eq_spec` in `DogeLib.Cryptography.Proofs.Hash.ScryptPow` proves the digest equal to the
RFC 7914 model with these parameters, for every 80-byte input.
The definition makes no constant-time claim.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Scrypt

/-- `ROTL(a, b)` of Core: rotation of `a` by `n` bits towards the high bits. -/
@[inline] def rotl (a : UInt32) (n : UInt32) : UInt32 := (a <<< n) ||| (a >>> (32 - n))

/-- One statement of `xor_salsa8`'s loop: `x[i] ^= ROTL(x[j] + x[k], n)`. -/
@[inline] def step (x : Vector UInt32 16) (i j k : Fin 16) (n : UInt32) : Vector UInt32 16 :=
  x.set i (x[i] ^^^ rotl (x[j] + x[k]) n)

/-- One pass of the loop body of `xor_salsa8`: the column statements, then the row statements,
in Core's order. -/
def doubleRound (x : Vector UInt32 16) : Vector UInt32 16 :=
  -- Columns.
  let x := step x  4  0 12  7; let x := step x  9  5  1  7
  let x := step x 14 10  6  7; let x := step x  3 15 11  7
  let x := step x  8  4  0  9; let x := step x 13  9  5  9
  let x := step x  2 14 10  9; let x := step x  7  3 15  9
  let x := step x 12  8  4 13; let x := step x  1 13  9 13
  let x := step x  6  2 14 13; let x := step x 11  7  3 13
  let x := step x  0 12  8 18; let x := step x  5  1 13 18
  let x := step x 10  6  2 18; let x := step x 15 11  7 18
  -- Rows.
  let x := step x  1  0  3  7; let x := step x  6  5  4  7
  let x := step x 11 10  9  7; let x := step x 12 15 14  7
  let x := step x  2  1  0  9; let x := step x  7  6  5  9
  let x := step x  8 11 10  9; let x := step x 13 12 15  9
  let x := step x  3  2  1 13; let x := step x  4  7  6 13
  let x := step x  9  8 11 13; let x := step x 14 13 12 13
  let x := step x  0  3  2 18; let x := step x  5  4  7 18
  let x := step x 10  9  8 18
  step x 15 14 13 18

/-- `xor_salsa8(B, Bx)`: `B ^= Bx`, four passes of the loop body on a copy (`i = 0, 2, 4, 6`),
then the copy added to `B` word by word. Returns the new `B`. -/
def xorSalsa8 (b bx : Vector UInt32 16) : Vector UInt32 16 :=
  let b := Vector.zipWith (· ^^^ ·) b bx
  Vector.zipWith (· + ·) b (Nat.repeat doubleRound 4 b)

/-- The state `X[0..31]` as its halves `X[0..15]` and `X[16..31]`. -/
abbrev State := Vector UInt32 16 × Vector UInt32 16

/-- `xor_salsa8(&X[0], &X[16])`, then `xor_salsa8(&X[16], &X[0])`. -/
def blockMix (x : State) : State :=
  let lo := xorSalsa8 x.1 x.2
  (lo, xorSalsa8 x.2 lo)

/-- `le32dec`: four bytes from `off`, least significant first. -/
@[inline] def le32dec (b : ByteArray) (off : Nat) : UInt32 :=
  b[off]!.toUInt32 ||| (b[off + 1]!.toUInt32 <<< 8) |||
    (b[off + 2]!.toUInt32 <<< 16) ||| (b[off + 3]!.toUInt32 <<< 24)

/-- `X[k] = le32dec(&B[4 * k])` for `k = 0 … 31`. -/
def decode (b : ByteArray) : State :=
  (Vector.ofFn fun k => le32dec b (4 * k.val), Vector.ofFn fun k => le32dec b (64 + 4 * k.val))

/-- `le32enc`: the four bytes of `w`, least significant first. -/
@[inline] def le32enc (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- `le32enc(&B[4 * k], X[k])` for `k = 0 … 31`. -/
def encode (x : State) : ByteArray :=
  ⟨((x.1.toList ++ x.2.toList).flatMap le32enc).toArray⟩

/-- The first loop, for `n` more iterations: append the 32 words of `X` to `V`, then apply BlockMix.
Returns `V` and the final `X`. -/
def fill : Nat → State → Array UInt32 → Array UInt32 × State
  | 0, x, v => (v, x)
  | n + 1, x, v => fill n (blockMix x) (v ++ x.1.toArray ++ x.2.toArray)

/-- The second loop, for `n` more iterations: `j = 32 * (X[16] & 1023)`, `X[k] ^= V[j + k]`
for `k = 0 … 31`, then BlockMix.
For a scratchpad of 1024 stored states, every `!` read is in bounds, so its default is never read.
`flat_getElem!_lo` and `flat_getElem!_hi` in `DogeLib.Cryptography.Proofs.Hash.ScryptPow` prove it. -/
def mix (v : Array UInt32) : Nat → State → State
  | 0, x => x
  | n + 1, x =>
    let j := ((32 : UInt32) * (x.2[0] &&& 1023)).toNat
    let lo := Vector.ofFn fun k : Fin 16 => x.1[k] ^^^ v[j + k.val]!
    let hi := Vector.ofFn fun k : Fin 16 => x.2[k] ^^^ v[j + 16 + k.val]!
    mix v n (blockMix (lo, hi))

/-- Both loops of `scrypt_1024_1_1_256_sp_generic`, from the decoded PBKDF2 output. -/
def roMix (x : State) : State :=
  let (v, x) := fill 1024 x (Array.emptyWithCapacity 32768)
  mix v 1024 x

/-- The first `n` bytes of `b`, with zeros past its end. -/
def prefixBytes (b : ByteArray) (n : Nat) : Bytes n :=
  ⟨List.ofFn fun i : Fin n => b[i.val]!, List.length_ofFn⟩

/-- `scrypt_1024_1_1_256_sp_generic`: the scrypt digest of an 80-byte input, in the order that
Core writes it to its output buffer (the internal order of `uint256`).
PBKDF2 never returns `none` for 128 or 32 output bytes, so the empty default of `getD` is never used.
`pbkdf2_some` in `DogeLib.Cryptography.Proofs.Hash.ScryptPow` proves it. -/
def scrypt_1024_1_1_256 (input : Bytes 80) : Hash256 :=
  let pw := input.val.toByteArray
  let b := (Pbkdf2.pbkdf2 pw pw 1 128).getD ByteArray.empty
  let x := roMix (decode b)
  prefixBytes ((Pbkdf2.pbkdf2 pw (encode x) 1 32).getD ByteArray.empty) 32

end DogeLib.Cryptography.Hash.Scrypt
