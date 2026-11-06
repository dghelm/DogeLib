module

/-!
# `ArithUint256`

The 256-bit unsigned integers of Dogecoin Core's `arith_uint256`, as far as the difficulty retarget uses them, and the compact encoding of a target.

The source is `src/arith_uint256.h` and `src/arith_uint256.cpp` at Dogecoin Core `e0a1c15` (SOURCES.md, D12 and D13).
Core stores a value as eight 32-bit words and computes each operation word by word.
This module states the arithmetic result of each operation on the value that the words represent, modulo 2^256:

```text
operator*=(uint32_t)   arith_uint256.cpp 55-65    a * b mod 2^256, the last carry is lost
operator/=             arith_uint256.cpp 83-107   floor(a / b), Core throws when b = 0
operator<<=            arith_uint256.cpp 21-36    a * 2^n mod 2^256
operator>>=            arith_uint256.cpp 38-53    floor(a / 2^n)
bits()                 arith_uint256.cpp 171-184  position of the highest set bit plus one
GetLow64()             arith_uint256.h 245-249    a mod 2^64
SetCompact             arith_uint256.cpp 204-222  compact encoding to value, sign and overflow flags
GetCompact             arith_uint256.cpp 224-245  value to compact encoding
```

`DogeLib.Work.ArithUint256Words` models multiplication, both shifts, `bits()` and `GetLow64()` over eight words.
`DogeLib.Work.Proofs.ArithUint256Words` proves that these models agree with the arithmetic results on every input.
The correspondence between Core's source and each Lean model is checked by review.

`DogeLib.Work.ArithUint256Division` models word division, comparison, addition, negation and subtraction.
`DogeLib.Work.Proofs.ArithUint256Division` proves arithmetic equivalence for every word input, with a nonzero divisor for successful division.
The division model also represents Core's zero-divisor exception.
Core's own tests of the compact encoding run through these definitions in `tests/KnownAnswers/Work.lean`.

The compact encoding packs a number into 32 bits, like a floating-point number in base 256:

```text
bits 31..24   nSize, the length of the number in bytes
bit  23       the sign bit, 0x00800000
bits 22..0    the mantissa, the top bytes of the number
value         mantissa * 256^(nSize - 3), negated if the sign bit is set
```

`SetCompact` computes the value modulo 2^256 and reports the sign and an overflow as separate flags.
`GetCompact` never sets the sign bit for a number unless its caller asks for a negative encoding.
-/

@[expose] public section

namespace DogeLib.Work

/-- A value of Core's `arith_uint256`: a number below 2^256. -/
abbrev ArithUint256 := Fin (2 ^ 256)

namespace ArithUint256

/-- The number `n` modulo 2^256.
Core keeps a result modulo 2^256 when it does not fit in eight 32-bit words. -/
def ofNat (n : Nat) : ArithUint256 := ⟨n % 2 ^ 256, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩

/-- `a *= b` for a 32-bit `b`, `operator*=(uint32_t)` (arith_uint256.cpp lines 55-65).
Core multiplies word by word and drops the carry from the top word, so the result is `a * b` modulo 2^256. -/
def mulUInt32 (a : ArithUint256) (b : UInt32) : ArithUint256 := ofNat (a.val * b.toNat)

/-- `a /= b`, `operator/=` (arith_uint256.cpp lines 83-107).
Core's long division computes the quotient `a / b` rounded down.
Core throws `uint_error` when `b` is zero (line 92), so this definition takes a proof that it is not. -/
def div (a b : ArithUint256) (_nonzero : b.val ≠ 0) : ArithUint256 :=
  ⟨a.val / b.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩

/-- `a <<= shift`, `operator<<=` (arith_uint256.cpp lines 21-36).
Bits shifted above bit 255 are lost, so the result is `a * 2^shift` modulo 2^256. -/
def shiftLeft (a : ArithUint256) (shift : Nat) : ArithUint256 := ofNat (a.val <<< shift)

/-- `a >>= shift`, `operator>>=` (arith_uint256.cpp lines 38-53): `a / 2^shift` rounded down. -/
def shiftRight (a : ArithUint256) (shift : Nat) : ArithUint256 :=
  ⟨a.val >>> shift, by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩

/-- `bits()` (arith_uint256.cpp lines 171-184): the position of the highest set bit plus one, or zero for zero. -/
def bits (a : ArithUint256) : Nat := if a.val = 0 then 0 else a.val.log2 + 1

/-- `GetLow64()` (arith_uint256.h lines 245-249): the low 64 bits, that is, `a` modulo 2^64. -/
def getLow64 (a : ArithUint256) : Nat := a.val % 2 ^ 64

/-! ## Compact encoding -/

/-- What `SetCompact` returns: the value it stores, and the two flags it writes through its pointer arguments. -/
structure SetCompactResult where
  /-- The value that `SetCompact` stores, modulo 2^256. -/
  value : ArithUint256
  /-- `*pfNegative`: the mantissa that remains is not zero, and the sign bit is set. -/
  fNegative : Bool
  /-- `*pfOverflow`: the mantissa that remains is not zero, and the encoded number is at least 2^256. -/
  fOverflow : Bool
  deriving DecidableEq, Repr

/--
`SetCompact(nCompact, pfNegative, pfOverflow)` (arith_uint256.cpp lines 204-222).

`nSize` is the top byte, and `nWord` is the low 23 bits.
When `nSize` is 3 or less, the value is `nWord` shifted right by `3 - nSize` bytes.
Otherwise it is `nWord` shifted left by `nSize - 3` bytes, modulo 2^256.

Both flags read `nWord` after the right shift.
So for `nSize` of 3 or less, a sign bit with no remaining mantissa bits does not set `fNegative`.
The value ignores the sign bit, and a caller that needs the sign reads `fNegative`.
-/
def setCompact (nCompact : UInt32) : SetCompactResult :=
  let nSize := nCompact.toNat >>> 24
  let nWord := nCompact.toNat &&& 0x007fffff
  let nWord := if nSize ≤ 3 then nWord >>> (8 * (3 - nSize)) else nWord
  let value := if nSize ≤ 3 then ofNat nWord else shiftLeft (ofNat nWord) (8 * (nSize - 3))
  { value
    fNegative := nWord != 0 && (nCompact.toNat &&& 0x00800000) != 0
    fOverflow := nWord != 0 &&
      (decide (nSize > 34) || (decide (nWord > 0xff) && decide (nSize > 33)) ||
        (decide (nWord > 0xffff) && decide (nSize > 32))) }

/--
`GetCompact(fNegative)` (arith_uint256.cpp lines 224-245).

`nSize` is the length of `a` in bytes, and the mantissa is its top three bytes.
For `nSize` of 3 or less, Core shifts the 64-bit `GetLow64()` left and truncates it to 32 bits.
Both the 64-bit wrap and the truncation appear below, although the value never exceeds 24 bits.

The mantissa must not have the sign bit set.
If it does, `GetCompact` drops the low byte of the mantissa and adds one to `nSize`.
Core then asserts that the mantissa fits in 23 bits and that `nSize` is below 256 (lines 240 and 241).
`getCompact_assertions` in `DogeLib.Work.Proofs.ArithUint256` proves that both hold for every value.

The sign bit is set only when `fNegative` is true and the mantissa is not zero.
The difficulty retarget calls `GetCompact()` with the default, `fNegative = false`.
-/
def getCompact (a : ArithUint256) (fNegative : Bool := false) : UInt32 :=
  let nSize := (bits a + 7) / 8
  let nCompact :=
    if nSize ≤ 3 then (getLow64 a <<< (8 * (3 - nSize))) % 2 ^ 64 % 2 ^ 32
    else getLow64 (shiftRight a (8 * (nSize - 3))) % 2 ^ 32
  let (nCompact, nSize) :=
    if nCompact &&& 0x00800000 != 0 then (nCompact >>> 8, nSize + 1) else (nCompact, nSize)
  let nCompact := nCompact ||| (nSize <<< 24)
  let nCompact := nCompact ||| (if fNegative && (nCompact &&& 0x007fffff) != 0 then 0x00800000 else 0)
  UInt32.ofNat nCompact

end ArithUint256

end DogeLib.Work
