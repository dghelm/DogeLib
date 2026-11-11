module

public import DogeLib.Cryptography.Hash.Hmac

/-!
# PBKDF2-HMAC-SHA-256

The construction follows RFC 8018 §5.2, with HMAC-SHA-256 as the PRF.
The password and salt are arbitrary byte arrays.
The counts are natural numbers, and output lengths above `(2^32 - 1) * 32` return `none`.
Zero iterations computes `U₁`, and zero output bytes returns an empty array.
These extensions follow the pinned VG model, whereas RFC 8018 requires positive counts and output lengths.

This executable uses whole-message HMAC, without cached hash states.
It makes no constant-time or resource-bound claim.
`pbkdf2_eq_spec` relates it to the list model with executable SHA-256.
`pbkdf2_eq_fips` uses the FIPS 180-4 model under explicit password and salt bounds.

The definitions transcribe pyca/verified-garbage `lean/VerifiedGarbage/Spec/Pbkdf2.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e` over `ByteArray`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation specializes the PRF to HMAC-SHA-256, uses `Nat.fold` for output blocks,
and replaces the list prefix with a byte-array extraction.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Pbkdf2

/-- Four bytes of the block index, most significant byte first, modulo 2^32. -/
def int (i : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (i / 2 ^ 24), UInt8.ofNat (i / 2 ^ 16),
    UInt8.ofNat (i / 2 ^ 8), UInt8.ofNat i]⟩

/-- Bytewise XOR, truncated to the shorter input when their sizes differ. -/
def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨Array.zipWith (· ^^^ ·) a.data b.data⟩

/-- Apply `n` further HMAC steps to `u`, and XOR each result into `t`. -/
def iterate (password : ByteArray) : Nat → ByteArray → ByteArray → ByteArray
  | 0, _, t => t
  | n + 1, u, t =>
    let u' := Hmac.hmac password u
    iterate password n u' (xorBytes t u')

/-- Output block `Tᵢ`: XOR the first `c` HMAC iterates, or return `U₁` when `c = 0`. -/
def block (password salt : ByteArray) (c i : Nat) : ByteArray :=
  let u := Hmac.hmac password (salt ++ int i)
  iterate password (c - 1) u u

/-- Concatenate the first `n` output blocks, in increasing block-index order. -/
def blocks (password salt : ByteArray) (c n : Nat) : ByteArray :=
  n.fold (fun i _ out => out ++ block password salt c (i + 1)) ByteArray.empty

/--
Derive `dkLen` bytes with PBKDF2-HMAC-SHA-256, or return `none` above `(2^32 - 1) * 32` bytes.
Zero iterations uses `U₁`, and zero output bytes returns `some` of an empty array.
RFC 8018 §5.2 requires `c ≥ 1` and `dkLen ≥ 1`.

Core's `PBKDF2_SHA256` holds `c` and its loop counter `j` in `uint64_t`, with the loop test `j <= c` (D61, lines 71, 80 and 100).
At `c = 2^64 - 1` with `dkLen > 0` the counter wraps and that loop does not end, and a larger `c` has no Core counterpart.
With `dkLen = 0` Core's outer loop at line 88 runs no iteration.
This definition returns a result for every `c`, so a correspondence with Core can cover only `c < 2^64 - 1` or `dkLen = 0`.
Core's scrypt digest calls it with `c = 1`.
-/
def pbkdf2 (password salt : ByteArray) (c dkLen : Nat) : Option ByteArray :=
  if (2 ^ 32 - 1) * 32 < dkLen then none
  else some ((blocks password salt c ((dkLen + 32 - 1) / 32)).extract 0 dkLen)

end DogeLib.Cryptography.Hash.Pbkdf2
