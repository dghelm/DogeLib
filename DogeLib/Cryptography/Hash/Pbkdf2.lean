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
The proof `pbkdf2_eq_spec` relates it to the separate list model.
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
-/
def pbkdf2 (password salt : ByteArray) (c dkLen : Nat) : Option ByteArray :=
  if (2 ^ 32 - 1) * 32 < dkLen then none
  else some ((blocks password salt c ((dkLen + 32 - 1) / 32)).extract 0 dkLen)

end DogeLib.Cryptography.Hash.Pbkdf2
