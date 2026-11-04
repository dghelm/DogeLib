module

public import DogeLib.Work.ArithUint256Words

/-!
# Byte conversion for arithmetic targets

The grouped reads model `UintToArith256` in Dogecoin Core `e0a1c15`,
`src/arith_uint256.cpp` lines 254-260 (SOURCES.md, D13).
`ReadLE32` interprets four bytes in little-endian order (SOURCES.md, D37, `src/crypto/common.h` lines 24-29).
Core's `uint256S` (D22 lines 151-156) calls `base_blob::SetHex` (D11 lines 30-56).
The hex parser restricts this call to an `0x` prefix and exactly 64 hexadecimal digits.
It rejects other inputs instead of modeling Core's whitespace, prefix and truncation cases.

The adapted code is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notices:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work.ArithUint256

/-- A `uint256`'s 32 bytes, indexed in Core's internal little-endian order (D22). -/
abbrev TargetBytes := Fin 32 → UInt8

/-- The independent radix-256 interpretation of any fixed byte count. -/
def evalBytes : (n : Nat) → (Fin n → UInt8) → Nat
  | 0, _ => 0
  | n + 1, bs => (bs 0).toNat + 256 * evalBytes n (fun i => bs i.succ)

/-- Interpret all 32 bytes as an arithmetic target, modulo 2^256. -/
def ofTargetBytes (bs : TargetBytes) : ArithUint256 := ofNat (evalBytes 32 bs)

namespace Words

/-- One `ReadLE32` group of `UintToArith256` (D13 lines 257-258).
The byte weights state the portable meaning of Core's `memcpy` and `le32toh`. -/
def readLE32 (bs : TargetBytes) (i : Fin 8) : UInt32 :=
  UInt32.ofNat ((bs ⟨4 * i.val, by omega⟩).toNat +
    256 * (bs ⟨4 * i.val + 1, by omega⟩).toNat +
    65536 * (bs ⟨4 * i.val + 2, by omega⟩).toNat +
    16777216 * (bs ⟨4 * i.val + 3, by omega⟩).toNat)

/-- Core's eight ascending `ReadLE32` assignments (D13 lines 254-260). -/
def uintToArith256 (bs : TargetBytes) : Words := fun i => readLE32 bs i

end Words

/-- Core's hexadecimal digit interpretation, restricted to ASCII hexadecimal characters (D38 lines 37-58). -/
def targetHexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

/-- Core's backwards nibble scan for exactly 64 digits after `0x` (D11 lines 30-56).
All other formats return `none`.
The last digit supplies the low nibble of byte zero. -/
def targetBytesOfHex (hex : String) : Option TargetBytes := do
  let chars := hex.toList
  if chars.take 2 != ['0', 'x'] || chars.length != 66 then none else do
    let digits ← (chars.drop 2).mapM targetHexDigit
    let reversed := digits.reverse.toArray
    if h : reversed.size = 64 then
      return fun i => reversed[2 * i.val]'(by omega) |||
        (reversed[2 * i.val + 1]'(by omega) <<< 4)
    else none

/-- Core's mainnet and testnet powLimit literal (D14 lines 88 and 248). -/
def mainnetPowLimitHex : String :=
  "0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-- Core's regtest powLimit literal (D14 line 392). -/
def regtestPowLimitHex : String :=
  "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

end DogeLib.Work.ArithUint256
