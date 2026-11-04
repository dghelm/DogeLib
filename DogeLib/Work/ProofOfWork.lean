module

public import DogeLib.Base.Bytes
public import DogeLib.Work.ArithUint256Bytes
public import DogeLib.Work.Retarget

/-!
# Supplied-hash proof of work

`CheckProofOfWork` in Dogecoin Core `e0a1c15`, `src/pow.cpp` lines 117-135 (SOURCES.md, D17), checks a compact target and a supplied hash.
It does not compute scrypt or validate a header.
Only `powLimit` is read from the parameter record.
Hash bytes retain Core's internal order, with byte zero least significant for `UintToArith256` (D13 lines 254-260).

The adapted check is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notices from `src/pow.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work

/-- Interpret a supplied hash through Core's eight little-endian `UintToArith256` reads (D13).
No digest computation occurs here. -/
def hashToArith256 (hash : Hash256) : ArithUint256 :=
  ArithUint256.Words.toArith (ArithUint256.Words.uintToArith256
    (fun i => hash.val[i.val]'(by have := hash.property; omega)))

/-- The target range check of D17 lines 124-128, for every compact encoding.
Negative, zero, overflowing and above-limit targets fail.
Noncanonical encodings can pass. -/
def validProofOfWorkTarget (nBits : UInt32) (params : RetargetParams) : Bool :=
  let target := ArithUint256.setCompact nBits
  if target.fNegative || target.value == 0 || target.fOverflow || target.value > params.powLimit then
    false
  else true

/-- Core's `CheckProofOfWork` (D17 lines 117-135) for an arbitrary supplied hash and compact target.
It accepts exactly a target within range and a hash at most that target.
The caller supplies the digest and selects the network parameters. -/
def checkProofOfWork (hash : Hash256) (nBits : UInt32) (params : RetargetParams) : Bool :=
  if !validProofOfWorkTarget nBits params then false
  else if hashToArith256 hash > (ArithUint256.setCompact nBits).value then false
  else true

end DogeLib.Work
