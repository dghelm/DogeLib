module

public import DogeLib.Serialization.Bytes
public import DogeLib.Transaction.Txid

/-!
# Pure block headers

The fields and prefix codec follow `CPureBlockHeader::SerializationOp` (SOURCES.md, D10).
`getHash` follows `CPureBlockHeader::GetHash` in `src/primitives/pureheader.cpp` at the same Core pin.
The version retains all bits of Core's signed int32 field.
The hash is double SHA-256, not the scrypt proof-of-work hash.
A Core `CBlockHeader` with bit 8 set appends AuxPoW data after these 80 bytes.
This module models only the pure header, including when that bit is set.

The adaptation retains raw fields and hashing, with a total prefix codec in place of Core's stream methods.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/primitives/pureheader.h`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2013 The Bitcoin developers
Distributed under the MIT/X11 software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/-- The six raw fields of Core's `CPureBlockHeader`, without contextual validation (D10). -/
structure PureBlockHeader where
  /-- The bits of Core's signed `nVersion`. -/
  nVersion : UInt32
  /-- The previous block hash in internal byte order. -/
  hashPrevBlock : Hash256
  /-- The transaction Merkle root in internal byte order. -/
  hashMerkleRoot : Hash256
  /-- The unsigned timestamp field. -/
  nTime : UInt32
  /-- The compact target field, without a range check. -/
  nBits : UInt32
  /-- The nonce field. -/
  nNonce : UInt32
  deriving DecidableEq

/-- The pure header fields in serialization order (D10). -/
def PureBlockHeader.toProd (h : PureBlockHeader) :
    UInt32 × Hash256 × Hash256 × UInt32 × UInt32 × UInt32 :=
  (h.nVersion, h.hashPrevBlock, h.hashMerkleRoot, h.nTime, h.nBits, h.nNonce)

/-- The pure header with the supplied fields in serialization order. -/
def PureBlockHeader.ofProd (p : UInt32 × Hash256 × Hash256 × UInt32 × UInt32 × UInt32) :
    PureBlockHeader := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩

/-- The 80-byte pure header codec, with a prefix decoder that returns `none` on truncation. -/
instance instCodecPureBlockHeader : Codec PureBlockHeader :=
  Codec.ofEquiv PureBlockHeader.toProd PureBlockHeader.ofProd inferInstance

/-- The signed interpretation of Core's version bits. -/
def PureBlockHeader.signedVersion (h : PureBlockHeader) : Int32 := h.nVersion.toInt32

/-- Core's `IsAuxpow` flag test (D10), without parsing or validating an AuxPoW payload. -/
def PureBlockHeader.isAuxpow (h : PureBlockHeader) : Bool := h.nVersion &&& 0x100 != 0

/-- Core's block hash: double SHA-256 of the pure header bytes, in internal digest order. -/
def PureBlockHeader.getHash (h : PureBlockHeader) : Hash256 :=
  Transaction.digestToHash256 (Cryptography.Hash.Sha256d.hash (Codec.encode h).toByteArray)

end DogeLib.Block
