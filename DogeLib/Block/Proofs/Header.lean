module

public import DogeLib.Serialization.Proofs.Bytes
public import DogeLib.Transaction.Proofs.Txid
public import DogeLib.Block.Header

/-!
# Pure header codec and digest properties

The codec laws hold for all raw field values, input bytes and suffixes.
They establish exact prefix consumption, without header validity or AuxPoW parsing.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/-- Every pure header round-trips, and every accepted prefix is its exact encoding. -/
instance instLawfulCodecPureBlockHeader : LawfulCodec PureBlockHeader :=
  LawfulCodec.ofEquiv PureBlockHeader.toProd PureBlockHeader.ofProd
    (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- Every raw pure header decodes from its encoding with any suffix preserved. -/
theorem PureBlockHeader.decode_encode (h : PureBlockHeader) (rest : List UInt8) :
    Codec.decode (Codec.encode h ++ rest) = some (h, rest) :=
  LawfulCodec.decode_encode h rest

/-- Every successful pure-header decode consumes exactly the encoding of the returned header. -/
theorem PureBlockHeader.decode_sound (bs rest : List UInt8) (h : PureBlockHeader)
    (hd : Codec.decode bs = some (h, rest)) : bs = Codec.encode h ++ rest :=
  LawfulCodec.decode_canonical bs h rest hd

/-- Every raw pure header encodes to exactly 80 bytes. -/
theorem PureBlockHeader.encode_length (h : PureBlockHeader) : (Codec.encode h).length = 80 := by
  change (Codec.encode h.nVersion ++ (Codec.encode h.hashPrevBlock ++
    (Codec.encode h.hashMerkleRoot ++ (Codec.encode h.nTime ++
    (Codec.encode h.nBits ++ Codec.encode h.nNonce))))).length = 80
  simp only [List.length_append, Bytes.encode_length]
  change 4 + (32 + (32 + (4 + (4 + 4)))) = 80
  rfl

/-- Every pure header's block hash contains exactly the double SHA-256 digest of its encoding. -/
theorem PureBlockHeader.getHash_val (h : PureBlockHeader) :
    h.getHash.val = (Cryptography.Hash.Sha256d.hash (Codec.encode h).toByteArray).toList :=
  Transaction.digestToHash256_val _ (Cryptography.Hash.Sha256d.size_hash _)

end DogeLib.Block
