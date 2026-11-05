module

public import DogeLib.Exports.Json
public import DogeLib.Block.Header
public import DogeLib.Block.Merkle

/-!
# Block oracle operations

The adapter exposes the pure header codec, block hash and transaction Merkle computation.
SOURCES.md D10, D40 and D42 name the pinned Core functions.
`docs/oracle.md` defines the JSON contract and the Merkle leaf bound.
These operations check no header or block validity rule.
-/

@[expose] public section
namespace DogeLib.Block.Exports
open Lean (Json)
open DogeLib.Exports
open DogeLib.Serialization

/-- Argument `key` as exactly 32 bytes in internal hash order. -/
def argHash (args : Args) (key : String) : Except Failure Hash256 := do
  let bs ← argHex args key
  if h : bs.length = 32 then return ⟨bs, h⟩
  else throw (.request s!"argument {key} must contain exactly 32 bytes")

/-- The six raw fields of a header, with unknown nested fields rejected. -/
def argHeader (args : Args) : Except Failure PureBlockHeader := do
  let .obj fields ← arg args "header" | throw (.request "header must be an object")
  for (key, _) in fields do
    unless ["version", "prev_block_hex", "merkle_root_hex", "time", "bits", "nonce"].contains key do
      throw (.request s!"unknown header field {key}")
  return ⟨← argU32 fields "version", ← argHash fields "prev_block_hex",
    ← argHash fields "merkle_root_hex", ← argU32 fields "time", ← argU32 fields "bits",
    ← argU32 fields "nonce"⟩

/-- Every raw header field, with both hash byte orders and unsigned version bits. -/
def headerJson (h : PureBlockHeader) : Json :=
  Json.mkObj ([("version", natJson h.nVersion.toNat), ("time", natJson h.nTime.toNat),
    ("bits", natJson h.nBits.toNat), ("nonce", natJson h.nNonce.toNat)] ++
    hashFields "prev_block" h.hashPrevBlock ++ hashFields "merkle_root" h.hashMerkleRoot)

/-- Read an 80-byte pure header prefix and preserve all bytes after it. -/
def readHeader : Operation where
  name := "header.read"
  args := ["bytes_hex"]
  run fields := do
    let bs ← argHex fields "bytes_hex"
    match Codec.decode (α := PureBlockHeader) bs with
    | none => throw (.spec (Json.mkObj [("kind", "read"), ("reason", "truncated")]))
    | some (h, rest) => return Json.mkObj [("header", headerJson h),
        ("consumed", natJson (bs.length - rest.length)), ("rest_hex", .str (hexOf rest))]

/-- Serialize the supplied raw fields as exactly 80 pure header bytes. -/
def encodeHeader : Operation where
  name := "header.encode"
  args := ["header"]
  run fields := do
    return Json.mkObj [("bytes_hex", .str (hexOf (Codec.encode (← argHeader fields))))]

/-- Double SHA-256 of the supplied pure header fields, in both byte orders. -/
def hashHeader : Operation where
  name := "header.hash"
  args := ["header"]
  run fields := do
    return Json.mkObj (hashFields "hash" (← argHeader fields).getHash)

/-- Compute a Merkle root and mutation flag for at most 2^31 internal-order leaves. -/
def computeMerkle : Operation where
  name := "merkle.compute"
  args := ["leaves_hex"]
  run fields := do
    let .arr entries ← arg fields "leaves_hex" | throw (.request "leaves_hex must be an array")
    unless entries.size ≤ 2 ^ 31 do throw (.request "leaves_hex must have at most 2^31 entries")
    let leaves ← entries.toList.zipIdx.mapM fun (entry, index) => do
      let key := s!"leaves_hex[{index}]"
      argHash (Std.TreeMap.Raw.ofList [(key, entry)]) key
    let result := computeMerkleRoot leaves
    return Json.mkObj (hashFields "root" result.root ++ [("mutated", .bool result.mutated)])

/-- The pure header and Merkle operations of the oracle. -/
def operations : List Operation := [readHeader, encodeHeader, hashHeader, computeMerkle]

end DogeLib.Block.Exports
