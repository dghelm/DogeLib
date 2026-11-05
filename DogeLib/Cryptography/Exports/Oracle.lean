module

public import DogeLib.Exports.Json
public import DogeLib.Cryptography.Hash.Hash160
public import DogeLib.Cryptography.Hash.Sha1

/-!
# Hash oracle operations

Each operation hashes the exact bytes of `bytes_hex` and returns digest bytes without reversal.
The specification functions and Core sources appear in SOURCES.md.
`docs/oracle.md` defines the JSON contract.
-/

@[expose] public section
namespace DogeLib.Cryptography.Exports
open Lean (Json)
open DogeLib.Exports

/-- Adapt a whole-byte hash to a request with `bytes_hex` and a `digest_hex` result. -/
def hashOperation (name : String) (hash : ByteArray → ByteArray) : Operation where
  name := name
  args := ["bytes_hex"]
  run fields := do
    let digest := hash (← argHex fields "bytes_hex").toByteArray
    return Json.mkObj [("digest_hex", .str (hexOf digest.data.toList))]

/-- The hash operations of the oracle, with twenty-byte digests in output order. -/
def operations : List Operation :=
  [hashOperation "hash.ripemd160" Hash.Ripemd160.hash,
   hashOperation "hash.hash160" Hash.Hash160.hash,
   hashOperation "hash.sha1" Hash.Sha1.hash]

end DogeLib.Cryptography.Exports
