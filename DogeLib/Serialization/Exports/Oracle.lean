module

public import DogeLib.Exports.Json
public import DogeLib.Serialization.CompactSize

/-!
# `Serialization.Exports.Oracle`

The CompactSize operations of the oracle. `docs/oracle.md` defines their arguments and results.

- `compactsize.encode` runs `CompactSize.encode`, Core's `WriteCompactSize`.
- `compactsize.read` runs `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check.
-/

@[expose] public section

namespace DogeLib.Serialization.Exports

open Lean (Json)
open DogeLib.Exports

/-- The `error` object of a CompactSize read error. -/
def readErrorJson : CompactSize.ReadError → Json
  | .truncated => Json.mkObj [("kind", "read"), ("reason", "truncated")]
  | .nonCanonical => Json.mkObj [("kind", "read"), ("reason", "non_canonical")]
  | .tooLarge => Json.mkObj [("kind", "read"), ("reason", "too_large")]

/-- `compactsize.encode`: the encoding of `value`. -/
def compactSizeEncode : Operation where
  name := "compactsize.encode"
  args := ["value"]
  run args := do
    let n ← argU64 args "value"
    return Json.mkObj [("bytes_hex", .str (hexOf (CompactSize.encode n)))]

/-- `compactsize.read`: the value at the start of `bytes_hex`, the count of bytes read, and the remainder. -/
def compactSizeRead : Operation where
  name := "compactsize.read"
  args := ["bytes_hex"]
  run args := do
    let bs ← argHex args "bytes_hex"
    match CompactSize.decodeBounded bs with
    | .error e => throw (.spec (readErrorJson e))
    | .ok (n, rest) =>
      return Json.mkObj [("value", u64Json n), ("consumed", natJson (bs.length - rest.length)),
        ("rest_hex", .str (hexOf rest))]

/-- The operations of this layer. -/
def operations : List Operation := [compactSizeEncode, compactSizeRead]

end DogeLib.Serialization.Exports
