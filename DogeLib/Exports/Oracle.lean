module

public import DogeLib.Serialization.Exports.Oracle
public import DogeLib.Transaction.Exports.Oracle

/-!
# `Exports.Oracle`

The oracle's response to one line of input, in the record format `dogelib-oracle/2` of `docs/oracle.md`.

A line is one JSON object, the request: `{"id": ..., "op": "...", ...arguments}`.
The response is `{"id": ..., "ok": {...}}` or `{"id": ..., "error": {...}}`.
`id` is the request's `id`, or `null` when the line has none or is not a JSON object.
An error of kind `request` means the oracle could not interpret the request. Any other kind is an error of the specification.
A blank line has no response.
-/

@[expose] public section

namespace DogeLib.Exports

open Lean (Json)

/-- The name of the record format. -/
def formatName : String := "dogelib-oracle/2"

/-- The `ok` object of `oracle.version`. -/
def versionJson : Json := Json.mkObj [("format", .str formatName)]

/-- `oracle.version`: the name of the record format. -/
def oracleVersion : Operation where
  name := "oracle.version"
  args := []
  run _ := return versionJson

/-- Every operation of the oracle. -/
def operations : List Operation :=
  oracleVersion :: Serialization.Exports.operations ++ Transaction.Exports.operations

/-- The `error` object of a failure. -/
def failureJson : Failure → Json
  | .request m => Json.mkObj [("kind", "request"), ("message", .str m)]
  | .spec e => e

/-- The `ok` object for the fields of a request object, or the failure. -/
def runRequest (fields : Args) : Except Failure Json := do
  let .str name ← arg fields "op" | throw (.request "argument op must be a string")
  let some op := operations.find? (·.name == name) | throw (.request s!"unknown operation {name}")
  for (key, _) in fields do
    unless key == "id" || key == "op" || op.args.contains key do
      throw (.request s!"unknown argument {key} for operation {name}")
  op.run fields

/-- The response to one line of input, or `none` for a blank line. -/
def respond (line : String) : Option Json :=
  let line := line.trimAscii.copy
  if line.isEmpty then none
  else
    let (id, result) : Json × Except Failure Json := match Json.parse line with
      | .error e => (.null, .error (.request s!"invalid JSON: {e}"))
      | .ok (.obj fields) => ((fields.get? "id").getD .null, runRequest fields)
      | .ok _ => (.null, .error (.request "the request must be a JSON object"))
    some <| match result with
      | .ok j => Json.mkObj [("id", id), ("ok", j)]
      | .error f => Json.mkObj [("id", id), ("error", failureJson f)]

end DogeLib.Exports
