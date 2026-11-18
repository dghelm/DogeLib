module

public import DogeLib.Serialization.Exports.Oracle
public import DogeLib.Transaction.Exports.Oracle
public import DogeLib.Work.Exports.Oracle
public import DogeLib.Block.Exports.Oracle
public import DogeLib.Block.Exports.Validate
public import DogeLib.Cryptography.Exports.Oracle
public import DogeLib.Script.Exports.Oracle

/-!
# `Exports.Oracle`

The oracle's response to one line of input, in the record format `dogelib-oracle/1` of `docs/oracle.md`.

A line is one JSON object, the request: `{"id": ..., "op": "...", ...arguments}`.
The response is `{"id": ..., "ok": {...}}` or `{"id": ..., "error": {...}}`.
`id` is the request's `id`, or `null` when the line has none or is not a JSON object.
An error of kind `request` means the oracle could not interpret the request. Other kinds report specification errors or adapter resource limits.
A blank line has no response.
-/

@[expose] public section

namespace DogeLib.Exports

open Lean (Json)

/-- The name of the record format. -/
def formatName : String := "dogelib-oracle/1"

/-- The `ok` object of `oracle.version`. -/
def versionJson : Json := Json.mkObj [("format", .str formatName)]

/-- `oracle.version`: the name of the record format. -/
def oracleVersion : Operation where
  name := "oracle.version"
  args := []
  run _ := return versionJson

/-- Every operation of the oracle. -/
def operations : List Operation :=
  oracleVersion :: Serialization.Exports.operations ++ Transaction.Exports.operations ++ Work.Exports.operations ++
    Block.Exports.operations ++ [Block.Exports.blockValidate] ++ Cryptography.Exports.operations ++ Script.Exports.operations

/-- The `error` object of a failure. -/
def failureJson : Failure → Json
  | .request m => Json.mkObj [("kind", "request"), ("message", .str m)]
  | .spec e => e

/-- The `ok` object for the fields of a request object, or the failure. -/
def runRequestWith (ops : List Operation) (fields : Args) : Except Failure Json := do
  let .str name ← arg fields "op" | throw (.request "argument op must be a string")
  let some op := ops.find? (·.name == name) | throw (.request s!"unknown operation {name}")
  for (key, _) in fields do
    unless key == "id" || key == "op" || op.args.contains key do
      throw (.request s!"unknown argument {key} for operation {name}")
  op.run fields

/-- The response to one line of input, or `none` for a blank line, where `run` answers the fields of a request object. -/
def respondM {m : Type → Type} [Monad m] (run : Args → m (Except Failure Json)) (line : String) : m (Option Json) := do
  let line := line.trimAscii.copy
  if line.isEmpty then return none
  let (id, result) : Json × Except Failure Json ← match Json.parse line with
    | .error e => pure (.null, .error (.request s!"invalid JSON: {e}"))
    | .ok (.obj fields) => do pure ((fields.get? "id").getD .null, ← run fields)
    | .ok _ => pure (.null, .error (.request "the request must be a JSON object"))
  return some <| match result with
    | .ok j => Json.mkObj [("id", id), ("ok", j)]
    | .error f => Json.mkObj [("id", id), ("error", failureJson f)]

/-- The response to one line of input, or `none` for a blank line. -/
def respondWith (ops : List Operation) (line : String) : Option Json :=
  Id.run (respondM (fun fields => pure (runRequestWith ops fields)) line)

/-- Run a request with the baseline oracle operations. -/
def runRequest (fields : Args) : Except Failure Json := runRequestWith operations fields

/-- Answer a line with the baseline oracle operations. -/
def respond (line : String) : Option Json := respondWith operations line

/--
Run a request in `IO`.
A `block.validate` request with the argument `blocks_file` reads that file through `Block.Exports.blockValidateFile`.
Every other request has the result of `runRequest`.
-/
def runRequestIO (fields : Args) : IO (Except Failure Json) :=
  if fields.get? "op" == some (.str Block.Exports.blockValidate.name) && fields.contains "blocks_file" then
    Block.Exports.blockValidateFile fields
  else
    pure (runRequest fields)

/-- Answer a line in `IO`, with `runRequestIO`. This is the response of the `dogelib-oracle` executable. -/
def respondIO (line : String) : IO (Option Json) := respondM runRequestIO line

end DogeLib.Exports
