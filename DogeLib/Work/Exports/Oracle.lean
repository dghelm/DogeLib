module

public import DogeLib.Exports.Json
public import DogeLib.Work.NextWork

/-!
# Work oracle operations

The JSON adapter for compact targets, retarget arithmetic and finite work views.
`docs/oracle.md` defines the requests and the boundary with Core's caller preconditions.
The specification functions follow SOURCES.md D6, D13, D14 and D17.
-/

@[expose] public section

namespace DogeLib.Work.Exports

open Lean (Json)
open DogeLib.Exports

/-- A required JSON boolean, without numeric coercion. -/
def argBool (args : Args) (key : String) : Except Failure Bool := do
  let .bool b ← arg args key | throw (.request s!"argument {key} must be a boolean")
  return b

/-- A network name from the work format. -/
def argNetwork (args : Args) : Except Failure WorkNetwork := do
  match ← arg args "network" with
  | .str "mainnet" => return .mainnet
  | .str "testnet" => return .testnet
  | .str "regtest" => return .regtest
  | _ => throw (.request "network must be mainnet, testnet or regtest")

/-- A 256-bit magnitude in hexadecimal, most significant byte first. -/
def argTarget (args : Args) : Except Failure ArithUint256 := do
  let bs ← argHex args "value_hex"
  unless bs.length = 32 do throw (.request "value_hex must contain exactly 32 bytes")
  return ArithUint256.ofNat (bs.foldl (fun n b => n * 256 + b.toNat) 0)

/-- A fixed-width hexadecimal magnitude, most significant byte first. -/
def targetHex (value : ArithUint256) : String :=
  hexOf ((List.range 32).map fun i => UInt8.ofNat (value.val >>> (8 * (31 - i))))

/-- One block-index entry with no unknown fields. -/
def blockIndexOfJson (j : Json) : Except Failure BlockIndex := do
  let .obj fields := j | throw (.request "chain entries must be objects")
  for (key, _) in fields do
    unless ["height", "time", "bits"].contains key do
      throw (.request s!"unknown chain entry field {key}")
  return ⟨(← argU32 fields "height").toNat, ← argU32 fields "time", ← argU32 fields "bits"⟩

/-- A newest-first finite chain view. -/
def argView (args : Args) : Except Failure (List BlockIndex) := do
  let .arr entries ← arg args "chain" | throw (.request "chain must be an array")
  entries.toList.mapM blockIndexOfJson

/-- The typed errors of the finite-view adapter, separate from consensus rejection. -/
def viewErrorJson (error : NextWorkError) : Json :=
  let reason := match error with
    | .heightOutOfRange => "height_out_of_range"
    | .inconsistentHeights => "inconsistent_heights"
    | .firstHeightUnderflow => "first_height_underflow"
    | .missingAncestor => "missing_ancestor"
    | .zeroInterval => "zero_interval"
  Json.mkObj [("kind", .str "work_view"), ("reason", .str reason)]

/-- `SetCompact`, including the stored magnitude and both flags. -/
def setCompact : Operation where
  name := "work.set_compact"
  args := ["compact"]
  run fields := do
    let result := ArithUint256.setCompact (← argU32 fields "compact")
    return Json.mkObj [("value_hex", .str (targetHex result.value)),
      ("negative", .bool result.fNegative), ("overflow", .bool result.fOverflow)]

/-- `GetCompact` with the caller's explicit sign argument. -/
def getCompact : Operation where
  name := "work.get_compact"
  args := ["value_hex", "negative"]
  run fields := do
    let result := ArithUint256.getCompact (← argTarget fields) (← argBool fields "negative")
    return Json.mkObj [("compact", natJson result.toNat)]

/-- The retarget arithmetic with independently selected network parameters and UInt32 times. -/
def calculateNext : Operation where
  name := "work.calculate_next"
  args := ["network", "selection_height", "last_height", "last_time", "last_bits", "first_time"]
  run fields := do
    let params := getConsensus (← argNetwork fields) (← argU32 fields "selection_height")
    let height ← argInt fields "last_height" 0 2147483646
    let lastTime ← argU32 fields "last_time"
    let bits ← argU32 fields "last_bits"
    let firstTime ← argU32 fields "first_time"
    let result := calculateDogecoinNextWorkRequired params.toRetargetParams
      (Int32.ofInt (height + 1)) (Int64.ofNat lastTime.toNat) (Int64.ofNat firstTime.toNat) bits
    return Json.mkObj [("bits", natJson result.toNat)]

/-- Next-work selection on a finite chain, with the specification's typed view errors. -/
def next : Operation where
  name := "work.next"
  args := ["network", "chain", "candidate_time"]
  run fields := do
    let network ← argNetwork fields
    let view ← argView fields
    let time ← argU32 fields "candidate_time"
    match nextWorkRequired network view time with
    | .ok bits => return Json.mkObj [("bits", natJson bits.toNat)]
    | .error error => throw (.spec (viewErrorJson error))

/-- The four work operations of the oracle. -/
def operations : List Operation := [setCompact, getCompact, calculateNext, next]

end DogeLib.Work.Exports
