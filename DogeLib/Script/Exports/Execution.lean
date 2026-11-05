module

public import DogeLib.Script

/-! A pure execution boundary for the decoding and state stage. -/

@[expose] public section

namespace DogeLib.Script.Exports

/-- Report the missing execution capability for every script and initial state.
The result carries no acceptance or rejection verdict. -/
def execute (_script : List UInt8) (_state : ExecutionState) : UnsupportedFeature :=
  .execution

end DogeLib.Script.Exports
