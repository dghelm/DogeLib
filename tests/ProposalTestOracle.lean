module

public import ProposalExamples.Exports

/-!
The entry point of the test executable `proposal-test-oracle`: `ProposalExamples.Exports.runTest`.
It answers the requests of `dogelib-proposal-oracle`, and its argument `revision` also names the two examples of the framework.
-/

public section

/-- Answer each line of standard input, or print the version object with `--version`. -/
def main (argv : List String) : IO UInt32 := ProposalExamples.Exports.runTest argv
