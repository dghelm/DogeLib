module

public import DogeLib.Proposals.Exports

/-!
The entry point of `dogelib-proposal-oracle`: `DogeLib.Proposals.Exports.run`.

The file is outside the `ProposalExports` library.
`DogeLib.Exports.Main` declares `main` for `dogelib-oracle`, and `lake exe check-decls` loads both export libraries in one environment, where two declarations of `main` cannot coexist.
Every other definition of the executable is in `DogeLib.Proposals.Exports.Validate`, which the declaration check reads.
-/

public section

/-- Answer each line of standard input, or print the version object with `--version`. -/
def main (argv : List String) : IO UInt32 := DogeLib.Proposals.Exports.run argv
