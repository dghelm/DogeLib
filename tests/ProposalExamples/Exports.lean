module

public import DogeLib.Proposals.Exports
public import ProposalExamples

/-!
# `ProposalExamples.Exports`

The revisions of the test executable `proposal-test-oracle`: the revisions of `dogelib-proposal-oracle`, and the two examples of the framework.
Neither example is a proposal for Dogecoin, so the shipped executable does not name them.
The tests of the proposal executable and of the impact tools use it, and so do the short-range impact runs.
They run a planted fault and a known soft fork through the code of the shipped executable.

`ExampleFaultyLocktime` has the variants `corrected` and `faulty`. `ExampleVersionVerify` has no variant.
Every other part of the executable is `DogeLib.Proposals.Exports.runWith`, the code of `dogelib-proposal-oracle`.
-/

@[expose] public section

namespace ProposalExamples.Exports

open DogeLib.Exports DogeLib.Block DogeLib.Script DogeLib.Proposals.Framework DogeLib.Proposals.Exports

/-- The text of a script error of `ExampleVersionVerify`: Core's text for a baseline error, and a name for an error of the example. -/
def describeExampleError : ExampleVersionVerify.ExampleScriptError → String
  | .inl e => e.description
  | .inr .negativeOperand => "ExampleVersionVerify: negative operand"
  | .inr .versionTooLow => "ExampleVersionVerify: version too low"

/-- The text of an unsupported script reason of `ExampleVersionVerify`. -/
def describeExampleUnsupported : ExampleVersionVerify.ExampleScriptUnsupported → String
  | .inl u => reprStr u
  | .inr .missingContext => "ExampleVersionVerify: missing context"

/-- `ExampleFaultyLocktime` with a variant, as a revision of the executable. -/
def faultyLocktimeRevision (v : ExampleFaultyLocktime.Variant) :
    BlockRevision ScriptError Unsupported Fields Fields :=
  ExampleFaultyLocktime.blockRevision v coreVerifier

/-- `ExampleVersionVerify` as a revision of the executable. -/
def versionVerifyRevision :
    BlockRevision ExampleVersionVerify.ExampleScriptError ExampleVersionVerify.ExampleScriptUnsupported Fields Fields :=
  ExampleVersionVerify.blockRevision coreVerifier

/-- The two examples as revisions that a request can name, with `coreVerifier`. -/
def exampleRevisions : List NamedRevision :=
  [⟨"ExampleFaultyLocktime", some "corrected",
      revisedHook (faultyLocktimeRevision .corrected) ScriptError.description reprStr,
      revisedBody (faultyLocktimeRevision .corrected) noGuard⟩,
    ⟨"ExampleFaultyLocktime", some "faulty",
      revisedHook (faultyLocktimeRevision .faulty) ScriptError.description reprStr,
      revisedBody (faultyLocktimeRevision .faulty) noGuard⟩,
    ⟨"ExampleVersionVerify", none,
      revisedHook versionVerifyRevision describeExampleError describeExampleUnsupported,
      revisedBody versionVerifyRevision noGuard⟩]

/-- The revisions of `proposal-test-oracle`: the examples, then the revisions of `dogelib-proposal-oracle`. -/
def testRevisions : List NamedRevision := exampleRevisions ++ revisions

/-- The name of the test executable. -/
def testProgramName : String := "proposal-test-oracle"

/-- The entry point of `proposal-test-oracle`: `runWith` with `testRevisions`. -/
def runTest (argv : List String) : IO UInt32 := runWith testProgramName testRevisions argv

end ProposalExamples.Exports
