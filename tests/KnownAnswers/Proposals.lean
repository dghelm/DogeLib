import KnownAnswers.Proposals.ExampleFaultyLocktime
import KnownAnswers.Proposals.ExampleVersionVerify

/-! Known answers of the proposed-revisions library, one module for each example. -/

/-- Named checks for the known answers of the proposed-revisions library, in alphabetical order. -/
def KnownAnswers.Proposals.checks : List (String × IO Nat) := [
  ("exampleFaultyLocktime", KnownAnswers.Proposals.ExampleFaultyLocktime.check),
  ("exampleVersionVerify", KnownAnswers.Proposals.ExampleVersionVerify.check)
]
