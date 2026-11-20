import KnownAnswers.Proposals.ExampleFaultyLocktime
import KnownAnswers.Proposals.ExampleVersionVerify
import KnownAnswers.Proposals.RelativeLockTime

/-! Known answers of the proposed-revisions library, one module for each example and for each proposed revision. -/

/-- Named checks for the known answers of the proposed-revisions library, in alphabetical order. -/
def KnownAnswers.Proposals.checks : List (String × IO Nat) := [
  ("exampleFaultyLocktime", KnownAnswers.Proposals.ExampleFaultyLocktime.check),
  ("exampleVersionVerify", KnownAnswers.Proposals.ExampleVersionVerify.check),
  ("relativeLockTime", KnownAnswers.Proposals.RelativeLockTime.check)
]
