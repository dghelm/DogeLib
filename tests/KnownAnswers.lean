import KnownAnswers.AuxPow
import KnownAnswers.Block
import KnownAnswers.ContextualParams
import KnownAnswers.Genesis
import KnownAnswers.Hash
import KnownAnswers.HeaderPow
import KnownAnswers.Script
import KnownAnswers.Scrypt
import KnownAnswers.ScryptPow
import KnownAnswers.Secp256k1
import KnownAnswers.Serialization
import KnownAnswers.SignedSpends
import KnownAnswers.Transaction
import KnownAnswers.Work

/-! Known answers from independent sources, run through the compiled specification. -/

/-- Topic check lists, in alphabetical order. -/
def KnownAnswers.checks : List (String × IO Nat) :=
  List.flatten [
    KnownAnswers.AuxPow.checks,
    KnownAnswers.Block.checks,
    KnownAnswers.ContextualParams.checks,
    KnownAnswers.Genesis.checks,
    KnownAnswers.Hash.checks,
    KnownAnswers.HeaderPow.checks,
    KnownAnswers.Script.checks,
    KnownAnswers.Scrypt.checks,
    KnownAnswers.ScryptPow.checks,
    KnownAnswers.Secp256k1.checks,
    KnownAnswers.Serialization.checks,
    KnownAnswers.SignedSpends.checks,
    KnownAnswers.Transaction.checks,
    KnownAnswers.Work.checks
  ]

/-- Entry point of `lake test`.
`--scrypt-rfc n` runs only section 12 case `n` (one-based), including optional expensive cases. -/
def main (args : List String) : IO UInt32 := do
  if let ["--scrypt-rfc", index] := args then
    let some n := index.toNat? | throw (IO.userError "expected a case number from 1 to 4")
    unless 1 ≤ n && n ≤ 4 do throw (IO.userError "expected a case number from 1 to 4")
    return if (← KnownAnswers.Scrypt.checkCase (n - 1)) == 0 then 0 else 1
  unless args.isEmpty do throw (IO.userError "usage: known-answers [--scrypt-rfc 1|2|3|4]")
  let mut failures := 0
  for (_, check) in KnownAnswers.checks do
    failures := failures + (← check)
  return if failures == 0 then 0 else 1
