module

public import DogeLib.Base.Proofs
public import DogeLib.Cryptography.Proofs
public import DogeLib.Serialization.Proofs
public import DogeLib.Transaction.Proofs
public import DogeLib.Work.Proofs

/-!
# `DogeLib.Proofs`

Root of the `Proofs` Lake library: imports the proofs of every layer.
`lake exe check-decls` imports this module, so a layer whose proofs it leaves out is not checked.
`scripts/test_check_decls.sh` fails when a layer's proof root is missing here.
-/
