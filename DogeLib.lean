module

public import DogeLib.Base
public import DogeLib.Block
public import DogeLib.Cryptography
public import DogeLib.Script
public import DogeLib.Serialization
public import DogeLib.Transaction
public import DogeLib.Work

/-!
# `DogeLib`

Dogecoin specifications, written in Lean.

Each layer lives in its own subtree:

- `DogeLib.Base` holds the byte representations that the other layers build on.
- `DogeLib.Serialization` holds the codecs between values and bytes.
- `DogeLib.Cryptography` holds the cryptographic primitives.
- `DogeLib.Transaction` holds transaction types, base and witness serialization, transaction IDs, legacy signature hashing, `CheckTransaction`, and the legacy signature-operation count.
- `DogeLib.Work` holds proof-of-work arithmetic: 256-bit word models, compact targets, difficulty retargets, next-work selection, median time past, and block proof.
- `DogeLib.Block` holds pure and full headers, AuxPoW, Merkle roots, header proof of work, version gating, contextual headers, and header sequences.
  It also holds mainnet block subsidy, version bits, block serialization, `CheckBlock`, `ContextualCheckBlock`, coin sets, `CheckTxInputs`, signature-operation cost, `ConnectBlock`, and `validateBlock`.
- `DogeLib.Script` holds the instruction reader, execution state, Script numbers, `EvalScript`, encoding checks, signature checkers, `coreVerifier`, `VerifyScript`, and `verifyLegacySpend`.
-/
