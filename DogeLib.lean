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
- `DogeLib.Transaction` holds the transaction fields, their base serialization and the transaction ID.
- `DogeLib.Work` holds the proof-of-work arithmetic: compact targets, the difficulty retarget and the work of one block.
- `DogeLib.Block` holds pure headers, block hashes and transaction Merkle roots.
- `DogeLib.Script` holds the instruction reader of the Script interpreter, the state of one `EvalScript` call, Script numbers and the truth value of a stack item. It also holds the interpreter's errors and flags, and one `EvalScript` call for the opcodes of stage 2, including the numeric and hash opcodes.
-/
