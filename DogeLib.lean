module

public import DogeLib.Base
public import DogeLib.Cryptography
public import DogeLib.Serialization
public import DogeLib.Work

/-!
# `DogeLib`

Dogecoin specifications, written in Lean.

Each layer lives in its own subtree:

- `DogeLib.Base` holds the byte representations that the other layers build on.
- `DogeLib.Serialization` holds the codecs between values and bytes.
- `DogeLib.Cryptography` holds the cryptographic primitives.
- `DogeLib.Work` holds the proof-of-work arithmetic: compact targets and the difficulty retarget.
-/
