# Coverage

What DogeLib implements, per operation and per kind of evidence ([CONTRIBUTING.md](CONTRIBUTING.md#coverage-and-status)). Each column records a separate claim. A blank cell means nothing exists.

SHA-256 and double SHA-256 are the only operations implemented.

## Legend

| Column | Meaning |
| --- | --- |
| Definition | An executable definition exists in the specification target |
| Theorems | Named theorems, each with its domain and hypotheses or a link to them |
| Comparison | Comparison evidence: which implementation, which corpus, which revision, which run |
| Refinement | A proved relationship to another implementation, naming that implementation |
| Excluded | Inputs, modes, or eras deliberately outside the current claims |

Use *conditional* in the Theorems column when a theorem depends on a hypothesis that no caller yet discharges.

## Operations

Add rows in sorted order by operation name. Change only the cells your evidence supports.

| Operation | Definition | Theorems | Comparison | Refinement | Excluded |
| --- | --- | --- | --- | --- | --- |
| Double SHA-256 | `Cryptography.Hash.Sha256d.hash` | `size_hash`: 32 bytes. `hash_eq_spec`: equals the FIPS 180-4 model applied twice, for messages shorter than 2^61 bytes | `lake test`: the genesis coinbase txid and the three genesis block hashes that Dogecoin Core asserts | None | Messages of 2^61 bytes or more |
| SHA-256 | `Cryptography.Hash.Sha256.hash` | `hash_eq_spec`: equals a separate FIPS 180-4 model, for messages shorter than 2^61 bytes | `lake test`: 129 NIST CAVP vectors (CAVS 11.0) through the compiled code | None | Messages of 2^61 bytes or more, and inputs that are not whole bytes |
