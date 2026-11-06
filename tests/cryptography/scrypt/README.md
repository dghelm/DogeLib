# RFC 7914 scrypt known answers

`tests/KnownAnswers.lean`, namespace `KnownAnswers.Scrypt`, records the input and expected output bytes from [RFC 7914](https://www.rfc-editor.org/rfc/rfc7914).
The test calls the compiled list model without a replacement for its reference ROMix fill.
No expected value comes from DogeLib or from a separate run of the model.

The default checks compare these complete outputs:

| Section | Operation | Parameters | Output bytes |
| --- | --- | --- | --- |
| 8 | Salsa20/8 core | Sixteen little-endian words | 64 |
| 9 | scryptBlockMix | `r = 1` | 128 |
| 10 | scryptROMix | `r = 1`, `N = 16` | 128 |
| 12, case 1 | scrypt | Empty password and salt, `N = 16`, `r = 1`, `p = 1` | 64 |

The section 9 and 10 inputs are the same 128 bytes.
The byte order is the RFC's printed order, without digest reversal.
Password and salt strings in section 12 use ASCII bytes.
Parameter rejection checks also cover `N = 0`, `1`, `3` and `65536` with `r = 1`, zero `r` or `p`, excessive `p`, and zero or excessive output length.

## Errata

The [RFC Editor errata search](https://errata.rfc-editor.org/search/?rfc_number=7914) was read on 2026-11-06, before the vectors were transcribed.
It lists six entries:

| Erratum | Status | Subject | Treatment |
| --- | --- | --- | --- |
| 5871 | Verified | ASN.1 in §7.1 | Outside this model |
| 6972 | Verified | Parameter advice in §2 | No algorithm or vector change |
| 5971 | Reported | Remove the upper bound on `N` in §2 | Retain the published bound, as pinned VG does |
| 5972 | Reported | The same bound in §5 | Retain the published bound |
| 5973 | Reported | The same bound in §6 | Retain the published bound |
| 6452 | Reported | Integerify wording in §5 | Retain the published final-block integer interpretation |

None changes the known answers in sections 8–12.
Integerify reads the final 64-byte block, rather than one byte or the entire input.
The model retains the published bound `N < 2^(128 * r / 8)`.
The reported proposals do not change this contract.

## Test cost

[Design record 0004](../../../docs/design/0004-header-proof-of-work.md#test-cost) requires compiled known answers and measured cost.
It sets no numeric timeout.
This lane chose 10 seconds per optional section 12 case, with the planner's approval.
The measurements below used Lean `v4.35.0`, the native `known-answers` executable, and CPU affinity `0-7` on 2026-11-06.
They are individual observations on a shared machine, rather than performance guarantees.

| Section 12 case | Parameters (`N`, `r`, `p`) | Result | Default test |
| --- | --- | --- | --- |
| 1 | 16, 1, 1 | Complete 64-byte output agrees, 9 ms in an isolated run | Included |
| 2 | 1024, 8, 16 | Timed out at 10 seconds, with exit status 124 and no comparison result | Excluded |
| 3 | 16384, 8, 1 | Timed out at 10 seconds, with exit status 124 and no comparison result | Excluded |
| 4 | 1048576, 8, 1 | Not run | Excluded |

The complete default `lake test` run passed all four known answers and the parameter rejection checks.
Salsa20/8 and BlockMix each took less than 1 ms, ROMix took 9 ms, and the small scrypt case took 10 ms.

The reference fill computes each stored iterate separately.
One complete ROMix therefore applies BlockMix `N * (N + 3) / 2` times.
Each BlockMix applies Salsa20/8 `2 * r` times, and scrypt computes `p` ROMix blocks.
The four section 12 cases thus require 304, 134610944, 2147876864 and 8796118188032 Salsa20/8 calls.
These counts explain the exclusion of case 4 after the timeouts of cases 2 and 3.
They do not estimate compiler allocations or establish a runtime bound.

The model retains the quadratic fill, and the generic sequential-fill theorem does not replace it at runtime.

After `lake build known-answers`, run an individual case with these commands:

```bash
taskset -c 0-7 .lake/build/bin/known-answers --scrypt-rfc 1
timeout 10s taskset -c 0-7 .lake/build/bin/known-answers --scrypt-rfc 2
timeout 10s taskset -c 0-7 .lake/build/bin/known-answers --scrypt-rfc 3
```

The selector also accepts case 4, but that case needs a separate resource decision before a run.
`lake test` runs only the default cases and the rejection checks.
It evaluates no scrypt digest in the kernel and uses no `native_decide`.
The fixed Dogecoin executable and its header vectors belong to the next lane.
