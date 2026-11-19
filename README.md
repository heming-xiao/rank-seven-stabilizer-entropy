# Exact nonlocal stabilizer Rényi entropy at Schmidt rank seven

**Community research draft v1**

**Heming Xiao**  
Project Initiator and Lead  
Independent Research

This draft presents a proof that the ordered computational-basis Schmidt
representative minimizes the second-order stabilizer Rényi entropy over
local unitaries for every pure state of Schmidt rank seven on an arbitrary
qubit bipartition. The proof combines an analytic reduction and exact
integer interval comparisons.

OpenAI Codex agents developed the main proof, verification code, and
manuscript. Independent human review is invited, especially of the
compression-defect accounting and the transfer from tied fourth and
fifth Schmidt probabilities to arbitrary rank-seven spectra.

## Research and verification status

Lean formalization is in progress. Follow [the Lean README](lean/README.md)
for the statements checked and the [build audit](certificates/rank7/lean_shared_odd_leakage_build.log)
for the exact verified snapshot. The full main theorem and full interval
replay remain under formalization. We will update the Lean source, scope
statement, and build records as further parts of the proof are checked.

## Contents

| Path | Contents |
| --- | --- |
| [paper/](paper/) | [Research draft PDF](paper/rank7_submission.pdf) and [LaTeX source](paper/rank7_submission.tex) |
| [proof/](proof/) | [Proof guide](proof/rank7_submission_proof_guide.md), derivations, and technical reviews |
| [lean/](lean/) | Lean sources, pinned toolchain, and [build instructions](lean/README.md) |
| [verification/](verification/) | C++ and Python verifiers with [reproduction commands](verification/README.md) |
| [certificates/](certificates/) | [Run records and certificates](certificates/README.md) |
| [literature/](literature/) | [Literature checks and reference material](literature/README.md) |
| [CITATION.cff](CITATION.cff) | Citation metadata for this version of the project materials |
| [SHA256SUMS.txt](SHA256SUMS.txt) | SHA-256 digests of the release files |

## Quick checks

From the repository root, run the receipt coverage check with Python 3.

```sh
python verification/verify_rank7_tail_interval_union.py --require-complete
```

For a fresh traversal, use the compiler and commands in
[verification/README.md](verification/README.md). For Lean, use the
bundled-library build and pinned Mathlib instructions in
[lean/README.md](lean/README.md).
