# Exact nonlocal stabilizer Rényi entropy at Schmidt rank seven

**Preprint v2 · 21 November 2026**

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

Lean 4.36.0 checks the full interval cover, the attained minimum over the complex local-unitary orbit for a state given in seven-term Schmidt form, and the explicit minimum formula. All 5,683 project modules passed strict compilation. The [final axiom log](certificates/rank7/Rank7TheoremAudit.log) covers seven declarations. Independent human review remains open.

- [Read the revised paper](paper/rank7_submission.pdf).
- [Download the complete v5 reproduction package](reproduction/rank-seven-reproduction-v5.zip). Extract it and follow the top-level README to check the hashes and rebuild the formal proof.
- [Cite the paper and its reproduction materials on Zenodo](https://doi.org/10.5281/zenodo.24421820).

## Contents

| Path | Contents |
| --- | --- |
| [paper/](paper/) | [Research draft PDF](paper/rank7_submission.pdf) and [LaTeX source](paper/rank7_submission.tex) |
| [proof/](proof/) | [Proof guide](proof/rank7_submission_proof_guide.md), derivations, and technical reviews |
| [lean/](lean/) | Earlier Lean development and a guide to the full v5 build |
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
[verification/README.md](verification/README.md). For the full Lean proof, use the README in the [v5 reproduction package](reproduction/rank-seven-reproduction-v5.zip).
