# Exact nonlocal stabilizer Rényi entropy at Schmidt rank seven

**Preprint v3.1 · 22 November 2026**

**Heming Xiao**  
Project Initiator and Lead  
Independent Research

Correspondence: [ruimiyomi@gmail.com](mailto:ruimiyomi@gmail.com)

This draft presents a proof that the ordered computational-basis Schmidt
representative minimizes the second-order stabilizer Rényi entropy over
local unitaries for every pure state of Schmidt rank seven on an arbitrary
qubit bipartition. The proof combines an analytic reduction and exact
integer interval comparisons.

## Author contributions and responsibility

Heming Xiao initiated and directed this independent research project. He chose Schmidt rank seven as the research target, set the verification objectives, coordinated separate AI-agent reviews, and oversaw the preparation of the public reproducibility materials. He also requested a fresh build from the public sources to test whether a reader could reproduce the Lean results by following the published instructions.

OpenAI Codex agents using GPT-6.2 Sol and GPT-6.2 Astra developed the mathematical arguments, formalized the proof in Lean, wrote the verification code, and drafted the manuscript. Xiao has not personally verified the complete mathematical proof. To his knowledge, a full review by an external human expert remains pending. He takes responsibility for accurately reporting the research process, contributions, and verification status, and will investigate reported errors and publish corrections where warranted.

## Research and verification status

Lean 4.36.0 checks the full interval cover, the attained minimum over the complex local-unitary orbit for a state given in seven-term Schmidt form, and the explicit minimum formula. All 5,683 project modules passed strict compilation. The [final axiom log](certificates/rank7/Rank7TheoremAudit.log) covers seven declarations. Independent human review remains open.

On 22 November 2026, a GPT-6.2 Astra agent in a separate Codex project reproduced the complete Lean build in a clean workspace using the public v5 sources. All 5,683 modules compiled, and the newly generated axiom audit matched the published log byte for byte. See the [fresh-build report and audit evidence](certificates/rank7/reproduction-2026-11-22/README.md).

- [Read the revised paper](paper/rank7_submission.pdf).
- [Download the complete v5 reproduction package](reproduction/rank-seven-reproduction-v5.zip). Extract it and follow the top-level README to check the hashes and rebuild the formal proof.
- [View all archived versions on Zenodo](https://doi.org/10.5281/zenodo.24410528).

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
