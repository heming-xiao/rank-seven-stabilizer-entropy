# Fresh build of the public rank-seven Lean proof

22 November 2026

At Xiao’s request, a GPT-6.2 Astra agent in a separate Codex project rebuilt all 5,683 project modules from the public v5 Lean sources in a clean Windows workspace using Lean 4.36.0. The build took 9 hours, 38 minutes and 27 seconds. The newly generated axiom audit matched the published log byte for byte. For both the theorem establishing the minimum and the corollary giving its explicit value, the audit listed only propext, Classical.choice, and Quot.sound. The build included the full interval cover. The external C++ and Python calculations were outside the scope of this run.

The run used the package archived with preprint v2. The v2 and v3 packages contain byte-identical copies of the Lean source archive (lean-v5.zip). The [v2 record](https://doi.org/10.5281/zenodo.24421820) identifies the download used for this run. The [v3 record](https://doi.org/10.5281/zenodo.24424358) hosts the revised manuscript.

## Build and audit

The agent ran the v5 bundle integrity check, fetched the pinned toolchain and public dependency cache, and compiled the project sources. The source bundle contained no compiled project objects. The build began with two jobs. After 134 modules it resumed from verified receipts with four jobs. The final build driver exited with code 0.

For a state supplied in seven-term Schmidt form, the two final declarations establish attainment by the sorted computational-basis representative and the explicit value of the minimum. Both allow complex local unitaries and unequal subsystem sizes. Neither declaration requires the caller to supply numerical interval coverage.

| Evidence | Result |
| --- | --- |
| [Fresh axiom audit](Rank7TheoremAudit.log) | Seven declarations. Audit SHA-256: `641a8287d091f50aa71f30d87a1b49828c915faf85a235dc02a69a3c3a4210a6` |
| [Build receipt summary](receipt-audit.json) | 5,683 successful module receipts and 15,664 project import edges |
| Lean source archive inside both packages | SHA-256: `37a013d66a93550bbe469e88f94553d35b186365acaa0e1ac930b6bb6cc4ab9f` |
