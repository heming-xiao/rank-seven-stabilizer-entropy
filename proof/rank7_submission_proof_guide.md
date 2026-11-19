# Proof supplement for the rank-seven submission

Research draft, 18 November 2026. Heming Xiao is the project initiator and
lead. This is an independent research project. OpenAI Codex agents developed
the main proof, verification code, and manuscript. Independent human review
is invited.

This supplement indexes the proof of Theorem 1 in
[the submission draft](../paper/rank7_submission.tex). The theorem concerns
the second-order stabilizer Rényi entropy of pure states over their
entire complex local-unitary orbit. All seven Schmidt probabilities
may vary, including ties. Each side may have any qubit dimension
that admits rank seven. The theorem establishes attainment by the
ordered computational representative.

## Analytic dependencies

| Step | Source and conclusion |
| --- | --- |
| Paired frames and unequal sides | [Proof assembly](rank7_tail_cover_assembly_round_2026-11-18.md), first section. The purity on a balanced cut is bounded by the geometric mean of two actual paired-frame purities. Leading computational ancillas preserve the purity pointwise in the passage from unequal to balanced cuts. |
| Exact purity comparison | [Sierant, Eq. (42), Eq. (175), Theorems 7 and 22](https://arxiv.org/html/2609.13106v2) supply the sector decomposition and the rank-seven exterior contraction, with equality at the ordered computational representative. [Compression identity](rank7_compression_slack_astra.md) retains the exact loss. The target is \(168E\le\mathcal D+96\mathcal D_F\), with \(E\) the normalized exterior gain. |
| Pauli sectors and paired geometry | [Paired Pauli defect and packing](rank7_three_equal_tails.md), introductory reductions, establishes the normalization and the joint mixed and anticommuting payments. [Signed exterior estimates](rank7_low_head_tail_prices.md), [weighted split](rank7_weighted_split_residual.md), and [leading Pauli allocation](rank7_leading_split_joint_payment.md) provide the two exterior comparisons and the corresponding physical charges. |
| Frame sectors and compactness | [Signed excesses](rank7_excess_ratio.md) handles either nonpositive excess. [Small third gaps](rank7_low_third_gap.md), [the half-fifth threshold](rank7_small_third_half.md), [zero shared width](rank7_zero_shared_width.md), and [compact domain](rank7_remaining_domain.md) give necessary bounds on any spectrum left for the interval comparisons. |
| Compression cuts | [Crossed compression](rank7_crossed_compression.md) derives the common trace loss and the nominal crossing cost. [Joint trace prices](rank7_joint_trace_prices.md) gives the ray inequalities. [Positive shared endpoints](rank7_positive_shared_tail_endpoints.md) accounts for the correction in both usable exterior comparisons, with the same physical remainder. |
| Transport to arbitrary fourth gap | [Mixed transport](rank7_mixed_cut_full_fourth_ray.md) handles the physical mixed remainder and two available cut prices. [Transfer of every branch](rank7_seed_branch_transfer.md) treats the compression-free and highest-width weighted tests and the region prunes. [Independent branch audit](reviews/rank7_seed_branch_transfer_independent_review.md) checks the hypotheses for both interval implementations. |
| Exact tie cover | [Upper proof](rank7_fourth_tie_bilinear.md) gives the two-tail multiaffine comparison. [Lower proof](rank7_tied_fourth_lower_fifth.md) gives the one-tail affine comparison. Both cover all positive frame-excess ratios using the listed seven rays. [Independent upper source audit](reviews/rank7_c_affine_highest_and_bilinear_independent_review.md) checks the upper contractions, compatibility test, and physical interpolation. |
| End regions and assembly | The [large fifth-to-seventh ratio result](rank7_fifth_two_and_positive_shared_endpoints.md) covers \(d/b\le1/2\). The [close-bottom theorem](rank7_near_two_tails.md) covers \(d/b\ge100/101\) since \(c\le b\). The [completed assembly](rank7_tail_cover_assembly_round_2026-11-18.md) verifies every shared endpoint. |

The mixed branch uses \(A_0=(101/100)168\) on positive exterior gain.
It first bounds the signed gain, then restores the signed terms using
disjoint Pauli and compression payments. Nonpositive exterior gain
is covered by nonnegativity of the two defects. The weighted and
prior-domain branches have their own justifications in the transfer
proof. This distinction specifies the conclusion of each C++ exit
path used in the theorem.

## Reproducing the interval comparisons

Run the following from the project root with Python and a C++20
compiler with signed 128-bit integer support. The recorded environment
uses Python 3.13.1, SymPy 1.13.1 for the mixed-transport check, and
MinGW GCC 16.2.0. On Windows add `.exe` to the executable names.
Use relative source and output filenames to accommodate MinGW builds
under a working directory containing non-ASCII characters.

```sh
python verification/verify_rank7_seed_branch_transfer.py
python verification/verify_rank7_mixed_cut_full_fourth_ray.py
python verification/verify_rank7_fifth_two.py
python verification/verify_rank7_near_three_tails.py
python verification/verify_rank7_near_two_tails.py
g++ -std=c++20 -O3 -o rank7_upper verification/verify_rank7_fourth_tie_bilinear.cpp
g++ -std=c++20 -O3 -o rank7_lower verification/verify_rank7_tied_fourth_lower_fifth.cpp
./rank7_upper 8 9 16
./rank7_lower 1 6
python verification/verify_rank7_tail_interval_union.py --require-complete
```

The upper executable accepts a lower numerator, an upper numerator,
and a common denominator. To replay the main band use
\((144,145,256)\), \((145,148,256)\), and
\((j,j+4,256)\) for \(j=148,152,\ldots,188\).
Exit zero follows exhaustion of the pending-box stack, and the output
records the three categories of accepted leaf. The lower executable
uses the six slab numbers listed in the lower proof.

The [upper proof](rank7_fourth_tie_bilinear.md) links the thirteen run logs.
The [lower-run record](rank7_seed_transfer_and_priority_round_2026-11-18.md)
lists all lower slab totals. Fresh independent builds reproduced the
[upper anchor](../certificates/rank7/upper_anchor_8_9_of_16.log) with
6,455,151 leaves at depth 39, and
[lower slab 1](../certificates/rank7/low_fifth_slab_1.log) and
[lower slab 3](../certificates/rank7/low_fifth_slab_3.log) with
503,922 and 689,806 leaves, respectively. Independent Python runs
also reproduced the [large-ratio check](../certificates/rank7/replay_large_fifth.log)
and the close-bottom checks for
[three small tails](../certificates/rank7/replay_close_bottom_three.log)
and [two small tails](../certificates/rank7/replay_close_bottom_two.log).
The Python union check validates the recorded closed endpoints and
execution summaries against the frozen source files. An independent
traversal replay uses the C++ executables. The exact union, including
its endpoints, was checked independently.

## Lean checks

The release includes the [Lean project](../lean/README.md) and its
[build audit](../certificates/rank7/lean_shared_odd_leakage_build.log).
The project checks the rectangular Pauli purity reduction, several
physical packing and compression inequalities, and selected interval
replays. It also proves the physical small shared-Gram leakage bound.
The full rank-seven theorem and the complete interval replay remain
under formalization. Future versions will record updates to the checked
scope and provide updated build logs. The C++ programs regenerate the interval
traversals described above.

To reproduce the bundled-library proof checks, run `lake build` in
`lean/` with Lean 4.36.0. The separate
[real-spectrum project](../lean/real/README.md) uses the pinned Mathlib
revision.
