# Rank-seven comparison on two full tail regions, 2026-11-18

Write the ordered probabilities as
\((\alpha,\beta,\gamma,a,b,c,d)\), with \(d>0\). The target
is order-two sorted computational-basis optimality for all rank-seven
spectra, all qubit bipartitions and arbitrary complex local unitaries.

## Fourth-gap transfer

New exact comparisons extend every accepted branch of the two
fourth–fifth tie verifiers to arbitrary fourth gap \(p=a-b\ge0\).
The mixed comparison pays the change of the true highest cut, the
nominal shared cut, and the crossing allowance together on the remaining
\(q=\gamma-a\ge2d/3\) region. The separate transfer proof handles
the weighted highest-cut test and every older region used for pruning.
The Python checks passed for the rational constants, 39 exterior
coefficients and 161 combined payment coefficients. The bilinear
checker and preceding constituent estimates were independently reviewed.
A separate reviewer confirmed the lower mixed and weighted branches and the exceptional upper weighted transfer. [Independent review](reviews/rank7_seed_branch_transfer_independent_review.md).

- [Mixed-cut proof](rank7_mixed_cut_full_fourth_ray.md) and [checker](../verification/verify_rank7_mixed_cut_full_fourth_ray.py).
- [Transfer of all accepted branches](rank7_seed_branch_transfer.md) and [checker](../verification/verify_rank7_seed_branch_transfer.py).
- [Bilinear checker source review](reviews/rank7_c_affine_highest_and_bilinear_independent_review.md).

## Completed continuous regions

The lower fifth-probability checker completed all six of these closed
intervals in \(b/d\). Counts include discarded boxes covered by
known criteria. The source and included interval arithmetic hashes
are in the [proof note](rank7_tied_fourth_lower_fifth.md).

| Slab | \(b/d\) | Older | Weighted | Shared | Max depth | Completion record |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| 1 | \([5/4,4/3]\) | 787 | 4351 | 498784 | 30 | Computing agent's output |
| 2 | \([6/5,5/4]\) | 630 | 2360 | 459051 | 31 | Persisted log |
| 3 | \([23/20,6/5]\) | 757 | 2017 | 687032 | 31 | Computing agent's output |
| 4 | \([11/10,23/20]\) | 952 | 1718 | 830464 | 31 | Persisted log |
| 5 | \([21/20,11/10]\) | 1337 | 1455 | 951730 | 33 | Persisted log |
| 6 | \([101/100,21/20]\) | 1560 | 1099 | 904484 | 34 | Persisted log |

Total 4,350,568 accepted leaves. Together with the older close-bottom
theorem and fourth-gap transfer, this covers every rank-seven spectrum
with \(b/d\le4/3\), even away from the \(a=b\) face.
[Slab 2 log](../certificates/rank7/low_fifth_slab_2.log) and
[slabs 4–6 log](../certificates/rank7/low_fifth_slabs_4_6.log).

The independently source-reviewed upper bilinear checker completed
\(d/b\in[1/2,9/16]\) with 6,455,151 accepted leaves at depth 39.
The transfer and earlier \(b/d\ge2\) theorem give every rank-seven
spectrum with \(b/d\ge16/9\). 6 further closed intervals finished,
from \(d/b=144/256\) to \(164/256\), extending the upper region
to \(b/d\ge64/41\). The completions and the CLI source hash
are recorded in the upper bilinear proof. Neither new region requires a tie
or restricts the local-unitary orbit. [Upper bilinear proof](rank7_fourth_tie_bilinear.md).

## Remaining work

The entire unresolved domain now lies in \(4/3<b/d<64/41\), with
all the earlier necessary inequalities still in force. Completing the
upper bilinear verifier on \(41/64<d/b<3/4\) with a final review of the interval union would suffice for the full theorem. The old
execution session ended without recording completion of its second
slab. Two new lanes check disjoint cells using persistent per-cell logs.
The separate near-tie traversals also ended. Historical completed
slabs and counts are preserved, and subsequent runs should skip those
slabs. The \(b=c\) process had at least 112,600,000 accepted leaves
at depth 59 and no completed cover. The \(a=b=c\) process completed
its first three slabs (1,043,514 leaves), with 2,100,000 accepted
leaves last observed and no completion of slab 4.

The public priority recheck through November 18 found neither a proof
nor a counterexample matching the full rank-seven target. Sierant's
latest public revision explicitly leaves ordinary rank-seven spectra
open. Priority beyond the reviewed public literature remains unverified.
[Priority recheck](../literature/rank7_public_priority_recheck_2026-11-18.md).

Subjective result size 6/10 for two unrestricted continuous spectral
regions. No full-rank-seven claim is made.
