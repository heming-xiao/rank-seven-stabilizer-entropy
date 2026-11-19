# Upper replay on the 535-leaf subtree

Lean 4.36.0 checked `subtree535 : verifier.replay 14 23 (TailBox.toBox benchBox) = true` against the original upper traversal. The kernel evaluated `hints535` in 128.501 seconds including process startup. Its only printed axiom was `propext`. The general transfer theorem `RankSeven.HintReplay.checkSound` and its corollary `subtree535` print `propext`, `Classical.choice`, and `Quot.sound`. The audit is in `audit.log`.

The input box is stored in `HintData.lean`. The C++ exporter records 534 splits and 535 leaves, including 336 old-domain or contractor-pruned leaves and 199 corner leaves. All 199 corner leaves supply shift index 0. In the compact text traversal, the node and candidate records occupy 2,536 bytes. The factoring into Lean source declarations takes 11,203 bytes.

## Acceptance and coverage

At each node the Lean checker runs the original contractor. At a split it computes the original axis, checks the actual integer midpoint split and requires both child certificates. The proof that success implies acceptance of the original verifier allows early subdivision of an otherwise acceptable box. A leaf rechecks the corresponding old-domain or weighted comparison, or recomputes corner margins and blending on all four corners and all six sectors using the candidate shifts. Index lookup limits all candidates to the original tables. Candidate lists may omit losing shifts. Their six-sector union must cover the entire ray fan. Invalid entries make no contribution to that union.

A separate C++ stress test produced a box whose candidate list is [0,33]. In `Spot.lean` the Lean kernel checks that the list covers all sectors, [0] leaves uncovered sectors and [80] fails. It also checks a positive weighted example at index 2 and rejection of index 3. `KernelTiny.lean` checks a two-leaf original replay. Both checks use `decide +kernel`.

## Performance

The following numbers were timed inside the Lean evaluator and exclude process startup. Each method ran in five fresh processes in interleaved order.

| Approach | Median | Range |
| --- | ---: | ---: |
| Original full search | 1,602 | 1,507–1,618 |
| Prescribed tree and original search at every leaf | 764 | 755–807 |
| Prescribed tree and candidate shifts at leaves | 670 | 656–714 |

Skipping failed searches at internal nodes accounts for most of the 2.39-fold speedup on this particular tree. Candidate selection and leaf branch selection together improve the prescribed-tree benchmark by a further factor of 1.14. The data are in `timings.log`. The 128.501-second proof is a separate kernel measurement. The process used 9,760,849,920 bytes of working memory at one sample taken near 96.47 CPU seconds. This gives a lower bound on peak memory usage. These timings cover one subtree from the upper checker.

The same subtree also passed in 30 shards of at most 32 leaves with 29 checked joins. Two concurrent Lean processes took 74.604 seconds including the joins, with about 1.78 GiB aggregate sampled working memory. The kernel verified the two child endpoints at every join. The composition theorem is in [Rank7UpperHintShards.lean](../../../lean/Rank7UpperHintShards.lean). See [the sharded measurements](shards/measurement.json) and [the dependency audit](shards/Composed.log).

On eight corner leaves from the sample, computing the exact margin table took 4.138 seconds, compared with 4.227 seconds for the complete hinted acceptance check. Checking the blend on precomputed literal margins took 1.276 seconds. All three measurements include roughly 1.070 seconds of startup. The measured bottleneck is the interval arithmetic that constructs the four-by-seven table.

The point-product specialization checks the same 448 margin integers at these eight corner leaves. Median kernel time over three interleaved runs was 3.867 seconds for the original and 2.973 seconds for the specialization. See [the raw timing records](point_margins/bench_result.json). The integrated hint checker uses the specialization through a theorem that preserves its acceptance result exactly.

The integrated checker also proved the original 535-leaf subtree with the same 30 shards and 29 verified joins. In one run per variant with two workers, elapsed time fell from 71.681 to 59.426 seconds and sampled combined memory fell from 1.805 to 1.546 GiB. The control changes only the corner evaluator and its equality proof. Both terminal proofs use the same standard axioms. See the [control measurement](shards/control_measurement.json), [point-product measurement](shards/point_measurement.json), and [terminal dependency audit](shards/point_Composed.log).

## Reproduction

Build the project's `lean` directory using `lake build`. Copy this fixture directory to a scratch directory. Point the Lean 4.36 binary directory into `PATH` and put the scratch directory and the project's `lean/.lake/build/lib/lean` on `LEAN_PATH`. Run the following commands from the scratch directory. The C++ exporter works from the project sources and bounds the sample traversal by a node cap.

```powershell
python export.py "<project-directory>"
lean -o HintData.olean HintData.lean
lean --run BenchHints.lean full
lean --run BenchHints.lean shape
lean --run BenchHints.lean hints
lean -o Kernel535.olean Kernel535.lean
lean Audit.lean
python spotcheck.py
lean Spot.lean
lean KernelTiny.lean
```

To reproduce the sharded run on Windows, run `python shards/make.py` after the C++ exporter. Add the scratch `shards` directory to `LEAN_PATH` and run `python shards/run.py` with `psutil` installed.

For the eight margin grids, add the scratch `point_margins` directory to `LEAN_PATH`. From that directory run `lean -o CostValues.olean CostValues.lean`, followed by `lean KernelEight.lean`.

The checker and its general soundness theorem are in [Rank7UpperHintReplay.lean](../../../lean/Rank7UpperHintReplay.lean). The timing logs record the original run of this fixture.

The optional `lean Fixed535.lean` check takes a direct route to the same root's residual corner witnesses. It verifies that tightening the sixth-weight lower endpoint using the necessary inequality `101*d ≤ 100*c` retains every residual point and that shift 0 passes all six sectors of the tightened root. Thus this residual corner certificate uses one box. The preceding timings measure replay of the original 535 leaves.

### Actual slab paths and mixed covers

Lean checks 18 plain clipped and 26 banded subtree covers drawn from all 14 archived upper slab ranges. Each proof recomputes the path from its slab root and verifies a corner witness for every residual point in the resulting box. The banded samples prove that shift 0 fails on the unbanded box and passes after four or sixteen intervals in the seventh weight. The [recheck audit](slab_covers/recheck.log) lists the 44 saved proofs and their hashes. The bounded C++ counts in [the plain survey](slab_covers/bounded.log) and [the banded survey](slab_covers/bands_bounded.log) are exploratory. Full-slab coverage remains open.

The mixed checker also proves three enclosing subtrees that combine original leaves and the new residual certificates. One parent has both a 20-leaf ordinary proof and a 7-leaf mixed proof of the same scalar conclusion. Median runtime over three interleaved trials fell from 3.056 to 2.448 seconds. Two other examples use 14 and 7 mixed leaves on subtrees where bounded C++ enumeration counted 380 and 907 original leaves. See [the paired timing records](mixed_covers/paired_20.json) and [the three mixed examples](mixed_covers/timings.json).

To recheck the saved proofs, put the project's `lean/.lake/build/lib/lean` on `LEAN_PATH` after `lake build`. Run `lean` on each source in `slab_covers` and on the original and mixed fixtures in `mixed_covers`. For `Mixed128_104Domain.lean`, first compile `Mixed128_104.lean` to an object in scratch and add that directory to `LEAN_PATH`.

### Resumable cover of the 144–145 slab

[RefinedSlab.lean](frontier/RefinedSlab.lean) proves that each residual point in the initial `[144,145]/256` slab is either covered or belongs to one of 15 explicit valid boxes. Two bounded searches proved 34 and 32 leaves. The Lean checker reuses the first proof, replaces one of its 16 unresolved boxes by a completed proof, and checks the remaining endpoints. The three scalar branch conditions are the same as those in the mixed replay. The separate timeout fixture verifies that stopping immediately leaves the whole slab explicitly unresolved.

For proof replay, copy `frontier` to scratch and add that directory and the compiled project libraries to `LEAN_PATH`. Compile each `*Boxes.lean`, then the `*Closed*.lean` modules, then the `*Ledger.lean` modules with `lean -o <module>.olean <module>.lean`. Finally run `lean RefinedSlab.lean`. To generate fresh candidates, compile the saved `export.cpp` with the project root on the C++ include path and run `python export_proof.py Main --nodes 83 --ms 3000` in a scratch copy with Python's `psutil` installed. The runtime cap applies to candidate search.

[PhysicalDomainLedger.lean](frontier/PhysicalDomainLedger.lean) reuses the 16 accepted groups and 41 saved split equations. It preserves the physical tail domain on the accepted corner boxes and on the same 15 unresolved boxes. Given the existing signed corner estimates and positive leading excess, it supplies the conditional fixed-frame comparison on the covered portion. For this check, compile the original Main, Resume and Timeout ledgers first, then `RefinedSlab`, `DomainLedger` and `PhysicalDomainLedger`.

[SmallPhysicalLedger.lean](frontier/SmallPhysicalLedger.lean) extends this cover to four of those previously unresolved boxes. It checks nineteen additional leaves and gives the same conditional physical comparison or one of precisely eleven remaining valid boxes. For the recheck, build `SmallBoxes*`, then `SmallProof*`, `SmallClosure*`, `SmallDomainLedger`, and `SmallPhysicalLedger`. The [search records](frontier/small_selection.json), [timings](frontier/small_results.json), and [Lean recheck](frontier/recheck.log) record the completed refinements.

[SmallCertifiedLedger.lean](frontier/SmallCertifiedLedger.lean) applies the verified signed exterior estimates to the same eleven-box ledger. It derives the required head bound from the original slab membership. The first 41 modules in the [recheck audit](frontier/recheck.log) include this module.

### Adaptive split of one remaining box

The [certified physical ledger](frontier/AxisCertifiedLedger.lean) reduces the open list for `[144,145]/256` to ten boxes by closing `r0000000001`. The original split and the adaptive split use 71 and 25 leaves respectively for the same subtree. In one sequential run per policy the recorded wall times were 50.984 and 21.711 seconds. [Raw timing and frontier data](frontier/adaptive_result.json).

For replay, first compile the original and `Small*` modules as above, including `SmallCertifiedLedger`. Compile `AxisFastBoxes` and `AxisControlBoxes`, the two collections of numbered groups, the two closure modules, and finally `AxisDomainLedger`, `AxisPhysicalLedger`, and `AxisCertifiedLedger` in that order. The [audit](frontier/recheck.log) lists the hashes of these 70 sources and their kernel reports. Full-slab coverage remains open.

### Nine-box ledger and physical corner comparison

The [next closure](frontier/SectorCertifiedLedger.lean) removes `r000000000001` and preserves nine explicit valid boxes. The selected exact certificate uses 118 leaves and 117 splits. The [recorded run](frontier/sector_result.json) took 48.264 seconds with at most two workers.

Compile `SectorBoxBoxes`, the numbered `SectorBoxGroup*` modules, `SectorBoxClosure`, `SectorDomainLedger`, `SectorPhysicalLedger`, and `SectorCertifiedLedger` after the Axis modules. The [95-source audit](frontier/recheck.log) records this replay. After also building the real-spectrum package, [SectorRealPhysicalLedger.lean](real_frontier/SectorRealPhysicalLedger.lean) applies the paired-defect comparison to every covered signed corner for every highest-pair Gram value when `24*kappa >= 1` on the shared parameter. Its conclusion retains the older and weighted scalar classifications and the nine open boxes.
