# Lean checks for the rank-seven research draft

The full rank-seven theorem and the complete interval replay are still
being formalized. This directory and its build records will be updated
as more of the proof is checked.

From this directory, run `lake build` with Lean 4.36.0.
The project uses Lean's bundled libraries. See the
[latest build audit](../certificates/rank7/lean_shared_odd_leakage_build.log)
and the [C++ sample replay](../certificates/rank7/lean_pauli_interval_build.log).

## Statements checked

- [Rank7MixedCutRate.lean](Rank7MixedCutRate.lean) checks the cubic
  coefficient's debit bound in equation (4), the square-root bound
  and denominator-cleared versions of equation (5), and the final
  inequality carrying a seed comparison along the fourth-gap ray.
  These are symbolic theorems over an ordered commutative ring.
  The [original derivation](../proof/rank7_mixed_cut_full_fourth_ray.md)
  supplies the hypotheses on the Pauli quantities and cut widths.
- [Rank7TailCoverage.lean](Rank7TailCoverage.lean) proves that the
  13 closed intervals for the scaled ratio \(x=256d/b\) join
  on \([144,192]\), and that the main band joins the four other
  analytic or computational regions to cover \(0<x\le256\).
  The mathematical comparison inside each interval is a hypothesis.
- [Rank7PauliReduction.lean](Rank7PauliReduction.lean) proves the
  product-operator expectation identity in coefficient-matrix trace
  form and the transpose symmetry of the fourth Pauli tensor sum for
  any qubit count. It also checks the single-zero-ancilla fourth-moment
  factor and the finite real-coordinate Cauchy–Schwarz comparison
  used to pass from two paired bounds to a cross bound.
- [Rank7PauliTensor.lean](Rank7PauliTensor.lean) proves the
  fourth-copy expansion and the Pauli operator-sum identity for
  rectangular coefficient matrices. It also proves invariance of
  the normalized fourth moment under repeated leading-zero padding
  on the left. [Rank7PauliFrames.lean](Rank7PauliFrames.lean) proves
  the exact normalized paired-frame trace formula on any balanced
  cut, with the local fourth-copy sums unnormalized. The conjugated
  frame entries are explicit arguments of the algebraic identity.
  [Rank7ComplexPauliMoment.lean](Rank7ComplexPauliMoment.lean) proves
  that the product-Pauli expectation of a rectangular complex state
  is self-conjugate, and its fourth power equals the real embedding
  of the fourth power of its modulus.
- [Rank7PhysicalPairedReduction.lean](Rank7PhysicalPairedReduction.lean)
  defines physical stabilizer purity directly from the normalized
  sum of fourth powers of Pauli moduli. It proves invariance under
  transposition and computational zero padding, and the weighted
  Hermitian trace bound used in frame pairing.
  [Rank7RectangularPairedReduction.lean](Rank7RectangularPairedReduction.lean)
  compresses the exact rectangular purity trace to the common
  Schmidt source space, with each Pauli sum normalized by its own
  local dimension. For every pair of local qubit counts admitting
  rank seven, the computational representative's purity is
  dimension-independent, and `rankSevenComputationalComparison`
  proves the orbital purity bound from the two same-frame bounds.
- [Rank7PauliTwirlEntries.lean](Rank7PauliTwirlEntries.lean) evaluates
  the full four-copy Pauli matrix in every qubit dimension. Each
  bit must have even input parity, and all four input labels must
  have the same translation to their output labels. The normalized
  entry is 2 to the power −n wherever the bit conditions hold.
- [Rank7ExteriorPauliBase.lean](Rank7ExteriorPauliBase.lean) checks
  the physical three-qubit Pauli matrix on all 70 coordinate
  four-wedges via its signed determinants. The resulting matrix
  equals half the sum of the seven plane-wave Gram matrices.
  [Rank7ExteriorOccupation.lean](Rank7ExteriorOccupation.lean)
  verifies the signed one-hole permutation of the 56 triple
  coordinates and the resulting half-occupation identity for
  arbitrary coherent vectors. These are parts of the eight-point
  compression base used in [Sierant, §C.12](https://arxiv.org/html/2609.13106v2).
- [Rank7ProjectionBound.lean](Rank7ProjectionBound.lean) proves the
  projection-sandwich comparison, including the one-half case.
  [Rank7HermitianEffect.lean](Rank7HermitianEffect.lean) proves
  that a self-adjoint operator with quadratic form between zero
  and the identity has nonnegative defect T−T², by a sum of two
  nonnegative forms.
- [Rank7ExteriorOperators.lean](Rank7ExteriorOperators.lean) verifies
  the signed creation and annihilation operators on all 256 masks.
  It derives the canonical anticommutation relations, occupation
  idempotence and Hermitian self-adjointness, and the vanishing of
  occupation on four-fold wedges of vectors orthogonal to the hole.
  [Rank7PlaneProjector.lean](Rank7PlaneProjector.lean) verifies that the
  physical plane-wave matrix on 70 coordinates is an orthogonal
  projection and relates its contracted waves to the occupation basis.
  [Rank7EightPointCompression.lean](Rank7EightPointCompression.lean)
  combines these results to prove the half-occupation sandwich for the
  actual eight-point projector. It gives an exact bilinear norm-defect
  certificate with dual coefficients for an arbitrary hole mass.
  [Rank7ComplexScalar.lean](Rank7ComplexScalar.lean) implements
  complex scalars over an ordered ring and proves the norm and
  conjugation laws. [Rank7ComplexExteriorBridge.lean](Rank7ComplexExteriorBridge.lean)
  specializes the pairings and operators to those complex coordinates.
  [Rank7MissingHole.lean](Rank7MissingHole.lean) proves existence of
  a nonzero annihilator of at most seven columns on eight points.
  [Rank7ComplexEightPoint.lean](Rank7ComplexEightPoint.lean) uses all
  three results to prove the half-norm bound on arbitrary complex
  linear combinations of four-fold wedges from those columns.
- [Rank7GenericExteriorKernel.lean](Rank7GenericExteriorKernel.lean)
  verifies the normalized physical Pauli determinant kernel on all
  increasing four-wedge coordinates, in any qubit dimension. It has
  entry 4/2^n exactly when the input has zero XOR and the output
  is a translate of the input. The other entries vanish.
  [Rank7PlaneOrientation.lean](Rank7PlaneOrientation.lean) proves
  that binary translation preserves the orientation of a sorted
  plane, so the physical contributing terms all have positive sign.
- [Rank7HyperplaneIncidence.lean](Rank7HyperplaneIncidence.lean)
  proves the incidence count for every independent family of binary
  difference vectors and specializes it to four distinct affine points.
  [Rank7HyperplaneResolution.lean](Rank7HyperplaneResolution.lean)
  checks the plane and nonplane diagonal entries and the off-diagonal
  parallel-plane entries of the higher-dimensional coordinate
  recursion in [Sierant, §C.12, (222)–(224)](https://arxiv.org/html/2609.13106v2).
  [Rank7HyperplaneInduction.lean](Rank7HyperplaneInduction.lean)
  verifies the coordinate defect resolution over all nonzero
  binary hyperplanes and proves the congruence for the quadratic
  form of a coordinate embedding. It proves the induction for
  signed determinant lifts from the eight-point inequality and
  explicitly states the required chart and kernel compatibilities.
- [Rank7PhysicalExteriorCompression.lean](Rank7PhysicalExteriorCompression.lean)
  instantiates the induction on the actual normalized physical
  determinant kernel. The [ordered hyperplane chart](Rank7OrderedHyperplaneChart.lean)
  preserves coordinate order and translation support.
  [Rank7PhysicalExteriorSupport.lean](Rank7PhysicalExteriorSupport.lean)
  and [Rank7PhysicalChartRestriction.lean](Rank7PhysicalChartRestriction.lean)
  prove the parent and restricted kernel entries used by the induction.
  [Rank7ExteriorDeterminantBridge.lean](Rank7ExteriorDeterminantBridge.lean)
  identifies the complex eight-point exterior vectors with the signed
  determinant lift. For each qubit count of at least three, the resulting
  theorem bounds the physical kernel's quadratic form by the squared
  norm times 4/2^n on the lift of any complex seven-column matrix and
  any linear combination of the 35 source wedges.
- [Rank7PhysicalExteriorPositivity.lean](Rank7PhysicalExteriorPositivity.lean)
  writes the physical kernel quadratic form as a sum of scaled squares
  of the real and imaginary coefficient sums in each parallel-plane class.
  [Rank7ExteriorIsometry.lean](Rank7ExteriorIsometry.lean) proves the
  Cauchy–Binet identity for the fourth minors of two complex seven-column
  matrices. For an orthonormal frame its determinant lift is isometric.
  [Rank7ExteriorCompressionEffect.lean](Rank7ExteriorCompressionEffect.lean)
  identifies the exact compressed entries and their quadratic form.
  [Rank7PhysicalCompressionEffect.lean](Rank7PhysicalCompressionEffect.lean)
  combines these results. It proves that the normalized compression
  has quadratic form between zero and the identity and derives the
  two crossed spectral-cut bounds for the actual Pauli matrix.
- [Rank7FrameExteriorSector.lean](Rank7FrameExteriorSector.lean)
  transports the actual Pauli matrix through the fourth exterior
  lift by Cauchy–Binet. The alternating block of a single normalized
  frame in the rectangular trace is four times the spectral
  compression. Its paired trace is sixteen times the exact
  spectral quadratic trace on all 35 four-wedges.
- [Rank7FourCopySectors.lean](Rank7FourCopySectors.lean) checks the
  finite permutation projector multiplication table, transports
  the replica symmetry and Klein invariance to the compressed
  Pauli frame matrices, and proves the trace split for the actual
  normalized rectangular paired trace. The split has one
  symmetric, two equal mixed, and one alternating term, and
  distinct projectors have zero crossed trace.
  [Rank7AlternatingTrace.lean](Rank7AlternatingTrace.lean) proves
  that repeated tuples cancel and that the ordered-tuple
  alternating trace is 24 times the sorted-wedge trace. The
  physical raw alternating trace is therefore 384 times the
  quadratic trace of the normalized exterior compression.
- [Rank7SectorDefectAccounting.lean](Rank7SectorDefectAccounting.lean)
  derives the scalar sector equations and the coefficients 168
  and 96. [Rank7ComputationalExterior.lean](Rank7ComputationalExterior.lean)
  proves the seven computational columns are orthonormal and
  that their actual compressed Pauli projector is the diagonal
  indicator of zero-XOR four-subsets. Its compression loss is zero.
  [Rank7ComputationalPurity.lean](Rank7ComputationalPurity.lean)
  independently computes the actual computational purity as the
  stated polynomial, with coefficients 1, 14, and 168 for the
  single-site, two-site, and affine-plane monomials.
- [Rank7PhysicalDefectAssembly.lean](Rank7PhysicalDefectAssembly.lean)
  combines the sector decomposition, alternating trace, and
  verified computational reference to prove the exact physical
  purity difference \(168E-\mathcal D-96\mathcal D_F\). The
  combined defect vanishes at the computational frame. The full
  orbital purity comparison for unequal or equal cuts follows
  from two instances of `PairedDefectBound` on the physical
  frames. The module also proves that squaring the paired state
  squares its eigen-amplitudes for orthonormal frames and
  identifies Pauli trace coefficients in the seven-column source.
- [Rank7SymmetricDefect.lean](Rank7SymmetricDefect.lean) proves
  Pauli character orthogonality, a physical Fourier identity and
  the single-transposition reduction of the symmetric-minus-
  alternating trace. This gives an exact sum-of-squares formula
  for the symmetric correction of the assembled physical purity,
  with no assumed sector identity or sign.
- [Rank7MixedDefect.lean](Rank7MixedDefect.lean) checks the edge
  and triangle sum of squares and the second quadratic residual
  for finite Hermitian matrices, and obtains the exact factors
  in the mixed certificate. The explicit projection in odd
  Pauli word coordinates is proved idempotent.
  [Rank7PhysicalMixedFrame.lean](Rank7PhysicalMixedFrame.lean)
  constructs that frame from the actual Pauli matrices and
  evaluates the fourth trace and the sum of the mixed and
  alternating traces. [Rank7PhysicalMixedSpectrum.lean](Rank7PhysicalMixedSpectrum.lean)
  reduces the fourth trace to the exact rank-seven spectrum.
  [Rank7WedgeSquareIntertwiner.lean](Rank7WedgeSquareIntertwiner.lean)
  proves both Gram identities for the wedge-square columns.
  [Rank7MixedTransport.lean](Rank7MixedTransport.lean) proves the
  alternating and overlap trace transports. These give the
  physical mixed defect sum of squares and its nonnegativity
  in [Rank7PhysicalMixedDefect.lean](Rank7PhysicalMixedDefect.lean).
- [Rank7AnticommutingDefect.lean](Rank7AnticommutingDefect.lean)
  evaluates the quartic phase sums and proves the character
  square-norm inequality. [Rank7PauliEdgeBlocks.lean](Rank7PauliEdgeBlocks.lean)
  proves the corresponding inequality on complements of actual
  Pauli word pairs, using restricted character orthogonality.
  [Rank7PhysicalAntiQuartic.lean](Rank7PhysicalAntiQuartic.lean)
  derives the physical grouped quartic directly from Pauli
  matrix multiplication and its alternating trace.
  [Rank7PhysicalEdgeSwitching.lean](Rank7PhysicalEdgeSwitching.lean)
  computes the actual cyclic Pauli phase and proves the
  nonnegativity of the switched block.
  [Rank7AntiPairIncidence.lean](Rank7AntiPairIncidence.lean) and
  [Rank7AntiPlaneIncidence.lean](Rank7AntiPlaneIncidence.lean)
  prove the exact multiplicities of pairs and planes.
  [Rank7AntiDefectTransport.lean](Rank7AntiDefectTransport.lean)
  transports the expansion to the physical rank-seven defect
  and proves that it pays four divided by the local dimension
  times the full unordered anticommuting mass. The proof applies
  to every orthonormal seven-column frame.
- [Rank7PhysicalComparison.lean](Rank7PhysicalComparison.lean)
  proves all three physical Pauli defects are nonnegative and
  combines them with the nonnegative compression loss. It
  proves the paired purity comparison whenever the physical
  exterior gain is nonpositive. It also proves the comparison
  when the compression loss alone pays the gain.
- [Rank7JointProbePayment.lean](Rank7JointProbePayment.lean)
  proves the exact joint defect accounting for the actual shared and
  highest-pair Pauli probes of any orthonormal seven-frame. The same
  squared coordinate residual occurs with coefficients 16 and 8 in
  the mixed and anticommuting defects. Shifting the combined square
  with coefficient 24 produces both payments and their cross term.
  The linear pair polarization is also identified with physical
  traces and with the actual Pauli matching score and pair weights.
  [Rank7ProjectedProbeOverlap.lean](Rank7ProjectedProbeOverlap.lean)
  identifies the projected overlap trace with the actual weighted
  four-wedge sum. [Rank7JointProbeGram.lean](Rank7JointProbeGram.lean)
  proves the two probe norms and their cross term in the manuscript
  normalization.
- [Rank7OddSkewContraction.lean](Rank7OddSkewContraction.lean)
  constructs a nonzero kernel vector for any odd-order complex skew
  matrix by two-pivot elimination. If the matrix is a contraction,
  projection orthogonal to the kernel vector proves a squared
  Frobenius norm bound of order minus one.
  [Rank7PauliPairContraction.lean](Rank7PauliPairContraction.lean)
  proves physical odd-Pauli compression is skew and contractive on
  every subset of Schmidt labels. Together with the finite coefficient
  certificate in [Rank7PauliMatchingPrices.lean](Rank7PauliMatchingPrices.lean),
  this proves both per-word physical matching prices for every ordered
  seven-point spectrum. [Rank7WeightedProbeShift.lean](Rank7WeightedProbeShift.lean)
  inserts both prices into the same physical defect square and proves
  the basic moment order and six-point mass bound.
  [Rank7PauliReserveSlots.lean](Rank7PauliReserveSlots.lean)
  then retains 49 actual nonnegative anticommuting cut slots in the
  same defect bound. [Rank7ReserveMixedNorm.lean](Rank7ReserveMixedNorm.lean)
  bounds the mixed-sector projected norm by the matching reserve and
  proves simultaneous diagonal reserve bounds for two spectral cuts.
  [Rank7SixModeProbe.lean](Rank7SixModeProbe.lean) proves the six-mode
  polarization and a large-Gram bound.
  [Rank7SixPointRounding.lean](Rank7SixPointRounding.lean) supplies
  the directed row physically and proves the squared excess,
  sector price arithmetic, and Fourier error bounds. The small-Gram
  regime requires a physical sector with the normalized mass, trace
  bound, and Pauli weight bounds used by that estimate.
- [Rank7OddCutReserve.lean](Rank7OddCutReserve.lean) proves the
  actual rank-one Pauli leakage and the disjoint reserve payment
  given the corresponding odd-cut leakage at ranks three, five,
  and seven. [Rank7PhysicalTailBlend.lean](Rank7PhysicalTailBlend.lean)
  identifies the physical blended payment and the coefficient of
  the quadratic share, including the vanishing-tail case.
  Its diagonal-reserve version is unconditional. The strengthened
  receipt requires the remaining per-word odd-cut leakage and the
  rounded small-Gram sector. [Rank7OddTensorUncertainty.lean](Rank7OddTensorUncertainty.lean)
  now proves the real Pauli expectation bound on arbitrary odd
  tensor powers. [Rank7SlaterAlternant.lean](Rank7SlaterAlternant.lean)
  constructs the highest alternating eigenvector and proves its
  eigenvalue is the determinant. [Rank7SlaterUnionBound.lean](Rank7SlaterUnionBound.lean)
  connects the determinant to the one-leg projection loss, and
  [Rank7PhysicalOddLeakage.lean](Rank7PhysicalOddLeakage.lean)
  proves the required bound for all physical anticommuting pairs
  on arbitrary odd-rank orthonormal frames.
  [Rank7PhysicalOddTail.lean](Rank7PhysicalOddTail.lean)
  discharges the leakage premises for the signed tail receipt
  and the large-Gram blended payment. The small-Gram construction
  below supplies the rounded sector witness for the same blend.
  [Rank7ThreeLegFourier.lean](Rank7ThreeLegFourier.lean) proves the
  pointwise cross-term loss bounds `4/5` and `11/15` for the
  actual Pauli compression of any orthonormal three-column frame.
  The stronger bound applies where the squared expectation on the
  leading column is at most one half.
  [Rank7HeadPauliFourier.lean](Rank7HeadPauliFourier.lean) proves
  the ordinary and twisted transforms of the physical coefficients
  and the signed Parseval correction for the odd phase.
  [Rank7PhysicalFourierDefect.lean](Rank7PhysicalFourierDefect.lean)
  proves the global identity and the weak-mass bound for the actual
  compression. [Rank7HeavyPauliGroup.lean](Rank7HeavyPauliGroup.lean)
  constructs a maximal commuting group containing all labels with
  large leading expectation and bounds the middle mass outside it.
  [Rank7StabilizerCharacterBasis.lean](Rank7StabilizerCharacterBasis.lean)
  constructs a consistent lift to signed Pauli words and proves that
  the character projectors have trace one and are pairwise
  orthogonal on distinct cosets.
  [Rank7StabilizerCosetTransform.lean](Rank7StabilizerCosetTransform.lean)
  enumerates the character lines once each and proves their finite
  Parseval and population identities.
  [Rank7StabilizerPopulationRounding.lean](Rank7StabilizerPopulationRounding.lean)
  finds two distinct physical character lines whose missed middle
  weight is at most \(60\kappa/7\).
  [Rank7StabilizerSmallCodes.lean](Rank7StabilizerSmallCodes.lean)
  constructs the two disjoint parallel trace-two codes at
  \(200\kappa\le11\).
  [Rank7StabilizerOddSector.lean](Rank7StabilizerOddSector.lean)
  constructs their odd Pauli sector of normalized mass two, and
  [Rank7StabilizerSectorKernel.lean](Rank7StabilizerSectorKernel.lean)
  proves the exact restricted completeness formula on either coset.
  [Rank7StabilizerExteriorTrace.lean](Rank7StabilizerExteriorTrace.lean)
  bounds the exterior two-form trace on one coset.
  [Rank7CharacterFourOrbits.lean](Rank7CharacterFourOrbits.lean)
  adds the two matchings and proves the actual six-mode sector
  trace is at most five. [Rank7FiniteProjectionAngles.lean](Rank7FiniteProjectionAngles.lean)
  proves the generic two-sided projection estimates.
  [Rank7PhysicalProjectionAngles.lean](Rank7PhysicalProjectionAngles.lean)
  transports them to the actual Pauli weights and constructs
  the required small-Gram sector. It proves
  \(11\,\mathrm{sixMass}\le55+200\kappa\) in every Gram regime.
  [Rank7PhysicalUniformTail.lean](Rank7PhysicalUniformTail.lean)
  applies this bound to the actual frame and proves the blended
  tail receipt with both odd-cut and rounded-sector inputs
  discharged.
  [Rank7PhysicalEndpointPauli.lean](Rank7PhysicalEndpointPauli.lean)
  proves the reverse highest-pair term and connects the normalized
  upper rectangle's shared and highest shifts to the actual same-frame
  Pauli defect. The remaining Pauli reserve stays explicit in the
  theorem.
  [Rank7EndpointReserveSlots.lean](Rank7EndpointReserveSlots.lean)
  isolates disjoint reserve terms and pays the full highest-pair
  coefficient on that frame.
  [Rank7SharedTwoSlotReserve.lean](Rank7SharedTwoSlotReserve.lean)
  and [Rank7PhysicalEndpointReserve.lean](Rank7PhysicalEndpointReserve.lean)
  prove the corresponding shared reserve and combine all of the
  upper endpoint's Pauli terms.
  [Rank7PhysicalEndpointPrice.lean](Rank7PhysicalEndpointPrice.lean)
  identifies the remainder with the checker price using the two
  stated Gram-to-excess bounds.
  [Rank7EndpointLargeGrams.lean](Rank7EndpointLargeGrams.lean)
  derives those bounds in the two large Gram regimes.
  [Rank7HighestAnchorCommutation.lean](Rank7HighestAnchorCommutation.lean)
  localizes the highest small Gram branch to a physical commuting
  coset. The small Gram geometric bounds still need to be completed.
- [Rank7JointTracePrices.lean](Rank7JointTracePrices.lean)
  proves the two ratio prices from the scalar trace capacities,
  their concavity on the bounded segments, and positivity on
  the last unbounded ray from its initial value and slope.
  These are scalar bounds and still need the physical cut
  trace and compression estimates that produce their inputs.
- [Rank7CompressionCuts.lean](Rank7CompressionCuts.lean) connects
  the [Hermitian trace loss](Rank7Compression.lean) to the two
  [actual rank-seven spectral cuts](Rank7ExteriorCuts.lean).
  It checks all 35 four-wedge labels and the two crossing-error
  supports of sizes six and three. The off-diagonal row cap follows
  from the diagonal contraction slack. The
  [fractional trace bound](Rank7TraceRounding.lean) is verified
  for any finite list of eigenvalues in [0,1].
  [Rank7HermitianCoordinates.lean](Rank7HermitianCoordinates.lean)
  derives diagonal contraction slack from the positive-effect
  condition on the explicit real and imaginary coordinates, and
  feeds it into the two-cut comparison.
- [Rank7CutTrace.lean](Rank7CutTrace.lean) proves that each principal
  cut of the physical positive contraction is a positive contraction
  and identifies the exact crossed-cut cost with its trace variance.
  Given a unitary diagonalization on the selected coordinates, the
  eigenvalues lie in [0,1] and the fractional-trace bound applies.
  The [real spectrum package](real/README.md) obtains the
  diagonalization for actual complex matrices from pinned Mathlib
  and proves the physical cut bound without a spectral witness
  argument. It now derives the two actual nested trace prices and
  charges both affine supports to the same compression, with the
  nominal outside tax explicit. On the normalized upper tied chart,
  the highest tax vanishes and only the 1234 wedge can contribute to
  the shared tax, with the exact allowance used by the checker.
- [Rank7PhysicalCutCapacities.lean](Rank7PhysicalCutCapacities.lean)
  evaluates the one-hole marginal of the actual signed exterior Pauli
  kernel in arbitrary qubit dimension. For any three distinct
  columns of an orthonormal seven-frame, the odd-Pauli mass of their
  three-column contraction sums to the exact marginal. The Bessel
  inequality for its projection to frame columns proves the exact
  capacity on the weighted four-wedge diagonals for every triple
  of Schmidt labels. [Rank7PhysicalPairExchange.lean](Rank7PhysicalPairExchange.lean),
  [Rank7PhysicalHopping.lean](Rank7PhysicalHopping.lean),
  [Rank7PhysicalCompressedSwap.lean](Rank7PhysicalCompressedSwap.lean)
  and [Rank7PhysicalUniformOccupation.lean](Rank7PhysicalUniformOccupation.lean)
  prove the physical exchange and the three norm estimates for the
  directed calculation. [Rank7FiveShuffleCAR.lean](Rank7FiveShuffleCAR.lean)
  proves the five-slot shuffle identity including all multiplicities.
  [Rank7FiveFrameContractions.lean](Rank7FiveFrameContractions.lean)
  connects its exchange terms to the actual anchored Pauli field.
  [Rank7PhysicalTwoLinkBound.lean](Rank7PhysicalTwoLinkBound.lean)
  proves the physical operator norm with arbitrary complex source
  coefficients. [Rank7FiveVolumeBessel.lean](Rank7FiveVolumeBessel.lean)
  extracts the adjoint at the unit five-mode volume, and
  [Rank7PhysicalDirectedCapacity.lean](Rank7PhysicalDirectedCapacity.lean)
  proves all 42 directed capacity rows for every orthonormal
  seven-column frame and every allowed ambient qubit dimension.
  [Rank7PhysicalOmittedPair.lean](Rank7PhysicalOmittedPair.lean)
  expresses the actual omitted-pair row as a normalized
  common-spectator five-form trace. For every orthonormal seven-column
  frame in a three-qubit space the normalized row equals one.
  [Rank7PhysicalEightForm.lean](Rank7PhysicalEightForm.lean) proves
  the unique-spectator coefficient with its signed exterior
  orientation. [Rank7PhysicalTwoHoleTransport.lean](Rank7PhysicalTwoHoleTransport.lean)
  verifies the exact normal-order identity.
  [Rank7PhysicalEightTransport.lean](Rank7PhysicalEightTransport.lean)
  proves the cross-boundary sign change, and
  [Rank7TwoHolePhysicalTransportIdentity.lean](Rank7TwoHolePhysicalTransportIdentity.lean)
  gives the actual bilinear transport in arbitrary dimension.
  [Rank7TwoHoleReducingBlock.lean](Rank7TwoHoleReducingBlock.lean)
  verifies the reducing-block argument given its operator identities.
  [Rank7PhysicalTwoHoleOccupancy.lean](Rank7PhysicalTwoHoleOccupancy.lean)
  and [Rank7TwoHolePhysicalExchange.lean](Rank7TwoHolePhysicalExchange.lean)
  verify the actual occupation Gram identities and coefficient
  intertwinings. [Rank7PhysicalC2Synthesis.lean](Rank7PhysicalC2Synthesis.lean)
  proves the norm on the physical complementary synthesis, and
  [Rank7PhysicalC2Adjoint.lean](Rank7PhysicalC2Adjoint.lean) proves
  its adjoint estimate in odd-Pauli coordinates.
  [Rank7PhysicalC2Projected.lean](Rank7PhysicalC2Projected.lean)
  and [Rank7PhysicalProjectedTransport.lean](Rank7PhysicalProjectedTransport.lean)
  establish the projected complement bound and transport.
  [Rank7PhysicalWaveReproduction.lean](Rank7PhysicalWaveReproduction.lean)
  proves the physical tight-frame constant in ordered coordinates.
  [Rank7ComplexFiniteRangeBound.lean](Rank7ComplexFiniteRangeBound.lean)
  gives the complex Bessel assembly from the eigen-row identities.
  [Rank7PhysicalTwoHoleEigen.lean](Rank7PhysicalTwoHoleEigen.lean)
  proves those identities for the actual columns, and
  [Rank7PhysicalTwoHoleUpper.lean](Rank7PhysicalTwoHoleUpper.lean)
  uses [the five-face test](Rank7FiveFaceCapacity.lean) to prove
  all 21 omitted-pair capacities in every allowed local dimension.
- [Rank7PackingDual.lean](Rank7PackingDual.lean) verifies the linear
  programming dual inequality, sixteen geometric block certificates,
  all 205 regular quartic forward coefficients, and four weighted
  corners for each of 48 specified monomials. The costs are checked on
  the 35 rank-seven wedges. The geometric prices and objectives were
  also compared against [the source certificate](../certificates/rank7/rank7_uniform_cut_packing.json).
  [Rank7PackingInterpolation.lean](Rank7PackingInterpolation.lean)
  proves zero correction on the remaining 127 tail monomials,
  the resulting inequality on the full two-parameter probe square,
  and the signed forward debit including all five exceptions.
  [Rank7PackingPolynomial.lean](Rank7PackingPolynomial.lean)
  identifies all 210 forward monomials with the actual physical
  exterior gain. The physical signed and restored inequalities now
  prove all 98 legal packing rows internally, for every orthonormal
  seven-frame in any allowed local dimension.
- [Rank7Interval.lean](Rank7Interval.lean) proves outward rounding for
  the C++ verifier's fixed-point arithmetic, including signed
  multiplication, division by a positive interval, squaring,
  minimum, maximum and the positive part. It also checks a proposed
  integer square root, the upper verifier's discount prune, the
  two-ray mixing predicate, and bilinear interpolation on a rectangle.
- [Rank7UpperAnalytic.lean](Rank7UpperAnalytic.lean) proves the 1/13
  floor used in the upper verifier's shared price, the affine lower
  tangent used for the odd reserve, and the support-price inequality
  and monotonicity used for both trace cuts.
- [Rank7UpperCorner.lean](Rank7UpperCorner.lean) evaluates the upper
  verifier's signed corner margins on the scale 2^27.
  [Rank7CornerSample.lean](Rank7CornerSample.lean) independently
  recomputes 96 lower-endpoint records for one contracted box from
  the C++ traversal of [144/256, 145/256], matching every recorded
  endpoint. Kernel computation accepts all 24 mixes across the six
  adjacent-ray sectors and four corners. Two tests need positive
  weights on both payments. The
  [extractor](extract_rank7_corner_sample.py) reproduces the sample
  from the original C++ files with `g++` and Python, via a temporary
  instrumented copy. Run `python lean/extract_rank7_corner_sample.py`
  from the project root.
- [Rank7UpperContractor.lean](Rank7UpperContractor.lean) verifies
  that the upper verifier's actual rounded contractor preserves
  every point satisfying its explicit residual inequalities,
  including each rejection and empty-interval test.
  [Rank7UpperOldRegions.lean](Rank7UpperOldRegions.lean) verifies
  that the ten integer guard tests imply their actual real signs.
  Their physical branch comparisons are separate obligations.
- [Rank7UpperPrices.lean](Rank7UpperPrices.lean) checks the common
  shared shift, its clipped zero case, the tail reserve bound and
  monotonicity, the two trace support weights and the common
  multiaffine lower price. [Rank7BoxTraversal.lean](Rank7BoxTraversal.lean)
  proves that the rounded midpoint implements the C++ truncation
  on an ordered interval and that the children cover the parent.
  The recursive traversal theorem accepts a contractor and leaf
  test with proved soundness. The corner theorem combines the
  two boundary rays and allows different mixing weights at the
  four corners while interpolating the common margin.

- [Rank7UpperWeighted.lean](Rank7UpperWeighted.lean) proves enclosure
  of the C++ weighted margin, including the rational lower price of
  the squared positive-part square-root gap. Integer acceptance
  guarantees strictly positive real margin at an allowed shift.
  Failure of the real unit-shift comparison gives the two strict
  polynomial residual bounds when the completion is positive.
  [Rank7UpperResidual.lean](Rank7UpperResidual.lean) derives the head
  product bounds and the two ordered upper endpoint caps from these
  inequalities. Failure of the real old-region and unit-shift tests
  implies the exact contractor residual on the stated normalized
  branch.
- [Rank7UpperReplay.lean](Rank7UpperReplay.lean) implements the upper
  decision order, the four-corner sector search, the weighted split
  axis, and the recursive replay from the C++ initial boxes.
  The coverage theorem proves that a successful replay routes every
  residual point to one of the three branch implications. Those
  implications still require the physical comparisons. The normalized
  starting domain is proved to lie in the C++ root box.
  [Rank7UpperReplaySample.lean](Rank7UpperReplaySample.lean) independently
  recomputes the C++ starting box, first split axis, one example each
  of contractor rejection and the three acceptance branches, and
  one actual split with two accepted children. The sample weighted
  margin matches both integer endpoints. The inputs are reproduced
  by running [the extractor](extract_rank7_replay_sample.py) with
  `python lean/extract_rank7_replay_sample.py` from the project root.
  [Rank7UpperHintReplay.lean](Rank7UpperHintReplay.lean) proves that
  a successful split-and-shift plan implies success of the original
  replay. Lean recomputes the contractor and the split and verifies
  each proposed leaf. The [535-leaf fixture](../certificates/rank7/upper_hint_replay_sample/RESULTS.md)
  passed kernel checking as one tree and in 30 shards.
  [Rank7UpperHintShards.lean](Rank7UpperHintShards.lean) verifies the
  recombination of two shard proofs after checking their endpoints.
  [Rank7UpperEndpoint.lean](Rank7UpperEndpoint.lean) proves real
  enclosures for both margins at all 28 corner–ray pairs.
  [Rank7UpperEndpointPrices.lean](Rank7UpperEndpointPrices.lean)
  identifies the physical price contribution as multiaffine in the
  two tail coordinates.
  [Rank7UpperInterior.lean](Rank7UpperInterior.lean) proves the strict
  comparison throughout a box when the two geometric estimates
  bound the same gain at its corners.
  [Rank7UpperFrameGain.lean](Rank7UpperFrameGain.lean) constructs
  the actual fixed-frame gain polynomial, and
  [Rank7UpperRayCones.lean](Rank7UpperRayCones.lean) proves coverage by
  the six sector cones and both corresponding trace-price bounds.
  [Rank7UpperRayGeometry.lean](Rank7UpperRayGeometry.lean) identifies
  the maximum and positive-part expressions on every cone.
  [Rank7UpperPhysicalInterior.lean](Rank7UpperPhysicalInterior.lean)
  assembles these facts for the same frame at an interior spectrum.
  It requires the two physical geometric gain estimates at each
  corner and the stated physical trace lower bounds.
  [Rank7UpperPhysicalReplay.lean](Rank7UpperPhysicalReplay.lean)
  starts from a successful original replay and preserves the
  ordered-tail domain while routing to the old, weighted, or
  physical interior comparison.
  [Rank7UpperFrameTrace.lean](Rank7UpperFrameTrace.lean) derives
  the shared trace products from the actual physical packing rows.
  [Rank7UpperPairLoss.lean](Rank7UpperPairLoss.lean)
  proves the per-Pauli odd-cut loss.
  [Rank7UpperPairCap.lean](Rank7UpperPairCap.lean) sums it over the
  odd words and proves \(3L_{01}\le7\) on every actual orthonormal
  frame. [Rank7UpperPairReplay.lean](Rank7UpperPairReplay.lean)
  consumes original replay and derives its required leading-pair
  cap internally.
  [Rank7UpperCertifiedExterior.lean](Rank7UpperCertifiedExterior.lean)
  proves both signed exterior corner estimates under the normalized
  slab's head bound. The kernel checks the exact certificate
  correspondence for all 13,104 coefficients.
  [Rank7UpperCertifiedFrameReplay.lean](Rank7UpperCertifiedFrameReplay.lean)
  derives both exterior estimates and the pair cap internally for
  the original replay, with the head bound following from initial
  slab membership.
  [Rank7UpperPointMargin.lean](Rank7UpperPointMargin.lean) proves the
  point-specialized margin table exactly equals the original table.
  The hint checker now uses this evaluator and preserves the
  original acceptance result.
  [Rank7UpperNearCollar.lean](Rank7UpperNearCollar.lean) also uses
  the necessary residual cut \(101d\le 100c\) to safely narrow the
  sixth-weight interval before evaluating a common shift. The
  [535-leaf root](../certificates/rank7/upper_hint_replay_sample/Fixed535.lean)
  then yields all six sector witnesses from a single box. This
  certifies that sample's residual coverage by the corner
  criterion. The physical leaf conclusion is still separate.
  [Rank7UpperNearBands.lean](Rank7UpperNearBands.lean) allows the
  same clip after bisecting the seventh-weight interval alone.
  Lean checks 44 actual subtree paths and their residual corner
  covers across all 14 archived upper slab ranges.
  [Rank7UpperCoveredTree.lean](Rank7UpperCoveredTree.lean)
  combines original, clipped, and banded proofs in one tree.
  [Rank7UpperCoveredFrame.lean](Rank7UpperCoveredFrame.lean)
  preserves the physical tail bounds on every accepted region
  and routes a successful mixed certificate to the same
  fixed-frame result as original replay.
  [Rank7UpperFrontier.lean](Rank7UpperFrontier.lean) verifies bounded
  partial covers and replaces completed open boxes without
  replaying earlier proofs. The actual `[144,145]/256` slab
  has a checked cover with nine explicit unresolved boxes.
  [Rank7UpperAdaptiveSplit.lean](Rank7UpperAdaptiveSplit.lean) checks
  the contractor and both children for a chosen-coordinate split.
  The [physical ledger](../certificates/rank7/upper_hint_replay_sample/frontier/AxisCertifiedLedger.lean)
  closes one additional subtree. Both the 71-leaf original split
  and the 25-leaf adaptive split certify this same subtree.
  The [nine-box ledger](../certificates/rank7/upper_hint_replay_sample/frontier/SectorCertifiedLedger.lean)
  then closes one more box using 118 leaves and 117 checked splits.
  The [real physical ledger](../certificates/rank7/upper_hint_replay_sample/real_frontier/SectorRealPhysicalLedger.lean)
  applies the paired-defect inequality to its accepted signed corners
  when the shared Gram meets its large-branch threshold.
  [Rank7UpperDomainFrontierFrame.lean](Rank7UpperDomainFrontierFrame.lean)
  applies the conditional fixed-frame comparison to covered points
  and preserves the physical tail bounds on each remaining box.
- [Rank7LowerContractor.lean](Rank7LowerContractor.lean) implements
  and proves sound every lower C++ contractor clamp and both
  empty-box exits for the stated normalized residual conditions.
  [Rank7LowerContractorSample.lean](Rank7LowerContractorSample.lean)
  matches the exact C++ integer endpoints of the six canonical initial
  boxes and their first contractions. Regenerate them with
  `python lean/extract_rank7_lower_contractor.py` from the project root.
- [Rank7LowerLeaves.lean](Rank7LowerLeaves.lean) proves all eight
  lower old-region signs and the outward weighted leaf margin.
  The real guard failure implies the lower contractor residual.
  [Rank7Interval.lean](Rank7Interval.lean) certifies the integer
  square root and the corresponding directed interval.
  [Rank7LowerCorner.lean](Rank7LowerCorner.lean) encloses the exact
  conjugate-root widths, common prices, and all split and singleton
  margins at both shared endpoints on seven rays. For every point
  in an evaluated box with the four exact roots, integer acceptance
  supplies a shared shift choice and a positive real mix at the
  boundary rays of each sector at each endpoint.
  [Rank7LowerReplay.lean](Rank7LowerReplay.lean) proves residual
  coverage given successful replay and the physical leaf implications.
  [Rank7LowerReplaySample.lean](Rank7LowerReplaySample.lean) checks four
  classification cases, both weighted endpoints and all 28 shared
  numbers for the sampled shift. Regenerate the C++ inputs with
  `python lean/extract_rank7_lower_leaf_sample.py`.
  [Rank7LowerSignedExterior.lean](Rank7LowerSignedExterior.lean)
  checks the exact signed split and singleton bounds at both
  real endpoints for the same fixed frame and shift.
  [Rank7LowerCertifiedFrameReplay.lean](Rank7LowerCertifiedFrameReplay.lean)
  gives the strict physical exterior gain comparison against the
  scalar shared payment for each interior tail point on the shared
  branch of a successful slab replay.
  [Rank7LowerPhysicalGainScale.lean](Rank7LowerPhysicalGainScale.lean)
  identifies the comparison numerator on the original spectrum.
  [Rank7RealLowerCutPrice.lean](real/Rank7RealLowerCutPrice.lean)
  proves the physical shared compression price at the full nominal
  cut width, with the exact 1234 allowance.
  [Rank7LowerPhysicalPauliSlots.lean](Rank7LowerPhysicalPauliSlots.lean)
  proves the simultaneous actual Pauli leading and rank-six payments.
  [Rank7RealLowerPhysicalComparison.lean](real/Rank7RealLowerPhysicalComparison.lean)
  combines these prices and cancels the entering-wedge term exactly.
  On a successful slab replay, the shared exit gives the physical
  paired-defect inequality. The large-Gram entry point constructs
  the four roots and discharges both geometry bounds internally.
  [Rank7RealLowerSmallHead.lean](real/Rank7RealLowerSmallHead.lean)
  closes the old small-head exit on the raw spectrum for every
  orthonormal frame when `x+2*y <= 1`. It uses the ordered
  tail triangle and verifies 100 exact packing certificates.
  [Rank7RealLowerAllWeighted.lean](real/Rank7RealLowerAllWeighted.lean)
  handles all four accepted lower weighted shifts when
  `z*(x-1)-3*x-5/2 <= 0` and `x^2 <= 5*z^2`, under the stated
  actual Gram-to-excess inequalities.
- [Rank7HighestCodeLocalization.lean](Rank7HighestCodeLocalization.lean)
  locates an actual paired-character code of dimension two in the
  highest small-Gram regime. Its population exceeds 3/4 and the
  paired squared transition exceeds 9/16.
  [Rank7HighestCodeTransport.lean](Rank7HighestCodeTransport.lean)
  identifies this population with the projection of the first two
  physical frame columns and gives the exterior-coset cap
  `4*b*(1-b)` for squared amplitudes.
  [Rank7HighestCosetFourier.lean](Rank7HighestCosetFourier.lean)
  identifies the centered Fourier mean on the paired code and bounds
  each squared inside-coset residual by `(1-b)^2`.
  [Rank7HighestPhysicalConcentration.lean](Rank7HighestPhysicalConcentration.lean)
  now proves the integrated moment bound and selects a physical
  stabilizer plane with total head-column population above 19/10.
  [Rank7HighestExteriorComponents.lean](Rank7HighestExteriorComponents.lean)
  supplies the exact four-component source Gram and occupation bounds.
  [Rank7HighestTailTransfer.lean](Rank7HighestTailTransfer.lean)
  identifies the linear exterior output with the physical link.
  [Rank7HighestTransferBound.lean](Rank7HighestTransferBound.lean)
  proves the uniform 5/2 norm bound for the actual linear tail output.
  [Rank7HighestAnchorVectors.lean](Rank7HighestAnchorVectors.lean)
  reduces the small-Gram link bound to one physical stabilizer line
  and an arbitrary partner, through explicit anchor factorizations.
  [Rank7HighestAnchorPauliTrace.lean](Rank7HighestAnchorPauliTrace.lean)
  expresses the anchored tail output in literal all-word Pauli minors.
  [Rank7AnchorExteriorHomogeneous.lean](Rank7AnchorExteriorHomogeneous.lean)
  proves the homogeneous character occupation inequality. The
  [physical derivation](../proof/rank7_highest_anchor_lean_bridge.md)
  records the coordinate route to the physical comparison.
  [Rank7AnchorAllFock.lean](Rank7AnchorAllFock.lean) proves the triple
  contraction and occupation score for arbitrary tails of degree at
  most five. [Rank7HighestScaledSlater.lean](Rank7HighestScaledSlater.lean)
  identifies the bound with ten minors on actual orthogonal tail
  columns of common squared norm.
  [Rank7HighestAnchorCoefficient.lean](Rank7HighestAnchorCoefficient.lean)
  completes the actual Pauli transport and proves `2*v <= 5*kappaOne`
  for every orthonormal physical rank-seven frame and every weight
  vector. The [proof summary](../certificates/rank7/highestPhysicalPrice.md)
  gives the character, orbit, and finite coefficient steps.
- [Rank7SharedCharacterHeadPrice.lean](Rank7SharedCharacterHeadPrice.lean)
  gives the sharp head price on the commuting half-group, bounds
  actual head expectations off the two preserving cosets, and sums
  the disjoint terms in the exact diagonal Fourier defect.
  [Rank7SharedSmallGramScalar.lean](Rank7SharedSmallGramScalar.lean)
  verifies the leakage constants under the stated exterior hypotheses.
  [Rank7SharedMiddleCosets.lean](Rank7SharedMiddleCosets.lean)
  proves the exact complementary-coset middle cross-mass bound
  and obtains physical weighted code leakage below 1/7 whenever
  `24*kappa <= 1`. [Rank7SharedRoundedSector.lean](Rank7SharedRoundedSector.lean)
  proves that the selected codes are disjoint and parallel. The
  odd-Pauli weight outside the selected cosets is at most `7*kappa/11`.
  [Rank7SharedUnionTransport.lean](Rank7SharedUnionTransport.lean)
  checks the four-site projector, proves that every selected odd
  Pauli test gives zero amplitude between its range and complement,
  and bounds the crossed tensor mass using the two physical column
  leakages. [Rank7SharedOddLeakage.lean](Rank7SharedOddLeakage.lean)
  proves Parseval on the skew sector and uses the vanishing selected
  coefficients to charge the crossed mass to the complementary odd
  words. For every orthonormal physical seven-frame with
  `24*kappa <= 1`, it constructs a four-character union whose weighted
  leakage `E = outsideEnergy(1) + outsideEnergy(2) + 2*outsideEnergy(0)`
  satisfies `297*E <= 196*kappa`.
  [Rank7SharedExteriorStability.lean](Rank7SharedExteriorStability.lean)
  checks that the five-site occupation tests count each coordinate
  at most four times. It proves the quadratic bound `excess <= 18*E`
  from the one-outside cross estimate and the norm bounds on the
  exterior components.

The main module [RankSeven.lean](RankSeven.lean) imports the checks.
The audited dependencies comprise Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The numerical equality for the
sample uses only `propext`, and its mix-predicate result has no axioms.

## Requirements for a full Lean proof

1. Extend the signed physical comparisons to the small shared-Gram
   regime. [Rank7RealPhysicalHighest.lean](real/Rank7RealPhysicalHighest.lean)
   now pays the highest-pair geometry from the actual frame and
   closes the signed comparisons on `24*kappa >= 1`. On the other
   shared branch, prove the color restriction and bound the actual
   one-outside Pauli cross terms to instantiate `excess <= 18*E`
   for the four-character union chosen above.
   Prove the analytic anchor regions,
   transfers, and necessity of contractor residuals.
2. Prove the physical implications for the remaining old and weighted
   classifications. Extend the certificates to every slab and every
   box, including Boolean replay success for the lower shared exit.
3. Use the resulting analytic and box certificates for both
   paired comparison inputs of
   `rankSevenComputationalComparisonOfDefects` and the entropy result.
   The existing C++ receipts store
   counts and completion summaries for the central 127,384,781 leaves.
   The receipt-union script checks the reported region intervals and
   completion summaries. Lean has replayed the arithmetic and mixing
   tests for one contracted box, the five upper traversal cases,
   and the small split subtree.
   The conditional regional comparisons also rely on the other
   computational cells and the analytic anchor regions.

The [rank-seven report](../paper/rank7_submission.tex) is still partially formalized.
