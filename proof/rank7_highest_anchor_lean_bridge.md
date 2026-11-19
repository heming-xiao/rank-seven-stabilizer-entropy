# One stabilizer anchor and a five-dimensional tail

Let G be a maximal commuting Pauli-label group on n qubits, d=2^n, and let L be any signed commuting lift. Its d mutually orthogonal rank-one character blocks give a basis of character lines. Fix any one of these lines s. The physical exterior kernel on normalized wedges is the restriction of Π=d^−2 Σ_p W_p^{⊗4}, where W_p ranges over all Hermitian Pauli words. Put q=4/d. For a five-dimensional subspace Y with orthonormal basis u_i, and any v, the complex Hilbert-space inequality is

    Σ_{i<j} ||Π(s∧v∧u_i∧u_j)||² ≤ 2q ||s∧v||².                    (A)

The tail Y may meet either of the first two lines. The following proof also treats dimensions below five. The Lean status of each step appears at the end.

## The anchored physical Gram

Initially take s of norm one and v perpendicular to s. Label triples by three distinct character lines different from the anchor. Define P to be the coordinate projection onto triples T whose three characters multiply to the anchor character. In additive character notation this is T₁+T₂+T₃=s. Let C_s be exterior multiplication by s. Then

    0 ≤ C_s† Π C_s ≤ q P.                                             (B)

For the support inclusion, a fourfold product of character-projector columns outside the zero total character block is annihilated by the Pauli average. Translate the summed word p by a stabilizer label g that anticommutes with the total character. All four copies acquire the common Pauli cocycle, whose fourth power is one. Each input gains its physical lifted-g character and the product of the four signs is minus one. Hence the sum equals its negative. The calculation holds for arbitrary output coordinates and survives linear combinations and antisymmetrization. Rank-one character lines are spanned by their nonzero raw-projector columns.

For the norm, take any four-form Ψ with s occupied and write U_p=Λ⁴W_p and r=W_p s as a line. Occupation projections for s,r commute, since distinct character lines are orthogonal, and U_p interchanges them. Therefore

    <Ψ,U_p Ψ>=<n_r Ψ,U_p n_r Ψ> ≤ ||n_r Ψ||².

Indeed the component with r vacant on the left is orthogonal to U_p Ψ, where r is occupied; in the remaining term U_p can be applied after projecting onto r because s is occupied on the left. The right-hand inequality uses the real part or the absolute value and the unitarity of U_p. Every character line arises from exactly d words p. Since Σ_r n_r=4 on four-forms, averaging gives <Ψ,ΠΨ>≤q||Ψ||². The support statement applies to the component outside P; applying the norm result to C_s Pτ proves (B). This argument requires no restriction on the ambient one-particle support of τ.

## The creation score

The anchored triples form a Steiner system on the character lines different from s. For a set S of occupied sites let f(S) be the number of its anchored triples. If U is obtained from S by adjoining one site, then f(U)−f(S)≤floor(|S|/2). The pairs of S completing the added site are a matching because their opposite endpoints have a uniquely determined character modulo G.

For arbitrary complex Fock amplitudes ω supported in degrees through five, the exact superlevel argument yields

    <C_v ω,f C_v ω> ≤ ||v||² (<ω,fω>+2||ω||²).                      (C)

For every integer k≥0, the output of C_v on {f>k+2} depends only on the input on {f>k}. Exterior creation is norm-bounded by ||v|| from the CAR. Truncating first, then summing squared norms of all these thresholds, charges at most the two missing lowest levels. This proves (C) without orthogonality conditions or choice of a stochastic coupling. The finite list of sites may contain the anchor as an available site.

## Arbitrary tail position

By (B), the left-hand side of (A) divided by q is bounded by the sum over anchored coordinate triples of <β_T,Λ²P_Y β_T>, with β_T=a_v e_T. Every β_T is supported in v⊥. If v=0 the claim follows directly. Otherwise take W to be the image of P_{v⊥}Y. The compression P_{v⊥}P_Y P_{v⊥} is a positive contraction supported on W; its second exterior power is bounded by the projection onto Λ²W. This follows by diagonalizing the compression in W, or by exterior contractivity. It now suffices to bound Σ_T||a_{β_T}Ω||² where Ω is a unit volume form of W, since squared contraction on such a volume form equals the squared norm of the Λ²W projection. Here dim W≤5 and a_v Ω=0.

Set D_T=a_{e_T}. The triple CAR gives D_T C_v=a_{a_v e_T}−C_v D_T. Its two terms on Ω are orthogonal, because the first has no v occupancy and the second has v occupied. Moreover ||C_v D_TΩ||²=||v||²||D_TΩ||². Therefore

    Σ_T ||a_{β_T}Ω||² = <C_vΩ,f C_vΩ>−||v||²<Ω,fΩ> ≤ 2||v||².

The diagonal occupation sum equals f on each coordinate subset by definition. Applying (C) proves (A). Scaling s and projecting v into s⊥ leaves the claimed homogeneous inequality valid for every choice of s and v on the original complex Hilbert space.

## Checked boundaries and remaining Lean integration

* RankSeven.AnchorSteiner.insertion proves the character-triple increment for an arbitrary true transversal, anchor and ordering.
* RankSeven.AnchorSteinerTest.characterFiveTail proves the abstract contraction-and-insertion inequality, via superlevels. RankSeven.AnchorExteriorCreation.carGram proves exact CAR energy for the signed exterior creation/annihilation matrices on occupancy strings. RankSeven.AnchorExteriorHomogeneous.homogeneousCharacterFive proves (C) for the actual signed creation matrix with no normalization of v, and no assumed operator bound.
* RankSeven.AnchorCharacterSupport.physicalFourSelection proves vanishing of each off-plane product of actual physical character-projector columns under the all-word Pauli tensor average. The final call acts on each of the four input columns in computational coordinates.
* RankSeven.AnchorOrbitBound.orbitCount proves the exact size-d orbit multiplicity. RankSeven.AnchorOrbitBound.occupiedFourAverage proves the unscaled bound 4d times the mass for any four-occupation basis with the stated induced monomial, involutive, unit-phase action and the stated transported occupancy. The actual exterior Pauli action still needs to be instantiated at this interface in Lean.
* Remaining for RankSeven.HighestAnchorVectors.lineBound are the operator-level change from computational alternating Pauli minors to character occupations, realization of (B) by these support/norm theorems in that common basis, and the tail projection/triple CAR identity above in the measured transfer conventions. The companion agent owns the transfer-to-Pauli-minor identity. The end-to-end physical Lean theorem remains open.

Recheck.ps1 compiles all seven exact source files in dependency order, treating warnings as errors, with the source hashes checked before and after each Lean invocation. The log records all terminal axioms (propext, Classical.choice, Quot.sound). The source comparison and trace in this folder are separate from the mathematical argument above.
