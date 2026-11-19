import Rank7PhysicalPairedReduction
import Rank7PlaneOrientation

namespace RankSeven.RectangularPairedReduction

open Lean.Grind Pauli PhysicalPairedReduction ComplexPauliMoment
open ComplexScalar (star ofReal imaginaryUnit)

variable {R α β ι : Type} [CommRing R]

/-- The two Schmidt frames have the same finite column set. Their row sets
may have different dimensions. Only these columns enter the formula. -/
def coefficients (source : List ι) (U : α → ι → ComplexScalar R)
    (M : ι → ι → ComplexScalar R) (V : β → ι → ComplexScalar R) : α → β → ComplexScalar R :=
  matMul source (matMul source U M) (transpose V)

theorem conjugateCoefficients (source : List ι) (U : α → ι → ComplexScalar R)
    (M : ι → ι → ComplexScalar R) (V : β → ι → ComplexScalar R)
    (middleReal : conjugate M = M) :
    conjugate (coefficients source U M V) = coefficients source (conjugate U) M (conjugate V) := by
  unfold coefficients
  rw [conjugateMatMul, conjugateMatMul, middleReal]
  rfl

theorem fourCoefficients (source : List ι) (U : α → ι → ComplexScalar R)
    (M : ι → ι → ComplexScalar R) (V : β → ι → ComplexScalar R) :
    tensorFour (coefficients source U M V) =
      coefficients (fourIndices source) (tensorFour U) (tensorFour M) (tensorFour V) := by
  simp only [coefficients, fourMatMul, fourTranspose]

theorem rectangularFrameTrace (left : List α) (right : List β) (source : List ι)
    (U barU : α → ι → ComplexScalar R) (V barV : β → ι → ComplexScalar R)
    (H : ι → ι → ComplexScalar R) (J : α → α → ComplexScalar R)
    (K : β → β → ComplexScalar R) (hs : transpose H = H) (ks : transpose K = K) :
    coefficientTrace left right (coefficients source U H V) (coefficients source barU H barV) J K =
      pairedFrameTrace source H (matMul left (matMul left (transpose barU) J) U)
        (matMul right (matMul right (transpose V) K) barV) := by
  rw [coefficientTraceMatMul]
  simp only [coefficients, transposeMatMul, transposeTranspose, hs, ks, matMulAssoc]
  rw [traceMatMulSwap right source barV]
  simp only [pairedFrameTrace, matMulAssoc]

def scaleMatrix (c : ComplexScalar R) (A : α → β → ComplexScalar R) : α → β → ComplexScalar R :=
  fun i j => c * A i j

def normalizedFrame {n : Nat} (half : R) (U : Basis n → ι → ComplexScalar R) :
    Four ι → Four ι → ComplexScalar R :=
  scaleMatrix (ofReal (half^n)) (frameTwirl U)

private theorem matMulScale (xs : List β) (c d : ComplexScalar R)
    (A : α → β → ComplexScalar R) (B : β → ι → ComplexScalar R) :
    matMul xs (scaleMatrix c A) (scaleMatrix d B) = scaleMatrix (c*d) (matMul xs A B) := by
  funext i j
  unfold matMul scaleMatrix
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro k
  grind

private theorem scaleOne (A : α → β → ComplexScalar R) : scaleMatrix 1 A = A := by
  funext i j
  simp [scaleMatrix, Semiring.one_mul]

theorem pairedFrameTraceScale (xs : List ι) (c d : ComplexScalar R)
    (H A B : ι → ι → ComplexScalar R) :
    pairedFrameTrace xs H (scaleMatrix c A) (scaleMatrix d B) = c*d * pairedFrameTrace xs H A B := by
  unfold pairedFrameTrace
  rw [← scaleOne H, matMulScale, matMulScale, matMulScale, scaleOne H]
  simp only [Semiring.one_mul, Semiring.mul_one]
  unfold trace scaleMatrix
  rw [sumOverMulLeft]

theorem normalizedFrameHermitian {n : Nat} (half : R) (U : Basis n → ι → ComplexScalar R) :
    dagger (normalizedFrame half U) = normalizedFrame half U := by
  funext a b
  change star (ofReal (half^n) * frameTwirl U b a) = ofReal (half^n) * frameTwirl U a b
  rw [ComplexScalar.star_mul, ComplexScalar.star_ofReal]
  exact congrArg (fun z => ofReal (half^n) * z)
    (congrFun (congrFun (frameTwirlHermitian U) a) b)

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Exact physical purity trace on the common source space, with each local
Pauli sum normalized by its own qubit dimension. -/
theorem purityRectangularTrace {m n : Nat} (source : List ι) (half : R)
    (U : Basis m → ι → ComplexScalar R) (V : Basis n → ι → ComplexScalar R)
    (M : ι → ι → ComplexScalar R) (middleSymmetric : transpose M = M) (middleReal : conjugate M = M) :
    purity half (coefficients source U M V) =
      (pairedFrameTrace (fourIndices source) (tensorFour M)
        (normalizedFrame half U) (normalizedFrame half (conjugate V))).re := by
  let left := fourIndices (qubitIndices m)
  let right := fourIndices (qubitIndices n)
  let J : Four (Basis m) → Four (Basis m) → ComplexScalar R := unnormalizedTwirl imaginaryUnit
  let K : Four (Basis n) → Four (Basis n) → ComplexScalar R := unnormalizedTwirl imaginaryUnit
  have h := purityComplex half (coefficients source U M V)
  rw [normalizedPauliMoment, conjugateCoefficients _ _ _ _ middleReal, pauliMomentEqTrace,
    fourCoefficients, fourCoefficients] at h
  have symmetricFour : transpose (tensorFour M) = tensorFour M := by rw [← fourTranspose, middleSymmetric]
  have kSymm : transpose K = K := by
    funext a b
    exact unnormalizedTwirlTranspose imaginaryUnit a b
  have frame := rectangularFrameTrace left right (fourIndices source)
    (tensorFour U) (tensorFour (conjugate U)) (tensorFour V) (tensorFour (conjugate V))
    (tensorFour M) J K symmetricFour kSymm
  change _ = _ * coefficientTrace left right _ _ J K at h
  rw [frame] at h
  simp only [normalizedFrame, pairedFrameTraceScale]
  rw [Semiring.pow_add, ← realEmbeddingPow half m, ← realEmbeddingPow half n] at h
  have result := congrArg ComplexScalar.re h
  simpa only [ComplexScalar.re_ofReal, frameTwirl, conjugateInvolution, left, right, J, K] using result

/-- Reduction to the two physical paired purities on the two local
dimensions, for arbitrary rectangular complex Schmidt frames. -/
theorem rectangularPairedPurityBound [DecidableEq ι] {m n : Nat}
    (source : List ι) (nd : source.Nodup) (complete : ∀ i, i ∈ source) (half : R)
    (U : Basis m → ι → ComplexScalar R) (V : Basis n → ι → ComplexScalar R)
    (h : ι → R) (nonnegative : ∀ i, 0 ≤ h i) :
    let M := diagonal h
    2 * purity half (coefficients source U M V) ≤
      purity half (coefficients source U M (conjugate U)) +
      purity half (coefficients source (conjugate V) M V) := by
  dsimp only
  rw [purityRectangularTrace source half U V _ (diagonalSymmetric h) (diagonalReal h),
    purityRectangularTrace source half U (conjugate U) _ (diagonalSymmetric h) (diagonalReal h),
    purityRectangularTrace source half (conjugate V) V _ (diagonalSymmetric h) (diagonalReal h),
    conjugateInvolution, tensorDiagonal]
  have pairs := HyperplaneInduction.pairsNodup source source nd nd
  have fourNodup : (fourIndices source).Nodup := HyperplaneInduction.pairsNodup _ _ pairs pairs
  have fourComplete (a : Four ι) : a ∈ fourIndices source := by
    apply HyperplaneInduction.pairMember
    · exact HyperplaneInduction.pairMember (complete a.1.1) (complete a.1.2)
    · exact HyperplaneInduction.pairMember (complete a.2.1) (complete a.2.2)
  have fourNonnegative (a : Four ι) : 0 ≤ fourWeights h a :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (nonnegative _) (nonnegative _))
      (OrderedRing.mul_nonneg (nonnegative _) (nonnegative _))
  exact pairedTraceBound _ fourNodup fourComplete _ fourNonnegative _ _
    (normalizedFrameHermitian half U) (normalizedFrameHermitian half (conjugate V))

end Order

/-- The rank-seven pure-state coefficient matrix is the finite Schmidt
sum over the seven specified columns. -/
theorem coefficientsDiagonal [DecidableEq ι] (source : List ι) (nd : source.Nodup)
    (complete : ∀ i, i ∈ source) (U : α → ι → ComplexScalar R)
    (V : β → ι → ComplexScalar R) (h : ι → R) (a : α) (b : β) :
    coefficients source U (diagonal h) V a b =
      sumOver source (fun i => ofReal (h i) * U a i * V b i) := by
  unfold coefficients
  rw [matMulAssoc]
  unfold matMul
  apply sumOverCongr
  intro i
  change U a i * matMul source (diagonal h) (transpose V) i b = _
  rw [diagonalAction source nd h _ i b (complete i)]
  unfold transpose
  grind

def rankSevenCoefficients {m n : Nat} (U : Basis m → Fin 7 → ComplexScalar R)
    (V : Basis n → Fin 7 → ComplexScalar R) (h : Fin 7 → R) : Basis m → Basis n → ComplexScalar R :=
  fun a b => sumOver (List.finRange 7) (fun i => ofReal (h i) * U a i * V b i)

theorem rankSevenCoefficients_eq {m n : Nat} (U : Basis m → Fin 7 → ComplexScalar R)
    (V : Basis n → Fin 7 → ComplexScalar R) (h : Fin 7 → R) :
    coefficients (List.finRange 7) U (diagonal h) V = rankSevenCoefficients U V h := by
  funext a b
  exact coefficientsDiagonal _ (by decide) (fun _ => by simp) U V h a b

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem rankSevenPurityLeOfPaired {m n : Nat} (half : R)
    (U : Basis m → Fin 7 → ComplexScalar R) (V : Basis n → Fin 7 → ComplexScalar R)
    (h : Fin 7 → R) (nonnegative : ∀ i, 0 ≤ h i) (bound : R)
    (boundU : purity half (rankSevenCoefficients U (conjugate U) h) ≤ bound)
    (boundV : purity half (rankSevenCoefficients (conjugate V) V h) ≤ bound) :
    purity half (rankSevenCoefficients U V h) ≤ bound := by
  have cross := rectangularPairedPurityBound (List.finRange 7) (by decide) (fun _ => by simp)
    half U V h nonnegative
  dsimp only at cross
  rw [rankSevenCoefficients_eq, rankSevenCoefficients_eq, rankSevenCoefficients_eq] at cross
  grind

end Order

/-- The computational Schmidt columns occupy binary labels zero to six. -/
def computationalFrame (k : Nat) (a : Basis (k+3)) (i : Fin 7) : ComplexScalar R :=
  if PlaneOrientation.label (k+3) a = i.val then 1 else 0

private theorem computationalFrameSucc (k : Nat) (bit : Bool) (a : Basis (k+3)) (i : Fin 7) :
    computationalFrame (R := R) (k+1) (bit,a) i =
      if bit then 0 else computationalFrame k a i := by
  cases bit
  · simp [computationalFrame, PlaneOrientation.label]
  · have bound : 7 ≤ 2^(k+3) := by
      rw [Nat.pow_add]
      have pos := Nat.two_pow_pos k
      change 7 ≤ 2^k * 8
      omega
    have outside : 2^(k+3) + PlaneOrientation.label (k+3) a ≠ i.val := by omega
    simp [computationalFrame, PlaneOrientation.label, outside]

def computationalCoefficients (m n : Nat) (h : Fin 7 → R) :
    Basis (m+3) → Basis (n+3) → ComplexScalar R :=
  rankSevenCoefficients (computationalFrame m) (computationalFrame n) h

theorem computationalPadLeft (m n : Nat) (h : Fin 7 → R) :
    computationalCoefficients (m+1) n h = padLeft (computationalCoefficients m n h) := by
  funext a b
  rcases a with ⟨bit,row⟩
  unfold computationalCoefficients rankSevenCoefficients padLeft
  cases bit
  · change _ = sumOver (List.finRange 7)
      (fun i => ofReal (h i) * computationalFrame m row i * computationalFrame n b i)
    apply sumOverCongr
    intro i
    rw [computationalFrameSucc]
    rfl
  · change sumOver (List.finRange 7) _ = (0 : ComplexScalar R)
    have terms (i : Fin 7) : ofReal (h i) * computationalFrame (m+1) (true,row) i *
        computationalFrame n b i = 0 := by
      rw [computationalFrameSucc]
      simp [Semiring.mul_zero, Semiring.zero_mul]
    rw [sumOverCongr _ terms]
    generalize List.finRange 7 = xs
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      change (0 : ComplexScalar R) + sumOver xs (fun _ => 0) = 0
      rw [ih]
      grind

theorem computationalTranspose (m n : Nat) (h : Fin 7 → R) :
    transpose (computationalCoefficients m n h) = computationalCoefficients n m h := by
  funext a b
  unfold transpose computationalCoefficients rankSevenCoefficients
  apply sumOverCongr
  intro i
  grind

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem computationalPurityInvariant (half : R) (unitHalf : half+half=1) (m n : Nat) (h : Fin 7 → R) :
    purity half (computationalCoefficients m n h) = purity half (computationalCoefficients 0 0 h) := by
  have reduceLeft (a b : Nat) :
      purity half (computationalCoefficients a b h) = purity half (computationalCoefficients 0 b h) := by
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [computationalPadLeft]
      exact (purityPadLeftMany half unitHalf (computationalCoefficients a b h) 1).trans ih
  rw [reduceLeft]
  have swap := purityTranspose (m:=n+3) (n:=3) half (computationalCoefficients n 0 h)
  rw [computationalTranspose] at swap
  exact swap.trans (reduceLeft n 0)

/-- A bound for paired rank-seven frames at each size proves the full
two-frame purity inequality on any qubit bipartition. -/
theorem rankSevenComputationalComparison (half : R) (unitHalf : half+half=1) (h : Fin 7 → R)
    (nonnegative : ∀ i, 0 ≤ h i) (m n : Nat)
    (U : Basis (m+3) → Fin 7 → ComplexScalar R) (V : Basis (n+3) → Fin 7 → ComplexScalar R)
    (pairedLeft : purity half (rankSevenCoefficients U (conjugate U) h) ≤
      purity half (computationalCoefficients m m h))
    (pairedRight : purity half (rankSevenCoefficients (conjugate V) V h) ≤
      purity half (computationalCoefficients n n h)) :
    purity half (rankSevenCoefficients U V h) ≤ purity half (computationalCoefficients m n h) := by
  rw [computationalPurityInvariant half unitHalf m m] at pairedLeft
  rw [computationalPurityInvariant half unitHalf n n] at pairedRight
  rw [computationalPurityInvariant half unitHalf m n]
  exact rankSevenPurityLeOfPaired half U V h nonnegative _ pairedLeft pairedRight

end Order
end RankSeven.RectangularPairedReduction

#print axioms RankSeven.RectangularPairedReduction.purityRectangularTrace
#print axioms RankSeven.RectangularPairedReduction.rectangularPairedPurityBound
#print axioms RankSeven.RectangularPairedReduction.rankSevenPurityLeOfPaired
#print axioms RankSeven.RectangularPairedReduction.computationalPurityInvariant
#print axioms RankSeven.RectangularPairedReduction.rankSevenComputationalComparison
