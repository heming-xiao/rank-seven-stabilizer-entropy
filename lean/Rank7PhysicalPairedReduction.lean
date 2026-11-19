import Rank7ComplexPauliMoment
import Rank7HyperplaneInduction
import Rank7PlaneProjector

namespace RankSeven.PhysicalPairedReduction

open Lean.Grind Pauli ComplexPauliMoment
open ComplexScalar (star ofReal imaginaryUnit normSq)
open ComplexExterior (starSumOver)

variable {R α β γ : Type} [CommRing R]

private theorem realSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x + sumOver xs f).re = (f x).re + sumOver xs (fun a => (f a).re)
    rw [ComplexScalar.re_add, ih]

private theorem realEmbeddingAdd (a b : R) : ofReal (a+b) = ofReal a + ofReal b := by
  apply ComplexScalar.ext <;> simp <;> grind

private theorem realEmbeddingSum (xs : List α) (f : α → R) :
    ofReal (sumOver xs f) = sumOver xs (fun a => ofReal (f a)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ofReal (f x + sumOver xs f) = ofReal (f x) + sumOver xs (fun a => ofReal (f a))
    rw [← ih, realEmbeddingAdd]

private theorem realEmbeddingMul (a b : R) : ofReal (a*b) = ofReal a * ofReal b := by
  apply ComplexScalar.ext <;> simp <;> grind

theorem realEmbeddingPow (a : R) (n : Nat) : ofReal (a^n) = (ofReal a)^n := by
  induction n with
  | zero => simp only [Semiring.pow_zero]; rfl
  | succ n ih => rw [Semiring.pow_succ, Semiring.pow_succ, realEmbeddingMul, ih]

/-- Real stabilizer purity as a normalized sum of physical Pauli moduli. -/
def purity {m n : Nat} (half : R) (T : Basis m → Basis n → ComplexScalar R) : R :=
  half^(m+n) * sumOver (words m) (fun p => sumOver (words n) (fun q =>
    (normSq (productExpectation (qubitIndices m) (qubitIndices n) T (conjugate T)
      (wordEntry imaginaryUnit p) (wordEntry imaginaryUnit q)))^2))

def frameTwirl {n : Nat} (U : Basis n → α → ComplexScalar R) :
    Four α → Four α → ComplexScalar R :=
  let xs := fourIndices (qubitIndices n)
  matMul xs (matMul xs (transpose (tensorFour (conjugate U))) (unnormalizedTwirl imaginaryUnit))
    (tensorFour U)

def dagger (A : α → β → ComplexScalar R) : β → α → ComplexScalar R :=
  transpose (conjugate A)

theorem daggerProduct (middle : List β) (A : α → β → ComplexScalar R)
    (B : β → γ → ComplexScalar R) :
    dagger (matMul middle A B) = matMul middle (dagger B) (dagger A) := by
  unfold dagger
  rw [conjugateMatMul, transposeMatMul]

theorem daggerInvolution (A : α → β → ComplexScalar R) : dagger (dagger A) = A := by
  funext a b
  exact ComplexScalar.star_star _

theorem conjugateFour (A : α → β → ComplexScalar R) :
    conjugate (tensorFour A) = tensorFour (conjugate A) := by
  funext a b
  simp only [conjugate, tensorFour, tensor, ComplexScalar.star_mul]

theorem twirlHermitian (n : Nat) :
    dagger (unnormalizedTwirl (imaginaryUnit (R := R)) (n := n)) = unnormalizedTwirl imaginaryUnit := by
  funext a b
  unfold dagger transpose conjugate unnormalizedTwirl
  rw [starSumOver]
  apply sumOverCongr
  intro p
  simp only [tensorFour, tensor, ComplexScalar.star_mul, wordHermitian]

theorem frameTwirlHermitian {n : Nat} (U : Basis n → α → ComplexScalar R) :
    dagger (frameTwirl U) = frameTwirl U := by
  let xs := fourIndices (qubitIndices n)
  let B := tensorFour U
  let J := unnormalizedTwirl (imaginaryUnit (R := R)) (n := n)
  have form : frameTwirl U = matMul xs (matMul xs (dagger B) J) B := by
    unfold frameTwirl B dagger
    rw [conjugateFour]
  rw [form, daggerProduct, daggerProduct, twirlHermitian, daggerInvolution, matMulAssoc]

theorem conjugateInvolution (A : α → β → ComplexScalar R) : conjugate (conjugate A) = A := by
  funext a b
  exact ComplexScalar.star_star _

def diagonal [DecidableEq α] (h : α → R) (a b : α) : ComplexScalar R :=
  if a = b then ofReal (h a) else 0

def fourWeights (h : α → R) (a : Four α) : R :=
  (h a.1.1 * h a.1.2) * (h a.2.1 * h a.2.2)

theorem diagonalSymmetric [DecidableEq α] (h : α → R) :
    transpose (diagonal h) = diagonal h := by
  funext a b
  by_cases same : a = b
  · subst b
    rfl
  · have different := Ne.symm same
    simp [transpose, diagonal, same, different]

theorem diagonalReal [DecidableEq α] (h : α → R) :
    conjugate (diagonal h) = diagonal h := by
  funext a b
  by_cases same : a = b
  · simp [conjugate, diagonal, same]
  · simp only [conjugate, diagonal, ite_eq_right same]
    exact ComplexScalar.star_ofReal (0:R)

theorem tensorDiagonal [DecidableEq α] (h : α → R) :
    tensorFour (diagonal h) = diagonal (fourWeights h) := by
  funext a b
  rcases a with ⟨⟨a₀,a₁⟩,⟨a₂,a₃⟩⟩
  rcases b with ⟨⟨b₀,b₁⟩,⟨b₂,b₃⟩⟩
  simp only [diagonal, fourWeights, tensorFour, tensor, Prod.mk.injEq]
  by_cases e₀ : a₀ = b₀ <;> by_cases e₁ : a₁ = b₁ <;>
    by_cases e₂ : a₂ = b₂ <;> by_cases e₃ : a₃ = b₃ <;>
    simp [e₀,e₁,e₂,e₃,realEmbeddingMul,Semiring.zero_mul,Semiring.mul_zero]

theorem diagonalAction [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (h : α → R) (A : α → β → ComplexScalar R) (a : α) (b : β) (ha : a ∈ xs) :
    matMul xs (diagonal h) A a b = ofReal (h a) * A a b := by
  unfold matMul
  have term (j : α) : diagonal h a j * A j b =
      if a = j then ofReal (h a) * A j b else 0 := by
    by_cases same : a = j <;> simp [diagonal, same, Semiring.zero_mul]
  rw [sumOverCongr _ term]
  exact ExteriorPauliBase.sumOnIndex xs a _ nd ha

theorem pairedTraceDiagonal [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (complete : ∀ a, a ∈ xs) (h : α → R) (A B : α → α → ComplexScalar R) :
    pairedFrameTrace xs (diagonal h) A B =
      sumOver xs (fun a => sumOver xs (fun b => ofReal (h a) * A a b * ofReal (h b) * B b a)) := by
  unfold pairedFrameTrace trace
  rw [matMulAssoc xs xs (diagonal h) A (diagonal h)]
  rw [matMulAssoc xs xs (diagonal h) (matMul xs A (diagonal h)) B]
  apply sumOverCongr
  intro a
  rw [diagonalAction xs nd h _ a a (complete a)]
  rw [matMulAssoc xs xs A (diagonal h) B]
  change ofReal (h a) * sumOver xs (fun b => A a b * matMul xs (diagonal h) B b a) = _
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro b
  rw [diagonalAction xs nd h _ b a (complete b)]
  grind

theorem pairedTraceDiagonalReal [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (complete : ∀ a, a ∈ xs) (h : α → R) (A B : α → α → ComplexScalar R)
    (bHermitian : dagger B = B) :
    (pairedFrameTrace xs (diagonal h) A B).re =
      sumOver xs (fun a => sumOver xs (fun b => h a * h b *
        ((A a b).re * (B a b).re + (A a b).im * (B a b).im))) := by
  rw [pairedTraceDiagonal xs nd complete, realSum]
  apply sumOverCongr
  intro a
  rw [realSum]
  apply sumOverCongr
  intro b
  have entry : star (B a b) = B b a := congrFun (congrFun bHermitian b) a
  rw [← entry]
  simp only [ComplexScalar.re_mul, ComplexScalar.im_mul, ComplexScalar.re_ofReal,
    ComplexScalar.im_ofReal, ComplexScalar.re_star, ComplexScalar.im_star]
  grind

section Order

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem purityComplex {m n : Nat} (half : R) (T : Basis m → Basis n → ComplexScalar R) :
    ofReal (purity half T) =
      normalizedPauliMoment imaginaryUnit (ofReal half) T (conjugate T) := by
  unfold purity normalizedPauliMoment pauliMoment
  rw [realEmbeddingMul, realEmbeddingPow, realEmbeddingSum]
  congr 1
  apply sumOverCongr
  intro p
  rw [realEmbeddingSum]
  apply sumOverCongr
  intro q
  exact (pauliExpectationFourth T p q).symm

theorem purityFrameTrace {n : Nat} (half : R) (U M V : Basis n → Basis n → ComplexScalar R)
    (middleSymmetric : transpose M = M) (middleReal : conjugate M = M) :
    purity half (schmidtCoefficients (qubitIndices n) U M V) =
      half^(n+n) * (pairedFrameTrace (fourIndices (qubitIndices n)) (tensorFour M)
        (frameTwirl U) (frameTwirl (conjugate V))).re := by
  have h := purityComplex half (schmidtCoefficients (qubitIndices n) U M V)
  rw [conjugateSchmidt _ _ _ _ middleReal,
    normalizedPauliMomentEqPairedFrameTrace _ _ _ _ _ _ _ middleSymmetric] at h
  have realTrace := congrArg ComplexScalar.re h
  have subZero (x : R) : x - 0 = x := by grind
  simp only [ComplexScalar.re_ofReal, ← realEmbeddingPow, ComplexScalar.re_mul,
    ComplexScalar.im_ofReal, Semiring.zero_mul, subZero] at realTrace
  simpa only [frameTwirl, conjugateInvolution] using realTrace

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem conjugatePadLeft {m n : Nat} (T : Basis m → Basis n → ComplexScalar R) :
    conjugate (padLeft T) = padLeft (conjugate T) := by
  funext a b
  rcases a with ⟨bit, row⟩
  cases bit
  · rfl
  · exact ComplexScalar.star_ofReal (0:R)

theorem purityPadLeftMany {m n : Nat} (half : R) (unitHalf : half + half = 1)
    (T : Basis m → Basis n → ComplexScalar R) (k : Nat) :
    purity half (padLeftMany T k) = purity half T := by
  have units : ofReal half + ofReal half = (1 : ComplexScalar R) := by
    rw [← realEmbeddingAdd, unitHalf]
    rfl
  have conjugatePads : ∀ k, conjugate (padLeftMany T k) = padLeftMany (conjugate T) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change conjugate (padLeft (padLeftMany T k)) = padLeft (padLeftMany (conjugate T) k)
      rw [conjugatePadLeft, ih]
  have h : ofReal (purity half (padLeftMany T k)) = ofReal (purity half T) := by
    rw [purityComplex, purityComplex, conjugatePads]
    exact normalizedPauliMomentPadLeftMany imaginaryUnit (ofReal half) units T (conjugate T) k
  exact congrArg ComplexScalar.re h

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem expectationTranspose (left : List α) (right : List β)
    (T : α → β → ComplexScalar R) (P : α → α → ComplexScalar R)
    (Q : β → β → ComplexScalar R) :
    productExpectation right left (transpose T) (conjugate (transpose T)) Q P =
      productExpectation left right T (conjugate T) P Q := by
  unfold productExpectation
  rw [sumOverSwap right left]
  apply sumOverCongr
  intro a
  apply sumOverCongr
  intro b
  rw [sumOverSwap right left]
  apply sumOverCongr
  intro c
  apply sumOverCongr
  intro d
  unfold transpose conjugate
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem purityTranspose {m n : Nat} (half : R) (T : Basis m → Basis n → ComplexScalar R) :
    purity half (transpose T) = purity half T := by
  unfold purity
  rw [Nat.add_comm n m, sumOverSwap (words n) (words m)]
  simp only [expectationTranspose]

def padRight {m n : Nat} (T : Basis m → Basis n → ComplexScalar R) :
    Basis m → Basis (n+1) → ComplexScalar R := transpose (padLeft (transpose T))

theorem purityPadRight {m n : Nat} (half : R) (unitHalf : half + half = 1)
    (T : Basis m → Basis n → ComplexScalar R) : purity half (padRight T) = purity half T := by
  unfold padRight
  rw [purityTranspose (m:=n+1) (n:=m) half (padLeft (transpose T))]
  have h := purityPadLeftMany half unitHalf (transpose T) 1
  change purity (m:=n+1) (n:=m) half (padLeft (transpose T)) =
    purity (m:=n) (n:=m) half (transpose T) at h
  rw [h, purityTranspose (m:=m) (n:=n) half T]

private theorem sumOrder (xs : List α) (f g : α → R) (le : ∀ x, f x ≤ g x) :
    sumOver xs f ≤ sumOver xs g := by
  induction xs with
  | nil => change (0:R) ≤ 0; grind
  | cons a rest ih =>
    change f a + sumOver rest f ≤ g a + sumOver rest g
    have ha := le a
    grind

theorem pairedTraceBound [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (complete : ∀ a, a ∈ xs) (h : α → R) (nonnegative : ∀ a, 0 ≤ h a)
    (A B : α → α → ComplexScalar R) (aHermitian : dagger A = A) (bHermitian : dagger B = B) :
    2 * (pairedFrameTrace xs (diagonal h) A B).re ≤
      (pairedFrameTrace xs (diagonal h) A A).re + (pairedFrameTrace xs (diagonal h) B B).re := by
  rw [pairedTraceDiagonalReal xs nd complete h A B bHermitian,
    pairedTraceDiagonalReal xs nd complete h A A aHermitian,
    pairedTraceDiagonalReal xs nd complete h B B bHermitian]
  rw [sumOverMulLeft, ← sumOverAdd]
  apply sumOrder
  intro a
  rw [sumOverMulLeft, ← sumOverAdd]
  apply sumOrder
  intro b
  have realSquare := squareNonnegative ((A a b).re - (B a b).re)
  have imagSquare := squareNonnegative ((A a b).im - (B a b).im)
  have squaredDistance : 0 ≤ ((A a b).re - (B a b).re)^2 + ((A a b).im - (B a b).im)^2 := by
    grind
  have weighted := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (nonnegative a) (nonnegative b))
    squaredDistance
  grind

end Order
end RankSeven.PhysicalPairedReduction

#print axioms RankSeven.PhysicalPairedReduction.purityFrameTrace
#print axioms RankSeven.PhysicalPairedReduction.purityPadLeftMany
#print axioms RankSeven.PhysicalPairedReduction.purityPadRight
