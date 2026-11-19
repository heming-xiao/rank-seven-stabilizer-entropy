import Rank7HermitianCoordinates
import Rank7HyperplaneInduction
import Rank7PauliFrames

/-! The normalized compression of a real symmetric exterior kernel to complex
source coordinates. The only order hypotheses concern the original quadratic
form on the image of the lift and its norm. -/

namespace RankSeven.ExteriorCompressionEffect

open Lean.Grind Pauli Compression HyperplaneInduction
open ComplexScalar (star ofReal normSq)
open ExteriorCuts (Wedge7 wedges)

variable {R α β γ ι : Type} [CommRing R]

/-- Matrix action on a complex column vector. -/
def applyMatrix (xs : List β) (A : α → β → ComplexScalar R) (v : β → ComplexScalar R) (a : α) :
    ComplexScalar R := sumOver xs (fun b => A a b * v b)

private def dagger (L : α → β → ComplexScalar R) (b : β) (a : α) : ComplexScalar R :=
  star (L a b)

private def realMatrix (K : α × α → R) (a b : α) : ComplexScalar R := ofReal (K (a,b))

private theorem starSum (xs : List α) (f : α → ComplexScalar R) :
    star (sumOver xs f) = sumOver xs (fun i => star (f i)) := by
  induction xs with
  | nil => exact ComplexScalar.star_ofReal (0 : R)
  | cons a xs ih =>
    change star (f a + sumOver xs f) = star (f a) + sumOver xs (fun i => star (f i))
    rw [ComplexScalar.star_add,ih]

private theorem reSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).re = (f a).re + sumOver xs (fun i => (f i).re)
    rw [ComplexScalar.re_add, ih]

private theorem imSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).im = sumOver xs (fun i => (f i).im) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).im = (f a).im + sumOver xs (fun i => (f i).im)
    rw [ComplexScalar.im_add, ih]

private theorem daggerProduct (xs : List β) (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    dagger (matMul xs A B) = matMul xs (dagger B) (dagger A) := by
  funext c a
  unfold dagger matMul
  rw [starSum]
  apply sumOverCongr
  intro b
  rw [ComplexScalar.star_mul, CommSemiring.mul_comm]

private theorem daggerTwice (A : α → β → ComplexScalar R) : dagger (dagger A) = A := by
  funext a b
  exact ComplexScalar.star_star _

private theorem daggerReal (K : α × α → R) (h : ∀ a b, K (a,b) = K (b,a)) :
    dagger (realMatrix K) = realMatrix K := by
  funext a b
  unfold dagger realMatrix
  rw [ComplexScalar.star_ofReal, h]

private def pullback (ambient : List α) (K : α × α → R) (L : α → ι → ComplexScalar R) :
    ι → ι → ComplexScalar R :=
  matMul ambient (dagger L) (matMul ambient (realMatrix K) L)

/-- The normalized matrix is the scalar multiple of the conjugate-transpose
pullback, with both ambient matrix multiplications evaluated over the ambient list. -/
def normalizedMatrix (ambient : List α) (K : α × α → R) (L : α → ι → ComplexScalar R)
    (scale : R) (i j : ι) : ComplexScalar R := ofReal scale * pullback ambient K L i j

/-- Entrywise formula for comparing the normalized coordinates with an
explicit Pauli projector and two fourth-minor matrices. -/
theorem normalizedMatrix_entry (ambient : List α) (K : α × α → R) (L : α → ι → ComplexScalar R)
    (scale : R) (i j : ι) :
    normalizedMatrix ambient K L scale i j = ofReal scale * sumOver ambient (fun a =>
      sumOver ambient (fun b => star (L a i) * ofReal (K (a,b)) * L b j)) := by
  unfold normalizedMatrix pullback matMul dagger realMatrix
  congr 1
  apply sumOverCongr
  intro a
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro b
  grind

private theorem matrixHermitian (ambient : List α) (K : α × α → R) (symm : ∀ a b, K (a,b) = K (b,a))
    (L : α → ι → ComplexScalar R) (scale : R) (i j : ι) :
    normalizedMatrix ambient K L scale i j = star (normalizedMatrix ambient K L scale j i) := by
  have h : dagger (pullback ambient K L) = pullback ambient K L := by
    unfold pullback
    rw [daggerProduct, daggerProduct, daggerTwice, daggerReal K symm, matMulAssoc]
  unfold normalizedMatrix
  rw [ComplexScalar.star_mul, ComplexScalar.star_ofReal]
  exact congrArg (fun t => ofReal scale * t) (congrFun (congrFun h i) j).symm

def normalizedEntries (ambient : List α) (K : α × α → R) (symm : ∀ a b, K (a,b) = K (b,a))
    (L : α → ι → ComplexScalar R) (scale : R) : HermitianEntries ι R where
  realPart i j := (normalizedMatrix ambient K L scale i j).re
  imagPart i j := (normalizedMatrix ambient K L scale i j).im
  realSymmetric i j := by
    simpa only [ComplexScalar.re_star] using congrArg ComplexScalar.re (matrixHermitian ambient K symm L scale i j)
  imagSkew i j := congrArg ComplexScalar.im (matrixHermitian ambient K symm L scale i j)

private def innerC (xs : List α) (u v : α → ComplexScalar R) : ComplexScalar R :=
  sumOver xs (fun i => star (u i) * v i)

private theorem applyProduct (source : List γ) (middle : List β)
    (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) (v : γ → ComplexScalar R) :
    applyMatrix source (matMul middle A B) v = applyMatrix middle A (applyMatrix source B v) := by
  funext a
  exact congrFun (congrFun (matMulAssoc middle source A B (fun i (_ : Unit) => v i)) a) ()

private theorem innerDagger (source : List β) (ambient : List α) (L : α → β → ComplexScalar R)
    (v : β → ComplexScalar R) (u : α → ComplexScalar R) :
    innerC source v (applyMatrix ambient (dagger L) u) = innerC ambient (applyMatrix source L v) u := by
  unfold innerC applyMatrix dagger
  simp only [sumOverMulLeft, starSum, sumOverMulRight]
  rw [sumOverSwap source ambient]
  apply sumOverCongr
  intro a
  apply sumOverCongr
  intro i
  rw [ComplexScalar.star_mul]
  grind

private theorem innerScale (xs : List α) (scale : R) (v u : α → ComplexScalar R) :
    innerC xs v (fun i => ofReal scale * u i) = ofReal scale * innerC xs v u := by
  unfold innerC
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro i
  grind

private theorem applyNormalized (source : List ι) (ambient : List α) (K : α × α → R)
    (L : α → ι → ComplexScalar R) (scale : R) (v : ι → ComplexScalar R) :
    applyMatrix source (normalizedMatrix ambient K L scale) v =
      fun i => ofReal scale * applyMatrix source (pullback ambient K L) v i := by
  funext i
  unfold applyMatrix normalizedMatrix
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro j
  grind

private theorem ambientInner (xs : List α) (K : α × α → R) (z : α → ComplexScalar R) :
    (innerC xs z (applyMatrix xs (realMatrix K) z)).re = quadratic xs K z := by
  unfold innerC applyMatrix quadratic productIndices
  rw [reSum, sumOverFlatMap]
  apply sumOverCongr
  intro a
  rw [sumOverMulLeft, reSum]
  simp only [sumOver, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  simp only [realWeight,realMatrix,ComplexScalar.re_mul,ComplexScalar.im_mul,
    ComplexScalar.re_star, ComplexScalar.im_star, ComplexScalar.re_ofReal, ComplexScalar.im_ofReal]
  grind

/-- When vector entries are stored as two real functions, this recovers
the usual complex column used by the exterior lift. -/
def asColumn (v : ComplexCoordinates ι R) (i : ι) : ComplexScalar R :=
  ⟨v.realPart i, v.imagPart i⟩

private theorem entriesAct (source : List ι) (ambient : List α) (K : α × α → R)
    (symm : ∀ a b, K (a,b) = K (b,a)) (L : α → ι → ComplexScalar R) (scale : R)
    (v : ComplexCoordinates ι R) :
    asColumn ((normalizedEntries ambient K symm L scale).act source v) =
      applyMatrix source (normalizedMatrix ambient K L scale) (asColumn v) := by
  funext i
  apply ComplexScalar.ext
  · unfold applyMatrix
    rw [reSum]
    rfl
  · unfold applyMatrix
    rw [imSum]
    rfl

private theorem innerCoordinates (source : List ι) (v w : ComplexCoordinates ι R) :
    ComplexCoordinates.inner source v w = (innerC source (asColumn v) (asColumn w)).re := by
  unfold ComplexCoordinates.inner innerC
  rw [reSum]
  apply sumOverCongr
  intro i
  simp only [asColumn, ComplexScalar.re_mul, ComplexScalar.re_star, ComplexScalar.im_star]
  grind

/-- Real quadratic evaluation of the actual compressed Hermitian matrix. -/
theorem normalizedEntries_quadratic (source : List ι) (ambient : List α) (K : α × α → R)
    (symm : ∀ a b, K (a,b) = K (b,a)) (L : α → ι → ComplexScalar R) (scale : R)
    (v : ComplexCoordinates ι R) :
    ComplexCoordinates.inner source v ((normalizedEntries ambient K symm L scale).act source v) =
      scale * quadratic ambient K (applyMatrix source L (asColumn v)) := by
  rw [innerCoordinates, entriesAct, applyNormalized, innerScale]
  unfold pullback
  rw [applyProduct, applyProduct, innerDagger]
  rw [ComplexScalar.re_mul, ComplexScalar.re_ofReal, ComplexScalar.im_ofReal, ambientInner]
  grind

theorem innerSelf_eq_norm (xs : List ι) (v : ComplexCoordinates ι R) :
    ComplexCoordinates.inner xs v v = sumOver xs (fun i => normSq (asColumn v i)) := by
  apply sumOverCongr
  intro i
  simp [asColumn, ComplexScalar.normSq]
  grind

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- A normalized compression is an effect whenever the lift preserves the
source norm and the ambient quadratic form has the stated bounds on its image. -/
theorem normalizedEntries_effect (source : List ι) (ambient : List α) (K : α × α → R)
    (symm : ∀ a b, K (a,b) = K (b,a)) (L : α → ι → ComplexScalar R) (scale q : R)
    (scaleNonnegative : 0 ≤ scale) (inverse : scale * q = 1)
    (isometry : ∀ v : ι → ComplexScalar R, sumOver ambient (fun a => normSq (applyMatrix source L v a)) =
        sumOver source (fun i => normSq (v i)))
    (positive : ∀ v : ι → ComplexScalar R, 0 ≤ quadratic ambient K (applyMatrix source L v))
    (bounded : ∀ v : ι → ComplexScalar R, quadratic ambient K (applyMatrix source L v) ≤
      q * sumOver ambient (fun a => normSq (applyMatrix source L v a))) :
    (normalizedEntries ambient K symm L scale).IsCoordinateEffect source := by
  intro v
  rw [normalizedEntries_quadratic, innerSelf_eq_norm]
  refine ⟨OrderedRing.mul_nonneg scaleNonnegative (positive _), ?_⟩
  have hi := bounded (asColumn v)
  rw [isometry] at hi
  have prod := OrderedRing.mul_nonneg scaleNonnegative
    (show 0 ≤ q * sumOver source (fun i => normSq (asColumn v i)) -
      quadratic ambient K (applyMatrix source L (asColumn v)) by grind)
  have cancel := congrArg (fun t => t * sumOver source (fun i => normSq (asColumn v i))) inverse
  grind

/-- The 35 columns of fourth minors give the concrete Hermitian effect on
the coordinates consumed by the rank-seven cut and rounding theorems. -/
theorem normalizedExteriorEffect {S : Type} (ambient : List α) (rows : α → Fin 4 → S)
    (K : α × α → R) (symm : ∀ a b, K (a,b) = K (b,a)) (A : S → Fin 7 → ComplexScalar R)
    (scale q : R) (scaleNonnegative : 0 ≤ scale) (inverse : scale * q = 1)
    (isometry : ∀ v : Wedge7 → ComplexScalar R,
      sumOver ambient (fun a => normSq (exteriorLift rows A v a)) = sumOver wedges (fun i => normSq (v i)))
    (positive : ∀ v : Wedge7 → ComplexScalar R, 0 ≤ quadratic ambient K (exteriorLift rows A v))
    (bounded : ∀ v : Wedge7 → ComplexScalar R, quadratic ambient K (exteriorLift rows A v) ≤
      q * sumOver ambient (fun a => normSq (exteriorLift rows A v a))) :
    (normalizedEntries ambient K symm (fun a w => minor4 A (rows a) w) scale).IsCoordinateEffect wedges :=
  normalizedEntries_effect wedges ambient K symm _ scale q scaleNonnegative inverse isometry positive bounded

end Order
end RankSeven.ExteriorCompressionEffect

#print axioms RankSeven.ExteriorCompressionEffect.normalizedEntries_quadratic
#print axioms RankSeven.ExteriorCompressionEffect.normalizedExteriorEffect
