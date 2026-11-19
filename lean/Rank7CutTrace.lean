import Rank7PhysicalCompressionEffect
import Rank7TraceRounding
import Rank7PhysicalPairedReduction
import Rank7AnticommutingDefect

namespace RankSeven.CutTrace

open Lean.Grind Pauli Compression
open ExteriorCuts (cutCost indicator)
open PhysicalPairedReduction (diagonal diagonalAction dagger)
open ComplexScalar (ofReal star)
attribute [local instance] Semiring.natCast

variable {R α : Type} [CommRing R]

private theorem sumFiltered {C : Type} [CommRing C] (xs : List α) (keep : α → Bool) (f : α → C) :
    sumOver (xs.filter keep) f = sumOver xs (fun x => if keep x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons]
    cases h : keep a <;> simp [h,sumOver] at ih ⊢ <;> grind

private def supported (cut : α → Bool) (v : ComplexCoordinates α R) : ComplexCoordinates α R :=
  ⟨fun i => if cut i then v.realPart i else 0, fun i => if cut i then v.imagPart i else 0⟩

theorem cutAct (entries : HermitianEntries α R) (xs : List α) (cut : α → Bool) (v : ComplexCoordinates α R) :
    entries.act xs (supported cut v) = entries.act (xs.filter cut) v := by
  unfold HermitianEntries.act
  congr 1 <;> funext a <;> rw [sumFiltered] <;> apply sumOverCongr <;> intro j <;>
    cases h : cut j <;> simp [supported,h] <;> grind

theorem cutInner (xs : List α) (cut : α → Bool) (v w : ComplexCoordinates α R) :
    ComplexCoordinates.inner xs (supported cut v) w = ComplexCoordinates.inner (xs.filter cut) v w := by
  unfold ComplexCoordinates.inner
  rw [sumFiltered]
  apply sumOverCongr
  intro a
  cases h : cut a <;> simp [supported,h] <;> grind

theorem cutInnerSelf (xs : List α) (cut : α → Bool) (v : ComplexCoordinates α R) :
    ComplexCoordinates.inner xs (supported cut v) (supported cut v) =
      ComplexCoordinates.inner (xs.filter cut) v v := by
  unfold ComplexCoordinates.inner
  rw [sumFiltered]
  apply sumOverCongr
  intro a
  cases h : cut a <;> simp [supported,h] <;> grind

/-- Restricting the actual positive contraction to any set of wedge
coordinates preserves both inequalities in its quadratic form. -/
theorem restrictionEffect [LE R] (entries : HermitianEntries α R) (xs : List α) (cut : α → Bool)
    (effect : entries.IsCoordinateEffect xs) : entries.IsCoordinateEffect (xs.filter cut) := by
  intro v
  have e := effect (supported cut v)
  rw [cutAct,cutInner,cutInnerSelf] at e
  exact e

def matrix (entries : HermitianEntries α R) (a b : α) : ComplexScalar R :=
  ⟨entries.realPart a b,entries.imagPart a b⟩

theorem matrixHermitian (entries : HermitianEntries α R) :
    dagger (matrix entries) = matrix entries := by
  funext a b
  apply ComplexScalar.ext
  · exact entries.realSymmetric b a
  · change -entries.imagPart b a = entries.imagPart a b
    have skew := entries.imagSkew b a
    grind

private theorem realSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).re = (f a).re + sumOver xs (fun i => (f i).re)
    rw [ComplexScalar.re_add,ih]

private theorem imagSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).im = sumOver xs (fun i => (f i).im) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).im = (f a).im + sumOver xs (fun i => (f i).im)
    rw [ComplexScalar.im_add,ih]

private theorem traceSquareEqMass (entries : HermitianEntries α R) (xs : List α) :
    (trace xs (matMul xs (matrix entries) (matrix entries))).re =
      sumOver xs (fun a => sumOver xs (entries.mass a)) := by
  unfold trace matMul
  rw [realSum]
  apply sumOverCongr
  intro a
  rw [realSum]
  apply sumOverCongr
  intro b
  have e : matrix entries b a = star (matrix entries a b) :=
    (congrFun (congrFun (matrixHermitian entries) b) a).symm
  rw [e]
  simp only [matrix,ComplexScalar.re_mul,ComplexScalar.re_star,ComplexScalar.im_star]
  unfold HermitianEntries.mass
  grind

/-- The crossed-cut cost is exactly the trace variance of the physical
principal compression on the selected coordinates. -/
theorem cutCostTraceVariance (entries : HermitianEntries α R) (xs : List α) (cut : α → Bool) :
    let ys := xs.filter cut
    let T := matrix entries
    cutCost xs cut (rowSlack xs (fun i => entries.realPart i i) entries.mass) entries.mass =
      (trace ys T).re - (trace ys (matMul ys T T)).re := by
  dsimp only
  rw [Compression.cutCostEqTraces,traceSquareEqMass]
  unfold trace
  rw [realSum,sumFiltered]
  congr 1
  · apply sumOverCongr
    intro a
    cases cut a <;> simp [indicator,matrix] <;> grind
  · unfold ExteriorCuts.pairSum
    rw [sumFiltered]
    apply sumOverCongr
    intro a
    rw [sumFiltered]
    by_cases e : cut a = true
    · simp only [e,ite_true,indicator,Semiring.one_mul]
      apply sumOverCongr
      intro b
      cases cut b <;> simp <;> grind
    · have ef : cut a = false := Bool.eq_false_iff.mpr e
      simp only [ef,indicator,Bool.false_eq_true,ite_false,Semiring.zero_mul]
      induction xs with
      | nil => rfl
      | cons i is ih => change 0+sumOver is (fun _ => (0:R)) = 0; rw [ih]; grind

/-- Equality of finite matrix entries indexed by a selected list. -/
def AgreeOn (xs : List α) (A B : α → α → ComplexScalar R) : Prop :=
  ∀ i ∈ xs, ∀ j ∈ xs, A i j = B i j

theorem AgreeOn.product (xs : List α) {A B C D : α → α → ComplexScalar R}
    (left : AgreeOn xs A B) (right : AgreeOn xs C D) :
    AgreeOn xs (matMul xs A C) (matMul xs B D) := by
  intro i hi j hj
  unfold matMul
  apply AnticommutingDefect.sumCongrMem
  intro k hk
  rw [left i hi k hk, right k hk j hj]

theorem AgreeOn.diagonalSum (xs : List α) {A B : α → α → ComplexScalar R}
    (h : AgreeOn xs A B) : trace xs A = trace xs B := by
  apply AnticommutingDefect.sumCongrMem
  intro i hi
  exact h i hi i hi

omit [CommRing R] in
private theorem agreeRefl (xs : List α) (A : α → α → ComplexScalar R) :
    AgreeOn xs A A := fun _ _ _ _ => rfl

/-- Diagonalization of the principal matrix on the selected coordinates.
The existence theorem over the physical real numbers is a separate step. -/
structure SpectralWitness [DecidableEq α] (xs : List α) (T : α → α → ComplexScalar R) where
  values : α → R
  vectors : α → α → ComplexScalar R
  orthogonal : AgreeOn xs (matMul xs (dagger vectors) vectors) (diagonal (fun _ => 1))
  reconstruct : AgreeOn xs T (matMul xs vectors (matMul xs (diagonal values) (dagger vectors)))

private theorem diagonalRight [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (h : α → R) (A : α → α → ComplexScalar R) (i j : α) (hj : j ∈ xs) :
    matMul xs A (diagonal h) i j = ofReal (h j)*A i j := by
  have hT := congrFun (congrFun (transposeMatMul xs A (diagonal h)) j) i
  rw [PhysicalPairedReduction.diagonalSymmetric] at hT
  change matMul xs A (diagonal h) i j = matMul xs (diagonal h) (transpose A) j i at hT
  rw [hT,diagonalAction xs nd _ _ _ _ hj]
  rfl

theorem traceSpectrum [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (T : α → α → ComplexScalar R) (S : SpectralWitness xs T) :
    (trace xs T).re = sumOver xs S.values := by
  rw [S.reconstruct.diagonalSum xs,traceMatMulSwap xs xs S.vectors,matMulAssoc]
  rw [(AgreeOn.product xs (agreeRefl xs (diagonal S.values)) S.orthogonal).diagonalSum xs]
  unfold trace
  rw [realSum]
  apply AnticommutingDefect.sumCongrMem
  intro i hi
  rw [diagonalAction xs nd _ _ _ _ hi]
  simp [diagonal,ComplexScalar.re_mul, ComplexScalar.im_ofReal]
  grind

theorem traceSquareSpectrum [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (T : α → α → ComplexScalar R) (S : SpectralWitness xs T) :
    (trace xs (matMul xs T T)).re = sumOver xs (fun i => (S.values i)^2) := by
  let U := S.vectors
  let V := dagger U
  let D := diagonal S.values
  let I : α → α → ComplexScalar R := diagonal (fun _ => 1)
  have firstSwap : trace xs (matMul xs T T) =
      trace xs (matMul xs U (matMul xs D (matMul xs (matMul xs V U) (matMul xs D V)))) := by
    rw [(AgreeOn.product xs S.reconstruct S.reconstruct).diagonalSum xs]
    unfold U V D
    simp only [matMulAssoc] <;> rfl
  rw [firstSwap]
  have replaceInner : AgreeOn xs
      (matMul xs D (matMul xs (matMul xs V U) (matMul xs D V)))
      (matMul xs D (matMul xs I (matMul xs D V))) :=
    AgreeOn.product xs (agreeRefl xs D) (AgreeOn.product xs S.orthogonal (agreeRefl xs (matMul xs D V)))
  rw [(AgreeOn.product xs (agreeRefl xs U) replaceInner).diagonalSum xs]
  rw [traceMatMulSwap xs xs U,matMulAssoc,matMulAssoc,matMulAssoc]
  have replaceOuter : AgreeOn xs
      (matMul xs D (matMul xs I (matMul xs D (matMul xs V U))))
      (matMul xs D (matMul xs I (matMul xs D I))) :=
    AgreeOn.product xs (agreeRefl xs D) (AgreeOn.product xs (agreeRefl xs I)
      (AgreeOn.product xs (agreeRefl xs D) S.orthogonal))
  rw [replaceOuter.diagonalSum xs]
  unfold trace
  rw [realSum]
  apply AnticommutingDefect.sumCongrMem
  intro i hi
  simp only [diagonalAction xs nd _ _ i i hi, D, I, diagonal, ite_true, ComplexScalar.re_mul,
    ComplexScalar.im_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal]
  grind

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem eigenvalueBounds [DecidableEq α] (entries : HermitianEntries α R) (xs : List α) (nd : xs.Nodup)
    (effect : entries.IsCoordinateEffect xs) (S : SpectralWitness xs (matrix entries))
    (k : α) (hk : k ∈ xs) : 0 ≤ S.values k ∧ S.values k ≤ 1 := by
  let U := S.vectors
  let V := dagger U
  let D := diagonal S.values
  let w : ComplexCoordinates α R := ⟨fun a => (U a k).re, fun a => (U a k).im⟩
  have form : AgreeOn xs (matMul xs (matrix entries) U)
      (matMul xs (matMul xs U D) (matMul xs V U)) := by
    have h := AgreeOn.product xs S.reconstruct (agreeRefl xs U)
    unfold U V D at *
    simp only [matMulAssoc] at h ⊢
    exact h
  have action (a : α) (ha : a ∈ xs) :
      matMul xs (matrix entries) U a k = ofReal (S.values k)*U a k := by
    have reduce := AgreeOn.product xs (agreeRefl xs (matMul xs U D)) S.orthogonal
    rw [form a ha k hk,reduce a ha k hk,diagonalRight xs nd _ _ _ _ hk,
      diagonalRight xs nd _ _ _ _ hk]
    change (1:ComplexScalar R)*_ = _
    rw [Semiring.one_mul]
  have realAct (a : α) (ha : a ∈ xs) : (entries.act xs w).realPart a = S.values k * w.realPart a := by
    have p := congrArg ComplexScalar.re (action a ha)
    simp only [matMul,realSum,ComplexScalar.re_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,
      matrix,HermitianEntries.act,w] at p ⊢
    grind
  have imagAct (a : α) (ha : a ∈ xs) : (entries.act xs w).imagPart a = S.values k * w.imagPart a := by
    have p := congrArg ComplexScalar.im (action a ha)
    simp only [matMul,imagSum,ComplexScalar.im_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,
      matrix,HermitianEntries.act,w] at p ⊢
    grind
  have unitNorm : ComplexCoordinates.inner xs w w=1 := by
    have p := congrArg ComplexScalar.re (S.orthogonal k hk k hk)
    change (sumOver xs (fun a => star (U a k)*U a k)).re=(diagonal (fun _ => 1) k k).re at p
    simp only [diagonal,ite_true,ComplexScalar.re_ofReal] at p
    rw [realSum] at p
    unfold ComplexCoordinates.inner
    rw [←p]
    apply sumOverCongr
    intro a
    simp only [ComplexScalar.re_mul,ComplexScalar.re_star,ComplexScalar.im_star,w]
    grind
  have diagonalQuadratic : ComplexCoordinates.inner xs w (entries.act xs w) =
      S.values k * ComplexCoordinates.inner xs w w := by
    unfold ComplexCoordinates.inner
    rw [sumOverMulLeft]
    apply AnticommutingDefect.sumCongrMem
    intro a ha
    rw [realAct a ha,imagAct a ha]
    grind
  have h := effect w
  rw [diagonalQuadratic,unitNorm,Semiring.mul_one] at h
  exact h

/-- Once an actual diagonalization is provided, the chosen cut has the
claimed fractional trace variance. -/
theorem cutCostLowerFromSpectrum [DecidableEq α] (entries : HermitianEntries α R)
    (xs : List α) (nd : xs.Nodup) (cut : α → Bool) (effect : entries.IsCoordinateEffect xs)
    (S : SpectralWitness (xs.filter cut) (matrix entries)) (k : Nat) (r : R)
    (r0 : 0 ≤ r) (r1 : r < 1)
    (count : (trace (xs.filter cut) (matrix entries)).re = (Nat.cast k : R)+r) :
    r*(1-r) ≤ cutCost xs cut (rowSlack xs (fun i => entries.realPart i i) entries.mass) entries.mass := by
  let ys := xs.filter cut
  have unique : ys.Nodup := nd.filter _
  have ep := restrictionEffect entries xs cut effect
  have traceValue := traceSpectrum ys unique (matrix entries) S
  have traceSquared := traceSquareSpectrum ys unique (matrix entries) S
  rw [traceValue] at count
  have values (x : R) (member : x ∈ ys.map S.values) : 0 ≤ x ∧ x ≤ 1 := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
    exact eigenvalueBounds entries ys unique ep S a ha
  have rounded := RankSeven.traceRoundingSumSquares (ys.map S.values) values k r r0 r1 count
  simp only [List.map_map,Function.comp_def] at rounded
  change sumOver ys (fun a => S.values a*S.values a) ≤ _ at rounded
  rw [cutCostTraceVariance, traceValue,traceSquared]
  have eq := sumOverCongr ys (fun a => show (S.values a)^2=S.values a*S.values a by grind)
  rw [eq]
  change sumOver ys S.values = _ at count
  grind

end Order

end RankSeven.CutTrace

#print axioms RankSeven.CutTrace.restrictionEffect
#print axioms RankSeven.CutTrace.cutCostTraceVariance
#print axioms RankSeven.CutTrace.eigenvalueBounds
#print axioms RankSeven.CutTrace.cutCostLowerFromSpectrum
