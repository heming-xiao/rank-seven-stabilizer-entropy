import Rank7ComplexEightPoint
import Rank7HyperplaneInduction

namespace RankSeven.ExteriorDeterminantBridge

open Lean.Grind Pauli ExteriorOccupation ExteriorOperators ExteriorPauliBase
open HyperplaneInduction (sourceSite minor4 exteriorLift)

variable {C R : Type} [CommRing C] [CommRing R]

attribute [local instance] Ring.intCast

/-- Increasing physical row labels of an eight-point four-wedge. -/
def baseRows (u : Wedge) (j : Fin 4) : Point := atPosition (tupleOf u) j

/-- The four columns of the map in their increasing source order. -/
def columnsOf (A : Point → Fin 7 → C) (w : ExteriorCuts.Wedge7) : List (Point → C) :=
  [fun i => A i w.i, fun i => A i w.j, fun i => A i w.k, fun i => A i w.m]

private abbrev Factor := Point × Fin 4
private abbrev Term := Bool × List Factor

private def insertFactor (a : Factor) : List Factor → List Factor
  | [] => [a]
  | b :: tail => if a.1 ≤ b.1 then a :: b :: tail else b :: insertFactor a tail

private def prefixFactor (i : Point) (j : Fin 4) (m : Mask) (t : Term) : Term :=
  ((decide (signBelow i m < 0)) ^^ t.1, insertFactor (i,j) t.2)

/-- Record only occupied removals, ending at the vacuum, in column order. -/
private def paths : List (Fin 4) → Mask → List Term
  | [], m => if m.val = 0 then [(false, [])] else []
  | j :: js, m => (points.filter (fun i => occupied i m)).flatMap fun i =>
      (paths js (toggle i m)).map (prefixFactor i j m)

private def determinantTerm (r : Fin 4 → Point) (p : Permutation) : Term :=
  (oddPermutation p, [(r 0,p.1.1), (r 1,p.1.2), (r 2,p.2.1), (r 3,p.2.2)])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem fourPathTable : ∀ u : Wedge,
    (paths [0,1,2,3] (maskIndex u)).Perm
      (permutations.map (determinantTerm (baseRows u))) := by decide

private def factorsValue (x : Fin 4 → Point → C) : List Factor → C
  | [] => 1
  | (i,j) :: fs => x j i * factorsValue x fs

private def value (x : Fin 4 → Point → C) (t : Term) : C :=
  if t.1 then -(factorsValue x t.2) else factorsValue x t.2

private theorem insert_value (x : Fin 4 → Point → C) (a : Factor) (fs : List Factor) :
    factorsValue x (insertFactor a fs) = x a.2 a.1 * factorsValue x fs := by
  induction fs with
  | nil => rfl
  | cons b fs ih =>
    simp only [insertFactor]
    split
    · rfl
    · simp only [factorsValue, ih]
      grind

set_option maxRecDepth 100000 in
private theorem signCases : ∀ (i : Point) (m : Mask),
    signBelow i m = (if signBelow i m < 0 then -1 else 1) := by decide

private theorem prefix_value (x : Fin 4 → Point → C) (i : Point) (j : Fin 4)
    (m : Mask) (t : Term) :
    value x (prefixFactor i j m t) =
      (x j i * Int.cast (signBelow i m)) * value x t := by
  rcases t with ⟨s,fs⟩
  have h := signCases i m
  by_cases neg : signBelow i m < 0 <;>
    simp [neg] at h <;>
    cases s <;> simp [value, prefixFactor, insert_value, h] <;> grind

private theorem sumMap {α β : Type} (xs : List α) (g : α → β) (f : β → C) :
    sumOver (xs.map g) f = sumOver xs (fun a => f (g a)) := by
  simp only [sumOver, List.map_map, Function.comp_def]

private theorem sumFilterZero {α : Type} (xs : List α) (keep : α → Bool) (f : α → C)
    (zero : ∀ i, keep i = false → f i = 0) :
    sumOver xs f = sumOver (xs.filter keep) f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : keep a
    · rw [List.filter_cons, ha]
      change f a + sumOver xs f = sumOver (xs.filter keep) f
      rw [zero a ha, ih]
      grind
    · rw [List.filter_cons, ha]
      change f a + sumOver xs f = f a + sumOver (xs.filter keep) f
      rw [ih]

private theorem paths_value (x : Fin 4 → Point → C) (js : List (Fin 4)) (m : Mask) :
    exteriorProduct (js.map x) m = sumOver (paths js m) (value x) := by
  induction js generalizing m with
  | nil =>
    simp [exteriorProduct, vacuum, paths, sumOver]
    split <;> simp [value, factorsValue, Semiring.add_zero]
  | cons j js ih =>
    change sumOver points (fun i => x j i * site raiseCoeff i (exteriorProduct (js.map x)) m) =
      sumOver ((points.filter (fun i => occupied i m)).flatMap (fun i =>
        (paths js (toggle i m)).map (prefixFactor i j m))) (value x)
    rw [sumOverFlatMap, sumFilterZero points (fun i => occupied i m) _ (by
      intro i hi
      simp [site, raiseCoeff, hi]
      grind)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have occ := (List.mem_filter.mp hi).2
    rw [sumMap]
    simp only [site, raiseCoeff, occ, ite_true, ih, ← Semiring.mul_assoc, sumOverMulLeft,
      prefix_value]

private theorem sumPerm {α : Type} {xs ys : List α} (p : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- The mask creation signs and the determinant inversion signs give identical
coefficients for arbitrary columns over any commutative ring. -/
theorem exteriorProduct_eq_minor4 (A : Point → Fin 7 → C) (w : ExteriorCuts.Wedge7)
    (u : Wedge) :
    restrictFour (exteriorProduct (columnsOf A w)) u = minor4 A (baseRows u) w := by
  let x (j : Fin 4) (i : Point) := A i (sourceSite w j)
  change exteriorProduct (([0,1,2,3] : List (Fin 4)).map x) (maskIndex u) = _
  rw [paths_value, sumPerm (fourPathTable u), sumMap]
  apply sumOverCongr
  intro p
  simp only [value, determinantTerm, factorsValue, x, Semiring.mul_one, Semiring.mul_assoc]

/-- The 35 source coordinates as a linear combination of actual mask forms. -/
def liftTerms (A : Point → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    List (ComplexScalar R × List (Point → ComplexScalar R)) :=
  ExteriorCuts.wedges.map fun w => (v w, columnsOf A w)

theorem restrict_wedgeLinearCombination (A : Point → Fin 7 → ComplexScalar R)
    (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    restrictFour (ComplexExterior.wedgeLinearCombination (liftTerms A v)) =
      exteriorLift baseRows A v := by
  funext u
  unfold restrictFour ComplexExterior.wedgeLinearCombination liftTerms exteriorLift
  rw [sumMap]
  apply sumOverCongr
  intro w
  change v w * restrictFour (exteriorProduct (columnsOf A w)) u = _
  rw [exteriorProduct_eq_minor4, CommSemiring.mul_comm]

theorem compression_of_exteriorLift [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [OrderedRing R] (half : R) (unitHalf : 2 * half = 1)
    (A : Point → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    2 * ComplexExterior.squaredNorm (projectMaskWaves (ComplexScalar.ofReal half)
      (ComplexExterior.wedgeLinearCombination (liftTerms A v))) ≤
      ComplexExterior.squaredNorm (ComplexExterior.wedgeLinearCombination (liftTerms A v)) := by
  let cols := (List.finRange 7).map (fun j => fun i => A i j)
  apply ComplexExterior.eightPointComplexCompressionOfRows half unitHalf cols (by simp [cols])
  intro t ht
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp ht
  refine ⟨rfl, ?_⟩
  intro col hc
  apply List.mem_map.mpr
  rcases (show col = (fun i => A i w.i) ∨ col = (fun i => A i w.j) ∨
      col = (fun i => A i w.k) ∨ col = (fun i => A i w.m) from by simpa [columnsOf] using hc) with
      h|h|h|h
  all_goals exact ⟨_, List.mem_finRange _, h.symm⟩

private theorem sumZero {α : Type} (xs : List α) (f : α → C) (zero : ∀ i, f i = 0) :
    sumOver xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change f a + sumOver xs f = 0
    rw [zero, ih, Semiring.add_zero]

theorem liftTerms_grade (A : Point → Fin 7 → ComplexScalar R)
    (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    homogeneous 4 (ComplexExterior.wedgeLinearCombination (liftTerms A v)) := by
  intro m hm
  unfold ComplexExterior.wedgeLinearCombination liftTerms
  rw [sumMap]
  apply sumZero
  intro w
  have vanish := exteriorProduct_grade (columnsOf A w) m hm
  change v w * exteriorProduct (columnsOf A w) m = 0
  rw [vanish, Semiring.mul_zero]

/-- The 70 increasing wedge coordinates carry all of the norm in grade four. -/
theorem squaredNorm_grade_four (f : Form (ComplexScalar R)) (hf : homogeneous 4 f) :
    ComplexExterior.squaredNorm f = sumOver wedgeIndices (fun u => ComplexScalar.normSq (restrictFour f u)) := by
  rw [ComplexExterior.squaredNorm, ComplexExterior.formPairingStarSelf_re,
    sumFilterZero masks (fun m => degree m == 4) _ (by
      intro m outside
      rw [hf m (by simpa using outside), ComplexScalar.normSq_zero]),
    ← wedgeMasksOrdered, sumMap]
  rfl

/-- The eight-point compression bound directly on the 35-to-70 determinant lift. -/
theorem coordinate_compression [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [OrderedRing R] (half : R) (unitHalf : 2 * half = 1)
    (A : Point → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    2 * sumOver wedgeIndices (fun u => ComplexScalar.normSq
      (projectWaves (ComplexScalar.ofReal half) (exteriorLift baseRows A v) u)) ≤
    sumOver wedgeIndices (fun u => ComplexScalar.normSq (exteriorLift baseRows A v u)) := by
  have bound := compression_of_exteriorLift half unitHalf A v
  rw [squaredNorm_grade_four (projectMaskWaves (ComplexScalar.ofReal half)
    (ComplexExterior.wedgeLinearCombination (liftTerms A v))) (waveForm_grade_four _),
    squaredNorm_grade_four _ (liftTerms_grade A v), restrict_projectMaskWaves,
    restrict_wedgeLinearCombination] at bound
  exact bound

private theorem castSum {α : Type} (xs : List α) (f : α → Int) :
    Int.cast (R := C) (sumOver xs f) = sumOver xs (fun x => Int.cast (f x)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons a xs ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    rw [Ring.intCast_add, ih]

/-- The normalized physical Pauli entry is the half-scaled integer plane Gram entry. -/
theorem normalized_physical_eq_gram (i half : C) (hi : i^4 = 1) (unitHalf : 2*half = 1)
    (u v : Wedge) :
    half^6 * physicalExteriorSum i u v = half * Int.cast (planeGram u v) := by
  rw [normalized_physical_plane_gram _ _ hi unitHalf, planeGram, castSum]
  simp only [Ring.intCast_mul]

private theorem complexHalf (half : R) (hh : 2*half = 1) :
    2 * ComplexScalar.ofReal half = (1 : ComplexScalar R) := by
  apply ComplexScalar.ext
  · change 2 * half - 0 * 0 = 1
    grind
  · change 2 * 0 + 0 * half = 0
    grind

private theorem projectWavesEntries (half : R) (hh : 2*half = 1) (z : Wedge → ComplexScalar R)
    (u : Wedge) :
    projectWaves (ComplexScalar.ofReal half) z u = sumOver wedgeIndices (fun v =>
      ComplexScalar.ofReal (half * Int.cast (planeGram u v)) * z v) := by
  have one : (1 : ComplexScalar R)^4 = 1 := by grind
  rw [physicalExteriorAction _ _ one (complexHalf half hh)]
  apply sumOverCongr
  intro v
  rw [normalized_physical_eq_gram _ _ one (complexHalf half hh)]
  congr 1
  change ComplexScalar.ofReal half * ComplexScalar.ofReal (Int.cast (planeGram u v)) =
    ComplexScalar.ofReal (half * Int.cast (planeGram u v))
  apply ComplexScalar.ext <;> simp <;> grind

private theorem starSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    ComplexScalar.star (sumOver xs f) = sumOver xs (fun i => ComplexScalar.star (f i)) := by
  induction xs with
  | nil => exact ComplexScalar.star_ofReal (0 : R)
  | cons i xs ih =>
    change ComplexScalar.star (f i + sumOver xs f) =
      ComplexScalar.star (f i) + sumOver xs (fun j => ComplexScalar.star (f j))
    rw [ComplexScalar.star_add, ih]

private theorem reSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (f i + sumOver xs f).re = (f i).re + sumOver xs (fun j => (f j).re)
    rw [ComplexScalar.re_add, ih]

private theorem starProjection (half : R) (hh : 2*half = 1) (z : Wedge → ComplexScalar R) :
    (fun u => ComplexScalar.star (projectWaves (ComplexScalar.ofReal half) z u)) =
      projectWaves (ComplexScalar.ofReal half) (fun u => ComplexScalar.star (z u)) := by
  funext u
  rw [projectWavesEntries _ hh, starSum, projectWavesEntries _ hh]
  simp only [ComplexScalar.star_mul, ComplexScalar.star_ofReal]

private theorem wedgeNormPairing (z : Wedge → ComplexScalar R) :
    sumOver wedgeIndices (fun u => ComplexScalar.normSq (z u)) =
      (wedgePairing (fun u => ComplexScalar.star (z u)) z).re := by
  rw [wedgePairing, reSum]
  simp only [ComplexScalar.re_star_mul_self]

private theorem projectionQuadratic (half : R) (hh : 2*half = 1) (z : Wedge → ComplexScalar R) :
    sumOver wedgeIndices (fun u => ComplexScalar.normSq (projectWaves (ComplexScalar.ofReal half) z u)) =
      HyperplaneInduction.quadratic wedgeIndices (fun uv => half * Int.cast (planeGram uv.1 uv.2)) z := by
  rw [wedgeNormPairing, starProjection _ hh, projectWaves_selfAdjoint,
    projectWaves_idempotent _ (complexHalf half hh)]
  unfold wedgePairing HyperplaneInduction.quadratic productIndices
  rw [reSum, sumOverFlatMap]
  apply sumOverCongr
  intro u
  rw [projectWavesEntries _ hh, sumOverMulLeft, reSum, sumMap]
  apply sumOverCongr
  intro v
  unfold HyperplaneInduction.realWeight
  simp only [ComplexScalar.re_mul, ComplexScalar.im_mul, ComplexScalar.re_star, ComplexScalar.im_star,
    ComplexScalar.re_ofReal, ComplexScalar.im_ofReal]
  grind

private theorem diagonalQuadratic (half : R) (z : Wedge → ComplexScalar R) :
    HyperplaneInduction.quadratic wedgeIndices (fun uv => if uv.1 = uv.2 then half else 0) z =
      half * sumOver wedgeIndices (fun u => ComplexScalar.normSq (z u)) := by
  unfold HyperplaneInduction.quadratic productIndices
  rw [sumOverFlatMap, sumOverMulLeft]
  apply sumOverCongr
  intro u
  rw [sumMap]
  calc
    _ = sumOver wedgeIndices (fun v => if u=v then half * ComplexScalar.normSq (z v) else 0) := by
      apply sumOverCongr
      intro v
      by_cases h : u = v <;> simp [h, HyperplaneInduction.realWeight, ComplexScalar.normSq] <;> grind
    _ = _ := sumOnIndex wedgeIndices u _ (by decide) (List.mem_finRange _)

/-- The base defect in the physical increasing wedge basis. -/
def baseDefect (half : R) (uv : Wedge × Wedge) : R :=
  (if uv.1 = uv.2 then half else 0) - half * Int.cast (planeGram uv.1 uv.2)

theorem baseDefect_quadratic (half : R) (hh : 2*half = 1) (z : Wedge → ComplexScalar R) :
    HyperplaneInduction.quadratic wedgeIndices (baseDefect half) z =
      half * sumOver wedgeIndices (fun u => ComplexScalar.normSq (z u)) -
        sumOver wedgeIndices (fun u => ComplexScalar.normSq (projectWaves (ComplexScalar.ofReal half) z u)) := by
  rw [← diagonalQuadratic, projectionQuadratic _ hh]
  unfold HyperplaneInduction.quadratic baseDefect
  rw [← Compression.sumOverSub]
  apply sumOverCongr
  intro uv
  grind

/-- Unconditional base inequality for an arbitrary complex eight-by-seven map
and all 35 source exterior coordinates. -/
theorem base_quadratic_nonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
    [OrderedRing R] (half : R) (unitHalf : 2 * half = 1) (A : Point → Fin 7 → ComplexScalar R)
    (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    0 ≤ HyperplaneInduction.quadratic wedgeIndices (baseDefect half) (exteriorLift baseRows A v) := by
  rw [baseDefect_quadratic _ unitHalf]
  have h := coordinate_compression half unitHalf A v
  let total := sumOver wedgeIndices (fun u => ComplexScalar.normSq (exteriorLift baseRows A v u))
  let proj := sumOver wedgeIndices (fun u => ComplexScalar.normSq
    (projectWaves (ComplexScalar.ofReal half) (exteriorLift baseRows A v) u))
  change 2 * proj ≤ total at h
  change 0 ≤ half * total - proj
  have slack : 0 ≤ total - 2 * proj := by grind
  have mul := OrderedRing.mul_nonneg (show 0 ≤ half by grind) slack
  have factor := congrArg (fun t => t * proj) unitHalf
  grind

end RankSeven.ExteriorDeterminantBridge

#print axioms RankSeven.ExteriorDeterminantBridge.exteriorProduct_eq_minor4
#print axioms RankSeven.ExteriorDeterminantBridge.coordinate_compression
#print axioms RankSeven.ExteriorDeterminantBridge.base_quadratic_nonnegative
