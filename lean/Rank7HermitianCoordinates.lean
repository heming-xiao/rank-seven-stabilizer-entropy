import Rank7HermitianEffect

namespace RankSeven.Compression

open Lean.Grind
open Pauli (sumOver sumOverCongr sumOverAdd sumOverMulLeft sumOverMulRight sumOverSwap)

variable {R α : Type} [CommRing R]

/-- The real and imaginary coordinates of a vector in the same basis. -/
structure ComplexCoordinates (α R : Type) where
  realPart : α → R
  imagPart : α → R

namespace ComplexCoordinates

instance : Zero (ComplexCoordinates α R) := ⟨⟨fun _ => 0, fun _ => 0⟩⟩

instance : Sub (ComplexCoordinates α R) :=
  ⟨fun v w => ⟨fun i => v.realPart i - w.realPart i, fun i => v.imagPart i - w.imagPart i⟩⟩

instance : SMul R (ComplexCoordinates α R) :=
  ⟨fun c v => ⟨fun i => c * v.realPart i, fun i => c * v.imagPart i⟩⟩

/-- The real part of the Hermitian coordinate pairing. -/
def inner (indices : List α) (v w : ComplexCoordinates α R) : R :=
  sumOver indices fun i => v.realPart i * w.realPart i + v.imagPart i * w.imagPart i

theorem innerSymmetric (indices : List α) (v w : ComplexCoordinates α R) :
    inner indices v w = inner indices w v := by
  unfold inner
  apply sumOverCongr
  intro i
  grind

/-- The real unit vector in the specified complex coordinate. -/
def basis [DecidableEq α] (i : α) : ComplexCoordinates α R :=
  ⟨fun j => if i = j then 1 else 0, fun _ => 0⟩

private theorem sumZero (indices : List α) : sumOver indices (fun _ => (0 : R)) = 0 := by
  induction indices with
  | nil => rfl
  | cons j rest ih =>
    change (0 : R) + sumOver rest (fun _ => 0) = 0
    grind

private theorem sumSelect [DecidableEq α] (indices : List α) (i : α) (f : α → R)
    (unique : indices.Nodup) (member : i ∈ indices) :
    sumOver indices (fun j => if i = j then f j else 0) = f i := by
  induction indices with
  | nil => cases member
  | cons j rest ih =>
    obtain ⟨fresh, uniqueTail⟩ := List.nodup_cons.mp unique
    by_cases equal : i = j
    · subst j
      have zeroTail : sumOver rest (fun j => if i = j then f j else 0) = (0 : R) := by
        have terms : (rest.map fun j => if i = j then f j else 0) = rest.map (fun _ => 0) := by
          apply List.map_congr_left
          intro j inRest
          have unequal : ¬ i = j := fun same => fresh (same ▸ inRest)
          simp [unequal]
        calc
          _ = sumOver rest (fun _ => (0 : R)) := by
            unfold sumOver
            rw [terms]
          _ = 0 := sumZero rest
      change (if i = i then f i else 0) + sumOver rest (fun j => if i = j then f j else 0) = f i
      rw [ite_eq_left rfl, zeroTail]
      grind
    · have inTail : i ∈ rest := by
        rcases List.mem_cons.mp member with same | tail
        · exact False.elim (equal same)
        · exact tail
      change (if i = j then f j else 0) + sumOver rest (fun j => if i = j then f j else 0) = f i
      rw [ite_eq_right equal, ih uniqueTail inTail]
      grind

theorem innerBasisLeft [DecidableEq α] (indices : List α) (unique : indices.Nodup)
    (i : α) (member : i ∈ indices) (v : ComplexCoordinates α R) :
    inner indices (basis i) v = v.realPart i := by
  unfold inner
  rw [← sumSelect indices i v.realPart unique member]
  apply sumOverCongr
  intro j
  unfold basis
  by_cases equal : i = j <;> simp [equal] <;> grind

theorem basisNorm [DecidableEq α] (indices : List α) (unique : indices.Nodup)
    (i : α) (member : i ∈ indices) :
    inner indices (basis (R := R) i) (basis i) = 1 := by
  rw [innerBasisLeft indices unique i member]
  simp [basis]


variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem memberLeSum (indices : List α) (f : α → R)
    (nonnegative : ∀ j, 0 ≤ f j) {i : α} (member : i ∈ indices) :
    f i ≤ sumOver indices f := by
  induction indices with
  | nil => cases member
  | cons j rest ih =>
    change f i ≤ f j + sumOver rest f
    rcases List.mem_cons.mp member with same | tail
    · subst j
      have tailNonnegative := sumOverNonnegative rest f (fun k _ => nonnegative k)
      grind
    · have bound := ih tail
      have headNonnegative := nonnegative j
      grind

private theorem eqZeroOfSquareEqZero (a : R) (h : a ^ 2 = 0) : a = 0 := by
  by_cases positive : 0 < a
  · have contradiction := OrderedRing.mul_pos positive positive
    grind
  · by_cases negative : a < 0
    · have opposite : 0 < -a := by grind
      have contradiction := OrderedRing.mul_pos opposite opposite
      grind
    · grind

/-- The usual real inner product, for an index list that contains all
coordinates. Nondegeneracy follows from nonnegativity of each coordinate square. -/
def innerForm (indices : List α) (covers : ∀ i, i ∈ indices) :
    RealInnerForm R (ComplexCoordinates α R) where
  inner := inner indices
  symmetric := innerSymmetric indices
  zeroLeft v := by
    unfold inner
    rw [← sumZero indices]
    apply sumOverCongr
    intro i
    change (0 : R) * v.realPart i + 0 * v.imagPart i = 0
    grind
  subLeft v w z := by
    unfold inner
    rw [← sumOverSub]
    apply sumOverCongr
    intro i
    change (v.realPart i - w.realPart i) * z.realPart i +
      (v.imagPart i - w.imagPart i) * z.imagPart i = _
    grind
  smulLeft c v w := by
    unfold inner
    rw [sumOverMulLeft]
    apply sumOverCongr
    intro i
    change (c * v.realPart i) * w.realPart i + (c * v.imagPart i) * w.imagPart i = _
    grind
  nonnegative v := by
    unfold inner
    apply sumOverNonnegative
    intro i _
    have realNonnegative := squareNonnegative (v.realPart i)
    have imagNonnegative := squareNonnegative (v.imagPart i)
    grind
  eqZeroOfInnerSelfEqZero v zero := by
    let mass i := v.realPart i * v.realPart i + v.imagPart i * v.imagPart i
    change sumOver indices mass = 0 at zero
    have coordinatesZero (i : α) : v.realPart i = 0 ∧ v.imagPart i = 0 := by
      have massNonnegative (j : α) : 0 ≤ mass j := by
        dsimp only [mass]
        have realNonnegative := squareNonnegative (v.realPart j)
        have imagNonnegative := squareNonnegative (v.imagPart j)
        grind
      have bound := memberLeSum indices mass massNonnegative (covers i)
      dsimp only [mass] at bound
      rw [zero] at bound
      have realNonnegative := squareNonnegative (v.realPart i)
      have imagNonnegative := squareNonnegative (v.imagPart i)
      exact ⟨eqZeroOfSquareEqZero _ (by grind), eqZeroOfSquareEqZero _ (by grind)⟩
    cases v with
    | mk realPart imagPart =>
      congr
      · funext i
        exact (coordinatesZero i).1
      · funext i
        exact (coordinatesZero i).2

end ComplexCoordinates

/-- Matrix-vector multiplication, split into the two real coordinates. -/
def HermitianEntries.act (entries : HermitianEntries α R) (indices : List α)
    (v : ComplexCoordinates α R) : ComplexCoordinates α R :=
  ⟨fun i => sumOver indices fun j =>
      entries.realPart i j * v.realPart j - entries.imagPart i j * v.imagPart j,
    fun i => sumOver indices fun j =>
      entries.realPart i j * v.imagPart j + entries.imagPart i j * v.realPart j⟩

/-- The two coordinate terms contributed by the entry in row i and column j. -/
private def HermitianEntries.actionPair (entries : HermitianEntries α R)
    (v w : ComplexCoordinates α R) (i j : α) : R :=
  (entries.realPart i j * v.realPart j - entries.imagPart i j * v.imagPart j) * w.realPart i +
    (entries.realPart i j * v.imagPart j + entries.imagPart i j * v.realPart j) * w.imagPart i

private theorem HermitianEntries.innerActExpansion (entries : HermitianEntries α R)
    (indices : List α) (v w : ComplexCoordinates α R) :
    ComplexCoordinates.inner indices (entries.act indices v) w =
      sumOver indices (fun i => sumOver indices (entries.actionPair v w i)) := by
  unfold ComplexCoordinates.inner
  apply sumOverCongr
  intro i
  simp only [act]
  rw [sumOverMulRight, sumOverMulRight, ← sumOverAdd]
  rfl

theorem HermitianEntries.actSelfAdjoint (entries : HermitianEntries α R)
    (indices : List α) (v w : ComplexCoordinates α R) :
    ComplexCoordinates.inner indices (entries.act indices v) w =
      ComplexCoordinates.inner indices v (entries.act indices w) := by
  rw [ComplexCoordinates.innerSymmetric indices v (entries.act indices w),
    entries.innerActExpansion, entries.innerActExpansion]
  rw [sumOverSwap indices indices (entries.actionPair v w)]
  apply sumOverCongr
  intro j
  apply sumOverCongr
  intro i
  unfold actionPair
  rw [← entries.realSymmetric i j, entries.imagSkew j i]
  grind

theorem HermitianEntries.actBasis [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (i : α) (member : i ∈ indices) :
    entries.act indices (ComplexCoordinates.basis i) =
      ⟨fun j => entries.realPart j i, fun j => entries.imagPart j i⟩ := by
  have realColumn (j : α) :
      (entries.act indices (ComplexCoordinates.basis i)).realPart j =
        entries.realPart j i := by
    unfold act
    simp only [ComplexCoordinates.basis]
    rw [← ComplexCoordinates.sumSelect indices i (entries.realPart j) unique member]
    apply sumOverCongr
    intro k
    by_cases equal : i = k <;> simp [equal] <;> grind
  have imagColumn (j : α) :
      (entries.act indices (ComplexCoordinates.basis i)).imagPart j =
        entries.imagPart j i := by
    unfold act
    simp only [ComplexCoordinates.basis]
    rw [← ComplexCoordinates.sumSelect indices i (entries.imagPart j) unique member]
    apply sumOverCongr
    intro k
    by_cases equal : i = k <;> simp [equal] <;> grind
  cases output : entries.act indices (ComplexCoordinates.basis i) with
  | mk re im =>
    congr
    · funext j
      simpa [output] using (realColumn j)
    · funext j
      simpa [output] using (imagColumn j)

theorem HermitianEntries.basisQuadratic [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (i : α) (member : i ∈ indices) :
    ComplexCoordinates.inner indices (ComplexCoordinates.basis i)
      (entries.act indices (ComplexCoordinates.basis i)) = entries.realPart i i := by
  rw [ComplexCoordinates.innerBasisLeft indices unique i member, entries.actBasis indices unique i member]

theorem HermitianEntries.basisImageNorm [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (i : α) (member : i ∈ indices) :
    ComplexCoordinates.inner indices (entries.act indices (ComplexCoordinates.basis i))
      (entries.act indices (ComplexCoordinates.basis i)) = sumOver indices (entries.mass i) := by
  rw [entries.actBasis indices unique i member]
  unfold ComplexCoordinates.inner
  apply sumOverCongr
  intro j
  change entries.realPart j i * entries.realPart j i +
    entries.imagPart j i * entries.imagPart j i = entries.mass i j
  rw [entries.massSymmetric i j]
  unfold HermitianEntries.mass
  grind

variable [LE R]

/-- The upstream premise that the physical compression is a positive effect,
expressed using its actual matrix action and the real quadratic form. -/
def HermitianEntries.IsCoordinateEffect (entries : HermitianEntries α R) (indices : List α) : Prop :=
  ∀ v : ComplexCoordinates α R,
    0 ≤ ComplexCoordinates.inner indices v (entries.act indices v) ∧
      ComplexCoordinates.inner indices v (entries.act indices v) ≤
        ComplexCoordinates.inner indices v v

theorem HermitianEntries.effectDiagonalBounds [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (effect : entries.IsCoordinateEffect indices)
    (i : α) (member : i ∈ indices) :
    0 ≤ entries.realPart i i ∧ entries.realPart i i ≤ 1 := by
  have bound := effect (ComplexCoordinates.basis i)
  rw [entries.basisQuadratic indices unique i member,
    ComplexCoordinates.basisNorm indices unique i member] at bound
  exact bound

variable [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Derive the diagonal of T-T² from its effect premise, using a coordinate
basis vector to identify its quadratic value and its image norm. -/
theorem HermitianEntries.effectRowSlack [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (covers : ∀ i, i ∈ indices)
    (effect : entries.IsCoordinateEffect indices) (i : α) :
    0 ≤ rowSlack indices (fun j => entries.realPart j j) entries.mass i := by
  let form := ComplexCoordinates.innerForm (R := R) indices covers
  have bound := effectNormLeQuadratic form (entries.act indices) (entries.actSelfAdjoint indices)
    (fun v => (effect v).1) (fun v => (effect v).2) (ComplexCoordinates.basis i)
  change ComplexCoordinates.inner indices (entries.act indices (ComplexCoordinates.basis i))
      (entries.act indices (ComplexCoordinates.basis i)) ≤
    ComplexCoordinates.inner indices (ComplexCoordinates.basis i)
      (entries.act indices (ComplexCoordinates.basis i)) at bound
  rw [entries.basisImageNorm indices unique i (covers i),
    entries.basisQuadratic indices unique i (covers i)] at bound
  unfold rowSlack
  grind

open ExteriorCuts (Wedge7 wedges product4 sharedLower amplitude error cutCost pos)

/-- The crossed rank-seven cut bound accepts the physical effect premise
directly. The row slack needed by the earlier theorem is derived here. -/
theorem effectRealLossControlsRankSevenCuts [DecidableRel (α := R) (· ≤ ·)]
    (entries : HermitianEntries Wedge7 R) (s : Fin 7 → R) (half : R) (unitHalf : 2 * half = 1)
    (nonnegative : ∀ i, 0 ≤ s i) (sorted : ∀ i j, i ≤ j → s j ≤ s i)
    (effect : entries.IsCoordinateEffect wedges) :
    let lₛ := sharedLower s
    let uₛ := product4 s 0 2 5 6
    let l₁ := product4 s 0 2 4 5
    let u₁ := product4 s 0 1 5 6
    let a := amplitude s
    let w i := entries.realPart i i
    let slack := rowSlack wedges w entries.mass
    (pos (uₛ-lₛ))^2 * cutCost wedges (fun i => i.level.low) slack entries.mass +
    (pos (u₁-l₁))^2 * cutCost wedges (fun i => i.level.high) slack entries.mass -
      sumOver wedges (fun i =>
        ((if i.lowBad then error lₛ uₛ (a i) else 0) +
         (if i.highBad then error l₁ u₁ (a i) else 0)) * (w i*(1-w i))) ≤
      diagonalLoss wedges a w - entries.realQuadraticTrace wedges a :=
  realLossControlsRankSevenCuts entries s half unitHalf nonnegative sorted
    (entries.effectRowSlack wedges ExteriorCuts.wedgesNodup ExteriorCuts.memWedges effect)

end RankSeven.Compression
