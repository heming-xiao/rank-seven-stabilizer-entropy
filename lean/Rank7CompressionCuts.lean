import Rank7Compression
import Rank7ExteriorCuts

namespace RankSeven.Compression

open Lean.Grind
open Pauli (sumOver sumOverCongr sumOverAdd sumOverMulLeft)
open ExteriorCuts (indicator crossing offDiagonal pairSum cutCost pos)

variable {R α : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumWithoutDiagonal [DecidableEq α] (indices : List α) (i : α) (f : α → R)
    (unique : indices.Nodup) (member : i ∈ indices) :
    sumOver indices (fun j => if i = j then 0 else f j) = sumOver indices f - f i := by
  induction indices with
  | nil => cases member
  | cons j rest ih =>
    have ⟨headFresh, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases main : i = j
    · subst j
      have tail : sumOver rest (fun j => if i = j then 0 else f j) = sumOver rest f := by
        unfold sumOver
        congr 1
        apply List.map_congr_left
        intro j inRest
        have unequal : ¬ i = j := fun equal => headFresh (equal ▸ inRest)
        simp [unequal]
      change (if i = i then 0 else f i) + sumOver rest (fun j => if i = j then 0 else f j) =
        f i + sumOver rest f - f i
      rw [tail]
      simp <;> grind
    · have inTail : i ∈ rest := by
        rcases List.mem_cons.mp member with same | tail
        · exact False.elim (main same)
        · exact tail
      change (if i = j then 0 else f j) + sumOver rest (fun j => if i = j then 0 else f j) =
        f j + sumOver rest f - f i
      rw [ite_eq_right main, ih tailUnique inTail]
      grind

theorem HermitianEntries.massDiagonal (entries : HermitianEntries α R) (i : α) :
    entries.mass i i = entries.realPart i i ^ 2 := by
  have skew := entries.imagSkew i i
  have realDiagonal : entries.imagPart i i = 0 := by grind
  unfold mass
  rw [realDiagonal]
  grind

theorem HermitianEntries.rowCap [DecidableEq α] (entries : HermitianEntries α R)
    (indices : List α) (unique : indices.Nodup) (i : α) (member : i ∈ indices)
    (slack : 0 ≤ rowSlack indices (fun j => entries.realPart j j) entries.mass i) :
    sumOver indices (offDiagonal entries.mass i) ≤ entries.realPart i i * (1 - entries.realPart i i) := by
  change sumOver indices (fun j => if i = j then 0 else entries.mass i j) ≤ _
  rw [sumWithoutDiagonal indices i (entries.mass i) unique member, entries.massDiagonal i]
  unfold rowSlack at slack
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem indicatorCrossing (a b : Bool) :
    (crossing a b : R) = indicator a * (1 - indicator b) := by
  cases a <;> cases b <;> simp [crossing, indicator] <;> grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- Relates the crossing-charge formula to Trace(R T R) minus the squared
    norm of the same compression, in the original matrix coordinates. -/
theorem cutCostEqTraces (indices : List α) (cut : α → Bool) (diag : α → R)
    (mass : α → α → R) :
    cutCost indices cut (rowSlack indices diag mass) mass =
      sumOver indices (fun i => indicator (cut i) * diag i) -
      pairSum indices (fun i j => indicator (cut i) * indicator (cut j) * mass i j) := by
  unfold cutCost pairSum rowSlack
  rw [← sumOverAdd, ← sumOverSub]
  apply sumOverCongr
  intro i
  have row :
      indicator (cut i) * sumOver indices (mass i) -
          (sumOver indices fun j => crossing (cut i) (cut j) * mass i j) =
        sumOver indices (fun j => indicator (cut i) * indicator (cut j) * mass i j) := by
    rw [sumOverMulLeft, ← sumOverSub]
    apply sumOverCongr
    intro j
    rw [indicatorCrossing]
    grind
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem HermitianEntries.realLossEqHalf (entries : HermitianEntries α R)
    (indices : List α) (amplitude : α → R) (half : R) (unitHalf : 2*half = 1) :
    diagonalLoss indices amplitude (rowSlack indices (fun i => entries.realPart i i) entries.mass) +
      half * squaredGapCost indices amplitude entries.mass =
      diagonalLoss indices amplitude (fun i => entries.realPart i i) -
        entries.realQuadraticTrace indices amplitude := by
  have identity := entries.realLossIdentity indices amplitude
  dsimp only at identity
  have doubled := congrArg (fun x => half * x) identity
  grind

open ExteriorCuts (Wedge7 wedges product4 sharedLower amplitude error)

/-- The two actual rank-seven cuts and their six/three-wedge errors are
    controlled by the Hermitian compression trace loss. The row cap is
    derived from the diagonal of the contraction defect. -/
theorem realLossControlsRankSevenCuts [DecidableRel (α := R) (· ≤ ·)]
    (entries : HermitianEntries Wedge7 R) (s : Fin 7 → R) (half : R) (unitHalf : 2*half = 1)
    (nonnegative : ∀ i, 0 ≤ s i) (sorted : ∀ i j, i ≤ j → s j ≤ s i)
    (contraction : ∀ i, 0 ≤ rowSlack wedges (fun j => entries.realPart j j) entries.mass i) :
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
      diagonalLoss wedges a w - entries.realQuadraticTrace wedges a := by
  have estimate := ExteriorCuts.rankSevenCrossedCuts s nonnegative sorted
    (rowSlack wedges (fun i => entries.realPart i i) entries.mass) (fun i => entries.realPart i i)
    entries.mass half unitHalf contraction entries.massNonnegative entries.massSymmetric
    (fun i => entries.rowCap wedges ExteriorCuts.wedgesNodup i (ExteriorCuts.memWedges i) (contraction i))
  change _ ≤ diagonalLoss wedges (amplitude s)
      (rowSlack wedges (fun i => entries.realPart i i) entries.mass) +
    half * squaredGapCost wedges (amplitude s) entries.mass at estimate
  rw [entries.realLossEqHalf wedges (amplitude s) half unitHalf] at estimate
  exact estimate

end RankSeven.Compression

#print axioms RankSeven.Compression.cutCostEqTraces
#print axioms RankSeven.Compression.realLossControlsRankSevenCuts
