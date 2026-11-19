import Rank7Compression
import Rank7ExteriorOperators

namespace RankSeven

open Lean.Grind Pauli

variable {C α : Type} [CommRing C]

private theorem sumOverCongrMem (xs : List α) {f g : α → C}
    (entries : ∀ x ∈ xs, f x = g x) : sumOver xs f = sumOver xs g := by
  unfold sumOver
  rw [List.map_congr_left entries]

private theorem sumOfZeros (xs : List α) : sumOver xs (fun _ => (0 : C)) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change 0 + sumOver xs (fun _ => (0 : C)) = 0
    rw [ih]
    grind

def deleteColumn [DecidableEq α] (xs : List α) (j : α) : List α :=
  xs.filter (fun i => decide (i ≠ j))

theorem deleteColumn_mem [DecidableEq α] {xs : List α} {j i : α} :
    i ∈ deleteColumn xs j ↔ i ∈ xs ∧ i ≠ j := by
  rw [deleteColumn, List.mem_filter]
  simp only [decide_eq_true_eq]

theorem columnSplit [DecidableEq α] (xs : List α) (pivot : α) (f : α → C)
    (distinct : xs.Nodup) (present : pivot ∈ xs) :
    (deleteColumn xs pivot).length + 1 = xs.length ∧
    sumOver xs f = f pivot + sumOver (deleteColumn xs pivot) f := by
  induction xs with
  | nil => cases present
  | cons a xs ih =>
    obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    by_cases same : a = pivot
    · subst a
      have filterTail : deleteColumn xs pivot = xs := by
        apply List.filter_eq_self.mpr
        intro i member
        have ne : i ≠ pivot := fun eq => fresh (eq ▸ member)
        exact decide_eq_true ne
      have deleted : deleteColumn (pivot :: xs) pivot = xs := by
        unfold deleteColumn at *
        rw [List.filter_cons, ite_eq_right (by simp : ¬ (decide (pivot ≠ pivot) = true)), filterTail]
      rw [deleted]
      exact ⟨rfl, rfl⟩
    · have inTail : pivot ∈ xs := by
        rcases List.mem_cons.mp present with first | later
        · exact False.elim (same first.symm)
        · exact later
      obtain ⟨size, sums⟩ := ih tailDistinct inTail
      have chosen : deleteColumn (a :: xs) pivot = a :: deleteColumn xs pivot := by
        unfold deleteColumn
        rw [List.filter_cons, ite_eq_left (decide_eq_true same)]
      rw [chosen]
      constructor
      · simp only [List.length_cons]
        omega
      · change f a + sumOver xs f = f pivot + (f a + sumOver (deleteColumn xs pivot) f)
        rw [sums]
        grind

/-- A finite homogeneous system with more columns than rows has a
    nonzero solution over a domain. Elimination clears the pivot
    instead of dividing, so the proof also applies to ordered rings. -/
theorem shortRowsHaveKernel [DecidableEq α]
    (oneNonzero : (1 : C) ≠ 0)
    (mulNonzero : ∀ a b : C, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (rows : List (α → C)) (cols : List α)
    (distinct : cols.Nodup) (short : rows.length < cols.length) :
    ∃ x : α → C, (∃ i ∈ cols, x i ≠ 0) ∧
      ∀ r ∈ rows, sumOver cols (fun i => r i * x i) = 0 := by
  suffices all : ∀ n : Nat, ∀ (rows : List (α → C)) (cols : List α),
      rows.length = n → cols.Nodup → rows.length < cols.length →
      ∃ x : α → C, (∃ i ∈ cols, x i ≠ 0) ∧
        ∀ r ∈ rows, sumOver cols (fun i => r i * x i) = 0 by
    exact all rows.length rows cols rfl distinct short
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rows cols lengthEq distinct short
    cases rows with
    | nil =>
      cases cols with
      | nil => exact False.elim (by simp at short)
      | cons i cols =>
        refine ⟨fun _ => 1, ⟨i, List.mem_cons_self, oneNonzero⟩, ?_⟩
        intro _ member
        cases member
    | cons first rows =>
      by_cases nonzero : ∃ p ∈ cols, first p ≠ 0
      · obtain ⟨pivot, inCols, pivotNonzero⟩ := nonzero
        let free := deleteColumn cols pivot
        let eliminate (r : α → C) (i : α) := first pivot * r i - r pivot * first i
        have smaller : (rows.map eliminate).length < free.length := by
          have size := (columnSplit cols pivot first distinct inCols).1
          change free.length + 1 = cols.length at size
          simp only [List.length_map]
          simp only [List.length_cons] at short
          omega
        have freeDistinct : free.Nodup := List.Pairwise.filter _ distinct
        obtain ⟨y, ⟨j, freeJ, yNonzero⟩, solvesFree⟩ :=
          ih (rows.map eliminate).length (by rw [← lengthEq, List.length_map, List.length_cons]; omega)
            (rows.map eliminate) free rfl freeDistinct smaller
        let head := sumOver free (fun i => first i * y i)
        let x (i : α) := if i = pivot then -head else first pivot * y i
        have someNonzero : ∃ i ∈ cols, x i ≠ 0 := by
          have jData := deleteColumn_mem.mp freeJ
          refine ⟨j, jData.1, ?_⟩
          unfold x
          rw [ite_eq_right jData.2]
          exact mulNonzero _ _ pivotNonzero yNonzero
        refine ⟨x, someNonzero, ?_⟩
        intro r inRows
        have restSum (r : α → C) :
            sumOver free (fun i => r i * x i) = first pivot * sumOver free (fun i => r i * y i) := by
          rw [sumOverMulLeft]
          apply sumOverCongrMem
          intro i member
          have nei := (deleteColumn_mem.mp member).2
          unfold x
          rw [ite_eq_right nei]
          grind
        rw [(columnSplit cols pivot (fun i => r i * x i) distinct inCols).2, restSum]
        change r pivot * x pivot + first pivot * sumOver free (fun i => r i * y i) = 0
        rcases List.mem_cons.mp inRows with rfl | inTail
        · unfold x
          rw [ite_eq_left rfl]
          grind
        · have eliminated := solvesFree (eliminate r) (List.mem_map.mpr ⟨r, inTail, rfl⟩)
          have combine :
              sumOver free (fun i => eliminate r i * y i) =
                first pivot * sumOver free (fun i => r i * y i) - r pivot * head := by
            change _ = _ - r pivot * sumOver free (fun i => first i * y i)
            rw [sumOverMulLeft, sumOverMulLeft, ← Compression.sumOverSub]
            apply sumOverCongr
            intro i
            unfold eliminate
            grind
          rw [combine] at eliminated
          unfold x
          rw [ite_eq_left rfl]
          grind
      · have tailShort : rows.length < cols.length := by simp only [List.length_cons] at short; omega
        have fewer : rows.length < n := by rw [← lengthEq, List.length_cons]; omega
        obtain ⟨x, witness, solves⟩ := ih rows.length fewer rows cols rfl distinct tailShort
        refine ⟨x, witness, ?_⟩
        intro r member
        rcases List.mem_cons.mp member with eq | inTail
        · subst r
          have vanish : ∀ i ∈ cols, first i * x i = 0 := by
            intro i member
            have zero : first i = 0 := Classical.byContradiction (fun h => nonzero ⟨i, member, h⟩)
            rw [zero]
            grind
          rw [sumOverCongrMem cols vanish, sumOfZeros]
        · exact solves r inTail

/-- The eight-point Schmidt support of at most seven rows has a nonzero
    annihilating covector. The statement uses the exterior-algebra pairing. -/
theorem sevenRowsHaveHole (oneNonzero : (1 : C) ≠ 0)
    (mulNonzero : ∀ a b : C, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (rows : List (ExteriorOccupation.Point → C)) (rankBound : rows.length ≤ 7) :
    ∃ hole : ExteriorOccupation.Point → C, (∃ i, hole i ≠ 0) ∧
      ∀ row ∈ rows, ExteriorOperators.pairing hole row = 0 := by
  have short : rows.length < ExteriorOccupation.points.length := by
    simp [ExteriorOccupation.points]
    omega
  obtain ⟨hole, ⟨i, _, hi⟩, vanishes⟩ :=
    shortRowsHaveKernel oneNonzero mulNonzero rows ExteriorOccupation.points
      (List.nodup_finRange _) short
  refine ⟨hole, ⟨i, hi⟩, ?_⟩
  intro row present
  rw [ExteriorOperators.pairing, sumOverCongr _ (fun i => CommSemiring.mul_comm (hole i) (row i))]
  exact vanishes row present

end RankSeven

#print axioms RankSeven.shortRowsHaveKernel
#print axioms RankSeven.sevenRowsHaveHole
