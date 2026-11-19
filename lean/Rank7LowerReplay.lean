import Rank7LowerCorner

namespace RankSeven.LowerReplay

open Interval LowerContractor

def toBox (box : Region) : Box 4 :=
  fun i => [box.z, box.y, box.x, box.b][i.val]'i.isLt

def fromBox (box : Box 4) : Region :=
  ⟨box 0,box 1,box 2,box 3⟩

theorem fromToBox (box : Region) : fromBox (toBox box) = box := by
  cases box
  rfl

private def axisWeight (i : Fin 4) : Int := if i=3 then 3 else 1

/-- The strict comparison gives the same first-axis tie rule as C++. -/
def axis (box : Box 4) : Fin 4 :=
  (List.finRange 4).foldl (fun best i =>
    let a := box i
    let b := box best
    if axisWeight i*(a.hi-a.lo)*(cppGrid.scale+b.lo) >
      axisWeight best*(b.hi-b.lo)*(cppGrid.scale+a.lo) then i else best) 0

inductive Result where
  | unresolved
  | oldRegion
  | weighted
  | shared
  deriving DecidableEq, Repr

def compare (depth : Nat) (box : Region) : Result :=
  if LowerLeaves.acceptsOld cppGrid box then .oldRegion
  else if LowerLeaves.acceptsWeighted cppGrid box then .weighted
  else if 6≤depth && LowerCorner.accepts box then .shared
  else .unresolved

def verifier : BoxVerifier 4 where
  contract box := (reduce cppGrid (fromBox box)).map toBox
  accept depth box := decide (compare depth (fromBox box) ≠ .unresolved)
  axis := axis

def replay (slab : Fin 6) : Bool :=
  verifier.replay 76 0 (toBox (initial slab))


private theorem splitValid {box left right : Box 4} {i : Fin 4}
    (valid : Valid cppGrid (fromBox box)) (split : box.trySplit i=some (left,right)) :
    Valid cppGrid (fromBox left) ∧ Valid cppGrid (fromBox right) := by
  have b := UpperReplay.splitLimits split 3
  have z := UpperReplay.splitLimits split 0
  have x := UpperReplay.splitLimits split 2
  exact ⟨⟨Int.le_trans valid.bLower b.1,Int.lt_of_lt_of_le valid.zPositive z.1,
    Int.lt_of_lt_of_le valid.xPositive x.1⟩,
    ⟨Int.le_trans valid.bLower b.2.2.1,Int.lt_of_lt_of_le valid.zPositive z.2.2.1,
    Int.lt_of_lt_of_le valid.xPositive x.2.2.1⟩⟩

section Ordered

open Lean.Grind

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

/-- Coverage on the normalized residual domain follows from successful
replay and the three branch implications. Only these physical implications,
and the numerical replay, remain as external inputs. -/
theorem replayRegion (x : Fin 4 → R) (P : Prop)
    (residual : Residual (x 0) (x 1) (x 2) (x 3))
    (old : LowerLeaves.OldCondition (x 0) (x 1) (x 2) (x 3) → P)
    (weighted : ∀ w, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) →
      0<LowerLeaves.weightedMargin (x 0) (x 1) (x 2) (x 3) w → P)
    (shared : ∀ box, Inside cppGrid box (x 0) (x 1) (x 2) (x 3) →
      (∀ sector : Fin 6, ∃ shift ∈ LowerCorner.shifts, ∃ rows,
        LowerCorner.margins box shift=some rows ∧ LowerCorner.sectorPass rows sector=true) → P)
    (fuel depth : Nat) (box : Box 4) (valid : Valid cppGrid (fromBox box))
    (inside : box.Contains cppGrid x) (success : verifier.replay fuel depth box=true) : P := by
  induction fuel generalizing depth box with
  | zero => simp [BoxVerifier.replay] at success
  | succ fuel ih =>
    have current : Inside cppGrid (fromBox box) (x 0) (x 1) (x 2) (x 3) :=
      ⟨inside 0,inside 1,inside 2,inside 3⟩
    obtain ⟨z,hz,zInside⟩ := reducePreserves residual valid current
    have reduced : verifier.contract box=some (toBox z) := by simp [verifier,hz]
    have zValid := reduceValid valid hz
    rw [BoxVerifier.replay,reduced] at success
    cases accept : verifier.accept depth (toBox z) with
    | true =>
      have accepted : compare depth z≠.unresolved := by simpa [verifier,fromToBox] using accept
      unfold compare at accepted
      split at accepted
      · rename_i test
        exact old (LowerLeaves.acceptedOldCondition zValid zInside test)
      · split at accepted
        · rename_i test
          obtain ⟨w,admissible,positive⟩ := LowerLeaves.acceptedWeightedMargin zInside test
          exact weighted w admissible positive
        · split at accepted
          · rename_i test
            exact shared z zInside (LowerCorner.acceptedWitness (Bool.and_eq_true_iff.mp test).2)
          · exact False.elim (accepted rfl)
    | false =>
      simp only [accept,Bool.false_eq_true,ite_false] at success
      have validTo : Valid cppGrid (fromBox (toBox z)) := (fromToBox z).symm ▸ zValid
      have insideTo : (toBox z).Contains cppGrid x := by
        intro j
        have finite : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
        rcases finite j with rfl | rfl | rfl | rfl
        · exact zInside.zInside
        · exact zInside.yInside
        · exact zInside.xInside
        · exact zInside.bInside
      cases cut : (toBox z).trySplit (verifier.axis (toBox z)) with
      | none => simp [cut] at success
      | some pair =>
        obtain ⟨left,right⟩ := pair
        simp only [cut,Bool.and_eq_true] at success
        obtain ⟨leftValid,rightValid⟩ := splitValid validTo cut
        rcases Box.coverBySplit cut insideTo with inLeft | inRight
        · exact ih (depth+1) left leftValid inLeft success.1
        · exact ih (depth+1) right rightValid inRight success.2

end Ordered

end RankSeven.LowerReplay

#print axioms RankSeven.LowerReplay.replayRegion
