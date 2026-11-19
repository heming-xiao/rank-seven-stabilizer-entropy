import Rank7UpperHintReplay

namespace RankSeven.CollarBatch
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner HintReplay
attribute [local instance] Ring.intCast Semiring.natCast

/-- Intersect the tail rectangle with the lower c endpoint implied by 101*d < 100*c.
The other endpoints, including the upper c endpoint, stay in the box. -/
def collar (g : Grid) (b : TailBox) : TailBox :=
  { b with c := ⟨max b.c.lo (Bounds.mul g (Bounds.rational g 101 100) b.d).lo,b.c.hi⟩ }

def batchCheck (b : TailBox) (ids : List Nat) : Bool :=
  match UpperContractor.contract cppGrid b with
  | none => true
  | some z => hintedCorners (collar cppGrid z) ids

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem collarContains {g : Grid} {b : TailBox} {h k q c d : R}
    (near : 101*d≤100*c) (ins : Inside g b h k q c d) : Inside g (collar g b) h k q c d := by
  have ratio := quotientEq (101:R) (show 0<(100:R) by grind only)
  have eq := congrArg (fun t : R => t*d) ratio
  have le : ((101:R)/100)*d ≤ c := by
    apply cancelLe (show (0:R)<100 by grind only)
    grind only
  have boxed := Bounds.mulSound (fractionSound (R:=R) g 101 100 (by decide)) ins.dInside
  refine ⟨ins.hInside,ins.kInside,ins.qInside,?_,ins.dInside⟩
  apply insideEndpoints.mpr
  change value g (max b.c.lo _) ≤ c ∧ c ≤ value g b.c.hi
  refine ⟨?_,(insideEndpoints.mp ins.cInside).2⟩
  rw [Int.max_def]
  split
  · exact Std.le_trans (insideEndpoints.mp boxed).1 le
  · exact (insideEndpoints.mp ins.cInside).1

/-- Output matches the successful corner premise of UpperReplay.replayRegion.
Only residual scalar points in the input box need to be covered. -/
theorem batchWitness {b : TailBox} {ids : List Nat} {h k q c d : R}
    (res : Residual h k q c d) (valid : Valid cppGrid b) (ins : Inside cppGrid b h k q c d)
    (pass : batchCheck b ids = true) :
    ∃ z, Inside cppGrid z h k q c d ∧
      ∀ sector : Fin 6, ∃ shift ∈ UpperReplay.shifts, ∃ rows,
        UpperCorner.margins z shift = some rows ∧ UpperReplay.sectorPass rows sector = true := by
  obtain ⟨z,hz,hins⟩ := contractPreserves res valid ins
  rw [batchCheck,hz] at pass
  exact ⟨_,collarContains (Std.le_of_lt res.nearCut) hins,
    acceptedCornersWitness (hintedCornersSound _ _ pass)⟩

end RankSeven.CollarBatch
#print axioms RankSeven.CollarBatch.collarContains
#print axioms RankSeven.CollarBatch.batchWitness
