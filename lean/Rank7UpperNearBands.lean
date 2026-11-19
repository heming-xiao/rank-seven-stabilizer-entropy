import Rank7UpperNearCollar

namespace RankSeven.CollarBatch.Bands
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner HintReplay
attribute [local instance] Ring.intCast Semiring.natCast

def midpoint (b : TailBox) := min b.d.hi ((b.d.lo+b.d.hi)/2)
def left (b : TailBox) : TailBox := {b with d := ⟨b.d.lo,midpoint b⟩}
def right (b : TailBox) : TailBox := {b with d := ⟨midpoint b,b.d.hi⟩}

def check : Nat → TailBox → List Nat → Bool
  | 0,b,ids => batchCheck b ids
  | n+1,b,ids => check n (left b) ids && check n (right b) ids

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem covered {g : Grid} {b : TailBox} {h k q c d : R} (ins : Inside g b h k q c d) :
    Inside g (left b) h k q c d ∨ Inside g (right b) h k q c d := by
  obtain ⟨lo, hi⟩ := insideEndpoints.mp ins.dInside
  by_cases s : d ≤ value g (midpoint b)
  · exact Or.inl ⟨ins.hInside,ins.kInside,ins.qInside,ins.cInside,insideEndpoints.mpr ⟨lo,s⟩⟩
  · exact Or.inr ⟨ins.hInside,ins.kInside,ins.qInside,ins.cInside,insideEndpoints.mpr ⟨show value g (midpoint b) ≤ d by grind only,hi⟩⟩

theorem checkWitness (n : Nat) {b : TailBox} {ids : List Nat} {h k q c d : R}
    (res : Residual h k q c d) (valid : Valid cppGrid b) (ins : Inside cppGrid b h k q c d)
    (pass : check n b ids = true) :
    ∃ z, Inside cppGrid z h k q c d ∧
      ∀ sector : Fin 6, ∃ shift ∈ UpperReplay.shifts, ∃ rows,
        UpperCorner.margins z shift = some rows ∧ UpperReplay.sectorPass rows sector = true := by
  induction n generalizing b with
  | zero => exact batchWitness res valid ins pass
  | succ n ih =>
    obtain ⟨lp,rp⟩ := Bool.and_eq_true_iff.mp pass
    rcases covered ins with il|ir
    · have vl : Valid cppGrid (left b) :=
        ⟨valid.cLowerPositive,valid.hLowerPositive,valid.qLowerPositive,Int.le_trans (Int.min_le_left _ _) valid.dUpperUnit⟩
      exact ih vl il lp
    · have vr : Valid cppGrid (right b) :=
        ⟨valid.cLowerPositive,valid.hLowerPositive,valid.qLowerPositive,valid.dUpperUnit⟩
      exact ih vr ir rp
end RankSeven.CollarBatch.Bands
#print axioms RankSeven.CollarBatch.Bands.checkWitness
