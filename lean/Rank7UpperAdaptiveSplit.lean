import Rank7UpperDomainFrontier
namespace RankSeven.AdaptiveSplit
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner UpperPhysicalInterior UpperPhysicalReplay UpperDomainFrontier

/-- The indicated coordinate is part of the certificate. Both children are
identical to the directed grid midpoint children after the original contractor. -/
def childrenOn (b : TailBox) (i : Fin 5) : Option (TailBox×TailBox) := do
  let z ← contract cppGrid b
  let (l,r) ← (TailBox.toBox z).trySplit i
  return (fromBox l,fromBox r)

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem combine {b l r : TailBox} (i : Fin 5) (eq : childrenOn b i=some (l,r))
    (left : Accounts R l []) (right : Accounts R r []) : Accounts R b [] := by
  intro x res valid dom inside
  obtain ⟨z,hz,zi⟩ := contractPreserves res valid inside
  have contain : (TailBox.toBox z).Contains cppGrid x := by
    intro j
    have cases : ∀ j : Fin 5,j=0∨j=1∨j=2∨j=3∨j=4 := by decide
    rcases cases j with rfl|rfl|rfl|rfl|rfl
    · exact zi.hInside
    · exact zi.kInside
    · exact zi.qInside
    · exact zi.cInside
    · exact zi.dInside
  have vz : Valid cppGrid (fromBox (TailBox.toBox z)) := (fromToBox z).symm ▸ contractValid valid hz
  have dz : TailRectangle (fromBox (TailBox.toBox z)) := (fromToBox z).symm ▸ contractRectangle dom hz
  unfold childrenOn at eq
  simp only [hz] at eq
  cases split : (TailBox.toBox z).trySplit i with
  | none => simp [split] at eq
  | some pair =>
    obtain ⟨l',r'⟩ := pair
    have same : (fromBox l',fromBox r')=(l,r) := by simpa [split] using eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    obtain ⟨ld,rd⟩ := childDomain vz dz split
    rcases Box.coverBySplit split contain with il|ir
    · exact left x res ld.1 ld.2 ⟨il 0,il 1,il 2,il 3,il 4⟩
    · exact right x res rd.1 rd.2 ⟨ir 0,ir 1,ir 2,ir 3,ir 4⟩
end RankSeven.AdaptiveSplit
#print axioms RankSeven.AdaptiveSplit.combine
