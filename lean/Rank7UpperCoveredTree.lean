import Rank7UpperNearBands
import Rank7UpperHintShards

namespace RankSeven.UpperCoveredTree
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner HintShards
attribute [local instance] Ring.intCast Semiring.natCast

/-- An ordinary node may carry an entire pre-existing certified replay subtree.
A band count of zero requests the lower-tail clip on just the current box. -/
inductive Plan where
  | ordinary (fuel : Nat) (hint : HintReplay.Plan)
  | bands (levels : Nat) (shifts : List Nat)
  | split (left right : Plan)
  deriving Inhabited

def check (p : Plan) (b : TailBox) (depth : Nat) : Bool :=
  match p with
  | .ordinary fuel h => HintReplay.check fuel depth (TailBox.toBox b) h
  | .bands levels ids => CollarBatch.Bands.check levels b ids
  | .split l r => match children b with
    | none => false
    | some (bl,br) => check l bl (depth+1) && check r br (depth+1)

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def Covered (x : Fin 5 → R) : Prop :=
  UpperOldRegions.OldCondition (x 0) (x 1) (x 2) (x 3) (x 4) ∨
  (∃ u, (u=1 ∨ u=5/4 ∨ u=3/2) ∧
    0<UpperWeighted.margin (x 0) (x 1) (x 2) (x 3) (x 4) u) ∨
  (∃ z, Inside cppGrid z (x 0) (x 1) (x 2) (x 3) (x 4) ∧ ∀ sector : Fin 6,
    ∃ shift ∈ UpperReplay.shifts, ∃ rows,
      UpperCorner.margins z shift = some rows ∧ UpperReplay.sectorPass rows sector = true)

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem coordinateInside {x : Fin 5 → R} {b : TailBox}
    (ins : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4)) :
    (TailBox.toBox b).Contains cppGrid x := by
  intro i
  have e : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by
    obtain ⟨i,hi⟩ := i
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> simp
  rcases e with rfl|rfl|rfl|rfl|rfl
  · exact ins.hInside
  · exact ins.kInside
  · exact ins.qInside
  · exact ins.cInside
  · exact ins.dInside

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem fromCoordinates {x : Fin 5 → R} {b : Box 5}
    (ins : b.Contains cppGrid x) : Inside cppGrid (fromBox b) (x 0) (x 1) (x 2) (x 3) (x 4) :=
  ⟨ins 0,ins 1,ins 2,ins 3,ins 4⟩

theorem childrenCover {x : Fin 5 → R} {b l r : TailBox}
    (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4)) (valid : Valid cppGrid b)
    (ins : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4)) (eq : children b=some (l,r)) :
    (Valid cppGrid l ∧ Inside cppGrid l (x 0) (x 1) (x 2) (x 3) (x 4)) ∨
    (Valid cppGrid r ∧ Inside cppGrid r (x 0) (x 1) (x 2) (x 3) (x 4)) := by
  obtain ⟨z,hz,zins⟩ := contractPreserves res valid ins
  have hc : verifier.contract (TailBox.toBox b)=some (TailBox.toBox z) := by
    simp [verifier,fromToBox,hz]
  unfold children at eq
  simp only [hc] at eq
  cases sp : (TailBox.toBox z).trySplit (verifier.axis (TailBox.toBox z)) with
  | none => simp [sp] at eq
  | some pair =>
    obtain ⟨l',r'⟩ := pair
    have pairEq : (fromBox l',fromBox r') = (l,r) := by simpa [sp] using eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj pairEq
    have vz : Valid cppGrid (fromBox (TailBox.toBox z)) := (fromToBox z).symm ▸ contractValid valid hz
    obtain inL|inR := Box.coverBySplit sp (coordinateInside zins)
    · exact Or.inl ⟨validSubbox vz (splitLimits sp 3).1 (splitLimits sp 0).1
        (splitLimits sp 2).1 (splitLimits sp 4).2.1,fromCoordinates inL⟩
    · exact Or.inr ⟨validSubbox vz (splitLimits sp 3).2.2.1 (splitLimits sp 0).2.2.1
        (splitLimits sp 2).2.2.1 (splitLimits sp 4).2.2.2,fromCoordinates inR⟩

/-- The only leaf conclusions are the three physical interfaces of replayRegion.
The contractor, split axis, midpoint and both descendant proofs are checked. -/
theorem checkSound (x : Fin 5 → R) (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4))
    (p : Plan) (b : TailBox) (depth : Nat) (valid : Valid cppGrid b)
    (ins : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4))
    (ok : check p b depth=true) : Covered x := by
  induction p generalizing b depth with
  | ordinary fuel h =>
    apply replayRegion x (Covered x) res Or.inl (fun u hu pos => Or.inr (Or.inl ⟨u,hu,pos⟩))
      (fun z zi hs => Or.inr (Or.inr ⟨z,zi,hs⟩)) fuel depth (TailBox.toBox b)
    · exact (fromToBox b).symm ▸ valid
    · exact coordinateInside ins
    · exact HintReplay.checkSound _ _ _ h ok
  | bands n ids =>
    exact Or.inr (Or.inr (CollarBatch.Bands.checkWitness n res valid ins ok))
  | split a b' ihl ihr =>
    unfold check at ok
    cases eq : children b with
    | none => simp [eq] at ok
    | some pair =>
      obtain ⟨l,r⟩ := pair
      simp only [eq,Bool.and_eq_true] at ok
      rcases childrenCover res valid ins eq with ⟨v,i⟩|⟨v,i⟩
      · exact ihl _ _ v i ok.1
      · exact ihr _ _ v i ok.2
/-- Compose independently frozen subtrees, checking the actual contractor and split equality. -/
theorem glue {x : Fin 5 → R} {b l r : TailBox}
    (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4)) (valid : Valid cppGrid b)
    (inside : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4))
    (childrenEq : children b=some (l,r))
    (lp : Valid cppGrid l → Inside cppGrid l (x 0) (x 1) (x 2) (x 3) (x 4) → Covered x)
    (rp : Valid cppGrid r → Inside cppGrid r (x 0) (x 1) (x 2) (x 3) (x 4) → Covered x) :
    Covered x := by
  rcases childrenCover res valid inside childrenEq with ⟨v,i⟩|⟨v,i⟩
  · exact lp v i
  · exact rp v i

end RankSeven.UpperCoveredTree
#print axioms RankSeven.UpperCoveredTree.childrenCover
#print axioms RankSeven.UpperCoveredTree.checkSound
