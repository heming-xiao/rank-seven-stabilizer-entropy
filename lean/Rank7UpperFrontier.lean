import Rank7UpperCoveredTree

namespace RankSeven.UpperFrontier
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner UpperCoveredTree HintShards
attribute [local instance] Ring.intCast Semiring.natCast

/-- A residual point belongs to the physically justified covered set or to an
explicit unresolved box, with that box's downstream validity available. -/
def Accounts (R : Type) [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (b : TailBox) (frontier : List TailBox) : Prop :=
  ∀ (x : Fin 5 → R), Residual (x 0) (x 1) (x 2) (x 3) (x 4) →
    Valid cppGrid b → Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4) →
    Covered x ∨ ∃ u ∈ frontier, Valid cppGrid u ∧ Inside cppGrid u (x 0) (x 1) (x 2) (x 3) (x 4)

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem unresolved (b : TailBox) : Accounts R b [b] :=
  fun _ _ valid inside => Or.inr ⟨b,List.mem_cons_self,valid,inside⟩

theorem verified (p : Plan) (b : TailBox) (depth : Nat) (pass : check p b depth=true) :
    Accounts R b [] :=
  fun x res valid ins => Or.inl (checkSound x res p b depth valid ins pass)

/-- Compose only after recomputing the contracted split and both child boxes. -/
theorem split {b l r : TailBox} {lf rf : List TailBox} (eq : children b=some (l,r))
    (left : Accounts R l lf) (right : Accounts R r rf) : Accounts R b (lf++rf) := by
  intro x res v i
  rcases childrenCover res v i eq with ⟨vl,il⟩|⟨vr,ir⟩
  · rcases left x res vl il with good|⟨u,um,uv,ui⟩
    · exact Or.inl good
    · exact Or.inr ⟨u,List.mem_append_left _ um,uv,ui⟩
  · rcases right x res vr ir with good|⟨u,um,uv,ui⟩
    · exact Or.inl good
    · exact Or.inr ⟨u,List.mem_append_right _ um,uv,ui⟩

/-- Replace any completed or partially refined frontier box by its own
certificate, allowing downstream jobs to reuse the previous proof untouched. -/
theorem refine {b : TailBox} {front : List TailBox} (prior : Accounts R b front)
    (replacement : TailBox → List TailBox)
    (update : ∀ u ∈ front, Accounts R u (replacement u)) :
    Accounts R b (front.flatMap replacement) := by
  intro x res v i
  rcases prior x res v i with good|⟨u,um,uv,ui⟩
  · exact Or.inl good
  · rcases update u um x res uv ui with good|⟨w,wm,wv,wi⟩
    · exact Or.inl good
    · exact Or.inr ⟨w,List.mem_flatMap.mpr ⟨u,um,wm⟩,wv,wi⟩

theorem complete {b : TailBox} (proof : Accounts R b []) (x : Fin 5 → R)
    (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4)) (v : Valid cppGrid b)
    (i : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4)) : Covered x := by
  rcases proof x res v i with yes|⟨u,um,_⟩
  · exact yes
  · simp at um
end RankSeven.UpperFrontier
#print axioms RankSeven.UpperFrontier.split
#print axioms RankSeven.UpperFrontier.refine
