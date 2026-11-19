import Rank7UpperCoveredFrame

namespace RankSeven.UpperDomainFrontier
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner UpperCoveredTree HintShards
open UpperPhysicalReplay UpperPhysicalInterior

abbrev Here {R : Type} [Field R] [LE R] (b : TailBox) (x : Fin 5 → R) :=
  Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4)

abbrev Covered {R : Type} [Field R] [LE R] [LT R] (x : Fin 5 → R) : Prop :=
  UpperOldRegions.OldCondition (x 0) (x 1) (x 2) (x 3) (x 4) ∨
  (∃ u : R,(u=1∨u=5/4∨u=3/2) ∧ 0<UpperWeighted.margin (x 0) (x 1) (x 2) (x 3) (x 4) u) ∨
  ∃ z,TailRectangle z ∧ Here z x ∧ Witnesses z

abbrev OpenPoint {R : Type} [Field R] [LE R] (front : List TailBox) (x : Fin 5 → R) : Prop :=
  ∃ u ∈ front, Valid cppGrid u ∧ TailRectangle u ∧ Here u x

def Accounts (R : Type) [Field R] [LE R] [LT R] (b : TailBox) (front : List TailBox) : Prop :=
  ∀ (x : Fin 5 → R), Residual (x 0) (x 1) (x 2) (x 3) (x 4) →
    Valid cppGrid b → TailRectangle b → Here b x → Covered x ∨ OpenPoint front x

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The original split contractor leaves both tail endpoint inequalities valid
on either child, including the child which is still on the open frontier. -/
theorem rectangles {b l r : TailBox} (v : Valid cppGrid b) (d : TailRectangle b)
    (eq : children b=some (l,r)) : TailRectangle l ∧ TailRectangle r :=
  UpperCoveredFrame.childRectangles v d eq

omit [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem unresolved (b : TailBox) : Accounts R b [b] :=
  fun _ _ v d i => Or.inr ⟨b,List.mem_cons_self,v,d,i⟩

theorem verified (p : Plan) (b : TailBox) (depth : Nat) (pass : check p b depth=true) :
    Accounts R b [] := by
  intro x res valid dom inside
  exact Or.inl (UpperCoveredFrame.checkWithDomain x (Covered x) res Or.inl
    (fun u hu hp => Or.inr (Or.inl ⟨u,hu,hp⟩))
    (fun z dz iz wit => Or.inr (Or.inr ⟨z,dz,iz,wit⟩)) p b depth valid dom inside pass)

theorem split {b l r : TailBox} {lf rf : List TailBox} (eq : children b=some (l,r))
    (left : Accounts R l lf) (right : Accounts R r rf) : Accounts R b (lf++rf) := by
  intro x res v d i
  obtain ⟨ld,rd⟩ := rectangles v d eq
  rcases childrenCover res v i eq with ⟨vl,il⟩|⟨vr,ir⟩
  · rcases left x res vl ld il with good|⟨u,um,uv,ud,ui⟩
    · exact Or.inl good
    · exact Or.inr ⟨u,List.mem_append_left _ um,uv,ud,ui⟩
  · rcases right x res vr rd ir with good|⟨u,um,uv,ud,ui⟩
    · exact Or.inl good
    · exact Or.inr ⟨u,List.mem_append_right _ um,uv,ud,ui⟩

omit [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem refine {b : TailBox} {front : List TailBox} (prior : Accounts R b front)
    (replacement : TailBox → List TailBox)
    (update : ∀ u ∈ front, Accounts R u (replacement u)) :
    Accounts R b (front.flatMap replacement) := by
  intro x res v d i
  rcases prior x res v d i with good|⟨u,um,uv,ud,ui⟩
  · exact Or.inl good
  · rcases update u um x res uv ud ui with good|⟨w,wm,wv,wd,wi⟩
    · exact Or.inl good
    · exact Or.inr ⟨w,List.mem_flatMap.mpr ⟨u,um,wm⟩,wv,wd,wi⟩

omit [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem complete {b : TailBox} (proof : Accounts R b []) (x : Fin 5 → R)
    (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4)) (v : Valid cppGrid b)
    (d : TailRectangle b) (i : Here b x) : Covered x := by
  rcases proof x res v d i with yes|⟨u,um,_⟩
  · exact yes
  · simp at um
end RankSeven.UpperDomainFrontier
#print axioms RankSeven.UpperDomainFrontier.verified
#print axioms RankSeven.UpperDomainFrontier.split
#print axioms RankSeven.UpperDomainFrontier.refine
