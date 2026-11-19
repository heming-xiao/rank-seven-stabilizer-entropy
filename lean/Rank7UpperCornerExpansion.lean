import Rank7UpperCornerDual
namespace RankSeven.UpperCornerExpansion
open Lean.Grind Pauli UpperCornerDual ExteriorCuts PackingDual PackingInterpolation
attribute [local instance] Ring.intCast
abbrev Var := Fin 6
abbrev Key := Four Var
def vars := List.finRange 6
def keys := (fourIndices vars).filter fun m => decide (m.1.1≤m.1.2 ∧ m.1.2≤m.2.1 ∧ m.2.1≤m.2.2)
def assignments (m : Key) := (ExteriorPauliBase.permutations.map (GenericExteriorKernel.reorder m)).eraseDups
def key (m : Key) := ((m.1.1.val*6+m.1.2.val)*6+m.2.1.val)*6+m.2.2.val
private def radix : Nat → List Key → List Key
  | 0,xs => xs
  | k+1,xs =>
    let left (m : Key) := !(key m).testBit k
    radix k (xs.filter left) ++ radix k (xs.filter (fun m => !(left m)))
private theorem radixPerm (k : Nat) (xs : List Key) : (radix k xs).Perm xs := by
  induction k generalizing xs with
  | zero => exact List.Perm.refl _
  | succ k ih => exact ((ih _).append (ih _)).trans (List.filter_append_perm _ xs)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem sortedAssignmentList : radix 11 (keys.flatMap assignments) = fourIndices vars := by decide
private theorem assignmentPerm : (keys.flatMap assignments).Perm (fourIndices vars) := by
  rw [←sortedAssignmentList]; exact (radixPerm _ _).symm

private theorem sumPerm {C α : Type} [CommRing C] {xs ys : List α} (p : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem productPerm {C α : Type} [CommRing C] {xs ys : List α} (p : xs.Perm ys) (f : α → C) :
    (xs.map f).prod=(ys.map f).prod := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,List.prod_cons]; rw [ih]
  | swap => simp only [List.map_cons,List.prod_cons]; grind only
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

def mon {C : Type} [CommRing C] (v : Var→C) (m : Key) := v m.1.1*v m.1.2*v m.2.1*v m.2.2
private def slots {α : Type} (q : Four α) := [q.1.1,q.1.2,q.2.1,q.2.2]
private theorem sameMon {R : Type} [CommRing R] (b : Var→R) (m q : Key) (hq : q∈assignments m) : mon b q=mon b m := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hq)
  have tab : ExteriorPauliBase.permutations.all (fun p => decide ((slots p).Perm ([0,1,2,3] : List (Fin 4))))=true := by decide
  let f (j : Fin 4) := b (GenericExteriorKernel.position m j)
  have eq := productPerm (_root_.of_decide_eq_true (List.all_eq_true.mp tab p hp)) f
  change f p.1.1*(f p.1.2*(f p.2.1*(f p.2.2*1)))=b m.1.1*(b m.1.2*(b m.2.1*(b m.2.2*1))) at eq
  change f p.1.1*f p.1.2*f p.2.1*f p.2.2=b m.1.1*b m.1.2*b m.2.1*b m.2.2
  grind only

abbrev Factor := Var→Int
abbrev Product := Four Factor
def entry (p : Product) (m : Key) : Int := p.1.1 m.1.1*p.1.2 m.1.2*p.2.1 m.2.1*p.2.2 m.2.2
def coef (p : Product) (m : Key) := sumOver (assignments m) (entry p)
def linear {R : Type} [CommRing R] (v : Var→R) (f : Factor) := sumOver vars (fun i => Int.cast (f i)*v i)
def eval {R : Type} [CommRing R] (v : Var→R) (p : Product) := linear v p.1.1*linear v p.1.2*linear v p.2.1*linear v p.2.2

private theorem castSum {R α : Type} [CommRing R] (xs : List α) (f : α→Int) :
    Int.cast (R:=R) (sumOver xs f)=sumOver xs (fun i => Int.cast (f i)) := by
  induction xs with
  | nil => exact Ring.intCast_zero
  | cons a as ih => change Int.cast (f a+sumOver as f)=_; rw [Ring.intCast_add,ih]; rfl

private theorem productSum {R α β : Type} [CommRing R] (xs : List α) (ys : List β) (f : α×β→R) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

theorem expands {R : Type} [CommRing R] (v : Var→R) (p : Product) :
    eval v p=sumOver keys (fun m => Int.cast (coef p m)*mon v m) := by
  have rearrange : sumOver (fourIndices vars) (fun m => Int.cast (entry p m)*mon v m)=
      sumOver keys (fun m => Int.cast (coef p m)*mon v m) := by
    rw [←sumPerm assignmentPerm,sumOverFlatMap]; apply sumOverCongr; intro m
    rw [coef,castSum,sumOverMulRight]
    apply AnticommutingDefect.sumCongrMem; intro q hq; rw [sameMon v m q hq]
  rw [←rearrange]
  have mul {α β : Type} (xs : List α) (ys : List β) (f : α→R) (g : β→R) :
      sumOver xs f*sumOver ys g=sumOver (productIndices xs ys) (fun a => f a.1*g a.2) := by
    rw [productSum,sumOverMulRight]; apply sumOverCongr; intro a; rw [sumOverMulLeft]
  let f (g : Factor) (i : Var) := Int.cast (R:=R) (g i)*v i
  change (sumOver vars (f p.1.1)*sumOver vars (f p.1.2)*sumOver vars (f p.2.1))*sumOver vars (f p.2.2)=_
  rw [Semiring.mul_assoc (sumOver vars (f p.1.1)*sumOver vars (f p.1.2)),mul vars vars (f p.1.1),mul vars vars (f p.2.1),mul]
  apply sumOverCongr; intro m
  dsimp only [f,entry,mon]; simp only [Ring.intCast_mul]; grind only
end RankSeven.UpperCornerExpansion
#print axioms RankSeven.UpperCornerExpansion.expands
