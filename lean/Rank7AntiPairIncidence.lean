import Rank7PauliEdgeBlocks
import Rank7PhysicalAntiQuartic

/-! Incidence of unordered anticommuting edges with nonzero Pauli
directions and the symplectic complements of their chosen companions. -/
namespace RankSeven.AntiPairIncidence
open Lean.Grind Pauli PauliEdgeBlocks
open SymmetricDefect (anti unitWord)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem wordsComplete {n : Nat} (a : Word n) : a∈words n := by
  induction a with
  | empty => exact List.mem_cons_self
  | cons a w ih =>
    apply List.mem_flatMap.mpr; refine ⟨w,ih,?_⟩; cases a <;> simp

noncomputable def nonzeroWords (n : Nat) := (words n).filter (fun a => decide (a≠unitWord n))

theorem memNonzeroWords {n : Nat} (s : Word n) : s∈nonzeroWords n ↔ s≠unitWord n := by
  simp only [nonzeroWords,List.mem_filter,decide_eq_true_eq,wordsComplete,true_and]

noncomputable def companion {n : Nat} (s : Word n) :=
  if h : s≠unitWord n then Classical.choose (companionExists s h) else unitWord n

theorem companionAntiOfNe {n : Nat} (s : Word n) (h : s≠unitWord n) : anti s (companion s)=true := by
  rw [companion,dite_eq_left h]; exact Classical.choose_spec (companionExists s h)

theorem companionAnti {n : Nat} (s : Word n) (h : s∈nonzeroWords n) : anti s (companion s)=true :=
  companionAntiOfNe s ((memNonzeroWords s).mp h)

def edgeWeight {n : Nat} (f : Word n → R) (s r u : Word n) :=
  f (wordAdd r u)*f (wordAdd (wordAdd r u) s)

private theorem sumPerm {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → R) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

theorem shiftPerm {n : Nat} (s : Word n) : ((words n).map (fun a => wordAdd a s)).Perm (words n) := by
  have inject (a b : Word n) (e : wordAdd a s=wordAdd b s) : a=b := by
    have t := congrArg (fun z => wordAdd z s) e
    simpa only [wordAddCancel] using t
  have nd := MixedDefect.allWordsNodup n
  have moved : ((words n).map (fun a => wordAdd a s)).Nodup :=
    List.Pairwise.map _ (fun a b (ne : a≠b) e => ne (inject a b e)) nd
  apply List.perm_iff_count.mpr; intro a
  have mem : a∈(words n).map (fun b => wordAdd b s) :=
    List.mem_map.mpr ⟨wordAdd a s,wordsComplete _,wordAddCancel a s⟩
  rw [moved.count,nd.count]; simp [mem,wordsComplete]

theorem sumShift {n : Nat} (s : Word n) (f : Word n → R) :
    sumOver (words n) (fun a => f (wordAdd a s))=sumOver (words n) f := by
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (shiftPerm s) f

private theorem sumFilter {α : Type} (xs : List α) (p : α → Bool) (f : α → R) :
    sumOver (xs.filter p) f=sumOver xs (fun a => if p a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons]
    cases h : p a <;> simp [h,sumOver] at ih ⊢ <;> grind only

/-- Fixing a nonzero direction counts each complement coordinate twice if
we sum over ordered endpoints. The formula holds for any companion. -/
theorem directionPairMass {n : Nat} (f : Word n → R) (s r : Word n) (hr : anti s r=true) :
    sumOver (words n) (fun a => if anti a s then (f a)^2*(f (wordAdd a s))^2 else 0) =
      2*sumOver (perpendicularWords s r) (fun u => (edgeWeight f s r u)^2) := by
  let sel (a : Word n) : R := if anti a s && !anti a r then (f a)^2*(f (wordAdd a s))^2 else 0
  have row (a : Word n) : (if anti a s then (f a)^2*(f (wordAdd a s))^2 else 0) =
      sel a+sel (wordAdd a s) := by
    simp only [sel,antiAddLeft,antiSelf,hr,wordAddCancel]
    cases anti a s <;> cases anti a r <;> simp <;> grind only
  have choose (u : Word n) : sel (wordAdd u r) =
      if perpendicular s r u then (edgeWeight f s r u)^2 else 0 := by
    unfold edgeWeight sel perpendicular
    rw [wordAddComm r u]
    simp only [antiAddLeft,antiSelf,antiSymm r s,hr]
    cases anti u s <;> cases anti u r <;> simp <;> grind only
  have selected : sumOver (words n) sel=sumOver (perpendicularWords s r) (fun u => (edgeWeight f s r u)^2) := by
    rw [←sumShift r sel,perpendicularWords,sumFilter]
    exact sumOverCongr (words n) choose
  rw [sumOverCongr _ row,sumOverAdd,sumShift,selected]; grind only

/-- The ordered Pauli-pair sum can be reindexed along all directions, with
no comparison convention for pairs and with the zero direction of mass zero. -/
theorem orderedMassByDirection {n : Nat} (f : Word n → R) :
    PhysicalAntiQuartic.antiMass f =
      sumOver (words n) (fun s => sumOver (words n) (fun a =>
        if anti a s then (f a)^2*(f (wordAdd a s))^2 else 0)) := by
  unfold PhysicalAntiQuartic.antiMass
  rw [sumOverSwap (words n) (words n) (fun s a => if anti a s then (f a)^2*(f (wordAdd a s))^2 else 0)]
  apply sumOverCongr; intro a
  rw [←sumShift a (fun b => if anti a b then (f a)^2*(f b)^2 else 0)]
  apply sumOverCongr; intro s; rw [antiAddRight,antiSelf,wordAddComm s a]
  cases anti a s <;> rfl

theorem orderedAntiMass_eq_twice_edgeSquares {n : Nat} (f : Word n → R) :
    PhysicalAntiQuartic.antiMass f=2*sumOver (nonzeroWords n) (fun s =>
      sumOver (perpendicularWords s (companion s)) (fun u => (edgeWeight f s (companion s) u)^2)) := by
  rw [orderedMassByDirection,nonzeroWords,sumFilter,sumOverMulLeft]
  apply sumOverCongr; intro s
  by_cases nz : s≠unitWord n
  · rw [ite_eq_left (show decide (s≠unitWord n)=true from decide_eq_true nz)]
    exact directionPairMass f s (companion s) (companionAntiOfNe s nz)
  · have eq : s=unitWord n := Classical.not_not.mp nz
    rw [ite_eq_right (fun t => nz (_root_.of_decide_eq_true t)),Semiring.mul_zero]
    subst s; simp only [antiZero,Bool.false_eq_true,ite_false]
    induction words n with
    | nil => rfl
    | cons x xs ih => change 0+sumOver xs (fun _ => (0:R))=0; rw [ih]; grind only

/-- Unordered anticommuting pair mass equals the sum of the actual edge
weight squares, one term per representative in every nonzero direction. -/
theorem unorderedAntiMass_eq_edgeSquares (half : R) (unit : 2*half=1) {n : Nat} (f : Word n → R) :
    PhysicalAntiQuartic.unorderedAntiMass f=sumOver (nonzeroWords n) (fun s =>
      sumOver (perpendicularWords s (companion s)) (fun u => (edgeWeight f s (companion s) u)^2)) := by
  have eq := (PhysicalAntiQuartic.antiMass_twice f).symm.trans (orderedAntiMass_eq_twice_edgeSquares f)
  have h := congrArg (fun x => half*x) eq
  change half*(2*_)=half*(2*_) at h
  rw [←Semiring.mul_assoc,←Semiring.mul_assoc,CommSemiring.mul_comm half 2,unit,Semiring.one_mul,Semiring.one_mul] at h
  exact h

end RankSeven.AntiPairIncidence

#print axioms RankSeven.AntiPairIncidence.directionPairMass
#print axioms RankSeven.AntiPairIncidence.unorderedAntiMass_eq_edgeSquares
