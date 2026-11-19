import Rank7AnchorOccupation

namespace RankSeven.AnchorScoreEnumeration
open Lean.Grind Pauli AnchorSteiner AnchorExteriorFive
variable {I R : Type} [CommRing R]
local instance : NatCast R := Semiring.natCast

def pairList : List I → List (I×I)
  | [] => []
  | x::xs => xs.map (fun y=>(x,y)) ++ pairList xs

def tripleList : List I → List (I×I×I)
  | [] => []
  | x::xs => (pairList xs).map (fun t=>(x,t)) ++ tripleList xs

private theorem pairMembers (L : List I) (nd : L.Nodup) {a b : I} (h : (a,b)∈pairList L) :
    a∈L ∧ b∈L ∧ a≠b := by
  induction L with
  | nil => contradiction
  | cons x L ih =>
    obtain ⟨off,tail⟩:=List.nodup_cons.mp nd
    rcases List.mem_append.mp h with k|k
    · obtain ⟨i,hi,e⟩:=List.mem_map.mp k; cases e; exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hi,fun eq=>off (eq ▸ hi)⟩
    · obtain ⟨ha,hb,ne⟩:=ih tail k; exact ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb,ne⟩

theorem tripleDistinct (L : List I) (nd : L.Nodup) {a b c : I} (h : (a,b,c)∈tripleList L) :
    a≠b ∧ a≠c ∧ b≠c := by
  induction L with
  | nil => contradiction
  | cons x L ih =>
    obtain ⟨off,tail⟩:=List.nodup_cons.mp nd
    rcases List.mem_append.mp h with k|k
    · obtain ⟨i,hi,e⟩:=List.mem_map.mp k; cases e
      obtain ⟨hb,hc,bc⟩:=pairMembers L tail hi
      exact ⟨fun eq=>off (eq ▸ hb),fun eq=>off (eq ▸ hc),bc⟩
    · exact ih tail k

private theorem sumAppend {A : Type} (L M : List A) (f : A→R) :
    sumOver (L++M) f=sumOver L f+sumOver M f := by
  induction L with
  | nil => change sumOver M f=0+sumOver M f; grind only
  | cons i L ih => change f i+sumOver (L++M) f=f i+sumOver L f+sumOver M f; rw [ih]; grind only
private theorem sumMap {A B : Type} (L : List A) (p : A→B) (f : B→R) :
    sumOver (L.map p) f=sumOver L (fun a=>f (p a)) := by simp only [sumOver,List.map_map,Function.comp_def]

private theorem rowPrice (L : List I) (p : I→Bool) (w : R) :
    sumOver L (fun i=>if p i then w else 0)=(row p L:R)*w := by
  induction L with
  | nil => change 0=(Nat.cast 0:R)*w; grind
  | cons i L ih =>
    change (if p i then w else 0)+sumOver L _ = (Nat.cast ((if p i then 1 else 0)+row p L):R)*w
    rw [ih]; cases p i <;> simp <;> grind
private theorem pairPrice (L : List I) (p : I→I→Bool) (w : R) :
    sumOver (pairList L) (fun t=>if p t.1 t.2 then w else 0)=(pairs p L:R)*w := by
  induction L with
  | nil => change 0=(Nat.cast 0:R)*w; grind
  | cons i L ih => rw [pairList,sumAppend,sumMap,ih,rowPrice]; change _=(Nat.cast (row (p i) L + pairs p L):R)*w; grind

theorem triplePrice (L : List I) (p : I→I→I→Bool) (w : R) :
    sumOver (tripleList L) (fun t=>if p t.1 t.2.1 t.2.2 then w else 0)=(triples p L:R)*w := by
  induction L with
  | nil => change 0=(Nat.cast 0:R)*w; grind
  | cons i L ih => rw [tripleList,sumAppend,sumMap,ih,pairPrice L (p i) w]; change _=(Nat.cast (pairs (p i) L + triples p L):R)*w; grind

private theorem emptyRow (L : List I) : row (fun _=>false) L=0 := by
  induction L with
  | nil => rfl
  | cons i L ih => change 0+row _ L=0; omega
private theorem emptyPairs (L : List I) : pairs (fun _ _=>false) L=0 := by
  induction L with
  | nil => rfl
  | cons i L ih => change row _ L+pairs _ L=0; rw [emptyRow,ih]
private theorem filterRow (L : List I) (keep p : I→Bool) :
    row p (L.filter keep)=row (fun i=>keep i && p i) L := by
  induction L with
  | nil => rfl
  | cons i L ih => cases h:keep i <;> simp [h,row,ih]

private theorem filterPairs (L : List I) (keep : I→Bool) (p:I→I→Bool) :
    pairs p (L.filter keep)=pairs (fun a b=>keep a && (keep b && p a b)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h:keep a <;> simp [h,pairs,ih,filterRow,emptyRow]

theorem filterTriples (L : List I) (keep : I→Bool) (p:I→I→I→Bool) :
    triples p (L.filter keep)=triples (fun a b c=>keep a && (keep b && (keep c && p a b c))) L := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h:keep a <;> simp [h,triples,ih,filterPairs,emptyPairs]

theorem orderedFilter [DecidableEq I] (L : List I) (nd : L.Nodup) (z : Basis L.length) :
    L.filter (fun i=>decide (i∈occupied L z))=occupied L z := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    obtain ⟨off,tail⟩:=List.nodup_cons.mp nd
    rcases z with ⟨b,z⟩
    have sub (ys : List I) (u : Basis ys.length) : occupied ys u⊆ys := by
      induction ys with
      | nil => exact List.Subset.refl _
      | cons a ys hy => rcases u with ⟨bit,u⟩; cases bit
                        · exact fun _ h=>List.mem_cons_of_mem _ (hy u h)
                        · intro j h; rcases List.mem_cons.mp h with e|e
                          · exact List.mem_cons.mpr (Or.inl e)
                          · exact List.mem_cons_of_mem _ (hy u e)
    have no : i∉occupied L z := fun hi=>off (sub L z hi)
    cases b
    · simp [occupied,no]; exact ih tail z
    · change (i::L).filter (fun j=>decide (j∈i::occupied L z))=i::occupied L z
      simp only [List.filter_cons,List.mem_cons_self,decide_true,ite_true]
      congr 1
      calc
        _ = L.filter (fun j=>decide (j∈occupied L z)) := by
          apply List.filter_congr
          intro j hj; have ne : j≠i := fun e=>off (e ▸ hj)
          simp [ne]
        _ = _ := ih tail z

end RankSeven.AnchorScoreEnumeration
#print axioms RankSeven.AnchorScoreEnumeration.triplePrice
#print axioms RankSeven.AnchorScoreEnumeration.filterTriples
