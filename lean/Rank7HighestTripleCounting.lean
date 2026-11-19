import Rank7HighestChartOrbitPrice

namespace RankSeven.HighestTripleCounting

open Lean.Grind Pauli ComplexScalar AnchorScoreEnumeration
open HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits AnchorSteiner
open HighestFivePairMinors (coefficient)
open AnchorVacantScore (sites)
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

private theorem app {J : Type} (L M : List J) (f : J→R) : sumOver (L++M) f=sumOver L f+sumOver M f := by
  induction L with | nil => change _=0+_; grind only | cons i L ih => change f i+sumOver (L++M) f=f i+sumOver L f+sumOver M f; rw [ih]; grind only

private theorem sumMap {J K : Type} (L : List J) (g : J→K) (f : K→R) : sumOver (L.map g) f=sumOver L (fun i=>f (g i)) := by
  simp only [sumOver,List.map_map,Function.comp_def]

theorem doubleSheet (L : List I) (f : I→I→R) (symm : ∀i j,f j i=f i j) (diag : ∀i,f i i=0) :
    sumOver L (fun i=>sumOver L (f i))=2*sumOver (pairList L) (fun p=>f p.1 p.2) := by
  induction L with
  | nil => change 0=2*0; grind only
  | cons i L ih =>
    have e (j : I):sumOver (i::L) (f j)=f i j+sumOver L (f j):=by change f j i+_= _; rw [symm i j]; rfl
    change (f i i+sumOver L (f i))+sumOver L (fun j=>sumOver (i::L) (f j))=_
    rw [diag,sumOverCongr L e,sumOverAdd,ih,pairList,app,sumMap]; grind only

theorem tripleSheet (L : List I) (f : I→I→I→R)
    (s12 : ∀i j k,f j i k=f i j k) (s23 : ∀i j k,f i k j=f i j k) (diag : ∀i k,f i i k=0) :
    sumOver L (fun i=>sumOver L (fun j=>sumOver L (f i j)))=6*sumOver (tripleList L) (fun p=>f p.1 p.2.1 p.2.2) := by
  have xx (i j : I) : f i j i=0:=by rw [s23 i i j,diag]
  have yy (i j : I) : f i j j=0:=by rw [s12 j i j,xx]
  have zs {A : Type} (xs : List A) : sumOver xs (fun _=>(0:R))=0:=by
    induction xs with | nil => rfl | cons a xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
  induction L with
  | nil => change 0=6*0; grind only
  | cons i L ih =>
    have inner (u v : I) : sumOver (i::L) (f u v)=f u v i+sumOver L (f u v):=rfl
    have cyc (u v : I) : f u v i=f i u v := (s23 u i v).trans (s12 i u v)
    have one (u : I) : sumOver (i::L) (fun v=>sumOver (i::L) (f u v))=
        sumOver L (f i u)+sumOver L (f i u)+sumOver L (fun v=>sumOver L (f u v)) := by
      change sumOver (i::L) (f u i)+sumOver L (fun v=>sumOver (i::L) (f u v))=_
      rw [inner,yy]; simp only [inner,cyc,sumOverAdd]
      have e : f u i=f i u:=funext (s12 i u)
      rw [e]; grind only
    change sumOver (i::L) (fun v=>sumOver (i::L) (f i v))+sumOver L (fun u=>sumOver (i::L) (fun v=>sumOver (i::L) (f u v)))=_
    have d0 : f i i=fun _=>0:=funext (diag i)
    rw [one]; simp only [one,sumOverAdd,d0,zs,ih,doubleSheet L (f i) (s23 i) (yy i),tripleList,app,sumMap]
    grind only

noncomputable def price {n} {G : MaximalFamily n} {T : Transversal G} (a : Line T)
    (y : Line T→C) (Y : Fin 5→Line T→C) (p : Fin 5×Fin 5) (i j k : Line T) :=
  if hit a i j k then normSq (coefficient y Y (i,j,k) p) else 0

private theorem hitEq {n} {G : MaximalFamily n} {T : Transversal G} (a i j k : Line T) :
    hit a i j k=true ↔ plane a i j k := @decide_eq_true_eq _ (Classical.propDecidable _) |> Iff.of_eq

theorem anchoredTriples {n} {G : MaximalFamily n} {T : Transversal G} (a : Line T) (L : List (Line T))
    (y : Line T→C) (Y : Fin 5→Line T→C) (p : Fin 5×Fin 5) :
    sumOver L (fun i=>sumOver L (fun j=>sumOver L (price a y Y p i j)))=
      6*sumOver (sites a L) (fun t=>normSq (coefficient y Y t p)) := by
  let f:=price a y Y p
  have nz (z : C) : normSq (-z)=normSq z:=by simp only [normSq,re_neg,im_neg]; grind only
  have zero : normSq (0:C)=0:=by simp only [normSq,re_zero,im_zero]; grind only
  have symm1 (i j k : Line T) : f j i k=f i j k:=by
    have eq : coefficient y Y (j,i,k) p= -coefficient y Y (i,j,k) p:=by unfold coefficient; grind only
    unfold f price; rw [eq,nz]
    have cond : hit a j i k=hit a i j k:=by
      have e:hit a j i k=true ↔ hit a i j k=true:= (hitEq ..).trans ((swapAnchorTriple ..).trans (hitEq ..).symm)
      cases x:hit a j i k <;> cases z:hit a i j k <;> simp_all
    rw [cond]
  have symm2 (i j k : Line T) : f i k j=f i j k:=by
    have eq : coefficient y Y (i,k,j) p= -coefficient y Y (i,j,k) p:=by unfold coefficient; grind only
    unfold f price; rw [eq,nz]
    have cond : hit a i k j=hit a i j k:=by
      have e:hit a i k j=true ↔ hit a i j k=true:= (hitEq ..).trans ((swapTail ..).trans (hitEq ..).symm)
      cases x:hit a i k j <;> cases z:hit a i j k <;> simp_all
    rw [cond]
  have diag (i k : Line T) : f i i k=0:=by
    have eq : coefficient y Y (i,i,k) p=0:=by unfold coefficient; grind only
    unfold f price; rw [eq,zero]; split <;> rfl
  have eq:=tripleSheet L f symm1 symm2 diag
  apply eq.trans; apply congrArg (fun z=>6*z)
  have filt {J : Type} (xs : List J) (b : J→Bool) (u : J→R) :
      sumOver xs (fun z=>if b z then u z else 0)=sumOver (xs.filter b) u := by
    induction xs with | nil => rfl | cons i xs ih => cases t:b i <;> simp [sumOver,t] at ih ⊢ <;> grind only
  exact filt (tripleList L) (fun t=>hit a t.1 t.2.1 t.2.2) (fun t=>normSq (coefficient y Y t p))

end RankSeven.HighestTripleCounting

#print axioms RankSeven.HighestTripleCounting.doubleSheet
#print axioms RankSeven.HighestTripleCounting.tripleSheet
#print axioms RankSeven.HighestTripleCounting.anchoredTriples

