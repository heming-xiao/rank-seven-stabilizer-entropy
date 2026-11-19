import Rank7HighestChartSelection

namespace RankSeven.HighestChartOrbitPrice

open Lean.Grind Pauli ComplexScalar SymmetricDefect GenericExteriorKernel
open HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits
open HighestCharacterChart HighestChartAction HighestChartMinorTrace HighestChartSelection
open AnchorSteinerTest (mass)
open AnchorOrbitBound (gate orbitCount occupationPrice)
open FiniteProjectionAngles
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

def occ (r : Four I) := [r.1.1,r.1.2,r.2.1,r.2.2]

theorem posMem (r : Four I) (k : Fin 4) : position r k∈occ r := by
  have ex : k=0∨k=1∨k=2∨k=3:=by omega
  rcases ex with h|h|h|h <;> subst h <;> simp [occ,position]

private theorem fullFour (L : List I) (full : ∀i,i∈L) (r : Four I) : r∈fourIndices L :=
  HyperplaneInduction.pairMember (HyperplaneInduction.pairMember (full _) (full _))
    (HyperplaneInduction.pairMember (full _) (full _))

theorem moveTwice {n} {G : MaximalFamily n} (T : Transversal G) (p : Word n) (r : Four (Line T)) :
    fourMap (shift T p) (fourMap (shift T p) r)=r := by simp only [fourMap,shiftTwice]

theorem movePerm {n} {G : MaximalFamily n} (T : Transversal G) (p : Word n) :
    ((fourIndices T.reps.attach).map (fourMap (shift T p))).Perm (fourIndices T.reps.attach) := by
  classical
  let B:=fourIndices T.reps.attach
  let m:=fourMap (shift T p)
  have inv (r : Four (Line T)) : m (m r)=r:=moveTwice T p r
  have nd : B.Nodup:=
    HyperplaneInduction.pairsNodup _ _ (HyperplaneInduction.pairsNodup _ _ (linesNodup T) (linesNodup T))
      (HyperplaneInduction.pairsNodup _ _ (linesNodup T) (linesNodup T))
  have inj {r s : Four (Line T)} (h:m r=m s) : r=s:=by have eq:=congrArg m h; rwa [inv,inv] at eq
  have nn : (B.map m).Nodup:=List.Pairwise.map _ (fun _ _ neq eq=>neq (inj eq)) nd
  have full (r : Four (Line T)) : r∈B:=fullFour _ (fun b=>List.mem_attach _ b) r
  apply List.perm_iff_count.mpr; intro r
  have mem : r∈B.map m:=List.mem_map.mpr ⟨m r,full _,inv r⟩
  change (B.map m).count r=B.count r; rw [nn.count,nd.count]; simp only [mem,full,ite_true]

theorem moveOcc {n} {G : MaximalFamily n} (T : Transversal G) (p : Word n) (a : Line T) (r : Four (Line T)) :
    a∈occ (fourMap (shift T p) r) ↔ shift T p a∈occ r := by
  have e (b : Line T) : a=shift T p b ↔ shift T p a=b:=by
    constructor
    · intro h; rw [h,shiftTwice]
    · intro h; rw [←h,shiftTwice]
  simp only [occ,fourMap,List.mem_cons,List.not_mem_nil,or_false,e]

private theorem zeros {B H : Type} [CommRing H] (xs : List B) : sumOver xs (fun _=>(0:H))=0 := by
  induction xs with | nil => rfl | cons i xs ih => change 0+sumOver xs _=0; rw [ih]; grind only

open HighestAnchorPauliTrace (headFrame wordExpectation)
open FrameExteriorSector (sourceTuple)
open StabilizerCharacterBasis (Lift block)
open UpperPairCap (walls)

theorem fixedAnchor {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (v : Basis n→C) (w : ExteriorCuts.Wedge7) (hw : w∈walls)
    (r : Four (Line T)) (off : anchor T c∉occ r) :
    let H:=headFrame A (fun j=>block half F c j i) v
    blade (columns half F T c i H) r (sourceTuple w)=0 := by
  let H:=headFrame A (fun j=>block half F c j i) v
  have head : ∀w∈walls,w.i=0:=by decide
  have av (b : Line T) (hb : b∈occ r) : columns half F T c i H b w.i=0 := by
    rw [head w hw]; exact anchorOff half h2 F T c i b (fun eq=>off (eq ▸ hb))
  change blade (columns half F T c i H) r (sourceTuple w)=0
  unfold blade FourCopySectors.rawBlock FourCopySectors.act
  have one (p : ExteriorPauliBase.Permutation) :
      tensorFour (columns half F T c i H) (reorder r p) (sourceTuple w)=0 := by
    unfold tensorFour tensor reorder sourceTuple; rw [av _ (posMem r _)]; grind only
  simp only [one,Semiring.mul_zero,zeros]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumLE {B : Type} (xs : List B) (f g : B→R) (le : ∀w∈xs,f w≤g w) : sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i xs ih =>
    have a:=le i List.mem_cons_self; have b:=ih (fun w hw=>le w (List.mem_cons_of_mem i hw))
    change f i+sumOver xs f≤g i+sumOver xs g; grind only

private theorem countFour {A : Type} [DecidableEq A] (L : List A) (nd : L.Nodup) (full : ∀a,a∈L)
    (r : Four A) (q : R) (nn : 0≤q) :
    sumOver L (fun a=>if a∈occ r then q else 0)≤4*q := by
  let test (j a : A):=if j=a then q else 0
  let f a:=test r.1.1 a+test r.1.2 a+test r.2.1 a+test r.2.2 a
  have e (a : A) : (if a∈occ r then q else 0)≤f a := by
    unfold f test; simp only [occ,List.mem_cons,List.not_mem_nil,or_false]
    have flip (j : A) : (if j=a then q else 0)=(if a=j then q else 0):=by
      by_cases h:j=a
      · subst j; rfl
      · simp only [h,Ne.symm h,ite_false]
    rw [flip,flip,flip,flip]
    by_cases h:a=r.1.1 <;> by_cases k:a=r.1.2 <;> by_cases l:a=r.2.1 <;> by_cases m:a=r.2.2 <;>
      simp [h,k,l,m] <;> grind only
  have sum (j : A) : sumOver L (test j)=q:=ExteriorPauliBase.sumOnIndex L j (fun _=>q) nd (full j)
  have bound:=sumLE L _ _ (fun a _=>e a)
  unfold f at bound; simp only [sumOverAdd,sum] at bound; grind only

theorem orbitFour {n} {G : MaximalFamily n} (F : Lift G) (T : Transversal G) (a : Line T) (c : Word n) (V : Four (Line T)→C)
    (supported : ∀r,a∉occ r → V r=0) :
    let B:=fourIndices T.reps.attach
    sumOver (words n) (fun p=>sumOver B (fun r=>(star (V r)*(fourProduct (fun u=>star (step F T c p u)) r*V (fourMap (shift T p) r))).re))
      ≤ (2:R)^n*(4*mass B V) := by
  classical
  let B:=fourIndices T.reps.attach
  let price (b : Line T):=mass B (gate b occ V)
  let e (p : Word n):=sumOver B (fun r=>(star (V r)*(fourProduct (fun u=>star (step F T c p u)) r*V (fourMap (shift T p) r))).re)
  have bound : sumOver (words n) e≤sumOver (words n) (fun p=>price (shift T p a)):=by
    apply sumLE; intro p _
    exact occupationPrice T a p B occ (fourMap (shift T p)) V (fourProduct (fun u=>star (step F T c p u)))
      (movePerm T p) (moveTwice T p) (moveOcc T p a) supported (fourStepUnit F T c p)
  rw [orbitCount T a price] at bound
  have total : sumOver T.reps.attach price≤4*mass B V:=by
    change sumOver T.reps.attach (fun b=>sumOver B (fun r=>normSq (gate b occ V r)))≤4*sumOver B (fun r=>normSq (V r))
    rw [sumOverSwap,sumOverMulLeft B _ 4]
    apply sumLE; intro r _
    have point (b : Line T) : normSq (gate b occ V r)=(if b∈occ r then normSq (V r) else 0):=by by_cases t:b∈occ r <;> simp [gate,t]
    rw [sumOverCongr _ point]
    apply Std.le_trans _ (countFour _ (linesNodup T) (fun b=>List.mem_attach _ b) r (normSq (V r)) (normSq_nonnegative (V r)))
    apply sumLE; intro b _; by_cases t:b∈occ r <;> simp [t]
  have pos (k : Nat) : 0≤(2:R)^k:=by
    induction k with
    | zero => rw [Semiring.pow_zero]; exact Std.le_of_lt OrderedRing.zero_lt_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by have :=OrderedRing.zero_lt_one (R:=R); grind only)
  exact Std.le_trans bound (OrderedRing.mul_le_mul_of_nonneg_left total (pos n))

theorem physicalOrbitPrice {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (v : Basis n→C) (w : ExteriorCuts.Wedge7) (hw : w∈walls) :
    let h:=(block half F c i i).re
    let H:=headFrame A (fun j=>block half F c j i) v
    let D:=fun r=>blade (columns half F T c i H) r (sourceTuple w)
    24*h^4*half^n*sumOver (words n) (fun p=>(wordExpectation H p w).re)≤4*mass (fourIndices T.reps.attach) (masked D) := by
  classical
  let h:=(block half F c i i).re
  let H:=headFrame A (fun j=>block half F c j i) v
  let D:=fun r=>blade (columns half F T c i H) r (sourceTuple w)
  let a:=anchor T c
  let B:=fourIndices T.reps.attach
  let W:=sumOver (words n) (fun p=>(wordExpectation H p w).re)
  have av (r : Four (Line T)) (off : a∉occ r) : masked D r=0 := by
    have zero : D r=0:=fixedAnchor half h2 F T c i A v w hw r off
    by_cases aff:affine r <;> simp only [masked,zero,aff,ite_false,ite_true]
  have price:=orbitFour F T a c (masked D) av
  have e:=planeTrace half h2 F T c i H w
  change _=24*h^4*W at e
  have bound : 24*h^4*W≤(2:R)^n*(4*mass B (masked D)):=e ▸ price
  have nn (k : Nat) : 0≤half^k := by
    induction k with
    | zero => rw [Semiring.pow_zero]; exact Std.le_of_lt OrderedRing.zero_lt_one
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by have :=OrderedRing.zero_lt_one (R:=R); grind only)
  have sc:=OrderedRing.mul_le_mul_of_nonneg_left bound (nn n)
  have inv:=SectorDefectAccounting.dimensionInverse half h2 n
  change 24*h^4*half^n*W≤4*mass B (masked D)
  grind only

end RankSeven.HighestChartOrbitPrice

#print axioms RankSeven.HighestChartOrbitPrice.movePerm
#print axioms RankSeven.HighestChartOrbitPrice.fixedAnchor
#print axioms RankSeven.HighestChartOrbitPrice.orbitFour
#print axioms RankSeven.HighestChartOrbitPrice.physicalOrbitPrice

