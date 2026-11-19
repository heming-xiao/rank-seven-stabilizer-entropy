import Rank7HighestSlaterCoordinates
import Rank7AnchorAllFock

namespace RankSeven.HighestFivePairMinors

open Lean.Grind Pauli ComplexScalar AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive
open AnchorMixedCAR AnchorTripleEnergy HighestTailReplacement HighestSlaterCoordinates
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

def five : List (Fin 5) := [0,1,2,3,4]
def pairs : List (Fin 5×Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def minor (L : List I) (y a b c : I→C) (Y : Fin 5→I→C) (p : Fin 5×Fin 5) :=
  let m (x w : I→C):=dot L x (Y p.1)*dot L w (Y p.2)-dot L x (Y p.2)*dot L w (Y p.1)
  dot L a y*m b c-dot L b y*m a c+dot L c y*m a b

def holeTable (m : Fin 5×Fin 5→C) : Basis 5→C
  | (false,false,true,true,true,()) => m (0,1)
  | (false,true,false,true,true,()) => -m (0,2)
  | (false,true,true,false,true,()) => m (0,3)
  | (false,true,true,true,false,()) => -m (0,4)
  | (true,false,false,true,true,()) => m (1,2)
  | (true,false,true,false,true,()) => -m (1,3)
  | (true,false,true,true,false,()) => m (1,4)
  | (true,true,false,false,true,()) => m (2,3)
  | (true,true,false,true,false,()) => -m (2,4)
  | (true,true,true,false,false,()) => m (3,4)
  | _ => 0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem pullCoordinates (L : List I) (y a b c : I→C) (Y : Fin 5→I→C) :
    pullContract L Y five y a b c (filled five.length)=holeTable (minor L y a b c Y) := by
  funext ⟨i,j,k,l,m,()⟩
  cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
    simp only [pullContract,five,two,lower,filled,List.length_cons,List.length_nil,coordinate,star_star,holeTable,minor] <;> grind only

private theorem maskEnergy {d : Nat} (f : Basis (d+1)→C) :
    energy f=energy (fun z=>f (false,z))+energy (fun z=>f (true,z)) := by
  change Bool×Basis d→C at f
  have split {A B : Type} (xs : List A) (ys : List B) (F : A×B→R) :
      sumOver (productIndices xs ys) F=sumOver xs (fun i=>sumOver ys (fun j=>F (i,j))) := by
    unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
  unfold energy mass
  exact (split [false,true] (qubitIndices d) (fun z=>normSq (f z))).trans (by change _+(_+0)=_; grind only)

private theorem unitEnergy (f : Basis 0→C) : energy f=normSq (f ()) := by change _+0=_; grind only
private theorem negNorm (z : C) : normSq (-z)=normSq z := by simp only [normSq,re_neg,im_neg]; grind only
private theorem zeroNorm : normSq (0:C)=0 := by simp only [normSq,re_zero,im_zero]; grind only

set_option maxRecDepth 12000 in
theorem tableEnergy (m : Fin 5×Fin 5→C) : energy (holeTable m)=sumOver pairs (fun p=>normSq (m p)) := by
  rw [maskEnergy (d:=4)]
  simp only [maskEnergy (d:=3),maskEnergy (d:=2),maskEnergy (d:=1),maskEnergy (d:=0),unitEnergy,holeTable,zeroNorm,negNorm]
  unfold pairs sumOver; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; grind only

/-- For every original orthonormal five-frame, the exact energy of each anchored
triple contraction is the sum of squared 3×3 minors on its ten unordered pairs. -/
theorem tenPairMinors (L : List I) (y a b c : I→C) (Y : Fin 5→I→C)
    (unit : ∀j, dot L (Y j) (Y j)=1)
    (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0) :
    energy (contracted L y a b c (synth L Y five (filled five.length)))=
      sumOver pairs (fun p=>normSq (minor L y a b c Y p)) := by
  rw [contractedSlaterEnergy L Y five (by decide) (fun j _=>unit j) (fun i _ j _=>apart i j),
    pullCoordinates]; exact tableEnergy _

open HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits AnchorOccupation
open AnchorVacantScore (sites)

/-- A coordinate of y∧Yᵢ∧Yⱼ in the actual ordered character triple t. -/
def coefficient {A : Type} (y : A→C) (Y : Fin 5→A→C) (t : A×A×A) (p : Fin 5×Fin 5) :=
  let m (x w : A):=Y p.1 x*Y p.2 w-Y p.2 x*Y p.1 w
  y t.1*m t.2.1 t.2.2-y t.2.1*m t.1 t.2.2+y t.2.2*m t.1 t.2.1

theorem dotMode [DecidableEq I] (L : List I) (nd : L.Nodup) (i : I) (mem : i∈L) (h : I→C) :
    dot L (mode i) h=h i := by
  have e (j : I) : star (mode (R:=R) i j)*h j=(if i=j then h i else 0) := by
    by_cases eq:i=j
    · subst j; simp only [mode,ite_true]; have one : star (1:C)=1 := by apply ComplexScalar.ext <;> simp <;> grind only
      rw [one]; grind only
    · simp only [mode,eq,ite_false]; have zero : star (0:C)=0:=by apply ComplexScalar.ext <;> simp <;> grind only
      rw [zero]; grind only
  unfold dot; rw [sumOverCongr L e]
  have select (xs : List I) (nn : xs.Nodup) : sumOver xs (fun j=>if i=j then h i else 0)=if i∈xs then h i else 0 := by
    induction xs with
    | nil => simp [sumOver]
    | cons j xs ih =>
      obtain ⟨off,nt⟩:=List.nodup_cons.mp nn
      change (if i=j then h i else 0)+sumOver xs _=_
      rw [ih nt]; by_cases eq:i=j
      · subst j; simp [off]; grind only
      · by_cases m:i∈xs <;> simp [eq,m] <;> grind only
  simp only [select L nd,mem,ite_true]

theorem tripleMembers {A : Type} (L : List A) (t : A×A×A) (ht : t∈AnchorScoreEnumeration.tripleList L) :
    t.1∈L ∧ t.2.1∈L ∧ t.2.2∈L := by
  have pair {B : Type} (xs : List B) (p : B×B) (hm : p∈AnchorScoreEnumeration.pairList xs) : p.1∈xs ∧ p.2∈xs := by
    induction xs with
    | nil => contradiction
    | cons i xs ih =>
      rcases List.mem_append.mp hm with h|h
      · obtain ⟨j,hj,e⟩:=List.mem_map.mp h; cases e; exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hj⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1,List.mem_cons_of_mem _ (ih h).2⟩
  induction L with
  | nil => contradiction
  | cons i L ih =>
    rcases List.mem_append.mp ht with h|h
    · obtain ⟨p,hp,e⟩:=List.mem_map.mp h; cases e
      exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ (pair L p hp).1,List.mem_cons_of_mem _ (pair L p hp).2⟩
    · obtain ⟨a,b,c⟩:=ih h; exact ⟨List.mem_cons_of_mem _ a,List.mem_cons_of_mem _ b,List.mem_cons_of_mem _ c⟩


end RankSeven.HighestFivePairMinors

#print axioms RankSeven.HighestFivePairMinors.pullCoordinates
#print axioms RankSeven.HighestFivePairMinors.tableEnergy
#print axioms RankSeven.HighestFivePairMinors.tenPairMinors
#print axioms RankSeven.HighestFivePairMinors.dotMode
#print axioms RankSeven.HighestFivePairMinors.tripleMembers

