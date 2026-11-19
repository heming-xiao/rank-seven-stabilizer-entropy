import Rank7PhysicalCutCapacities

/-! The five-slot 2+3 antisymmetrizer. The ten choices of the first block
give 100 cross terms, in three double cosets of sizes 10, 60 and 30. -/
namespace RankSeven.FiveShuffleCAR
open Lean.Grind Pauli ComplexScalar HyperplaneIncidence
abbrev Five (α : Type) := (α × α) × ((α × α) × α)
abbrev Perm := Five (Fin 5)
def atSlot {α : Type} (u : Five α) (i : Fin 5) : α :=
  if i=0 then u.1.1 else if i=1 then u.1.2 else if i=2 then u.2.1.1 else if i=3 then u.2.1.2 else u.2.2
def act {α : Type} (p : Perm) (u : Five α) : Five α :=
  ((atSlot u p.1.1,atSlot u p.1.2),(atSlot u p.2.1.1,atSlot u p.2.1.2),atSlot u p.2.2)
def ident : Perm := ((0,1),(2,3),4)
def firstSwap : Perm := ((0,2),(1,3),4)
def secondSwap : Perm := ((2,3),(0,1),4)
private theorem slots (i : Fin 5) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by revert i; decide
theorem actAt {α : Type} (u : Five α) (p : Perm) (i : Fin 5) : atSlot (act p u) i=atSlot u (atSlot p i) := by
  rcases slots i with rfl|rfl|rfl|rfl|rfl <;> rfl
theorem actCompose {α : Type} (p q : Perm) (u : Five α) : act q (act p u) = act (act q p) u := by
  apply Prod.ext
  · exact Prod.ext (actAt u p q.1.1) (actAt u p q.1.2)
  · exact Prod.ext (Prod.ext (actAt u p q.2.1.1) (actAt u p q.2.1.2)) (actAt u p q.2.2)
theorem actIdent {α : Type} (u : Five α) : act ident u=u := by rfl

def indices {α : Type} (xs : List α) : List (Five α) :=
  productIndices (productIndices xs xs) (productIndices (productIndices xs xs) xs)
private theorem permuteSum {α C : Type} [CommRing C] {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2

theorem changeVariables {α C : Type} [DecidableEq α] [CommRing C] (xs : List α) (nd : xs.Nodup) (full : ∀x,x∈xs)
    (p q : Perm) (pq : act q p=ident) (qp : act p q=ident) (f : Five α → C) :
    sumOver (indices xs) (fun u => f (act p u))=sumOver (indices xs) f := by
  have pair {A B : Type} {as : List A} {bs : List B} {a : A} {b : B} (ha : a∈as) (hb : b∈bs) :
      (a,b)∈productIndices as bs := List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
  have complete (u : Five α) : u∈indices xs := pair (pair (full _) (full _)) (pair (pair (full _) (full _)) (full _))
  have two := HyperplaneInduction.pairsNodup xs xs nd nd
  have five : (indices xs).Nodup := HyperplaneInduction.pairsNodup _ _ two (HyperplaneInduction.pairsNodup _ _ two nd)
  have inj (u v : Five α) (e : act p u=act p v) : u=v := by
    have h := congrArg (act q) e; simpa only [actCompose,pq,actIdent] using h
  have pn : ((indices xs).map (act p)).Nodup := List.Pairwise.map _ (fun u v (ne : u≠v) e => ne (inj u v e)) five
  have perm : ((indices xs).map (act p)).Perm (indices xs) := by
    apply List.perm_iff_count.mpr; intro u
    have mem : u∈(indices xs).map (act p) := List.mem_map.mpr ⟨act q u,complete _,by rw [actCompose,qp,actIdent]⟩
    rw [pn.count,five.count]; simp [mem,complete]
  simpa only [sumOver,List.map_map,Function.comp_def] using permuteSum perm f

def blocks : List Perm := [((0,1),(2,3),4),
  ((0,1),(2,4),3),
  ((0,1),(3,2),4),
  ((0,1),(3,4),2),
  ((0,1),(4,2),3),
  ((0,1),(4,3),2),
  ((1,0),(2,3),4),
  ((1,0),(2,4),3),
  ((1,0),(3,2),4),
  ((1,0),(3,4),2),
  ((1,0),(4,2),3),
  ((1,0),(4,3),2)]
def choices : List (Fin 10) := List.finRange 10
def shuffle (i : Fin 10) : Perm := [((0,1),(2,3),4),
  ((0,2),(1,3),4),
  ((0,3),(1,2),4),
  ((0,4),(1,2),3),
  ((1,2),(0,3),4),
  ((1,3),(0,2),4),
  ((1,4),(0,2),3),
  ((2,3),(0,1),4),
  ((2,4),(0,1),3),
  ((3,4),(0,1),2)].getD i.val ident
private def inverseShuffle (i : Fin 10) : Perm := [((0,1),(2,3),4),
  ((0,2),(1,3),4),
  ((0,2),(3,1),4),
  ((0,2),(3,4),1),
  ((2,0),(1,3),4),
  ((2,0),(3,1),4),
  ((2,0),(3,4),1),
  ((2,3),(0,1),4),
  ((2,3),(0,4),1),
  ((2,3),(4,0),1)].getD i.val ident
private def inverseSlot (p : Perm) (k : Fin 5) : Fin 5 :=
  if p.1.1=k then 0 else if p.1.2=k then 1 else if p.2.1.1=k then 2 else if p.2.1.2=k then 3 else 4
private def inverse (p : Perm) : Perm := ((inverseSlot p 0,inverseSlot p 1),(inverseSlot p 2,inverseSlot p 3),inverseSlot p 4)
private def helper (i j : Fin 10) : Perm :=
  let selector : List (List Nat) := [[0,0,2,3,6,8,9,0,1,4],
    [0,0,2,3,6,0,1,8,9,4],
    [0,2,0,3,0,6,1,8,4,9],
    [0,2,3,0,0,1,6,4,8,9],
    [0,6,0,1,0,2,3,8,9,4],
    [0,0,6,1,2,0,3,8,4,9],
    [0,0,1,6,2,3,0,4,8,9],
    [0,0,6,1,2,8,4,0,3,9],
    [0,0,1,6,2,4,8,3,0,9],
    [0,1,0,6,4,2,8,3,9,0]]
  blocks.getD ((selector.getD i.val []).getD j.val 0) ident
private def change (i j : Fin 10) := act (inverseShuffle i) (helper i j)
private def rep (i j : Fin 10) :=
  if i=j then ident else if (shuffle i).1.1=(shuffle j).1.1 ∨ (shuffle i).1.1=(shuffle j).1.2 ∨
    (shuffle i).1.2=(shuffle j).1.1 ∨ (shuffle i).1.2=(shuffle j).1.2 then firstSwap else secondSwap
private def rightBlock (i j : Fin 10) := act (act (shuffle j) (change i j)) (rep i j)

def odd (p : Perm) : Bool :=
  (((List.finRange 5).flatMap (fun i => (List.finRange 5).filter (fun j => i<j && atSlot p j<atSlot p i))).length % 2)==1
private def neg (i j : Fin 10) := decide (rep i j=firstSwap)
set_option synthInstance.maxSize 200 in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 40000 in
private theorem table : choices.all (fun i => choices.all (fun j => decide (
    act (inverse (change i j)) (change i j)=ident ∧ act (change i j) (inverse (change i j))=ident ∧
    act (shuffle i) (change i j)=helper i j ∧ helper i j∈blocks ∧ rightBlock i j∈blocks ∧
    act (shuffle j) (change i j)=act (rightBlock i j) (rep i j) ∧
    (((odd (shuffle i) ^^ odd (shuffle j)) ^^ odd (helper i j)) ^^ odd (rightBlock i j))=neg i j )))=true := by decide

def BlockAlternating {α R : Type} [CommRing R] (Z : Five α → ComplexScalar R) : Prop :=
  ∀ p∈blocks, ∀ u, Z (act p u)=GenericExteriorKernel.signed (odd p) (Z u)
def merge {α R : Type} [CommRing R] (Z : Five α → ComplexScalar R) (u : Five α) :=
  sumOver choices (fun i => GenericExteriorKernel.signed (odd (shuffle i)) (Z (act (shuffle i) u)))

variable {R α : Type} [CommRing R]
private def corr (xs : List α) (Z : Five α → ComplexScalar R) (p : Perm) :=
  sumOver (indices xs) (fun u => (star (Z u)*Z (act p u)).re)
private def term (Z : Five α → ComplexScalar R) (i : Fin 10) (u : Five α) :=
  GenericExteriorKernel.signed (odd (shuffle i)) (Z (act (shuffle i) u))

private theorem signs (a b c d : Bool) (z w : ComplexScalar R) :
    (star (GenericExteriorKernel.signed a (GenericExteriorKernel.signed c z))*
        GenericExteriorKernel.signed b (GenericExteriorKernel.signed d w)).re =
      GenericExteriorKernel.signed (((a^^b)^^c)^^d) (star z*w).re := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [GenericExteriorKernel.signed,re_mul] <;> grind only

private theorem sumNeg {I : Type} (xs : List I) (f : I → R) :
    sumOver xs (fun i => -f i) = -sumOver xs f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih => change -f i+sumOver xs _= -(f i+sumOver xs _); rw [ih]; grind only

set_option synthInstance.maxSize 200 in
private theorem shufflePair [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ x,x∈xs)
    (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) (i j : Fin 10) (memi : i∈choices) (memj : j∈choices) :
    sumOver (indices xs) (fun u => (star (term Z i u)*term Z j u).re)=
      GenericExteriorKernel.signed (neg i j) (corr xs Z (rep i j)) := by
  obtain ⟨inv1,inv2,hl,hin,rin,hr,sgn⟩ := _root_.of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp table i memi) j memj)
  let k := change i j
  have e := changeVariables xs nd full k (inverse k) inv1 inv2 (fun u => (star (term Z i u)*term Z j u).re)
  rw [←e]
  have row (u : Five α) :
      (star (term Z i (act k u))*term Z j (act k u)).re =
        GenericExteriorKernel.signed (neg i j) (star (Z u)*Z (act (rep i j) u)).re := by
    unfold term; rw [actCompose,actCompose]; change _=_
    rw [hl,hr,←actCompose,hz _ hin,hz _ rin,signs,sgn]
  rw [sumOverCongr _ row]; unfold GenericExteriorKernel.signed corr
  cases neg i j <;> simp only [Bool.false_eq_true,ite_false,ite_true]; apply sumNeg

private def matchRep (p : Perm) (i j : Fin 10) : Bool := decide (rep i j=p)
set_option maxRecDepth 40000 in
private theorem countTable : choices.all (fun i => decide (
    (choices.filter (matchRep ident i)).length=1 ∧
    (choices.filter (matchRep firstSwap i)).length=6 ∧
    (choices.filter (matchRep secondSwap i)).length=3))=true := by decide

local instance : NatCast R := Semiring.natCast
private theorem sumIndicator {I : Type} (xs : List I) (p : I → Bool) (z : R) :
    sumOver xs (fun i => if p i then z else 0)=((xs.filter p).length:R)*z := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih =>
    change (if p i then z else 0)+sumOver xs _=_
    rw [List.filter_cons,ih]; cases p i <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons,Semiring.natCast_succ] <;> grind only

private theorem sumClasses (f : Perm → R) (i : Fin 10) (hi : i∈choices) :
    sumOver choices (fun j => GenericExteriorKernel.signed (neg i j) (f (rep i j))) =
    f ident-6*f firstSwap+3*f secondSwap := by
  have clas (j : Fin 10) :
      GenericExteriorKernel.signed (neg i j) (f (rep i j)) =
      ((if matchRep ident i j then f ident else 0)+(if matchRep firstSwap i j then -(f firstSwap) else 0))+
        (if matchRep secondSwap i j then f secondSwap else 0) := by
    have kinds : rep i j=ident ∨ rep i j=firstSwap ∨ rep i j=secondSwap := by
      unfold rep; split
      · exact Or.inl rfl
      · split; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl)
    rcases kinds with h|h|h <;> simp [neg,matchRep,h,GenericExteriorKernel.signed,ident,firstSwap,secondSwap] <;> grind only
  obtain ⟨a,b,c⟩ := _root_.of_decide_eq_true (List.all_eq_true.mp countTable i hi)
  rw [sumOverCongr _ clas,sumOverAdd,sumOverAdd,sumIndicator,sumIndicator,sumIndicator,a,b,c]
  have one : ((1:Nat):R)=1 := Semiring.natCast_one
  have two : ((2:Nat):R)=2 := by change ((1+1:Nat):R)=2; rw [Semiring.natCast_succ,one]; grind only
  have three : ((3:Nat):R)=3 := by change ((2+1:Nat):R)=3; rw [Semiring.natCast_succ,two]; grind only
  have six : ((6:Nat):R)=6 := by change ((2*3:Nat):R)=6; rw [Semiring.natCast_mul,two,three]; grind only
  rw [one,three,six]; grind only

private theorem reSum {I : Type} (xs : List I) (f : I → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

/-- Exact three-layer CAR identity for exterior multiplication of an alternating
two-slot and three-slot block, retaining fully ordered tensor coordinates. -/
theorem fiveShuffleCAR [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ x,x∈xs)
    (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) :
    sumOver (indices xs) (fun u => normSq (merge Z u)) =
    10 * (sumOver (indices xs) (fun u => normSq (Z u)) -
      6*sumOver (indices xs) (fun u => (star (Z u)*Z (act firstSwap u)).re) +
      3*sumOver (indices xs) (fun u => (star (Z u)*Z (act secondSwap u)).re)) := by
  have exp (u : Five α) : normSq (merge Z u)=sumOver choices (fun i => sumOver choices (fun j =>
      (star (term Z i u)*term Z j u).re)) := by
    change normSq (sumOver choices (fun i => term Z i u))=_
    rw [←re_star_mul_self,ComplexExterior.starSumOver,sumOverMulRight]; simp only [sumOverMulLeft,reSum]
  rw [sumOverCongr _ exp,sumOverSwap]
  conv => lhs; arg 2; intro i; rw [sumOverSwap]
  have row (i : Fin 10) (hi : i∈choices) :
      sumOver choices (fun j => sumOver (indices xs) (fun u => (star (term Z i u)*term Z j u).re)) =
        corr xs Z ident-6*corr xs Z firstSwap+3*corr xs Z secondSwap := by
    exact (congrArg List.sum (List.map_congr_left (fun j hj => shufflePair xs nd full Z hz i j hi hj))).trans
      (sumClasses (corr xs Z) i hi)
  refine (congrArg List.sum (List.map_congr_left row)).trans ?_
  change sumOver choices (fun _ => corr xs Z ident-6*corr xs Z firstSwap+3*corr xs Z secondSwap)=_
  have scale (v : R) : sumOver choices (fun _ => v)=10*v := by
    change v+(v+(v+(v+(v+(v+(v+(v+(v+(v+0)))))))))=10*v; grind only
  rw [scale]; unfold corr; simp only [actIdent,re_star_mul_self]

end RankSeven.FiveShuffleCAR
#print axioms RankSeven.FiveShuffleCAR.fiveShuffleCAR
