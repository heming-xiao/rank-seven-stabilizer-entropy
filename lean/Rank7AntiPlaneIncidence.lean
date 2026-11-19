import Rank7PhysicalEdgeSwitching
import Rank7AntiPairIncidence

/-! Counting the cyclic anticommuting edge presentations of a physical Pauli
plane. The selected first endpoint is the one orthogonal to its companion. -/
namespace RankSeven.AntiPlaneIncidence

open Lean.Grind Pauli PhysicalAntiQuartic PhysicalEdgeSwitching PauliEdgeBlocks
open SymmetricDefect (anti unitWord)
open GenericExteriorKernel (reorder position)
open ExteriorPauliBase (permutations Permutation)

def direction {n : Nat} (w : Four (Word n)) := wordAdd w.1.1 w.1.2

def canonical {n : Nat} (r : Word n → Word n) (w : Four (Word n)) : Bool :=
  cyclicAnticommuting w && !anti w.1.1 (r (direction w))

def flip {α : Type} (u : Four α) : Four α := ((u.1.2,u.1.1),(u.2.2,u.2.1))

private def ind (b : Bool) : Int := if b then 1 else 0

private theorem cyclicFlip {n : Nat} (w : Four (Word n)) : cyclicAnticommuting (flip w)=cyclicAnticommuting w := by
  obtain ⟨⟨a,b⟩,c,d⟩ := w
  change (anti b a && anti a d && anti d c && anti c b)=(anti a b && anti b c && anti c d && anti d a)
  rw [antiSymm b a,antiSymm a d,antiSymm d c,antiSymm c b]
  cases anti a b <;> cases anti b c <;> cases anti c d <;> cases anti d a <;> decide

private theorem endpointPair {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (w : Four (Word n)) :
    ind (canonical r w)+ind (canonical r (flip w))=ind (cyclicAnticommuting w) := by
  simp only [canonical,cyclicFlip]
  have cy (x y : Bool) (e : y=(!x)) : ind (true && !x)+ind (true && !y)=ind true := by cases x <;> subst y <;> decide
  cases h : cyclicAnticommuting w
  · rfl
  · apply cy
    obtain ⟨⟨a,b⟩,c,d⟩ := w
    change anti b (r (wordAdd b a))= !anti a (r (wordAdd a b))
    have ab : anti a b=true := by
      change (anti a b && anti b c && anti c d && anti d a)=true at h
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1
    have d0 : wordAdd a b≠unitWord n := by
      intro eq; have e := (wordAddEqZero a b).mp eq; subst b; rw [antiSelf] at ab; contradiction
    have s := comp (wordAdd a b) d0
    rw [antiAddLeft] at s
    rw [wordAddComm b a]
    cases ea : anti a (r (wordAdd a b)) <;> cases eb : anti b (r (wordAdd a b)) <;> simp_all

private theorem permSum {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → Int) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem twiceCanonical {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (w : Four (Word n)) :
    2*sumOver permutations (fun p => ind (canonical r (reorder w p)))=
      sumOver permutations (fun p => ind (cyclicAnticommuting (reorder w p))) := by
  have tab : (permutations.map flip).Perm permutations := by decide
  have eq := permSum tab (fun p => ind (canonical r (reorder w p)))
  simp only [sumOver,List.map_map,Function.comp_def] at eq
  change sumOver permutations (fun p => ind (canonical r (flip (reorder w p))))=
    sumOver permutations (fun p => ind (canonical r (reorder w p))) at eq
  have m := sumOverCongr permutations (fun p => endpointPair r comp (reorder w p))
  rw [sumOverAdd,eq] at m; omega

/-- On an active physical plane there are exactly four presentations:
two anticommuting directions and two orders of the opposite edges. -/
theorem canonicalPresentations {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (a s t : Word n) :
    sumOver permutations (fun p => ind (canonical r (reorder (affineWords a s t) p)))=
      if anti s t then 0 else if anti a s || anti a t then 4 else 0 := by
  let w := affineWords a s t
  let rows (e : Fin 4 → Fin 4 → Bool) (p : Permutation) := e p.1.1 p.1.2 && e p.1.2 p.2.1 && e p.2.1 p.2.2 && e p.2.2 p.1.1
  have cnt : ∀ e h k : Bool, sumOver permutations (fun p => ind (rows (AnticommutingDefect.affineEdge e h k) p))=
      if e then 0 else if h || k then 8 else 0 := by decide
  have m := twiceCanonical r comp w
  have eq (p : Permutation) : cyclicAnticommuting (reorder w p)=
      rows (AnticommutingDefect.affineEdge (anti s t) (anti a s) (anti a t)) p := by
    change (anti (position (affineWords a s t) p.1.1) (position (affineWords a s t) p.1.2) && anti (position (affineWords a s t) p.1.2) (position (affineWords a s t) p.2.1) &&
      anti (position (affineWords a s t) p.2.1) (position (affineWords a s t) p.2.2) && anti (position (affineWords a s t) p.2.2) (position (affineWords a s t) p.1.1))=_
    simp only [affineWordEdges]; rfl
  simp only [eq,cnt] at m
  change sumOver permutations (fun p => ind (canonical r (reorder w p)))=_
  cases he : anti s t <;> cases ha : anti a s || anti a t <;> simp only [he,ha,Bool.false_eq_true,ite_false,ite_true] at m ⊢ <;> omega

private theorem antiChosen {n : Nat} (s r u : Word n) (sr : anti s r=true)
    (pu : perpendicular s r u=true) :
    anti (wordAdd r u) r=false := (edgeRepresentative s r u sr pu).2

theorem cycleCanonical {n : Nat} (r : Word n → Word n) (s u v : Word n)
    (sr : anti s (r s)=true) (hu : perpendicular s (r s) u=true) (hv : perpendicular s (r s) v=true) :
    canonical r (cycleWords s (r s) u v)=true ∧ direction (cycleWords s (r s) u v)=s := by
  have cycle := cycleWordsCyclic s (r s) u v sr hu hv
  have cyc : cyclicAnticommuting (cycleWords s (r s) u v)=true := by
    unfold cyclicAnticommuting; simp only [cycle.1,cycle.2.1,cycle.2.2.1,cycle.2.2.2]; rfl
  have dir : direction (cycleWords s (r s) u v)=s := by
    unfold cycleWords direction; cases anti u v <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals rw [←wordAddAssoc,wordAddSelf,wordAddComm (unitWord _) s,wordAddZero]
  refine ⟨?_,dir⟩
  simp only [canonical,cyc,dir]
  have a := antiChosen s (r s) u sr hu
  unfold cycleWords; cases anti u v <;> simp [a]


abbrev EdgeIndex (n : Nat) := Word n × Word n × Word n

def present {n : Nat} (r : Word n → Word n) (e : EdgeIndex n) : Bool :=
  anti e.1 (r e.1) && perpendicular e.1 (r e.1) e.2.1 && perpendicular e.1 (r e.1) e.2.2

def encode {n : Nat} (r : Word n → Word n) (e : EdgeIndex n) := cycleWords e.1 (r e.1) e.2.1 e.2.2

def decode {n : Nat} (r : Word n → Word n) (w : Four (Word n)) : EdgeIndex n :=
  let s := direction w
  let v := if anti w.2.1 (r s) then w.2.2 else w.2.1
  (s,wordAdd w.1.1 (r s),wordAdd v (r s))

private theorem addBack {n : Nat} (a b : Word n) : wordAdd (wordAdd a b) a = b := by
  rw [wordAddComm a b,wordAddCancel]

private theorem addBoth {n : Nat} (a b : Word n) : wordAdd a (wordAdd a b)=b := by
  rw [←wordAddAssoc,wordAddSelf,wordAddComm (unitWord _) b,wordAddZero]

theorem decodeEncode {n : Nat} (r : Word n → Word n) (e : EdgeIndex n) (valid : present r e=true) :
    decode r (encode r e)=e := by
  obtain ⟨s,u,v⟩ := e
  change (anti s (r s) && perpendicular s (r s) u && perpendicular s (r s) v)=true at valid
  obtain ⟨h,hv⟩ := Bool.and_eq_true_iff.mp valid
  obtain ⟨sr,hu⟩ := Bool.and_eq_true_iff.mp h
  have dir := (cycleCanonical r s u v sr hu hv).2
  have b := antiChosen s (r s) v sr hv
  have b' : anti (wordAdd (wordAdd (r s) v) s) (r s)=true := by rw [antiAddLeft,b,sr]; rfl
  change decode r (cycleWords s (r s) u v)=(s,u,v)
  unfold decode; rw [dir]
  unfold cycleWords; cases anti u v <;> simp [b,b',addBack]

private theorem labelFourth {n : Nat} (a b c d : Word n) (h : totalLabel ((a,b),(c,d))=unitWord n) :
    wordAdd c (wordAdd a b)=d := by
  change productLabel (productLabel (productLabel a b) c) d=unitWord n at h
  simp only [productLabelIsWordAdd] at h
  rw [wordAddComm c (wordAdd a b)]
  exact (wordAddEqZero _ _).mp h

theorem encodeDecode {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (w : Four (Word n)) (z : totalLabel w=unitWord n) (can : canonical r w=true) :
    present r (decode r w)=true ∧ encode r (decode r w)=w := by
  obtain ⟨⟨a,b⟩,c,d⟩ := w
  let s := wordAdd a b
  have bEq : wordAdd a s=b := addBoth a b
  have dEq : wordAdd c s=d := labelFourth _ _ _ _ z
  change ((anti a b && anti b c && anti c d && anti d a) && !anti a (r s))=true at can
  obtain ⟨h,chosen⟩ := Bool.and_eq_true_iff.mp can
  obtain ⟨h,da⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h,cd⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ab,_⟩ := Bool.and_eq_true_iff.mp h
  have az : anti a (r s)=false := by cases ha : anti a (r s) <;> simp_all
  have as_anti : anti a s=true := by unfold s; rw [antiAddRight,antiSelf,ab]; rfl
  have cs : anti c s=true := by rw [←dEq,antiAddRight,antiSelf] at cd; simpa using cd
  have ds : anti d s=true := by rw [←dEq,antiAddLeft,antiSelf,cs]; rfl
  have ac : anti a c=false := by
    rw [←dEq,antiAddLeft,antiSymm c a,antiSymm s a,as_anti] at da
    cases h : anti a c <;> simp_all
  have ad : anti a d=true := (antiSymm a d).trans da
  have nonzero : s≠unitWord n := by intro e; rw [e,antiZero] at as_anti; contradiction
  have sr := comp s nonzero
  have u := edgeCoordinate s (r s) a sr as_anti az
  change (anti s (r s) && perpendicular s (r s) (wordAdd a (r s)) &&
    perpendicular s (r s) (wordAdd (if anti c (r s) then d else c) (r s)))=true ∧
    cycleWords s (r s) (wordAdd a (r s)) (wordAdd (if anti c (r s) then d else c) (r s))=((a,b),(c,d))
  cases cr : anti c (r s)
  · simp only [Bool.false_eq_true,ite_false]
    have v := edgeCoordinate s (r s) c sr cs cr
    have uv := representativesPairing s (r s) _ _ u.1 v.1
    rw [u.2,v.2,ac] at uv
    simp only [sr,u.1,v.1,cycleWords,←uv,u.2,v.2,bEq,dEq,Bool.false_eq_true,ite_false]
    exact ⟨rfl,True.intro⟩
  · simp only [ite_true]
    have dr : anti d (r s)=false := by rw [←dEq,antiAddLeft,cr,sr]; rfl
    have v := edgeCoordinate s (r s) d sr ds dr
    have uv := representativesPairing s (r s) _ _ u.1 v.1
    rw [u.2,v.2,ad] at uv
    have dBack : wordAdd d s=c := by rw [←dEq,wordAddCancel]
    simp only [sr,u.1,v.1,cycleWords,←uv,u.2,v.2,bEq,dBack,ite_true]
    exact ⟨rfl,True.intro⟩

open AnticommutingDefect (sumCongrMem)
variable {C : Type} [CommRing C]

attribute [local instance] Ring.intCast
noncomputable local instance {n} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem permRing {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem compose {α : Type} (u : Four α) (p q : Permutation) :
    reorder (reorder u p) q=reorder u (reorder p q) := by
  change ((position (reorder u p) _,position (reorder u p) _),(position (reorder u p) _,position (reorder u p) _))=_
  simp only [GenericExteriorKernel.position_reorder]; rfl

private def orbit {α : Type} (f : Four α → C) (u : Four α) := sumOver permutations (fun p => f (reorder u p))

private theorem orbitSymmetric {α : Type} (f : Four α → C) (u : Four α) (p : Permutation) (hp : p∈permutations) :
    orbit f (reorder u p)=orbit f u := by
  have table : permutations.all (fun p => decide ((permutations.map (reorder p)).Perm permutations))=true := by decide
  have h := permRing (_root_.of_decide_eq_true (List.all_eq_true.mp table p hp)) (fun q => f (reorder u q))
  simpa only [sumOver,List.map_map,Function.comp_def,orbit,compose] using h

private theorem cancelUnit (k inv a b : C) (unit : k*inv=1) (eq : k*a=k*b) : a=b := by
  have e := congrArg (fun z => inv*z) eq
  simp only [←Semiring.mul_assoc,CommSemiring.mul_comm inv k,unit,Semiring.one_mul] at e
  exact e

theorem planeWeightInvariant {n : Nat} (i : C) (isq : i^2= -1) (inv24 : C) (h24 : 24*inv24=1)
    (c : Word n → C) (w : Four (Word n)) (p : Permutation) (hp : p∈permutations) :
    planeTerm i c (reorder w p)=planeTerm i c w := by
  have m := orbitSymmetric (orderedTerm i c) w p hp
  unfold orbit at m; rw [orbitWeight i isq,orbitWeight i isq] at m
  have unit : (32:C)*(12*inv24)^5=1 := by
    have k : (2:C)*(12*inv24)=1 := by grind
    have pow := congrArg (fun x : C => x^5) k
    change (2*(12*inv24))^5=1^5 at pow
    grind
  exact cancelUnit 32 _ _ _ unit m

private theorem wordsFull {n : Nat} (p : Word n) : p∈words n := by
  induction p with
  | empty => exact List.mem_cons_self
  | cons a p ih => apply List.mem_flatMap.mpr; refine ⟨p,ih,?_⟩; cases a <;> simp

private abbrev WedgeDistinct {n : Nat} (u : Four (Word n)) := ExteriorIsometry.apart wordKey u

local instance {n : Nat} (u : Four (Word n)) : Decidable (WedgeDistinct u) := by
  unfold WedgeDistinct ExteriorIsometry.apart; infer_instance

private theorem distinctPerm {n : Nat} (w : Four (Word n)) (p : Permutation) (hp : p∈permutations) :
    WedgeDistinct (reorder w p) ↔ WedgeDistinct w := by
  let labels (a : Four (Word n)) (j : Fin 4) := wordKey (position a j)
  have off (u : Four (Word n)) : WedgeDistinct u ↔ ∀ j k : Fin 4, j≠k → labels u j≠labels u k := by
    constructor
    · intro h j k
      have all : ∀ t : Fin 4, t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by decide
      rcases all j with e|e|e|e <;> subst j <;> rcases all k with e|e|e|e <;> subst k <;>
        simp [labels,position,WedgeDistinct,ExteriorIsometry.apart] at * <;> grind
    · intro h
      refine ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 2 3 (by decide)⟩
  have tbl : permutations.all (fun p => (List.finRange 4).all (fun j => (List.finRange 4).all (fun k =>
        decide (position p j=position p k → j=k))))=true := by decide
  have inj (q : Permutation) (hq : q∈permutations) (j k : Fin 4) : position q j=position q k → j=k :=
    _root_.of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp tbl q hq) j (List.mem_finRange _)) k (List.mem_finRange _))
  have keep (v : Four (Word n)) (q : Permutation) (hq : q∈permutations) (d : WedgeDistinct v) :
      WedgeDistinct (reorder v q) := by
    apply (off _).mpr; intro j k ne
    unfold labels; rw [GenericExteriorKernel.position_reorder,GenericExteriorKernel.position_reorder]
    exact (off v).mp d _ _ (fun e => ne (inj q hq j k e))
  constructor
  · intro h
    have table : permutations.all (fun p => decide (FourCopySectors.inverse p∈permutations ∧ reorder p (FourCopySectors.inverse p)=FourCopySectors.ident))=true := by decide
    have inv := _root_.of_decide_eq_true (List.all_eq_true.mp table p hp)
    have m := keep _ _ inv.1 h
    rw [compose,inv.2] at m
    exact m
  · exact keep w p hp

private theorem castSum {α : Type} (xs : List α) (f : α → Int) :
    Int.cast (R:=C) (sumOver xs f)=sumOver xs (fun p => Int.cast (R:=C) (f p)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons a xs ih => change Int.cast (R:=C) (f a+sumOver xs f)=_ ; rw [Ring.intCast_add,ih]; rfl

private theorem constOrbit (z : C) : sumOver permutations (fun _ => z)=24*z := by
  have cnt : sumOver permutations (fun _ => (1:Int))=24 := by decide
  calc
    _ = sumOver permutations (fun _ => Int.cast (R:=C) (1:Int)*z) := by rw [Ring.intCast_ofNat 1]; grind
    _ = _ := by rw [←sumOverMulRight,←castSum,cnt,Ring.intCast_ofNat 24]

private theorem zeroSum {α : Type} (xs : List α) (f : α → C) (z : ∀ x∈xs, f x=0) : sumOver xs f=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change f x+sumOver xs f=0; rw [z _ List.mem_cons_self,ih (fun i hi => z i (List.mem_cons_of_mem _ hi))]; grind

private theorem fullToSortedOrbits {n : Nat} (inv24 : C) (h24 : 24*inv24=1)
    (f : Four (Word n) → C) (deg : ∀ w, ¬WedgeDistinct w → f w=0) :
    sumOver (fourIndices (words n)) f=
      sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (orbit f) := by
  let ts := fourIndices (words n)
  have symmetry := FourCopySectors.fullPermuted (words n) (MixedDefect.allWordsNodup n) wordsFull
  have reindexed (p : Permutation) (hp : p∈permutations) : sumOver ts (fun w => f (reorder w p))=sumOver ts f := by
    simpa only [sumOver,List.map_map,Function.comp_def] using permRing (symmetry p hp) f
  have all : sumOver ts (orbit f)=24*sumOver ts f := by
    unfold orbit; rw [sumOverSwap,←constOrbit]; exact sumCongrMem _ _ _ reindexed
  have sorting := ExteriorIsometry.orderedToSorted (words n) wordsFull (MixedDefect.allWordsNodup n) wordKey (orbit f)
    (orbitSymmetric f) (fun w h => zeroSum _ _ (fun p hp => deg _ (fun d => h ((distinctPerm w p hp).mp d))))
  change sumOver ts (orbit f)=_ at sorting; rw [all] at sorting
  exact cancelUnit 24 _ _ _ h24 sorting

noncomputable def canonicalWeight {n : Nat} (r : Word n → Word n) (i : C) (c : Word n → C) (w : Four (Word n)) : C :=
  if WedgeDistinct w then if canonical r w then planeTerm i c w else 0 else 0

theorem canonicalWeightedSum {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (i : C) (isq : i^2= -1) (inv24 : C) (h24 : 24*inv24=1) (c : Word n → C) :
    sumOver (fourIndices (words n)) (canonicalWeight r i c)=4*
      sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c) := by
  rw [fullToSortedOrbits inv24 h24 (canonicalWeight r i c) (fun w h => ite_eq_right h),sumOverMulLeft]
  apply sumCongrMem; intro w hw
  have inc := _root_.of_decide_eq_true (List.mem_filter.mp hw).2
  have sep : WedgeDistinct w := by unfold WedgeDistinct ExteriorIsometry.apart; omega
  let count := sumOver permutations (fun p => ind (canonical r (reorder w p)))
  have weighted : orbit (canonicalWeight r i c) w=Int.cast (R:=C) count*planeTerm i c w := by
    unfold orbit count; rw [castSum,sumOverMulRight]
    apply sumCongrMem; intro p hp
    have dist := (distinctPerm w p hp).mpr sep
    simp only [canonicalWeight,ite_eq_left dist,planeWeightInvariant i isq inv24 h24 c w p hp]
    cases canonical r (reorder w p) <;> simp [ind] <;> grind
  rw [weighted]
  by_cases zero : totalLabel w=unitWord n
  · let a := w.1.1
    let s := productLabel a w.1.2
    let t := productLabel a w.2.1
    have form : w=affineWords a s t := zeroFrame w zero
    have m := canonicalPresentations r comp a s t
    rw [←form] at m
    change count=_ at m
    unfold planeTerm
    change _*(if totalLabel w=unitWord n ∧ anti s t=false ∧ (anti a s || anti a t)=true then _ else 0)=4*(if totalLabel w=unitWord n ∧ anti s t=false ∧ (anti a s || anti a t)=true then _ else 0)
    cases he : anti s t <;> cases ha : anti a s || anti a t <;> simp [he,ha,zero] at m ⊢ <;> rw [m,Ring.intCast_ofNat] <;> grind
  · simp [planeTerm,zero]; grind

noncomputable def edgeList {n : Nat} (r : Word n → Word n) : List (EdgeIndex n) :=
  (productIndices (words n) (productIndices (words n) (words n))).filter (present r)

noncomputable def rowList {n : Nat} (r : Word n → Word n) : List (Four (Word n)) :=
  (fourIndices (words n)).filter (fun w => decide (totalLabel w=unitWord n) && canonical r w)

private theorem edgeMember {n : Nat} (r : Word n → Word n) (e : EdgeIndex n) :
    e∈edgeList r ↔ present r e=true := by
  have all : e∈productIndices (words n) (productIndices (words n) (words n)) :=
    List.mem_flatMap.mpr ⟨e.1,wordsFull _,List.mem_map.mpr ⟨e.2,HyperplaneInduction.pairMember (wordsFull _) (wordsFull _),rfl⟩⟩
  simp [edgeList,all]

private theorem rowMember {n : Nat} (r : Word n → Word n) (w : Four (Word n)) :
    w∈rowList r ↔ totalLabel w=unitWord n ∧ canonical r w=true := by
  have all : w∈fourIndices (words n) := HyperplaneInduction.pairMember
    (HyperplaneInduction.pairMember (wordsFull _) (wordsFull _)) (HyperplaneInduction.pairMember (wordsFull _) (wordsFull _))
  simp [rowList,all]

theorem chartPerm {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true) :
    ((edgeList r).map (encode r)).Perm (rowList r) := by
  have ws := MixedDefect.allWordsNodup n
  have ps := HyperplaneInduction.pairsNodup _ _ ws ws
  have nodup : (edgeList r).Nodup := (HyperplaneInduction.pairsNodup _ _ ws ps).filter _
  have rows : (rowList r).Nodup := (HyperplaneInduction.pairsNodup _ _ ps ps).filter _
  have ndMap (xs : List (EdgeIndex n)) (unique : xs.Nodup) (good : ∀ e∈xs,present r e=true) : (xs.map (encode r)).Nodup := by
    induction xs with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
      obtain ⟨hx,hxs⟩ := List.nodup_cons.mp unique
      apply List.nodup_cons.mpr
      refine ⟨?_,ih hxs (fun e he => good e (List.mem_cons_of_mem _ he))⟩
      intro h; obtain ⟨e,he,eq⟩ := List.mem_map.mp h
      have m := congrArg (decode r) eq
      rw [decodeEncode _ _ (good e (List.mem_cons_of_mem _ he)),decodeEncode _ _ (good x List.mem_cons_self)] at m
      exact hx (m ▸ he)
  have mapped := ndMap (edgeList r) nodup (fun e he => (edgeMember r e).mp he)
  apply List.perm_iff_count.mpr; intro w
  rw [mapped.count,rows.count]
  have equiv : w∈(edgeList r).map (encode r) ↔ w∈rowList r := by
    constructor
    · intro hw; obtain ⟨⟨s,u,v⟩,he,rfl⟩ := List.mem_map.mp hw
      have val := (edgeMember r _).mp he
      change (anti s (r s) && perpendicular s (r s) u && perpendicular s (r s) v)=true at val
      obtain ⟨h,hv⟩ := Bool.and_eq_true_iff.mp val
      obtain ⟨sr,hu⟩ := Bool.and_eq_true_iff.mp h
      exact (rowMember r _).mpr ⟨cycleWordsLabelZero s (r s) u v,(cycleCanonical r s u v sr hu hv).1⟩
    · intro hw; obtain ⟨z,can⟩ := (rowMember r w).mp hw
      obtain ⟨he,hw⟩ := encodeDecode r comp w z can
      exact List.mem_map.mpr ⟨decode r w,(edgeMember r _).mpr he,hw⟩
  by_cases h : w∈rowList r
  · simp [h,equiv.mpr h]
  · have hn : ¬w∈(edgeList r).map (encode r) := fun he => h (equiv.mp he)
    simp only [ite_eq_right hn,ite_eq_right h]

private theorem filteredSum {α : Type} (xs : List α) (keep : α → Bool) (f : α → C) :
    sumOver (xs.filter keep) f=sumOver xs (fun a => if keep a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases h : keep x <;> simp [h,sumOver] at ih ⊢ <;> grind

theorem edgeWeightedSum {n : Nat} (r : Word n → Word n) (comp : ∀ s, s≠unitWord n → anti s (r s)=true)
    (i : C) (isq : i^2= -1) (inv24 : C) (h24 : 24*inv24=1) (c : Word n → C) :
    sumOver (edgeList r) (fun e => if WedgeDistinct (encode r e) then planeTerm i c (encode r e) else 0)=4*
      sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c) := by
  let f (w : Four (Word n)) := if WedgeDistinct w then planeTerm i c w else 0
  have per := permRing (chartPerm r comp) f
  change sumOver (edgeList r) (fun e => f (encode r e))=_
  calc
    _ = sumOver (rowList r) f := by simpa only [sumOver,List.map_map,Function.comp_def] using per
    _ = sumOver (fourIndices (words n)) (canonicalWeight r i c) := by
      unfold rowList; rw [filteredSum]; apply sumOverCongr; intro w
      by_cases sep : WedgeDistinct w <;> by_cases z : totalLabel w=unitWord n <;> cases h : canonical r w <;>
        simp [f,canonicalWeight,sep,z,h,planeTerm]
    _ = _ := canonicalWeightedSum r comp i isq inv24 h24 c

private def axisDigit : Axis → Nat | .identity => 0 | .x => 1 | .y => 2 | .z => 3

private theorem injectKey {n : Nat} (p q : Word n) (e : wordKey p=wordKey q) : p=q := by
  have consKey {j : Nat} (axis : Axis) (w : Word j) : wordKey (.cons axis w)=4*wordKey w+axisDigit axis := by cases axis <;> rfl
  induction p with
  | empty => cases q; rfl
  | cons a p ih => cases q with
    | cons b q => cases a <;> cases b <;> simp only [consKey,axisDigit] at e <;> first | (congr 1; exact ih q (by omega)) | omega

private theorem cycleDistinct {n : Nat} (s r u v : Word n) (sr : anti s r=true) (hu : perpendicular s r u=true)
    (hv : perpendicular s r v=true) : WedgeDistinct (cycleWords s r u v) ↔ u≠v := by
  let a := wordAdd r u
  let b := wordAdd r v
  have az : anti a r=false := (edgeRepresentative s r u sr hu).2
  have bz : anti b r=false := (edgeRepresentative s r v sr hv).2
  have ao : anti (wordAdd a s) r=true := by rw [antiAddLeft,az,sr]; rfl
  have bo : anti (wordAdd b s) r=true := by rw [antiAddLeft,bz,sr]; rfl
  have odd {x y : Word n} (hx : anti x r=false) (hy : anti y r=true) : wordKey x≠wordKey y := by
    intro e; obtain rfl := injectKey _ _ e; rw [hx] at hy; contradiction
  constructor
  · intro d e; subst v; rw [cycleWords,antiSelf] at d
    exact d.2.1 rfl
  · intro uv
    have ne : a≠b := by
      intro e; have h := congrArg (wordAdd r) e
      change wordAdd r (wordAdd r u)=wordAdd r (wordAdd r v) at h
      rw [addBoth,addBoth] at h; exact uv h
    have nn : wordKey a≠wordKey b := fun h => ne (injectKey _ _ h)
    have mm : wordKey (wordAdd a s)≠wordKey (wordAdd b s) := by
      intro h; have e := congrArg (fun t => wordAdd t s) (injectKey _ _ h)
      change wordAdd (wordAdd a s) s=wordAdd (wordAdd b s) s at e
      rw [wordAddCancel,wordAddCancel] at e; exact ne e
    have aa := odd az ao; have bb := odd bz bo; have ab := odd az bo; have ba := odd bz ao
    change WedgeDistinct (if anti u v then ((a,wordAdd a s),(wordAdd b s,b)) else ((a,wordAdd a s),(b,wordAdd b s)))
    cases anti u v <;> simp only [Bool.false_eq_true,ite_false,ite_true,WedgeDistinct,ExteriorIsometry.apart] <;> grind only

private theorem cyclicPlaneWeight {n : Nat} (i : C) (c : Word n → C) (w : Four (Word n)) (z : totalLabel w=unitWord n)
    (cyc : cyclicAnticommuting w=true) : planeTerm i c w=monomial c w*quarticPhase i w := by
  obtain ⟨⟨a,b⟩,t,d⟩ := w
  change (anti a b && anti b t && anti t d && anti d a)=true at cyc
  obtain ⟨h,da⟩ := Bool.and_eq_true_iff.mp cyc
  obtain ⟨h,td⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ab,bt⟩ := Bool.and_eq_true_iff.mp h
  let s := wordAdd a b
  have adir : anti a s=true := by unfold s; rw [antiAddRight,antiSelf,ab]; rfl
  have de : wordAdd t s=d := labelFourth _ _ _ _ z
  have at' : anti a t=false := by
    rw [←de,antiAddLeft,antiSymm t a,antiSymm s a,adir] at da
    cases h : anti a t <;> simp_all
  have ts : anti t s=true := by rw [←de,antiAddRight,antiSelf] at td; simpa using td
  have st : anti s (wordAdd a t)=false := by
    rw [antiAddRight,antiSymm s a,antiSymm s t,adir,ts]; rfl
  have ak : anti a (wordAdd a t)=false := by rw [antiAddRight,antiSelf,at']; rfl
  unfold planeTerm; simp only [z,productLabelIsWordAdd]
  change (if True ∧ anti s (wordAdd a t)=false ∧ (anti a s || anti a (wordAdd a t))=true then _ else _)=_
  simp [st,adir,ak,SymmetricDefect.phase]; grind

section Real

open ComplexScalar (ofReal imaginaryUnit)
open AntiPairIncidence (edgeWeight nonzeroWords companion)
variable {R : Type} [CommRing R]

private theorem complexRealSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=(f a).re+sumOver xs (fun a => (f a).re); rw [ComplexScalar.re_add,ih]

theorem physicalEdgeMonomial (half : R) (unit : 2*half=1) {n : Nat} (f : Word n → R) (s r u v : Word n)
    (sr : anti s r=true) (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    (if WedgeDistinct (cycleWords s r u v) then
      planeTerm imaginaryUnit (fun p => ofReal (f p)) (cycleWords s r u v) else 0).re =
        edgeWeight f s r u*physicalEdgeMatrix half s r u v*edgeWeight f s r v := by
  let w := cycleWords s r u v
  by_cases e : u=v
  · have deg := mt (cycleDistinct s r u v sr hu hv).mp (not_not_intro e)
    simp only [ite_eq_right deg,physicalEdgeMatrix,ite_eq_left e,ComplexScalar.re_zero]; grind
  have d := (cycleDistinct s r u v sr hu hv).mpr e
  rw [ite_eq_left d]
  have cyc := cycleWordsCyclic s r u v sr hu hv
  have cy : cyclicAnticommuting w=true := by
    unfold cyclicAnticommuting; simp only [w,cyc.1,cyc.2.1,cyc.2.2.1,cyc.2.2.2]; rfl
  have z : totalLabel w=unitWord n := cycleWordsLabelZero _ _ _ _
  change (planeTerm imaginaryUnit (fun p => ofReal (f p)) w).re=_
  rw [cyclicPlaneWeight _ _ _ z cy]
  have m : monomial (fun p => ofReal (f p)) w=ofReal (edgeWeight f s r u * edgeWeight f s r v) := by
    unfold w monomial cycleWords edgeWeight; cases anti u v <;>
      simp only [Bool.false_eq_true,ite_false,ite_true]; all_goals apply ComplexScalar.ext <;> simp <;> grind
  rw [m,physicalEdgeMatrix,ite_eq_right e]
  dsimp only
  rw [physicalQuadTrace imaginaryUnit ComplexScalar.imaginaryUnit_sq,cycleWordsLabelZero,ite_eq_left rfl]
  have embed : (2:ComplexScalar R)^n=ofReal ((2:R)^n) := (PhysicalPairedReduction.realEmbeddingPow (2:R) n).symm
  have inv := SectorDefectAccounting.dimensionInverse half unit n
  rw [embed]
  change (ofReal (edgeWeight f s r u * edgeWeight f s r v) * quarticPhase (imaginaryUnit (R:=R)) w).re =
    edgeWeight f s r u*(half^n*(ofReal ((2:R)^n)*quarticPhase imaginaryUnit w).re)*edgeWeight f s r v
  simp only [ComplexScalar.re_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal]; grind


private theorem sumProducts {α β : Type} (xs : List α) (ys : List β) (f : α × β → R) :
    sumOver (productIndices xs ys) f=sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro x
  simp [sumOver,List.map_map,Function.comp_def]

private theorem zeroCompanion (n : Nat) : anti (unitWord n) (companion (unitWord n))=false := by rw [antiSymm,antiZero]

private theorem nestedEdges {n : Nat} (F : EdgeIndex n → R) :
    sumOver (edgeList companion) F =
      sumOver (nonzeroWords n) (fun s =>
        let xs := perpendicularWords s (companion s)
        sumOver xs (fun u => sumOver xs (fun v => F (s,u,v)))) := by
  unfold edgeList nonzeroWords; simp only [filteredSum,sumProducts]
  apply sumOverCongr; intro s
  by_cases nonzero : s≠unitWord n
  · have sr := AntiPairIncidence.companionAntiOfNe s nonzero
    simp only [decide_eq_true_eq,ite_eq_left nonzero,perpendicularWords,filteredSum]
    apply sumOverCongr; intro u
    cases pu : perpendicular s (companion s) u
    · simp only [Bool.false_eq_true,ite_false]; apply zeroSum; intro v _
      simp [present,sr,pu]
    · simp only [ite_true]; apply sumOverCongr; intro v; simp [present,sr,pu]
  · have eq := Classical.not_not.mp nonzero; subst s
    simp only [decide_eq_true_eq,ite_eq_right (not_not_intro rfl)]
    apply zeroSum; intro u _; apply zeroSum; intro v _; simp [present,zeroCompanion]

/-- Actual physical plane-to-edge incidence identity with one representative
of each anticommuting edge and both orders of the two parallel edges. -/
theorem physicalPlaneEdgeSum (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1) {n : Nat} (f : Word n → R) :
    4*(sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey))
      (planeTerm imaginaryUnit (fun p => ofReal (f p)))).re =
    sumOver (nonzeroWords n) (fun s =>
      let r := companion s
      let xs := perpendicularWords s r
      sumOver xs (fun u => sumOver xs (fun v => edgeWeight f s r u*physicalEdgeMatrix half s r u v*edgeWeight f s r v))) := by
  let coeff (p : Word n) := ofReal (f p)
  have inv : (24:ComplexScalar R)*ofReal inv24=1 := by
    change ofReal (24:R)*ofReal inv24=_
    apply ComplexScalar.ext <;> simp <;> grind
  have exactSum := edgeWeightedSum companion AntiPairIncidence.companionAntiOfNe imaginaryUnit ComplexScalar.imaginaryUnit_sq
    (ofReal inv24) inv coeff
  have summed := congrArg ComplexScalar.re exactSum
  have weighted (e : EdgeIndex n) (he : e∈edgeList companion) :
      (if WedgeDistinct (encode companion e) then planeTerm imaginaryUnit coeff (encode companion e) else 0).re=
        edgeWeight f e.1 (companion e.1) e.2.1*physicalEdgeMatrix half e.1 (companion e.1) e.2.1 e.2.2*
          edgeWeight f e.1 (companion e.1) e.2.2 := by
    have m := (edgeMember companion e).mp he
    obtain ⟨h,hv⟩ := Bool.and_eq_true_iff.mp m
    obtain ⟨sr,hu⟩ := Bool.and_eq_true_iff.mp h
    exact physicalEdgeMonomial half unit f _ _ _ _ sr hu hv
  rw [complexRealSum, sumCongrMem _ _ _ weighted,nestedEdges] at summed
  simp only [ComplexScalar.re_mul,show (4:ComplexScalar R).re=4 from rfl,
    show (4:ComplexScalar R).im=0 from rfl] at summed
  change 4*(sumOver _ (planeTerm imaginaryUnit coeff)).re=_
  grind

end Real

end RankSeven.AntiPlaneIncidence

#print axioms RankSeven.AntiPlaneIncidence.canonicalPresentations
#print axioms RankSeven.AntiPlaneIncidence.chartPerm
#print axioms RankSeven.AntiPlaneIncidence.edgeWeightedSum
#print axioms RankSeven.AntiPlaneIncidence.physicalPlaneEdgeSum
