import Rank7PhysicalCompressionEffect
import Rank7FrameExteriorSector
import Rank7WedgeSquareIntertwiner

/-! The physical one-hole resolution in arbitrary binary dimension.
Triple coordinates here are ordered tensor coordinates, so coincident
or reordered sites are included in the signed kernel formula. -/
namespace RankSeven.PhysicalCutCapacities
open Lean.Grind Pauli GenericExteriorKernel ExteriorPauliBase HyperplaneIncidence
open PhysicalWedges (mapFourSites mapFourPosition)
open FourCopySectors (Perm)
abbrev Triple (α : Type) := (α × α) × α
def extend {α : Type} (u : Triple α) (t : α) : Four α := (u.1,(u.2,t))
def head {α : Type} (u : Four α) : Triple α := (u.1,u.2.1)
def mapTriple {α β : Type} (f : α → β) (u : Triple α) : Triple β := ((f u.1.1,f u.1.2),f u.2)
def permute {α : Type} (u : Triple α) (p : Perm) := head (reorder (extend u u.2) p)
def complete {n : Nat} (x : Triple (Basis n)) : Basis n :=
  xorBasis n (xorBasis n x.1.1 x.1.2) x.2
def triplePerms : List Perm := [((0,1),(2,3)),((0,2),(1,3)),((1,0),(2,3)),
  ((1,2),(0,3)),((2,0),(1,3)),((2,1),(0,3))]
private def kleinFour : List Perm := [((0,1),(2,3)),((1,0),(3,2)),((2,3),(0,1)),((3,2),(1,0))]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
local instance {C : Type} [CommRing C] : IntCast C := Ring.intCast

private theorem cosets : permutations.Perm (triplePerms.flatMap (fun p => kleinFour.map (reorder p))) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1200000 in
private theorem bitTable : triplePerms.all (fun p => kleinFour.all (fun k =>
    decide (oddPermutation (reorder p k)=oddPermutation p) &&
    decide (∀ a b c a' b' c' t : Bool,
      allowedBit (extend ((a,b),c) t) (reorder (extend ((a',b'),c') t) (reorder p k))=true ↔
      t=((a ^^ b) ^^ c) ∧ ((a,b),c)=permute ((a',b'),c') p)))=true := by decide

private theorem mapReorder {α β : Type} (f : α → β) (x : Four α) (p : Perm) :
    mapFourSites f (reorder x p)=reorder (mapFourSites f x) p := by
  apply PhysicalWedges.fourExt; intro j
  rw [mapFourPosition,position_reorder,position_reorder,mapFourPosition]

private theorem permuteMap {α β : Type} (f : α → β) (u : Triple α) (p : Perm) :
    mapTriple f (permute u p)=permute (mapTriple f u) p := by
  exact congrArg head (mapReorder f (extend u u.2) p)

private theorem tripleSplit {α β : Type} (x y : Triple (α × β)) :
    (mapTriple Prod.fst x=mapTriple Prod.fst y ∧ mapTriple Prod.snd x=mapTriple Prod.snd y) ↔ x=y := by
  rcases x with ⟨⟨⟨a,a'⟩,⟨b,b'⟩⟩,c,c'⟩
  rcases y with ⟨⟨⟨d,d'⟩,⟨e,e'⟩⟩,f,f'⟩
  simp only [mapTriple,Prod.mk.injEq]; grind only

private theorem sharedBitLift {n : Nat} (a b : Triple (Basis n)) (t : Basis n)
    (p k : Perm) (hp : p∈triplePerms) (hk : k∈kleinFour) :
    allowedTwirlEntry n (extend a t) (reorder (extend b t) (reorder p k))=true ↔
      t=complete a ∧ a=permute b p := by
  have e := (List.all_eq_true.mp (List.all_eq_true.mp bitTable p hp) k hk)
  have bit := _root_.of_decide_eq_true (Bool.and_eq_true_iff.mp e).2
  induction n with
  | zero =>
    rcases a with ⟨⟨⟨⟩,⟨⟩⟩,⟨⟩⟩; rcases b with ⟨⟨⟨⟩,⟨⟩⟩,⟨⟩⟩; cases t
    simp only [allowedTwirlEntry,true_iff]; refine ⟨rfl,?_⟩
    change (((),()),()) = (permute (((),()),()) p : (Unit × Unit) × Unit)
    rcases permute (((),()),()) p with ⟨⟨⟨⟩,⟨⟩⟩,⟨⟩⟩; rfl
  | succ n ih =>
    rcases t with ⟨t0,t1⟩
    change Triple (Bool × Basis n) at a b
    let a0 := mapTriple Prod.fst a
    let a1 := mapTriple Prod.snd a
    let b0 := mapTriple Prod.fst b
    let b1 := mapTriple Prod.snd b
    change (allowedBit (extend a0 t0) (mapFourSites Prod.fst (reorder (extend b (t0,t1)) (reorder p k))) &&
      allowedTwirlEntry n (extend a1 t1) (mapFourSites Prod.snd (reorder (extend b (t0,t1)) (reorder p k))))=true ↔ _
    rw [mapReorder,mapReorder,Bool.and_eq_true_iff]
    change (allowedBit (extend a0 t0) (reorder (extend b0 t0) (reorder p k))=true ∧
      allowedTwirlEntry n (extend a1 t1) (reorder (extend b1 t1) (reorder p k))=true) ↔
        (t0,t1)=((a0.1.1 ^^ a0.1.2 ^^ a0.2),complete a1) ∧ a=permute b p
    refine (and_congr (bit a0.1.1 a0.1.2 a0.2 b0.1.1 b0.1.2 b0.2 t0) (ih a1 b1 t1)).trans ?_
    rw [←tripleSplit a (permute b p),permuteMap,permuteMap]
    change ((_ ∧ a0=permute b0 p) ∧ (_ ∧ a1=permute b1 p)) ↔ ((t0,t1)=(_,_) ∧ a0=permute b0 p ∧ a1=permute b1 p)
    simp only [Prod.mk.injEq]; grind only

private theorem sumPerm {C α : Type} [CommRing C] {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

def tripleAlt {C α : Type} [CommRing C] [DecidableEq α] (a b : Triple α) : C :=
  sumOver triplePerms (fun p => if a=permute b p then signed (oddPermutation p) 1 else 0)

/-- The physical fourth-site coincidence kernel factors into a Steiner
completion constraint and the signed three-slot antisymmetrizer. -/
theorem sharedSiteKernel {C : Type} [CommRing C] {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1)
    (a b : Triple (Basis n)) (t : Basis n) :
    exteriorKernel i h (extend a t) (extend b t) =
      if t=complete a then 4*h^n*tripleAlt a b else 0 := by
  rw [kernel_as_signed_translations i h hi hh,sumPerm cosets,sumOverFlatMap]
  let val (p : Perm) : C := if t=complete a ∧ a=permute b p then signed (oddPermutation p) (h^n) else 0
  have part (p : Perm) (hp : p∈triplePerms) :
      sumOver (kleinFour.map (reorder p)) (fun q =>
        if allowedTwirlEntry n (extend a t) (reorder (extend b t) q) then signed (oddPermutation q) (h^n) else 0) =
        4*val p := by
    change sumOver kleinFour (fun k => if allowedTwirlEntry n (extend a t) (reorder (extend b t) (reorder p k))
      then signed (oddPermutation (reorder p k)) (h^n) else 0)=_
    have each (k : Perm) (hk : k∈kleinFour) :
        (if allowedTwirlEntry n (extend a t) (reorder (extend b t) (reorder p k)) then
          signed (oddPermutation (reorder p k)) (h^n) else 0)=val p := by
      have b' := List.all_eq_true.mp (List.all_eq_true.mp bitTable p hp) k hk
      have sg := _root_.of_decide_eq_true (Bool.and_eq_true_iff.mp b').1
      unfold val; rw [sg]; simp only [sharedBitLift a b t p k hp hk]
    rw [show (sumOver kleinFour (fun k => if allowedTwirlEntry n (extend a t) (reorder (extend b t) (reorder p k))
      then signed (oddPermutation (reorder p k)) (h^n) else 0))=sumOver kleinFour (fun _ => val p) from
      congrArg List.sum (List.map_congr_left each)]
    simp only [kleinFour,sumOver,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil]; grind only
  rw [show sumOver triplePerms (fun p => sumOver (kleinFour.map (reorder p)) (fun q =>
      if allowedTwirlEntry n (extend a t) (reorder (extend b t) q) then signed (oddPermutation q) (h^n) else 0)) =
      sumOver triplePerms (fun p => 4*val p) from congrArg List.sum (List.map_congr_left part)]
  by_cases eq : t=complete a
  · rw [ite_eq_left eq,tripleAlt,sumOverMulLeft]; apply sumOverCongr; intro p
    cases sg : oddPermutation p <;> by_cases same : a=permute b p <;> simp [signed,val,eq,same,sg] <;> grind only
  · rw [ite_eq_right eq]; unfold val; simp [eq,triplePerms,sumOver] <;> grind only

/-- Exact one-hole marginal, including every off-diagonal ordered triple. -/
theorem oneHoleResolution {C : Type} [CommRing C] {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1)
    (a b : Triple (Basis n)) :
    sumOver (qubitIndices n) (fun t => exteriorKernel i h (extend a t) (extend b t)) =
      4*h^n*tripleAlt a b := by
  simp only [sharedSiteKernel i h hi hh]
  refine (sumOverCongr (qubitIndices n) (g:=fun t => if complete a=t then 4*h^n*tripleAlt a b else 0)
    (fun t => ?_)).trans (ExteriorPauliBase.sumOnIndex (qubitIndices n) (complete a) (fun _ => 4*h^n*tripleAlt a b)
    (HyperplaneIncidence.normalsNodup n) (qubitIndicesComplete _))
  by_cases eq : t=complete a <;> simp [eq,Ne.symm]

section Frame
open ComplexScalar
open PhysicalPairedReduction (dagger)
variable {R : Type} [CommRing R]

private theorem sumPairs {C α β : Type} [CommRing C] (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]
  apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def triples {α : Type} (xs : List α) := productIndices (productIndices xs xs) xs
def tensorThree {α β C : Type} [CommRing C] (A : α → β → C) (u : Triple α) (v : Triple β) :=
  (A u.1.1 v.1.1*A u.1.2 v.1.2)*A u.2 v.2

private theorem mapPermThree {α β C : Type} [CommRing C] (A : α → β → C)
    (x : Triple α) (v : Triple β) (p : Perm) (hp : p∈triplePerms) :
    tensorThree A (permute x p) v =
      tensorThree A x (permute v (FourCopySectors.inverse p)) := by
  simp [triplePerms] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [tensorThree,permute,head,extend,reorder,position,FourCopySectors.inverse] <;> grind only

private theorem tripleTensorGram {α β : Type} [DecidableEq β] (xs : List α)
    (A : α → β → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0) (u v : Triple β) :
    sumOver (triples xs) (fun x => star (tensorThree A x u)*tensorThree A x v) =
      if u=v then 1 else 0 := by
  let h (i j : β) (x : α) := star (A x i)*A x j
  have e := factorProductSum (productIndices xs xs) xs
    (fun p : α × α => h u.1.1 v.1.1 p.1*h u.1.2 v.1.2 p.2) (h u.2 v.2)
  rw [factorProductSum] at e
  refine (sumOverCongr (triples xs) (g:=fun x => (h _ _ x.1.1*h _ _ x.1.2)*h _ _ x.2) (fun x => ?_)).trans (e.trans ?_)
  · unfold h tensorThree; simp only [star_mul]; grind only
  · unfold h; simp only [orth]
    rcases u with ⟨⟨a,b⟩,c⟩; rcases v with ⟨⟨d,e'⟩,f'⟩
    by_cases ad : a=d <;> by_cases be : b=e' <;> by_cases cf : c=f' <;> simp [ad,be,cf] <;> grind only

private def dot {α : Type} (xs : List α) (f g : α → ComplexScalar R) : ComplexScalar R :=
  sumOver xs (fun x => star (f x)*g x)
private def mv {α β : Type} (xs : List β) (A : α → β → ComplexScalar R) (f : β → ComplexScalar R) (i : α) :=
  sumOver xs (fun j => A i j*f j)
private theorem adjointDot {α β : Type} (src : List β) (amb : List α)
    (A : α → β → ComplexScalar R) (z : β → ComplexScalar R) (v : α → ComplexScalar R) :
    dot src z (mv amb (dagger A) v)=dot amb (mv src A z) v := by
  unfold dot mv dagger
  simp only [sumOverMulLeft,ComplexExterior.starSumOver,star_mul,sumOverMulRight]
  rw [sumOverSwap]
  apply sumOverCongr; intro x; apply sumOverCongr; intro i
  change star (z i)*(star (A x i)*v x)=star (A x i)*star (z i)*v x; grind only

private theorem reSum {α : Type} (xs : List α) (u : α → ComplexScalar R) :
    (sumOver xs u).re=sumOver xs (fun i => (u i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (u i+sumOver xs u).re=(u i).re+_; rw [re_add,ih]; rfl

theorem frameBessel [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {α β : Type} [DecidableEq β] (src : List β) (amb : List α) (nd : src.Nodup) (full : ∀ i,i∈src)
    (A : α → β → ComplexScalar R)
    (orth : ∀ i j,sumOver amb (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (v : α → ComplexScalar R) :
    sumOver src (fun i => normSq (sumOver amb (fun t => star (A t i)*v t))) ≤ sumOver amb (fun t => normSq (v t)) := by
  let c := mv amb (dagger A) v
  let z := mv src A c
  have back (i : β) : mv amb (dagger A) z i=c i := by
    let f (j : β) (_ : Unit) := c j
    change matMul amb (dagger A) (matMul src A f) i ()=c i
    rw [←matMulAssoc]
    change sumOver src (fun j => (sumOver amb (fun x => star (A x i)*A x j))*c j)=_
    simp only [orth]
    refine (sumOverCongr src (g:=fun j => if i=j then c j else 0) (fun j => ?_)).trans
      (ExteriorPauliBase.sumOnIndex src i c nd (full i))
    by_cases eq : i=j <;> simp [eq] <;> grind only
  have qq : dot amb z z=dot src c c := by
    have e := adjointDot src amb A c z
    rw [show mv amb (dagger A) z=c from funext back] at e; exact e.symm
  have qv : dot amb z v=dot src c c := (adjointDot src amb A c v).symm
  have norm (xs : List α) (f : α → ComplexScalar R) : (dot xs f f).re=sumOver xs (fun i => normSq (f i)) := by
    unfold dot; rw [reSum]; simp only [re_star_mul_self]
  have normc : (dot src c c).re=sumOver src (fun i => normSq (c i)) := by
    unfold dot; rw [reSum]; simp only [re_star_mul_self]
  have diff (i : α) : normSq (v i - z i)=normSq (v i)+normSq (z i)-2*(star (z i)*v i).re := by
    simp only [normSq,re_sub,im_sub,re_mul,re_star,im_star]; grind only
  have positive := Compression.sumOverNonnegative amb (fun i => normSq (v i-z i)) (fun _ _ => normSq_nonnegative _)
  rw [sumOverCongr _ diff,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←reSum] at positive
  change 0 ≤ sumOver amb (fun i => normSq (v i)) + sumOver amb (fun i => normSq (z i)) - 2*(dot amb z v).re at positive
  rw [←norm amb z,qq,qv,normc] at positive
  change sumOver src (fun i => normSq (c i)) ≤ _
  grind only

def distinct {α : Type} (u : Triple α) : Prop := u.1.1≠u.1.2 ∧ u.1.1≠u.2 ∧ u.1.2≠u.2

private theorem triplesNodup {α : Type} (xs : List α) (nd : xs.Nodup) : (triples xs).Nodup :=
  HyperplaneInduction.pairsNodup _ _ (HyperplaneInduction.pairsNodup _ _ nd nd) nd
private theorem triplesFull {α : Type} (xs : List α) (full : ∀ a,a∈xs) (u : Triple α) : u∈triples xs := by
  change u∈(productIndices xs xs).flatMap (fun a => xs.map (fun b => (a,b)))
  exact List.mem_flatMap.mpr ⟨u.1,HyperplaneInduction.pairMember (full _) (full _),List.mem_map.mpr ⟨u.2,full _,rfl⟩⟩

private def quad {α : Type} (xs : List α) (u : α → ComplexScalar R) (K : α → α → ComplexScalar R) :=
  sumOver xs (fun a => sumOver xs (fun b => star (u a)*K a b*u b))

private theorem threeGram {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (nd : xs.Nodup) (full : ∀ x,x∈xs)
    (A : α → β → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (u : Triple β) (du : distinct u) :
    quad (triples xs) (fun x => tensorThree A x u) tripleAlt=1 := by
  let ts := triples xs
  let z (x : Triple α) := tensorThree A x u
  let c (p : Perm) : ComplexScalar R := signed (oddPermutation p) 1
  let δ (a b : Triple α) (p : Perm) : ComplexScalar R := if a=permute b p then c p else 0
  change sumOver ts (fun a => sumOver ts (fun b => star (z a)*(sumOver triplePerms (δ a b))*z b))=_
  simp only [sumOverMulLeft,sumOverMulRight]
  rw [sumOverSwap ts ts]
  conv => lhs; arg 2; intro b; rw [sumOverSwap ts triplePerms]
  rw [sumOverSwap ts triplePerms]
  have select (p : Perm) (b : Triple α) :
      sumOver ts (fun a => star (z a)*δ a b p*z b)=c p*(star (z (permute b p))*z b) := by
    refine (sumOverCongr ts (g:=fun a => if permute b p=a then c p*(star (z a)*z b) else 0) (fun a => ?_)).trans
      (ExteriorPauliBase.sumOnIndex ts _ _ (triplesNodup xs nd) (triplesFull xs full _))
    by_cases eq : a=permute b p <;> simp [δ,eq,Ne.symm] <;> grind only
  simp only [select,←sumOverMulLeft]
  have rows (p : Perm) (hp : p∈triplePerms) :
      sumOver ts (fun b => star (z (permute b p))*z b)=(if permute u (FourCopySectors.inverse p)=u then 1 else 0) := by
    unfold z; simp only [mapPermThree A _ u p hp]; exact tripleTensorGram xs A orth _ u
  refine (congrArg List.sum (List.map_congr_left (g:=fun p => c p*
    (if permute u (FourCopySectors.inverse p)=u then 1 else 0)) (fun p hp => congrArg (fun w => c p*w) (rows p hp)))).trans ?_
  rcases u with ⟨⟨a,b⟩,d⟩
  obtain ⟨ab,ad,bd⟩ := du
  change a≠b at ab; change a≠d at ad; change b≠d at bd
  simp [triplePerms,permute,FourCopySectors.inverse,extend,head,reorder,position,c,oddPermutation,signed,ab,ad,bd,Ne.symm]
    <;> grind only

private def coef {α β : Type} (xs : List α) (z : α → ComplexScalar R) (F : α → β → ComplexScalar R) (p : β) :=
  sumOver xs (fun a => star (z a)*F a p)

private theorem pullGram {α β : Type} (xs : List α) (os : List β)
    (z : α → ComplexScalar R) (F : α → β → ComplexScalar R) (K : α → α → ComplexScalar R)
    (rel : ∀ a b,2*sumOver os (fun p => F a p*star (F b p))=3*K a b) :
    2*sumOver os (fun p => normSq (coef xs z F p))=3*(quad xs z K).re := by
  have e : 2*sumOver os (fun p => coef xs z F p*star (coef xs z F p))=3*quad xs z K := by
    unfold coef quad
    simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
    conv => lhs; arg 2; intro p; rw [sumOverSwap xs xs]
    rw [sumOverSwap os xs]
    apply sumOverCongr; intro a
    rw [sumOverSwap os xs]; apply sumOverCongr; intro b
    have g := congrArg (fun w => star (z a)*w*z b) (rel a b)
    change star (z a)*(2*sumOver os _)*z b=_ at g
    rw [sumOverMulLeft,sumOverMulLeft,sumOverMulRight] at g
    refine (sumOverCongr os (g:=fun p => star (z a)*(2*(F a p*star (F b p)))*z b) (fun p => ?_)).trans ?_
    · grind only
    · rw [g]; grind only
  have re := congrArg ComplexScalar.re e
  change (ofReal (2:R)*_).re=(ofReal (3:R)*_).re at re
  have er (d : R) (u : ComplexScalar R) : (ofReal d*u).re=d*u.re := by simp [re_mul,ofReal]; grind only
  rw [er,er,reSum] at re
  have diag (p : β) : (coef xs z F p*star (coef xs z F p)).re=normSq (coef xs z F p) := by
    rw [CommSemiring.mul_comm,re_star_mul_self]
  rw [sumOverCongr _ diag] at re
  grind only

def leg {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (u : Triple (Fin 7))
    (t : Basis n) (p : Word n) :=
  coef (triples (qubitIndices n)) (fun x => tensorThree A x u)
    (fun x p => WedgeSquareIntertwiner.wedgeSquareColumn half p (extend x t)) p

/-- Summing the one-hole marginal for an arbitrary physical triple of
orthonormal columns gives exactly its spectral mass in the odd Pauli frame. -/
theorem oneHoleFrameMass (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (u : Triple (Fin 7)) (du : distinct u) :
    2*sumOver (MixedDefect.oddWords n) (fun p => sumOver (qubitIndices n) (fun t => normSq (leg half A u t p))) =
      3*(4*half^n) := by
  let xs := qubitIndices n
  let ts := triples xs
  let os := MixedDefect.oddWords n
  let z (a : Triple (Basis n)) := tensorThree A a u
  let T := exteriorKernel (n:=n) (imaginaryUnit (R:=R)) (ofReal half)
  let q := 4*half^n
  have h2 : 2*ofReal half=(1:ComplexScalar R) := by
    change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  have occ (t : Basis n) : 2*sumOver os (fun p => normSq (leg half A u t p)) =
      3*(quad ts z (fun a b => T (extend a t) (extend b t))).re :=
    pullGram ts os z _ _ (fun a b => WedgeSquareIntertwiner.physicalWedgeSquareGram half unit _ _)
  have total : sumOver xs (fun t => quad ts z (fun a b => T (extend a t) (extend b t)))=ofReal q := by
    unfold quad
    rw [sumOverSwap xs ts]
    conv => lhs; arg 2; intro a; rw [sumOverSwap xs ts]
    simp only [←sumOverMulRight,←sumOverMulLeft]
    have marginal (a b : Triple (Basis n)) : sumOver xs (fun t => T (extend a t) (extend b t))=
        4*ofReal half^n*tripleAlt a b := oneHoleResolution imaginaryUnit (ofReal half) imaginaryUnit_fourth h2 a b
    simp only [marginal]
    have factor (a b : Triple (Basis n)) :
        star (z a)*(4*ofReal half^n*tripleAlt a b)*z b=(4*ofReal half^n)*(star (z a)*tripleAlt a b*z b) := by grind only
    simp only [factor,←sumOverMulLeft]
    have gram := threeGram xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) A orth u du
    change (4*ofReal half^n)*quad ts z tripleAlt=ofReal q
    rw [gram,Semiring.mul_one,←PhysicalPairedReduction.realEmbeddingPow]
    change ofReal (4:R)*ofReal (half^n)=ofReal q; apply ComplexScalar.ext <;> simp [q] <;> grind only
  rw [sumOverSwap,sumOverMulLeft,sumOverCongr xs occ,←sumOverMulLeft,←reSum,total]; rfl

def columnCoef {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (u : Four (Fin 7)) (p : Word n) :=
  coef (fourIndices (qubitIndices n)) (fun x => tensorFour A x u)
    (fun x p => WedgeSquareIntertwiner.wedgeSquareColumn half p x) p

theorem coefficientFromLeg {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (u : Triple (Fin 7)) (j : Fin 7) (p : Word n) :
    columnCoef half A (extend u j) p=sumOver (qubitIndices n) (fun t => star (A t j)*leg half A u t p) := by
  let xs := qubitIndices n
  let ps := productIndices xs xs
  let F (x : Four (Basis n)) := WedgeSquareIntertwiner.wedgeSquareColumn half p x
  change sumOver (productIndices ps ps) (fun x => star (tensorFour A x (extend u j))*F x)=
    sumOver xs (fun t => star (A t j)*sumOver (productIndices ps xs) (fun x => star (tensorThree A x u)*F (extend x t)))
  rw [sumPairs]; simp only [sumPairs,sumOverMulLeft]
  rw [sumOverSwap xs ps]
  apply sumOverCongr; intro ab; rw [sumOverSwap xs xs]
  change sumOver (productIndices xs xs) _ = _; rw [sumPairs]
  apply sumOverCongr; intro c; apply sumOverCongr; intro t
  simp only [tensorFour,tensor,extend,tensorThree,star_mul]; grind only

def rowMass {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (v : Four (Fin 7)) :=
  sumOver (MixedDefect.oddWords n) (fun p => normSq (columnCoef half A v p))

private theorem sumLe {α : Type} [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (xs : List α) (f g : α → R) (h : ∀ i,f i≤g i) : sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons a xs ih => change f a+sumOver xs f≤g a+sumOver xs g; have eq := h a; grind only

theorem rowMassCapacity [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (unit : 2*half=1) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (u : Triple (Fin 7)) (du : distinct u) :
    2*sumOver (List.finRange 7) (fun j => rowMass half A (extend u j)) ≤ 3*(4*half^n) := by
  rw [←oneHoleFrameMass half unit A orth u du]; unfold rowMass
  rw [sumOverSwap]; simp only [coefficientFromLeg]
  have bound (p : Word n) := frameBessel (List.finRange 7) (qubitIndices n) (List.nodup_finRange 7)
    (fun j => List.mem_finRange j) A orth (fun t => leg half A u t p)
  have e := sumLe (MixedDefect.oddWords n) _ _ bound
  grind only

open FourCopySectors (rawBlock act coefficient tensorEquivariant blockLeft blockRight)
open FrameExteriorSector (sourceTuple effectEntry)
private def J {n : Nat} := @unnormalizedTwirl (ComplexScalar R) _ n imaginaryUnit

private theorem twirlEqv (n : Nat) : FourCopySectors.Equivariant (J (R:=R) (n:=n)) := by
  intro p hp x y; unfold J unnormalizedTwirl; apply sumOverCongr; intro w
  exact tensorEquivariant _ p hp x y

private theorem kernelAlt (h : ComplexScalar R) {n : Nat} :
    exteriorKernel imaginaryUnit h (n:=n)= RectangularPairedReduction.scaleMatrix (h^(n+n)) (rawBlock .antisymmetric J) := by
  funext u v
  rw [show RectangularPairedReduction.scaleMatrix (h^(n+n)) (rawBlock .antisymmetric J) u v=
    h^(n+n)*act (coefficient .antisymmetric) (J u) v from congrArg (fun z => h^(n+n)*z)
      (AlternatingTrace.alternatingRight _ (twirlEqv n) u v)]
  unfold exteriorKernel wordMinor act J unnormalizedTwirl
  congr 1; rw [sumOverSwap]; apply sumOverCongr; intro p
  rw [sumOverMulLeft]; apply sumOverCongr; intro w
  unfold signed coefficient; cases oddPermutation p <;> simp <;> grind only

private theorem scaledBlock {α : Type} (h : ComplexScalar R) (T : Four α → Four α → ComplexScalar R) :
    rawBlock .antisymmetric (RectangularPairedReduction.scaleMatrix h T)=
      RectangularPairedReduction.scaleMatrix h (rawBlock .antisymmetric T) := by
  funext u v; unfold rawBlock act RectangularPairedReduction.scaleMatrix
  rw [sumOverMulLeft]; apply sumOverCongr; intro p; grind only

private theorem pullToQuad {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (v : Four (Fin 7)) :
    rawBlock .antisymmetric (FrameExteriorSector.frameTwirl half A) v v =
      quad (fourIndices (qubitIndices n)) (fun x => tensorFour A x v) (exteriorKernel imaginaryUnit (ofReal half)) := by
  let xs := fourIndices (qubitIndices n)
  let U := tensorFour A
  let V := transpose (tensorFour (fun a i => star (A a i)))
  let h := (ofReal half)^(n+n)
  change rawBlock .antisymmetric (RectangularPairedReduction.scaleMatrix h (matMul xs (matMul xs V J) U)) v v=_
  have eqv : FourCopySectors.Equivariant V := fun p hp x y => tensorEquivariant _ p hp y x
  have closed : FourCopySectors.PermutedList xs := FourCopySectors.fullPermuted _ (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  rw [scaledBlock,blockLeft,blockRight xs closed _ V J eqv,kernelAlt,matMulAssoc]
  change h*sumOver xs (fun x => V v x*sumOver xs (fun y => rawBlock .antisymmetric J x y*U y v))=
    sumOver xs (fun x => sumOver xs (fun y => star (U x v)*(h*rawBlock .antisymmetric J x y)*U y v))
  simp only [sumOverMulLeft]
  apply sumOverCongr; intro x; apply sumOverCongr; intro y
  simp only [V,U,tensorFour,tensor,transpose,star_mul]; grind only

theorem rowMass_eq_raw (half : R) (unit : 2*half=1) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (v : Four (Fin 7)) :
    2*rowMass half A v=3*(rawBlock .antisymmetric (FrameExteriorSector.frameTwirl half A) v v).re := by
  rw [pullToQuad]
  exact pullGram _ _ _ _ _ (fun a b => WedgeSquareIntertwiner.physicalWedgeSquareGram half unit a b)

private theorem frameEquiv {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :
    FourCopySectors.Equivariant (FrameExteriorSector.frameTwirl half A) := by
  intro p hp x y; apply congrArg (fun z => (ofReal half)^(n+n)*z)
  exact (FourCopySectors.frameStructure A).1 p hp x y

theorem massReorder {n : Nat} (half : R) (unit : 2*half=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (v : Four (Fin 7)) (p : Perm) (hp : p∈permutations) :
    2*rowMass half A (reorder v p)=2*rowMass half A v := by
  rw [rowMass_eq_raw half unit,rowMass_eq_raw half unit]
  let T := FrameExteriorSector.frameTwirl half A
  let s : ComplexScalar R := Int.cast (coefficient .antisymmetric p)
  have h := AlternatingTrace.alternatingRow (fun z => T z (reorder v p)) p hp v
  change rawBlock .antisymmetric T (reorder v p) (reorder v p)=s*rawBlock .antisymmetric T v (reorder v p) at h
  rw [AlternatingTrace.alternatingColumn T (frameEquiv half A) v v p hp] at h
  have sq : s*s=1 := by unfold s coefficient; cases oddPermutation p <;> simp <;> grind only
  change _=s*(s*_) at h
  rw [←Semiring.mul_assoc,sq,Semiring.one_mul] at h
  exact congrArg (fun z : ComplexScalar R => 3*z.re) h

theorem coordinateMass [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (w : ExteriorCuts.Wedge7) :
    2*rowMass half A (sourceTuple w) =
      3*(4*half^(k+3))*(PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w := by
  rw [rowMass_eq_raw half unit, AlternatingTrace.alternatingSortedEntry _ (frameEquiv half A),
    FrameExteriorSector.sector_eq_weight_mul_physicalEntry half unit k A]
  change 3*(ofReal (4*half^(k+3))*effectEntry half unit k A w w).re=_
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,effectEntry]; grind only

open ExteriorCuts (Wedge7 wedges)
def occupied (w : Wedge7) (i : Fin 7) := w.i==i || w.j==i || w.k==i || w.m==i
def covers (u : Triple (Fin 7)) (w : Wedge7) := occupied w u.1.1 && occupied w u.1.2 && occupied w u.2
def outside (u : Triple (Fin 7)) (j : Fin 7) := j != u.1.1 && j != u.1.2 && j != u.2
def extra (u : Triple (Fin 7)) (w : Wedge7) : Fin 7 :=
  if outside u w.i then w.i else if outside u w.j then w.j else if outside u w.k then w.k else w.m
private def insertPermutation (u : Triple (Fin 7)) (j : Fin 7) : Perm :=
  if j<u.1.1 then ((3,0),(1,2)) else if j<u.1.2 then ((0,3),(1,2)) else if j<u.2 then ((0,1),(3,2)) else ((0,1),(2,3))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3500000 in
private theorem incidence : ∀ a b c : Fin 7, a<b → b<c →
    let u : Triple (Fin 7) := ((a,b),c)
    ((wedges.filter (covers u)).map (extra u)).Perm ((List.finRange 7).filter (outside u)) ∧
      (wedges.filter (covers u)).all (fun w => decide (insertPermutation u (extra u w)∈permutations) &&
        decide (reorder (extend u (extra u w)) (insertPermutation u (extra u w))=sourceTuple w))=true := by decide

private theorem filtered {α : Type} (xs : List α) (p : α → Bool) (f : α → R) :
    sumOver (xs.filter p) f=sumOver xs (fun a => if p a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons]; cases h : p a <;> simp [h,sumOver] at ih ⊢ <;> grind only

/-- Every one of the 35 four-set inequalities on the arbitrary physical
frame. The four counted wedge labels are exactly the labels containing
the chosen triple, as in the packing verifier. -/
theorem physicalTripleCapacity [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (a b c : Fin 7) (ab : a<b) (bc : b<c) :
    sumOver wedges (fun w => if covers ((a,b),c) w then (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w else 0) ≤ 1 := by
  let u : Triple (Fin 7) := ((a,b),c)
  let ws := wedges.filter (covers u)
  let f (w : Wedge7) := (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w
  let q := 4*half^(k+3)
  let m (i : Fin 7) := 2*rowMass half A (extend u i)
  have du : distinct u := by change a≠b ∧ a≠c ∧ b≠c; omega
  have inc := incidence a b c ab bc
  have each (w : Wedge7) (hw : w∈ws) : 3*q*f w=m (extra u w) := by
    have e := Bool.and_eq_true_iff.mp (List.all_eq_true.mp inc.2 w hw)
    have z := massReorder half unit A (extend u (extra u w)) _ (_root_.of_decide_eq_true e.1)
    rw [_root_.of_decide_eq_true e.2,coordinateMass half unit k A] at z; exact z
  have eq : (3*q)*sumOver ws f=sumOver ((List.finRange 7).filter (outside u)) m := by
    rw [sumOverMulLeft]
    refine (congrArg List.sum (List.map_congr_left each)).trans ?_
    simpa only [sumOver,List.map_map,Function.comp_def] using (sumPerm inc.1 m)
  have pos (i : Fin 7) : 0≤m i := by
    have h := Compression.sumOverNonnegative (MixedDefect.oddWords (k+3)) (fun p => normSq (columnCoef half A (extend u i) p))
      (fun _ _ => normSq_nonnegative _)
    change 0≤2*_ ; unfold rowMass; grind only
  have le : sumOver ((List.finRange 7).filter (outside u)) m≤sumOver (List.finRange 7) m := by
    rw [filtered]; apply sumLe; intro j; cases outside u j <;> simp <;> exact pos j
  have cap := rowMassCapacity half unit A orth u du
  rw [sumOverMulLeft] at cap
  change sumOver (List.finRange 7) m≤3*q at cap
  have bound := Std.le_trans le cap
  rw [←eq] at bound
  have hp : 0<half := by grind only
  have power (j : Nat) : 0<half^j := by
    induction j with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ j ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih hp
  have qp : 0<q := OrderedRing.mul_pos (by grind) (power _)
  have sp : 0<3*q := OrderedRing.mul_pos (by grind) qp
  change sumOver wedges (fun w => if covers u w then f w else 0)≤1
  rw [←filtered]; change sumOver ws f≤1
  by_cases h : sumOver ws f≤1
  · exact h
  · have bad := OrderedRing.mul_pos sp (show 0<sumOver ws f-1 by grind)
    grind only

end Frame
end RankSeven.PhysicalCutCapacities

#print axioms RankSeven.PhysicalCutCapacities.oneHoleResolution
#print axioms RankSeven.PhysicalCutCapacities.oneHoleFrameMass
#print axioms RankSeven.PhysicalCutCapacities.physicalTripleCapacity
