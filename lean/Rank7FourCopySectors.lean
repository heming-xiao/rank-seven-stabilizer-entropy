import Rank7GenericExteriorKernel
import Rank7ComplexScalar
import Rank7HyperplaneInduction
import Rank7RectangularPairedReduction

/-! The replica-permutation projectors on the four-copy stabilizer space.
Their integer coefficients are scaled by 24, so the finite group calculation
is independent of both the scalar field and the qubit dimension. -/
namespace RankSeven.FourCopySectors

open Lean.Grind Pauli ExteriorPauliBase GenericExteriorKernel

abbrev Perm := ExteriorPauliBase.Permutation

def ident : Perm := ((0,1),(2,3))
def transposition : Perm := ((1,0),(2,3))
def rotation : Perm := ((1,2),(0,3))

def inverse (p : Perm) : Perm :=
  let find (j : Fin 4) : Fin 4 := if p.1.1=j then 0 else if p.1.2=j then 1 else if p.2.1=j then 2 else 3
  ((find 0,find 1),(find 2,find 3))

def klein (p : Perm) : Bool :=
  p == ident || p == ((1,0),(3,2)) || p == ((2,3),(0,1)) || p == ((3,2),(1,0))

inductive Sector where
  | symmetric | antisymmetric | mixedEven | mixedOdd
  deriving DecidableEq, Repr

def sectors : List Sector := [.symmetric,.antisymmetric,.mixedEven,.mixedOdd]

/-- Half the coefficient of the central (2,2) character projector. -/
private def halfMixed (p : Perm) : Int :=
  if klein p then 2 else if oddPermutation p then 0 else -1

/-- 24 times the coefficients of the two one-dimensional central projections
and of the two orthogonal transposition lines in the standard sector. -/
def coefficient (s : Sector) (p : Perm) : Int :=
  match s with
  | .symmetric => 1
  | .antisymmetric => if oddPermutation p then -1 else 1
  | .mixedEven => halfMixed p + halfMixed (reorder p transposition)
  | .mixedOdd => halfMixed p - halfMixed (reorder p transposition)

def convolution (f g : Perm → Int) (t : Perm) : Int :=
  sumOver permutations (fun p => f p * g (reorder (inverse p) t))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private theorem coefficientTable : sectors.all (fun s =>
    permutations.all (fun p => coefficient s (inverse p) == coefficient s p) &&
    sectors.all (fun t => permutations.all (fun p =>
      convolution (coefficient s) (coefficient t) p == if s=t then 24*coefficient s p else 0))) = true := by
  decide

theorem memSector (s : Sector) : s∈sectors := by cases s <;> decide

theorem selfAdjointCoefficient (s : Sector) (p : Perm) (hp : p∈permutations) :
    coefficient s (inverse p) = coefficient s p :=
  beq_iff_eq.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp coefficientTable s (memSector s))).1 p hp)

theorem projectorProduct (s t : Sector) (p : Perm) (hp : p∈permutations) :
    convolution (coefficient s) (coefficient t) p =
      if s=t then 24*coefficient s p else 0 :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp coefficientTable s (memSector s))).2 t (memSector t)) p hp)

def conjugate (h p : Perm) : Perm := reorder (inverse h) (reorder p h)

/-- The central standard coefficient is the two-dimensional character times two. -/
def mixedCoefficient (p : Perm) : Int := coefficient .mixedEven p + coefficient .mixedOdd p

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem centralTable : permutations.all (fun p =>
    (coefficient .symmetric p + coefficient .antisymmetric p + mixedCoefficient p ==
      if klein p then 6 else 0) &&
    permutations.all (fun h =>
      coefficient .symmetric (conjugate h p) == coefficient .symmetric p &&
      coefficient .antisymmetric (conjugate h p) == coefficient .antisymmetric p &&
      mixedCoefficient (conjugate h p) == mixedCoefficient p) &&
    (sumOver permutations (fun h => coefficient .mixedEven (conjugate h p)) ==
     sumOver permutations (fun h => coefficient .mixedOdd (conjugate h p)))) = true := by decide

theorem centralCoefficients (p h : Perm) (hp : p∈permutations) (hh : h∈permutations) :
    coefficient .symmetric (conjugate h p) = coefficient .symmetric p ∧
    coefficient .antisymmetric (conjugate h p) = coefficient .antisymmetric p ∧
    mixedCoefficient (conjugate h p) = mixedCoefficient p := by
  have e := List.all_eq_true.mp centralTable p hp
  simp only [Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at e
  obtain ⟨⟨a,b⟩,c⟩ := e.1.2 h hh
  exact ⟨a,b,c⟩

theorem coefficientResolution (p : Perm) (hp : p∈permutations) :
    coefficient .symmetric p + coefficient .antisymmetric p + mixedCoefficient p =
      if klein p then 6 else 0 := by
  have e := List.all_eq_true.mp centralTable p hp
  simp only [Bool.and_eq_true,beq_iff_eq] at e
  exact e.1.1

theorem mixedMultiplicity (p : Perm) (hp : p∈permutations) :
    sumOver permutations (fun h => coefficient .mixedEven (conjugate h p)) =
    sumOver permutations (fun h => coefficient .mixedOdd (conjugate h p)) := by
  have e := List.all_eq_true.mp centralTable p hp
  simp only [Bool.and_eq_true,beq_iff_eq] at e
  exact e.2

private def mapFour {α β : Type} (f : α → β) (u : Four α) : Four β :=
  ((f u.1.1,f u.1.2),(f u.2.1,f u.2.2))

private theorem reorderMap {α β : Type} (f : α → β) (u : Four α) (p : Perm) :
    mapFour f (reorder u p) = reorder (mapFour f u) p := by
  have e (i : Fin 4) : position (mapFour f u) i = f (position u i) := by
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
    rcases h with rfl|rfl|rfl|rfl <;> rfl
  simp only [mapFour,reorder] at e ⊢
  simp only [e]

private theorem bitsLeft (p : Perm) (kp : klein p = true) (hp : p∈permutations)
    (u v : Four Bool) : allowedBit (reorder u p) v = allowedBit u v := by
  have h : permutations.all (fun p => !klein p ||
      decide (∀ a b c d e f g h : Bool, allowedBit (reorder ((a,b),(c,d)) p) ((e,f),(g,h)) =
        allowedBit ((a,b),(c,d)) ((e,f),(g,h)))) = true := by decide
  have q := List.all_eq_true.mp h p hp
  simp only [kp,Bool.not_true,Bool.false_or,decide_eq_true_eq] at q
  exact q _ _ _ _ _ _ _ _

/-- Each of the four Klein elements acts pointwise as the identity on the
range of the actual Pauli stabilizer projector, in every dimension. -/
theorem kleinTwirl (n : Nat) (p : Perm) (hp : p∈permutations) (kp : klein p=true)
    (u v : Four (Basis n)) :
    allowedTwirlEntry n (reorder u p) v = allowedTwirlEntry n u v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (allowedBit (mapFour Prod.fst (reorder u p)) (firstBits v) &&
      allowedTwirlEntry n (mapFour Prod.snd (reorder u p)) (remainingBits v)) = _
    have h₁ := reorderMap (α:=Bool × Basis n) Prod.fst u p
    have h₂ := reorderMap (α:=Bool × Basis n) Prod.snd u p
    have e₁ := (congrArg (fun x => allowedBit x (firstBits v)) h₁).trans
      (bitsLeft p kp hp (firstBits u) (firstBits v))
    have e₂ := (congrArg (fun x => allowedTwirlEntry n x (remainingBits v)) h₂).trans
      (ih (remainingBits u) (remainingBits v))
    exact (congrArg (fun x => x && allowedTwirlEntry n (mapFour Prod.snd (reorder u p)) (remainingBits v)) e₁).trans
      (congrArg (fun x => allowedBit (firstBits u) (firstBits v) && x) e₂)

theorem kleinPauliProjector {C : Type} [CommRing C] (n : Nat) (i half : C)
    (hi : i^4=1) (hh : 2*half=1) (p : Perm) (hp : p∈permutations) (kp : klein p=true)
    (u v : Four (Basis n)) :
    half^(n+n)*unnormalizedTwirl i (reorder u p) v = half^(n+n)*unnormalizedTwirl i u v := by
  rw [normalizedTwirlEntry i half hi hh, normalizedTwirlEntry i half hi hh,kleinTwirl n p hp kp]

section Algebra
variable {C α : Type} [CommRing C]
local instance : IntCast C := Ring.intCast

private theorem sumMem {T : Type} (xs : List T) {f g : T → C}
    (h : ∀ x∈xs, f x=g x) : sumOver xs f = sumOver xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem sumPerm {T : Type} {xs ys : List T} (h : xs.Perm ys) (f : T → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

private theorem sumCast {T : Type} (xs : List T) (f : T → Int) :
    Int.cast (R:=C) (sumOver xs f) = sumOver xs (fun x => Int.cast (R:=C) (f x)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons x xs ih =>
    change Int.cast (R:=C) (f x + sumOver xs f) = Int.cast (f x) + _
    rw [Ring.intCast_add,ih]; rfl

private theorem compReorder {T : Type} (u : Four T) (p q : Perm) :
    reorder (reorder u p) q = reorder u (reorder p q) := by
  change ((position (reorder u p) _,position (reorder u p) _),
    (position (reorder u p) _,position (reorder u p) _)) = _
  simp only [GenericExteriorKernel.position_reorder]; rfl

set_option maxRecDepth 10000 in
private theorem translateTable : permutations.all (fun p =>
    decide ((permutations.map (reorder (inverse p))).Perm permutations) &&
    permutations.all (fun q => reorder p (reorder (inverse p) q) == q) &&
    decide ((permutations.map (conjugate p)).Perm permutations) &&
    decide (inverse p∈permutations) && decide (reorder p (inverse p) = ident) &&
    decide (reorder (inverse p) p = ident)) = true := by decide

private theorem translations (p : Perm) (hp : p∈permutations) :
    (permutations.map (reorder (inverse p))).Perm permutations ∧
    (∀ q∈permutations, reorder p (reorder (inverse p) q) = q) ∧
    (permutations.map (conjugate p)).Perm permutations ∧ inverse p∈permutations ∧
    reorder p (inverse p)=ident ∧ reorder (inverse p) p=ident := by
  have h := List.all_eq_true.mp translateTable p hp
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1,h.1.1.1.1.2,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩

/-- A concrete weighted replica action on fourth-tensor coordinates. -/
def act (c : Perm → Int) (f : Four α → C) (u : Four α) : C :=
  sumOver permutations (fun p => Int.cast (c p) * f (reorder u p))

theorem actConvolution (c d : Perm → Int) (f : Four α → C) (u : Four α) :
    act c (act d f) u = act (convolution c d) f u := by
  unfold act
  have row (p : Perm) (hp : p∈permutations) :
      Int.cast (R:=C) (c p) * sumOver permutations (fun q => Int.cast (d q) * f (reorder (reorder u p) q)) =
      sumOver permutations (fun t => (Int.cast (R:=C) (c p*d (reorder (inverse p) t))) * f (reorder u t)) := by
    rw [sumOverMulLeft]
    let g q := Int.cast (R:=C) (c p) * (Int.cast (d q) * f (reorder u (reorder p q)))
    change sumOver permutations (fun q => _ * (_ * f (reorder (reorder u p) q))) = _
    simp only [compReorder]
    change sumOver permutations g = _
    rw [←sumPerm (translations p hp).1 g]
    simp only [sumOver,List.map_map,Function.comp_def]
    apply congrArg List.sum; apply List.map_congr_left; intro t ht
    dsimp only [g]; rw [(translations p hp).2.1 t ht,Ring.intCast_mul]; grind
  rw [sumMem permutations row,sumOverSwap]
  apply sumOverCongr; intro t
  unfold convolution
  rw [sumCast,sumOverMulRight]

theorem actProduct (s t : Sector) (f : Four α → C) (u : Four α) :
    act (coefficient s) (act (coefficient t) f) u =
      if s=t then 24 * act (coefficient s) f u else 0 := by
  rw [actConvolution]; unfold act
  have e := sumMem (C:=C) permutations (f:=fun p => Int.cast (convolution (coefficient s) (coefficient t) p) * f (reorder u p))
    (g:=fun p => (if s=t then Int.cast (24*coefficient s p) else 0)*f (reorder u p))
    (fun p hp => by rw [projectorProduct s t p hp]; split <;> grind)
  rw [e]; split
  next _ => rw [sumOverMulLeft]; apply sumOverCongr; intro p; simp only [Ring.intCast_mul]; grind
  next _ =>
    simp only [Semiring.zero_mul]
    have z {T : Type} (xs : List T) : sumOver xs (fun _ => (0:C))=0 := by
      induction xs with
      | nil => rfl
      | cons x xs ih => change 0+sumOver xs _=0; rw [ih]; grind
    exact z _

theorem rawResolution (f : Four α → C) (fixed : ∀ u p, p∈permutations → klein p=true → f (reorder u p)=f u)
    (u : Four α) :
    act (coefficient .symmetric) f u + act (coefficient .antisymmetric) f u +
      (act (coefficient .mixedEven) f u + act (coefficient .mixedOdd) f u) = 24*f u := by
  unfold act
  rw [←sumOverAdd,←sumOverAdd,←sumOverAdd]
  let w p : Int := if klein p then 6 else 0
  have h : sumOver permutations w = 24 := by decide
  calc
    _ = sumOver permutations (fun p => Int.cast (R:=C) (w p) * f u) := by
      apply sumMem; intro p hp
      have e := congrArg (Int.cast (R:=C)) (coefficientResolution p hp)
      simp only [mixedCoefficient,Ring.intCast_add] at e
      cases k : klein p
      · simp [w,k] at e ⊢; grind
      · rw [fixed u p hp k]; simp [w,k] at e ⊢; grind
    _ = _ := by rw [←sumOverMulRight,←sumCast,h]; grind

end Algebra

section Trace
variable {C α β γ : Type} [CommRing C]
local instance : IntCast C := Ring.intCast

def representatives : List Perm := [ident,((1,0),(3,2)),rotation,transposition,((1,2),(3,0))]

def representative (p : Perm) : Perm :=
  if p=ident then ident else if klein p then ((1,0),(3,2)) else
    if !oddPermutation p then rotation else if reorder p p=ident then transposition else ((1,2),(3,0))

set_option maxRecDepth 10000 in
private theorem classTable :
    representatives.Nodup ∧ permutations.all (fun p =>
      decide (representative p∈representatives) &&
      permutations.any (fun h => conjugate h p == representative p)) = true ∧
    representatives.all (fun r =>
      sumOver permutations (fun p => if representative p=r then coefficient .mixedEven p else 0) ==
      sumOver permutations (fun p => if representative p=r then coefficient .mixedOdd p else 0)) = true := by
  decide

def characterTrace (c : Perm → Int) (τ : Perm → C) : C :=
  sumOver permutations (fun p => Int.cast (c p)*τ p)

/-- The two mixed lines have exactly equal weighted trace against every
class function. This needs no division by 24 or assumption about torsion. -/
theorem equalMixedTrace (τ : Perm → C)
    (classFn : ∀ h∈permutations, ∀ p∈permutations, τ (conjugate h p)=τ p) :
    characterTrace (coefficient .mixedEven) τ = characterTrace (coefficient .mixedOdd) τ := by
  have aggregate (s : Sector) : characterTrace (coefficient s) τ =
      sumOver representatives (fun r =>
        Int.cast (sumOver permutations (fun p => if representative p=r then coefficient s p else 0))*τ r) := by
    unfold characterTrace
    calc
      _ = sumOver permutations (fun p => sumOver representatives
          (fun r => Int.cast (R:=C) (if representative p=r then coefficient s p else 0)*τ r)) := by
        apply sumMem; intro p hp
        have fact := Bool.and_eq_true_iff.mp (List.all_eq_true.mp classTable.2.1 p hp)
        obtain ⟨h,hh,e⟩ := List.any_eq_true.mp fact.2
        have classEq := classFn h hh p hp
        rw [beq_iff_eq.mp e] at classEq
        rw [←classEq]
        have delta := sumOnIndex representatives (representative p) (fun r => Int.cast (R:=C) (coefficient s p)*τ r)
          classTable.1 (_root_.of_decide_eq_true fact.1)
        rw [←delta]
        apply sumOverCongr; intro r; split <;> grind
      _ = _ := by
        rw [sumOverSwap]; apply sumOverCongr; intro r
        rw [sumCast,sumOverMulRight]
  rw [aggregate,aggregate]
  apply sumMem; intro r hr
  rw [beq_iff_eq.mp (List.all_eq_true.mp classTable.2.2 r hr)]

def Equivariant (K : Four α → Four β → C) : Prop :=
  ∀ p∈permutations, ∀ x y, K (reorder x p) (reorder y p) = K x y

def KleinFixed (K : Four α → Four β → C) : Prop :=
  ∀ p∈permutations, klein p=true → ∀ x y, K (reorder x p) y = K x y

def PermutedList (xs : List (Four α)) : Prop :=
  ∀ p∈permutations, (xs.map (fun r => reorder r p)).Perm xs

theorem fullPermuted [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ x, x∈xs) :
    PermutedList (fourIndices xs) := by
  intro p hp
  have complete (r : Four α) : r∈fourIndices xs :=
    HyperplaneInduction.pairMember (HyperplaneInduction.pairMember (full _) (full _))
      (HyperplaneInduction.pairMember (full _) (full _))
  have two := HyperplaneInduction.pairsNodup xs xs nd nd
  have four : (fourIndices xs).Nodup := HyperplaneInduction.pairsNodup _ _ two two
  have inv := (translations p hp).2.2.2.2
  have inj (a b : Four α) (e : reorder a p = reorder b p) : a=b := by
    have h := congrArg (fun u => reorder u (inverse p)) e
    rw [compReorder,compReorder,inv.1] at h; exact h
  have mapNd : ((fourIndices xs).map (fun r => reorder r p)).Nodup :=
    List.Pairwise.map _ (fun a b (ne : a≠b) e => ne (inj a b e)) four
  apply List.perm_iff_count.mpr; intro r
  have present : r∈(fourIndices xs).map (fun r => reorder r p) := by
    refine List.mem_map.mpr ⟨reorder r (inverse p),complete _,?_⟩
    rw [compReorder,inv.2]; rfl
  rw [mapNd.count, four.count]; simp [present,complete]

private theorem changeVariables (xs : List (Four α)) (hx : PermutedList xs)
    (p : Perm) (hp : p∈permutations) (f : Four α → C) :
    sumOver xs (fun r => f (reorder r p)) = sumOver xs f := by
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (hx p hp) f

def permTrace (xs : List (Four α)) (K : Four α → Four α → C) (p : Perm) : C :=
  sumOver xs (fun r => K (reorder r p) r)

theorem permTraceClass (xs : List (Four α)) (hx : PermutedList xs) (K : Four α → Four α → C)
    (equiv : Equivariant K) (h : Perm) (hh : h∈permutations) (p : Perm) (_hp : p∈permutations) :
    permTrace xs K (conjugate h p) = permTrace xs K p := by
  unfold permTrace
  rw [←changeVariables xs hx h hh (fun r => K (reorder r (conjugate h p)) r)]
  apply sumOverCongr; intro r
  have c : reorder h (conjugate h p) = reorder p h := by
    unfold conjugate
    rw [←compReorder, (translations h hh).2.2.2.2.1]
    have e (j : Fin 4) : position ident j = j := by revert j; decide
    simp only [reorder,e]
  rw [compReorder,c,←compReorder,equiv h hh]

/-- One sector applied on the row side of a matrix, scaled by 24. -/
def rawBlock (s : Sector) (K : Four α → Four β → C) (x : Four α) (y : Four β) : C :=
  act (coefficient s) (fun r => K r y) x

theorem rawBlockTrace (xs : List (Four α)) (K : Four α → Four α → C) (s : Sector) :
    trace xs (rawBlock s K) = characterTrace (coefficient s) (permTrace xs K) := by
  unfold trace rawBlock act characterTrace permTrace
  rw [sumOverSwap]; apply sumOverCongr; intro p
  rw [sumOverMulLeft]

/-- Exact direct trace split with one mixed copy counted twice. The two
geometric hypotheses are simultaneous replica symmetry and trivial Klein
action on the row image, as satisfied by physical Pauli compression. -/
theorem traceSplit (xs : List (Four α)) (hx : PermutedList xs) (K : Four α → Four α → C)
    (equiv : Equivariant K) (fixed : KleinFixed K) :
    24*trace xs K = trace xs (rawBlock .symmetric K) + 2*trace xs (rawBlock .mixedEven K) +
      trace xs (rawBlock .antisymmetric K) := by
  have mix : trace xs (rawBlock .mixedEven K) = trace xs (rawBlock .mixedOdd K) := by
    rw [rawBlockTrace,rawBlockTrace]
    exact equalMixedTrace _ (permTraceClass xs hx K equiv)
  have res : trace xs (rawBlock .symmetric K) + trace xs (rawBlock .antisymmetric K) +
      (trace xs (rawBlock .mixedEven K) + trace xs (rawBlock .mixedOdd K)) = 24*trace xs K := by
    unfold trace
    rw [←sumOverAdd,←sumOverAdd,←sumOverAdd,sumOverMulLeft]
    apply sumOverCongr; intro r
    exact rawResolution (fun x => K x r) (fun x p hp h => fixed p hp h x r) r
  grind

end Trace
section PhysicalTrace
variable {C R α β γ δ : Type} [CommRing C] [CommRing R]
local instance : IntCast C := Ring.intCast

private def factors {S : Type} (u : Four S) := [u.1.1,u.1.2,u.2.1,u.2.2]

private def product : List C → C
  | [] => 1
  | c::cs => c * product cs

private theorem productPerm {xs ys : List C} (h : xs.Perm ys) : product xs=product ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [product,ih]
  | swap => simp only [product]; grind
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

theorem tensorEquivariant (H : α → β → C) : Equivariant (tensorFour H) := by
  intro p hp u v
  have table : permutations.all (fun q => decide ((factors q).Perm (factors ident))) = true := by decide
  have e := productPerm ((_root_.of_decide_eq_true (List.all_eq_true.mp table p hp)).map
    (fun j => H (position u j) (position v j)))
  simp only [factors,ident,List.map_cons,List.map_nil,product,Semiring.mul_one] at e
  dsimp only [tensorFour,tensor,reorder]
  change _ = (H (position u 0) (position v 0) * H (position u 1) (position v 1)) *
    (H (position u 2) (position v 2) * H (position u 3) (position v 3))
  simp only [Semiring.mul_assoc] at e ⊢
  exact e

theorem mulEquivariant (xs : List (Four β)) (hx : PermutedList xs)
    (A : Four α → Four β → C) (B : Four β → Four γ → C)
    (a : Equivariant A) (b : Equivariant B) : Equivariant (matMul xs A B) := by
  intro p hp x y
  unfold matMul
  rw [←changeVariables xs hx p hp (fun z => A (reorder x p) z * B z (reorder y p))]
  exact sumOverCongr xs (fun z => by rw [a p hp,b p hp])

theorem mulFixedLeft (xs : List (Four β)) (A : Four α → Four β → C) (B : Four β → Four γ → C)
    (a : KleinFixed A) : KleinFixed (matMul xs A B) := by
  intro p hp k x y
  unfold matMul
  exact sumOverCongr xs (fun z => by rw [a p hp k])

theorem mulFixedRight (xs : List (Four β)) (hx : PermutedList xs)
    (A : Four α → Four β → C) (B : Four β → Four γ → C)
    (a : Equivariant A) (b : KleinFixed B) : KleinFixed (matMul xs A B) := by
  intro p hp k x y
  unfold matMul
  rw [←changeVariables xs hx p hp (fun z => A (reorder x p) z * B z y)]
  exact sumOverCongr xs (fun z => by rw [a p hp,b p hp k])

theorem blockLeft (xs : List (Four β)) (s : Sector)
    (A : Four α → Four β → C) (B : Four β → Four γ → C) :
    rawBlock s (matMul xs A B) = matMul xs (rawBlock s A) B := by
  funext x y
  unfold rawBlock act matMul
  simp only [sumOverMulLeft,sumOverMulRight]
  rw [sumOverSwap]; apply sumOverCongr; intro z
  apply sumOverCongr; intro p; grind

theorem blockRight (xs : List (Four β)) (hx : PermutedList xs) (s : Sector)
    (A : Four α → Four β → C) (B : Four β → Four γ → C) (a : Equivariant A) :
    rawBlock s (matMul xs A B) = matMul xs A (rawBlock s B) := by
  funext x y
  unfold rawBlock act matMul
  simp only [sumOverMulLeft]
  rw [sumOverSwap xs permutations]
  apply sumMem; intro p hp
  rw [←changeVariables xs hx p hp (fun z => Int.cast (R:=C) (coefficient s p) * (A (reorder x p) z * B z y))]
  apply sumOverCongr; intro z
  rw [a p hp]; grind

theorem frameStructure {n : Nat} (U : Basis n → α → ComplexScalar R) :
    Equivariant (PhysicalPairedReduction.frameTwirl U) ∧ KleinFixed (PhysicalPairedReduction.frameTwirl U) := by
  let xs := fourIndices (qubitIndices n)
  let L := transpose (tensorFour (ComplexPauliMoment.conjugate U))
  let P := @unnormalizedTwirl (ComplexScalar R) _ n ComplexScalar.imaginaryUnit
  let B := tensorFour U
  letI : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
  have hx : PermutedList xs := fullPermuted (qubitIndices n) (HyperplaneIncidence.normalsNodup n) qubitIndicesComplete
  have left : Equivariant L := fun p hp x y => tensorEquivariant _ p hp y x
  have mid : Equivariant P := by
    intro p hp x y
    unfold P unnormalizedTwirl
    apply sumOverCongr; intro w
    exact tensorEquivariant _ p hp x y
  have fixed : KleinFixed P := by
    intro p hp k x y
    unfold P
    rw [unnormalizedTwirlEntry _ ComplexScalar.imaginaryUnit_fourth,
      unnormalizedTwirlEntry _ ComplexScalar.imaginaryUnit_fourth, kleinTwirl n p hp k]
  exact ⟨mulEquivariant xs hx _ B (mulEquivariant xs hx L P left mid) (tensorEquivariant _),
    mulFixedLeft xs _ B (mulFixedRight xs hx L P left fixed)⟩

/-- Transfer a sector to the first frame in the physical trace, using replica
equivariance of the inserted fourth tensor power. -/
theorem traceBlockFrame (xs : List (Four α)) (hx : PermutedList xs) (s : Sector)
    (H A B : Four α → Four α → C) (h : Equivariant H) :
    trace xs (rawBlock s (matMul xs (matMul xs (matMul xs H A) H) B)) =
      pairedFrameTrace xs H (rawBlock s A) B := by
  rw [blockLeft,blockLeft,blockRight xs hx s H A h]; rfl

/-- Distinct sector pairs give zero trace; equal ones give 24 times the
single-block trace since the coefficient projectors here are scaled by 24. -/
theorem pairedBlockOrthogonality (xs : List (Four α)) (hx : PermutedList xs) (s t : Sector)
    (H A B : Four α → Four α → C) (h : Equivariant H) (a : Equivariant A) :
    pairedFrameTrace xs H (rawBlock s A) (rawBlock t B) =
      if s=t then 24*pairedFrameTrace xs H (rawBlock s A) B else 0 := by
  let K := matMul xs (matMul xs (matMul xs H A) H) B
  have he : Equivariant (matMul xs (matMul xs H A) H) :=
    mulEquivariant xs hx _ H (mulEquivariant xs hx H A h a) h
  have rt : rawBlock t K = matMul xs (matMul xs (matMul xs H A) H) (rawBlock t B) :=
    blockRight xs hx t _ B he
  rw [←traceBlockFrame xs hx s H A (rawBlock t B) h,←rt,←traceBlockFrame xs hx s H A B h]
  change sumOver xs (fun x => act (coefficient s) (act (coefficient t) (fun y => K y x)) x) = _
  simp only [actProduct]
  by_cases e : s=t
  · simp only [e,ite_true]
    exact (sumOverMulLeft xs (fun x => rawBlock t K x x) 24).symm
  · simp only [e,ite_false]
    have z (ls : List (Four α)) : sumOver ls (fun _ => (0:C)) = 0 := by
      induction ls with
      | nil => rfl
      | cons _ _ ih => change 0+sumOver _ _=0; rw [ih]; grind
    exact z _

theorem pairedSectorTrace (xs : List (Four α)) (hx : PermutedList xs)
    (H A B : Four α → Four α → C) (h : Equivariant H)
    (a : Equivariant A) (b : Equivariant B) (fixed : KleinFixed A) :
    24*pairedFrameTrace xs H A B =
      pairedFrameTrace xs H (rawBlock .symmetric A) B +
      2*pairedFrameTrace xs H (rawBlock .mixedEven A) B +
      pairedFrameTrace xs H (rawBlock .antisymmetric A) B := by
  let HA := matMul xs H A
  have e := traceSplit xs hx (matMul xs (matMul xs HA H) B)
    (mulEquivariant xs hx _ B (mulEquivariant xs hx HA H (mulEquivariant xs hx H A h a) h) b)
    (mulFixedLeft xs _ B (mulFixedLeft xs HA H (mulFixedRight xs hx H A h fixed)))
  unfold HA at e
  simp only [traceBlockFrame xs hx _ H A B h] at e
  exact e

/-- Actual arbitrary rectangular physical qubit frames, with the Schmidt
matrix inserted through its fourth tensor power. No isotypic, Schur, or
pre-split trace hypothesis is required. -/
theorem physicalPairedSectorTrace [DecidableEq α] (sites : List α) (nd : sites.Nodup) (full : ∀ a, a∈sites)
    {n m : Nat} (U : Basis n → α → ComplexScalar R) (V : Basis m → α → ComplexScalar R)
    (M : α → α → ComplexScalar R) :
    let xs := fourIndices sites
    let H := tensorFour M
    let A := PhysicalPairedReduction.frameTwirl U
    let B := PhysicalPairedReduction.frameTwirl V
    24*pairedFrameTrace xs H A B = pairedFrameTrace xs H (rawBlock .symmetric A) B +
      2*pairedFrameTrace xs H (rawBlock .mixedEven A) B + pairedFrameTrace xs H (rawBlock .antisymmetric A) B :=
  pairedSectorTrace _ (fullPermuted sites nd full) _ _ _ (tensorEquivariant M)
    (frameStructure U).1 (frameStructure V).1 (frameStructure U).2

end PhysicalTrace

section Normalized
variable {R α : Type} [CommRing R]

theorem normalizedFrameStructure {n : Nat} (half : R) (U : Basis n → α → ComplexScalar R) :
    Equivariant (RectangularPairedReduction.normalizedFrame half U) ∧
    KleinFixed (RectangularPairedReduction.normalizedFrame half U) := by
  obtain ⟨eqv,fix⟩ := frameStructure U
  exact ⟨fun p hp x y => congrArg (fun z => ComplexScalar.ofReal (half^n) * z) (eqv p hp x y),
    fun p hp k x y => congrArg (fun z => ComplexScalar.ofReal (half^n) * z) (fix p hp k x y)⟩

theorem normalizedPairedSectorTrace [DecidableEq α] (sites : List α) (nd : sites.Nodup) (full : ∀ a, a∈sites)
    {n m : Nat} (half : R) (U : Basis n → α → ComplexScalar R) (V : Basis m → α → ComplexScalar R)
    (M : α → α → ComplexScalar R) :
    let xs := fourIndices sites
    let H := tensorFour M
    let A := RectangularPairedReduction.normalizedFrame half U
    let B := RectangularPairedReduction.normalizedFrame half V
    24*pairedFrameTrace xs H A B = pairedFrameTrace xs H (rawBlock .symmetric A) B +
      2*pairedFrameTrace xs H (rawBlock .mixedEven A) B + pairedFrameTrace xs H (rawBlock .antisymmetric A) B :=
  pairedSectorTrace _ (fullPermuted sites nd full) _ _ _ (tensorEquivariant M)
    (normalizedFrameStructure half U).1 (normalizedFrameStructure half V).1 (normalizedFrameStructure half U).2

end Normalized
end RankSeven.FourCopySectors
