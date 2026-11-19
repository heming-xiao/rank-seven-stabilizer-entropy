import Rank7PhysicalHopping

/-! One-mode uniform occupation, proved directly from the unique binary
completion and simultaneous translation invariance of the physical columns. -/
namespace RankSeven.PhysicalUniformOccupation
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase HyperplaneIncidence
open PhysicalCutCapacities (Triple triples extend complete)
open PhysicalHopping (PlaneField)
variable {R C : Type} [CommRing R] [CommRing C]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
local instance {C : Type} [CommRing C] : NatCast C := Semiring.natCast

private theorem completeIff {n} (x : Triple (Basis n)) (t : Basis n) :
    GenericExteriorKernel.parity (extend x t)=zero n ↔ t=complete x := by
  induction n with
  | zero => rcases t with ⟨⟩; rcases x with ⟨⟨⟨⟩,⟨⟩⟩,⟨⟩⟩; exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ n ih =>
    rcases t with ⟨t,z⟩
    rcases x with ⟨⟨⟨a,x⟩,b,y⟩,c,w⟩
    change (((a^^b)^^(c^^t)),GenericExteriorKernel.parity (extend ((x,y),w) z))=(false,zero n) ↔
      (t,z)=(((a^^b)^^c),complete ((x,y),w))
    simp only [Prod.mk.injEq,ih]
    cases a <;> cases b <;> cases c <;> cases t <;> simp

private theorem moveShift {n} (a b : Basis n) : xorBasis n (xorBasis n a b) a=b := by
  induction n with
  | zero => cases b; rfl
  | succ n ih => rcases a with ⟨a,v⟩; rcases b with ⟨b,w⟩; simp only [xorBasis,ih]; cases a <;> cases b <;> rfl

private theorem productSum {I J : Type} (xs : List I) (ys : List J) (f : I × J → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem tripleSum {n} (f : Triple (Basis n) → C) :
    sumOver (triples (qubitIndices n)) f=sumOver (qubitIndices n) (fun i => sumOver (qubitIndices n)
      (fun j => sumOver (qubitIndices n) (fun k => f ((i,j),k)))) := by
  unfold triples; rw [productSum,productSum]

private def G {n} (f g : Four (Basis n) → C) (a b : Basis n) :=
  sumOver (triples (qubitIndices n)) (fun u => f (extend u a)*g (extend u b))

private theorem gramUniform {n} {f g : Four (Basis n) → C} (hf : PlaneField f) (hg : PlaneField g) (a b : Basis n) :
    G f g a a=G f g b b := by
  let d := xorBasis n a b
  have row (i j k : Basis n) : f (extend ((i,j),k) a)*g (extend ((i,j),k) a) =
      f (extend ((xorBasis n d i,xorBasis n d j),xorBasis n d k) b)*g (extend ((xorBasis n d i,xorBasis n d j),xorBasis n d k) b) := by
    have hf0 := hf.invariant d (extend ((i,j),k) a)
    have hg0 := hg.invariant d (extend ((i,j),k) a)
    change f ((xorBasis n d i,xorBasis n d j),xorBasis n d k,xorBasis n d a)=_ at hf0
    change g ((xorBasis n d i,xorBasis n d j),xorBasis n d k,xorBasis n d a)=_ at hg0
    rw [moveShift] at hf0 hg0
    change _=f ((xorBasis n d i,xorBasis n d j),xorBasis n d k,b)*g ((xorBasis n d i,xorBasis n d j),xorBasis n d k,b)
    rw [hf0,hg0]
  let xs := qubitIndices n
  have tr (F : Basis n → Basis n → Basis n → C) :
      sumOver xs (fun i => sumOver xs (fun j => sumOver xs (fun k => F (xorBasis n d i) (xorBasis n d j) (xorBasis n d k))))=
      sumOver xs (fun i => sumOver xs (fun j => sumOver xs (F i j))) := by
    have e2 (i j) := PhysicalPairExchange.sumTranslate d (F (xorBasis n d i) (xorBasis n d j))
    have e1 (i) := PhysicalPairExchange.sumTranslate d (fun j => sumOver xs (F (xorBasis n d i) j))
    exact (sumOverCongr xs (fun i => (sumOverCongr xs (e2 i)).trans (e1 i))).trans
      (PhysicalPairExchange.sumTranslate d (fun i => sumOver xs (fun j => sumOver xs (F i j))))
  unfold G; rw [tripleSum,tripleSum]; simp only [row]
  exact tr (fun i j k => f (extend ((i,j),k) b)*g (extend ((i,j),k) b))

private theorem sum0 {I : Type} (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs <;> simp_all [sumOver,List.map,AddCommMonoid.zero_add]

theorem slices {n} {f g : Four (Basis n) → C} (hf : PlaneField f) (hg : PlaneField g) (a b : Basis n) :
    G f g a b = if a=b then G f g (zero n) (zero n) else 0 := by
  by_cases e : a=b
  · subst b; simp only [ite_true]; exact gramUniform hf hg a _
  · rw [ite_eq_right e,←sum0 (C:=C) (triples (qubitIndices n))]
    apply sumOverCongr; intro u
    by_cases ea : a=complete u
    · have eb : b≠complete u := fun eb => e (ea.trans eb.symm)
      rw [hg.supported _ (fun h => eb ((completeIff u b).mp h)),Semiring.mul_zero]
    · rw [hf.supported _ (fun h => ea ((completeIff u a).mp h)),Semiring.zero_mul]

private theorem sumConst {I : Type} (xs : List I) (v : C) : sumOver xs (fun _ => v)=(xs.length:C)*v := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih => change v+sumOver xs _=((xs.length+1:Nat):C)*v; rw [ih,Semiring.natCast_succ]; grind only

private theorem total {n} (f g : Four (Basis n) → C) :
    sumOver (fourIndices (qubitIndices n)) (fun u => f u*g u)=sumOver (qubitIndices n) (fun a => G f g a a) := by
  unfold G fourIndices
  simp only [productSum,tripleSum]
  symm; rw [sumOverSwap]; apply sumOverCongr; intro i; rw [sumOverSwap]
  apply sumOverCongr; intro j; rw [sumOverSwap]; rfl

def oneHole {n} (x : Basis n → C) (f : Four (Basis n) → C) (u : Triple (Basis n)) :=
  sumOver (qubitIndices n) (fun a => x a*f (extend u a))

private theorem expansion {n} (x y : Basis n → C) (f g : Four (Basis n) → C) :
    sumOver (triples (qubitIndices n)) (fun u => oneHole x f u*oneHole y g u)=
    sumOver (qubitIndices n) (fun a => sumOver (qubitIndices n) (fun b => x a*y b*G f g a b)) := by
  unfold oneHole G
  simp only [sumOverMulRight,sumOverMulLeft]
  conv => rhs; rw [sumOverSwap]
  rw [sumOverSwap]
  apply sumOverCongr; intro a; rw [sumOverSwap]
  apply sumOverCongr; intro b; apply sumOverCongr; intro u; grind only

/-- Polarized uniform single-mode occupation on all physical plane fields.
Multiplication by the ambient dimension avoids any inverse assumptions. -/
theorem uniformOccupation {n} (x y : Basis n → C) {f g : Four (Basis n) → C}
    (hf : PlaneField f) (hg : PlaneField g) :
    (2:C)^n * sumOver (triples (qubitIndices n)) (fun u => oneHole x f u*oneHole y g u)=
    sumOver (qubitIndices n) (fun a => x a*y a)*sumOver (fourIndices (qubitIndices n)) (fun u => f u*g u) := by
  let bs := qubitIndices n
  let m := G f g (zero n) (zero n)
  have dim := congrArg (fun t : Nat => (t:C)) (qubitIndicesLength n)
  have cast (k : Nat) : ((2^k:Nat):C)=(2:C)^k := by
    induction k with
    | zero => simp only [Semiring.natCast_one,Semiring.pow_zero]
    | succ k ih =>
      have two : ((2:Nat):C)=2 := by change ((1+1:Nat):C)=2; rw [Semiring.natCast_succ,Semiring.natCast_one]; grind only
      rw [Nat.pow_succ,Semiring.natCast_mul,ih,two,Semiring.pow_succ]
  have mass : sumOver (fourIndices bs) (fun u => f u*g u)=(2:C)^n*m := by
    rw [total]
    rw [sumOverCongr bs (fun a => gramUniform hf hg a (zero n)),sumConst]; exact congrArg (·*m) (dim.trans (cast n))
  have row (a : Basis n) :
      sumOver bs (fun b => x a*y b*G f g a b)=x a*y a*m := by
    refine (sumOverCongr bs (g:=fun b => if a=b then x a*y b*m else 0) (fun b => ?_)).trans
      (ExteriorPauliBase.sumOnIndex bs a _ (normalsNodup n) (qubitIndicesComplete _))
    rw [slices hf hg]; by_cases e : a=b <;> simp [e,m] <;> grind only
  rw [expansion,sumOverCongr bs row,←sumOverMulRight,mass]; grind only

private theorem starField {n} {f : Four (Basis n) → ComplexScalar R} (hf : PlaneField f) : PlaneField (fun u => star (f u)) := by
  constructor
  · intro d u; rw [hf.invariant]
  · intro u ne; rw [hf.supported u ne]; exact star_ofReal 0

private theorem reSum {I : Type} (xs : List I) (f : I → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

theorem unitModeOccupation {n} (x : Basis n → ComplexScalar R) (hx : sumOver (qubitIndices n) (fun a => star (x a)*x a)=1)
    {f : Four (Basis n) → ComplexScalar R} (hf : PlaneField f) :
    (2:R)^n * sumOver (triples (qubitIndices n)) (fun u => normSq (oneHole x f u))=
      sumOver (fourIndices (qubitIndices n)) (fun u => normSq (f u)) := by
  have h := uniformOccupation (fun a => star (x a)) x (starField hf) hf
  change (2:ComplexScalar R)^n * _=sumOver _ (fun a => star (x a)*x a)*_ at h
  rw [hx,Semiring.one_mul] at h
  have conj (u : Triple (Basis n)) : oneHole (fun a => star (x a)) (fun u => star (f u)) u=star (oneHole x f u) := by
    unfold oneHole; rw [ComplexExterior.starSumOver]; simp only [star_mul]
  simp only [conj] at h
  change ofReal (2:R)^n * _=_ at h; rw [←PhysicalPairedReduction.realEmbeddingPow] at h
  have he := congrArg ComplexScalar.re h
  have e (r : R) (z : ComplexScalar R) : (ofReal r*z).re=r*z.re := by simp [re_mul,ofReal]; grind only
  simpa only [e,reSum,re_star_mul_self] using he

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Ring.intCast

private theorem sumLe {I : Type} (xs : List I) (f g : I → R) (h : ∀ i∈xs, f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i is ih =>
    have a := h i List.mem_cons_self
    have b := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    change f i+sumOver is f ≤ g i+sumOver is g; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sum24 (v : R) : sumOver permutations (fun _ => v)=24*v := by
  have e : permutations.length=24 := by decide
  rw [sumConst,e]; change ((24:Nat):R)*v=24*v
  have two : ((2:Nat):R)=2 := by change ((1+1:Nat):R)=2; rw [Semiring.natCast_succ,Semiring.natCast_one]; grind only
  change ((((2+1)*2*2*2:Nat):R)*v)=24*v
  simp only [Semiring.natCast_mul,Semiring.natCast_add,Semiring.natCast_one,two]; grind only

private theorem squareSum24 (z : Permutation → ComplexScalar R) :
    normSq (sumOver permutations z)≤24*sumOver permutations (fun p => normSq (z p)) := by
  have e (p q : Permutation) : 2*(star (z p)*z q).re ≤ normSq (z p)+normSq (z q) := by
    have h := normSq_nonnegative (z p - z q)
    simp only [normSq,re_sub,im_sub,re_mul,re_star,im_star] at h ⊢; grind only
  have b := sumLe permutations _ _ (fun p _ => sumLe permutations _ _ (fun q _ => e p q))
  simp only [←sumOverMulLeft,sumOverAdd,sum24] at b
  have total : normSq (sumOver permutations z)=sumOver permutations (fun q => sumOver permutations (fun p => (star (z p)*z q).re)) := by
    rw [←re_star_mul_self,ComplexExterior.starSumOver,sumOverMulRight]
    simp only [sumOverMulLeft,reSum]; rw [sumOverSwap]
  rw [total,sumOverSwap]; grind only

private theorem sumPerm {I : Type} {xs ys : List I} (h : xs.Perm ys) (f : I → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2

private theorem altBound {n} (F : Four (Basis n) → ComplexScalar R) :
    sumOver (fourIndices (qubitIndices n)) (fun u => normSq (FourCopySectors.act (FourCopySectors.coefficient .antisymmetric) F u))≤
      576*sumOver (fourIndices (qubitIndices n)) (fun u => normSq (F u)) := by
  let xs := fourIndices (qubitIndices n)
  have op (u : Four (Basis n)) : normSq (FourCopySectors.act (FourCopySectors.coefficient .antisymmetric) F u)
      ≤24*sumOver permutations (fun p => normSq (F (reorder u p))) := by
    have h := squareSum24 (fun p => Int.cast (R:=ComplexScalar R) (FourCopySectors.coefficient .antisymmetric p)*F (reorder u p))
    have e (p : Permutation) : normSq (Int.cast (R:=ComplexScalar R) (FourCopySectors.coefficient .antisymmetric p)*F (reorder u p))=normSq (F (reorder u p)) := by
      unfold FourCopySectors.coefficient
      cases oddPermutation p <;> simp only [ite_false,ite_true,Bool.false_eq_true,Ring.intCast_one,Ring.intCast_neg,Semiring.one_mul] <;>
        simp [normSq,re_mul,im_mul] <;> grind only
    unfold FourCopySectors.act; rw [sumOverCongr permutations e] at h; exact h
  have bound := sumLe xs _ _ (fun u _ => op u)
  have perm := FourCopySectors.fullPermuted (qubitIndices n) (normalsNodup n) (@qubitIndicesComplete n)
  have invariant (p : Permutation) (hp : p∈permutations) :
      sumOver xs (fun u => normSq (F (reorder u p)))=sumOver xs (fun u => normSq (F u)) := by
    simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (perm p hp) (fun u => normSq (F u))
  rw [←sumOverMulLeft,sumOverSwap] at bound
  rw [show sumOver permutations (fun p => sumOver xs (fun u => normSq (F (reorder u p))))=
      sumOver permutations (fun _ => sumOver xs (fun u => normSq (F u))) from congrArg List.sum (List.map_congr_left invariant),sum24] at bound
  change sumOver xs _≤576*sumOver xs _; grind only
def wave {n} (half : R) (c : Word n → ComplexScalar R) (u : Four (Basis n)) :=
  sumOver (MixedDefect.oddWords n) (fun p => c p*WedgeSquareIntertwiner.wedgeSquareColumn half p u)

private def rawWave {n} (c : Word n → ComplexScalar R) (u : Four (Basis n)) :=
  sumOver (MixedDefect.oddWords n) (fun p => PhysicalMixedFrame.doubledWord p u*c p)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem waveEq {n} (half : R) (c : Word n → ComplexScalar R) (u : Four (Basis n)) :
    wave half c u=(ofReal half)^(n+2)*FourCopySectors.act (FourCopySectors.coefficient .antisymmetric) (rawWave c) u := by
  unfold wave WedgeSquareIntertwiner.wedgeSquareColumn WedgeSquareIntertwiner.alternatingWord FourCopySectors.act rawWave
  simp only [sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro w; apply sumOverCongr; intro p; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem scaledIsometry {I J : Type} [DecidableEq I] (xs : List I) (nd : xs.Nodup) (rs : List J)
    (M : J → I → ComplexScalar R) (k : R)
    (orth : ∀ i∈xs, ∀ j∈xs, 2 * sumOver rs (fun r => M r i * star (M r j)) =
      if i=j then ofReal k else 0) (y : I → ComplexScalar R) :
    2 * sumOver rs (fun r => normSq (sumOver xs (fun i => M r i*y i))) = k*sumOver xs (fun i => normSq (y i)) := by
  have pull :
    2*sumOver rs (fun r => (sumOver xs (fun i => M r i*y i))*star (sumOver xs (fun i => M r i*y i))) =
      ofReal k * sumOver xs (fun i => y i*star (y i)) := by
    simp only [ComplexExterior.starSumOver,star_mul,sumOverMulLeft,sumOverMulRight]
    rw [sumOverSwap]
    conv => lhs; arg 2; intro j; rw [sumOverSwap]
    apply congrArg List.sum; apply List.map_congr_left; intro j hj
    refine (sumOverCongr xs (g:=fun i => ((2:ComplexScalar R)*sumOver rs (fun r => M r i* star (M r j)))*(y i*star (y j))) (fun i => ?_)).trans ?_
    · simp only [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro r; grind only
    · refine (congrArg List.sum (List.map_congr_left (g:=fun i => if j=i then ofReal k*(y i*star (y i)) else 0) (fun i hi => ?_))).trans
        (ExteriorPauliBase.sumOnIndex xs j _ nd hj)
      rw [orth i hi j hj]; by_cases e : i=j <;> simp [e,Ne.symm] <;> grind only
  have eq := congrArg ComplexScalar.re pull
  have scale (v : ComplexScalar R) (a : R) : (ofReal a*v).re=a*v.re := by simp [re_mul,ofReal]; grind only
  change (ofReal (2:R)*_).re=(ofReal k*_).re at eq
  simp only [scale,reSum] at eq
  have self (z : ComplexScalar R) : (z*star z).re=normSq z := by rw [CommSemiring.mul_comm,re_star_mul_self]
  simpa only [self] using eq

private theorem rawNorm {n} (c : Word n → ComplexScalar R) :
    sumOver (fourIndices (qubitIndices n)) (fun u => normSq (rawWave c u))=
    ((2:R)^n*(2:R)^n)*sumOver (MixedDefect.oddWords n) (fun p => normSq (c p)) := by
  let D := (2:R)^n
  classical
  let bs := fourIndices (qubitIndices n)
  let os := MixedDefect.oddWords n
  have orth (p:Word n) (_ : p∈os) (q:Word n) (_ : q∈os) :
      2*sumOver bs (fun u => PhysicalMixedFrame.doubledWord (R:=R) p u * star (PhysicalMixedFrame.doubledWord q u))=
      if p=q then ofReal (2*(D*D)) else 0 := by
    rw [sumOverCongr bs (fun u => CommSemiring.mul_comm _ _),WedgeSquareIntertwiner.doubledWordOrthogonal]
    by_cases e : p=q
    · simp only [e,ite_true,MixedDefect.idEntry,Semiring.mul_one]
      change ofReal (2:R)*(ofReal (2:R)^n*ofReal (2:R)^n)=ofReal _
      rw [←PhysicalPairedReduction.realEmbeddingPow]
      apply ComplexScalar.ext <;> simp [D,re_mul,im_mul,ofReal] <;> grind only
    · simp [e,Ne.symm,MixedDefect.idEntry,Semiring.mul_zero]
  have h := scaledIsometry os (MixedDefect.oddWordsNodup n) bs (fun u p => PhysicalMixedFrame.doubledWord p u) (2*(D*D)) orth c
  change 2*sumOver bs (fun u => normSq (rawWave c u))=_ at h
  change sumOver bs (fun u => normSq (rawWave c u))=(D*D)*sumOver os _; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem dimCancel (half : R) (h2 : 2*half=1) (n : Nat) : half^n*(2:R)^n=1 := by
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
  | succ n ih =>
    simp only [Semiring.pow_succ]
    calc half^n*half*((2:R)^n*2) = (half^n*(2:R)^n)*(2*half) := by grind only
      _ = 1 := by rw [ih,h2,Semiring.one_mul]

/-- The odd Pauli wave synthesis has squared norm at most 36 in full ordered
four-site coordinates (24 times its 3/2 exterior tight-frame constant). -/
theorem physicalWaveBound (half : R) (unit : 2*half=1) {n} (c : Word n → ComplexScalar R) :
    sumOver (fourIndices (qubitIndices n)) (fun u => normSq (wave half c u))≤
      36*sumOver (MixedDefect.oddWords n) (fun p => normSq (c p)) := by
  let xs := fourIndices (qubitIndices n)
  let os := MixedDefect.oddWords n
  let F := rawWave c
  let G := FourCopySectors.act (FourCopySectors.coefficient .antisymmetric) F
  have bound := altBound F
  have scalar := dimCancel half unit n
  have sc (u) : normSq (wave half c u)=(half^(n+2))^2*normSq (G u) := by
    rw [waveEq,normSq_mul,←PhysicalPairedReduction.realEmbeddingPow,normSq_ofReal]
  rw [sumOverCongr xs sc,←sumOverMulLeft]
  change (half^(n+2))^2*sumOver xs (fun u => normSq (G u))≤36*sumOver os _
  change sumOver xs (fun u => normSq (G u))≤576*sumOver xs (fun u => normSq (F u)) at bound
  rw [rawNorm] at bound
  have pos := squareNonnegative (half^(n+2))
  have factor : (half^(n+2))^2 * (576*((2:R)^n*(2:R)^n))=36 := by
    rw [Semiring.pow_succ,Semiring.pow_succ]
    calc _ = 36*(half^n*(2:R)^n)^2 * (2*half)^4 := by grind only
      _ = 36 := by rw [scalar,unit]; grind only
  refine Std.le_trans (OrderedRing.mul_le_mul_of_nonneg_left bound pos) (Std.le_of_eq ?_)
  calc _ = ((half^(n+2))^2*(576*((2:R)^n*(2:R)^n)))*sumOver os (fun p => normSq (c p)) := by grind only
    _ = _ := by rw [factor]

/-- The physical zero-contraction layer for a unit mode: the three residual
coordinates are ordered, contributing the factor 3! to the exterior norm. -/
theorem physicalOneHoleBound (half : R) (unit : 2*half=1) {n} (x : Basis n → ComplexScalar R)
    (hx : sumOver (qubitIndices n) (fun a => star (x a)*x a)=1) (c : Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun u => normSq (oneHole x (wave half c) u))≤
      (36*half^n)*sumOver (MixedDefect.oddWords n) (fun p => normSq (c p)) := by
  have field := PhysicalHopping.fieldCombination (MixedDefect.oddWords n) c
    (WedgeSquareIntertwiner.wedgeSquareColumn half) (fun p _ => PhysicalHopping.pauliColumnField half p)
  have occ := unitModeOccupation x hx field
  change (2:R)^n*sumOver _ (fun u => normSq (oneHole x (wave half c) u))=sumOver _ (fun u => normSq (wave half c u)) at occ
  have h := physicalWaveBound half unit c
  have hn : 0≤half := by grind only
  have hp (k : Nat) : 0≤half^k := by
    induction k with
    | zero => simp only [Semiring.pow_zero]; grind only
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hn
  have dim := dimCancel half unit n
  have bound := OrderedRing.mul_le_mul_of_nonneg_left h (hp n)
  rw [←occ,←Semiring.mul_assoc,dim,Semiring.one_mul] at bound
  exact Std.le_trans bound (Std.le_of_eq (by grind only))
end Order

end RankSeven.PhysicalUniformOccupation
#print axioms RankSeven.PhysicalUniformOccupation.uniformOccupation
#print axioms RankSeven.PhysicalUniformOccupation.physicalOneHoleBound
