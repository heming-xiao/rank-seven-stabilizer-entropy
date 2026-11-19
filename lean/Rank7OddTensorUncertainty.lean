import Rank7OddCutReserve

/-! Repeated Pauli observables on arbitrary finite tensor powers. -/
namespace RankSeven.OddTensorUncertainty
open Lean.Grind Pauli ComplexScalar
open PhysicalPairedReduction (dagger)
open PauliPairContraction (image normSum)
open OddCutReserve (realInner)

def Sites (α : Type) : Nat → Type
  | 0 => Unit
  | r+1 => α×Sites α r

def indices {α : Type} (xs : List α) : (r : Nat) → List (Sites α r)
  | 0 => [()]
  | r+1 => productIndices xs (indices xs r)

def matrix {C α β : Type} [CommRing C] (A : α → β → C) : (r : Nat) → Sites α r → Sites β r → C
  | 0,_,_ => 1
  | r+1,x,y => A x.1 y.1*matrix A r x.2 y.2

instance siteEq {α : Type} [DecidableEq α] : (r : Nat) → DecidableEq (Sites α r)
  | 0 => (inferInstance : DecidableEq Unit)
  | r+1 => @instDecidableEqProd α (Sites α r) _ (siteEq r)

theorem indicesNodup {α : Type} (xs : List α) (nd : xs.Nodup) (r : Nat) : (indices xs r).Nodup := by
  induction r with
  | zero => change ([()] : List Unit).Nodup; decide
  | succ r ih => exact HyperplaneInduction.pairsNodup xs (indices xs r) nd ih

theorem indicesFull {α : Type} (xs : List α) (full : ∀ a,a∈xs) (r : Nat) (x : Sites α r) : x∈indices xs r := by
  induction r with
  | zero => cases x; exact List.mem_cons_self
  | succ r ih =>
    obtain ⟨a,y⟩ := x
    exact List.mem_flatMap.mpr ⟨a,full a,List.mem_map.mpr ⟨y,ih y,rfl⟩⟩

theorem matrixComp {C α β γ : Type} [CommRing C] (xs : List β) (A : α → β → C) (B : β → γ → C) (r : Nat) :
    matMul (indices xs r) (matrix A r) (matrix B r)=matrix (matMul xs A B) r := by
  induction r with
  | zero => funext x y; change (1:C)*1+0=1; grind only
  | succ r ih =>
    change matMul (productIndices xs (indices xs r)) (tensor A (matrix A r)) (tensor B (matrix B r))=_
    rw [←tensorMatMul,ih]; rfl

theorem matrixDagger {R α β : Type} [CommRing R] (A : α → β → ComplexScalar R) (r : Nat) :
    dagger (matrix A r)=matrix (dagger A) r := by
  induction r with
  | zero => funext x y; change star (1:ComplexScalar R)=1; apply ComplexScalar.ext <;> simp <;> grind only
  | succ r ih =>
    funext x y
    change star (A y.1 x.1*matrix A r y.2 x.2)=star (A y.1 x.1)*matrix (dagger A) r x.2 y.2
    rw [star_mul,←ih]; rfl

theorem matrixIdentity {C α : Type} [CommRing C] [DecidableEq α] (r : Nat) (x y : Sites α r) :
    matrix (fun a b : α => if a=b then (1:C) else 0) r x y=if x=y then 1 else 0 := by
  induction r with
  | zero => cases x; cases y; change (1:C)=if (() : Unit)=() then 1 else 0; rfl
  | succ r ih =>
    obtain ⟨a,x⟩ := x; obtain ⟨b,y⟩ := y
    change (if a=b then (1:C) else 0)*matrix _ r x y=if (a,x)=(b,y) then 1 else 0
    rw [ih]; by_cases h : a=b <;> by_cases j : x=y <;> simp [h,j] <;> grind only

theorem matrixScale {C α β : Type} [CommRing C] (A : α → β → C) (u : C) (r : Nat) (x : Sites α r) (y : Sites β r) :
    matrix (fun i j => u*A i j) r x y=u^r*matrix A r x y := by
  induction r with
  | zero => simp [matrix,Semiring.pow_zero]; grind only
  | succ r ih =>
    change (u*A x.1 y.1)*matrix _ r x.2 y.2 = u^(r+1)*(A x.1 y.1*matrix A r x.2 y.2)
    rw [ih,Semiring.pow_succ]; grind only

theorem negativeOddPower {C : Type} [CommRing C] (r : Nat) (h : r%2=1) : (-1:C)^r= -1 := by
  have both (m : Nat) : ((-1:C)^m=if m%2=1 then -1 else 1) := by
    induction m with
    | zero => simp [Semiring.pow_zero]
    | succ m ih =>
      rw [Semiring.pow_succ,ih]
      by_cases q : m%2=1
      · have z : ¬(m+1)%2=1 := by omega
        simp [q,z]; grind only
      · have z : (m+1)%2=1 := by omega
        simp [q,z]; grind only
  simpa only [h,ite_true] using both r

variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def pauli {n : Nat} (r : Nat) (p : Word n) := matrix (wordEntry (imaginaryUnit (R:=R)) p) r

private theorem unitEntry (n : Nat) (x y : Basis n) : wordEntry (imaginaryUnit (R:=R)) (SymmetricDefect.unitWord n) x y=if x=y then 1 else 0 := by
  induction n with
  | zero => cases x; cases y; simp [wordEntry,SymmetricDefect.unitWord]; grind only
  | succ n ih =>
    obtain ⟨a,x⟩ := x; obtain ⟨b,y⟩ := y
    cases a <;> cases b <;> by_cases e : x=y <;> simp [wordEntry,entry,SymmetricDefect.unitWord,ih,e] <;> grind only

theorem pauliHerm {n : Nat} (r : Nat) (p : Word n) : dagger (pauli (R:=R) r p)=pauli r p := by
  unfold pauli; rw [matrixDagger]
  have h : dagger (wordEntry (imaginaryUnit (R:=R)) p)=wordEntry imaginaryUnit p := by
    funext x y; exact ComplexPauliMoment.wordHermitian p y x
  rw [h]

theorem pauliGram {n : Nat} (r : Nat) (p : Word n) (x y : Sites (Basis n) r) :
    matMul (indices (qubitIndices n) r) (dagger (pauli (R:=R) r p)) (pauli r p) x y=if x=y then 1 else 0 := by
  rw [pauliHerm]; unfold pauli; rw [matrixComp]
  have t : matMul (qubitIndices n) (wordEntry (imaginaryUnit (R:=R)) p) (wordEntry imaginaryUnit p)=
      (fun x y => if x=y then 1 else 0) := by
    funext u v; rw [PhysicalAntiQuartic.physicalWordProduct imaginaryUnit imaginaryUnit_sq,PhysicalAntiQuartic.cocycleSelf,
      PhysicalAntiQuartic.labelSelf,unitEntry,Semiring.one_mul]
  rw [t,matrixIdentity]

theorem pauliIsometry {n : Nat} (r : Nat) (p : Word n) (z : Sites (Basis n) r → ComplexScalar R) :
    let xs := indices (qubitIndices n) r
    normSum xs (image xs (pauli r p) z)=normSum xs z :=
  PauliPairContraction.imageNorm _ _ (indicesNodup _ (HyperplaneIncidence.normalsNodup n) _)
    (indicesFull _ (@qubitIndicesComplete n) _) _ (pauliGram r p) z

theorem pauliAnti {n : Nat} (r : Nat) (odd : r%2=1) (p q : Word n) (ant : SymmetricDefect.anti p q=true)
    (x y : Sites (Basis n) r) :
    let xs := indices (qubitIndices n) r
    matMul xs (pauli (R:=R) r p) (pauli r q) x y= -matMul xs (pauli r q) (pauli r p) x y := by
  dsimp only; unfold pauli; rw [matrixComp,matrixComp]
  let M (a : Word n) := wordEntry (imaginaryUnit (R:=R)) a
  have anti : matMul (qubitIndices n) (M p) (M q)=fun u v => (-1)*matMul (qubitIndices n) (M q) (M p) u v := by
    funext u v
    have eq := PhysicalAntiQuartic.wordCommutation (imaginaryUnit (R:=R)) imaginaryUnit_sq p q u v
    simpa only [SymmetricDefect.chi,ant,SymmetricDefect.phase,ite_true] using eq
  change matrix (matMul (qubitIndices n) (M p) (M q)) r x y= -matrix _ r x y
  rw [anti,matrixScale,negativeOddPower r odd]; grind only

private theorem reSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=(f a).re+_; rw [re_add,ih]; rfl

theorem antiRealOrthogonal [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] {α : Type} (xs : List α) (P Q : α → α → ComplexScalar R)
    (hp : dagger P=P) (hq : dagger Q=Q)
    (anticommute : ∀ x y,matMul xs P Q x y= -matMul xs Q P x y) (v : α → ComplexScalar R) :
    realInner xs (image xs P v) (image xs Q v)=0 := by
  let Z (i : α) (_ : Unit) := v i
  let V (M : α → α → ComplexScalar R) := matMul xs M Z
  let prod (M N : α → α → ComplexScalar R) := matMul xs (dagger (V M)) (V N) () ()
  have realPart (M N) : (prod M N).re=realInner xs (fun i => V M i ()) (fun i => V N i ()) := reSum xs _
  have exp (M N) (hm : dagger M=M) : prod M N=matMul xs (dagger Z) (matMul xs (matMul xs M N) Z) () () := by
    unfold prod V; rw [PhysicalPairedReduction.daggerProduct,hm]; simp only [matMulAssoc]
  have negSum (f : α → ComplexScalar R) : sumOver xs (fun i => -f i)= -sumOver xs f := by
    have g := sumOverMulLeft xs f (-1); simpa only [Ring.neg_mul,Semiring.one_mul] using g.symm
  have opp : prod P Q= -prod Q P := by
    rw [exp P Q hp,exp Q P hq]
    change sumOver xs (fun i => star (v i)*sumOver xs (fun j => matMul xs P Q i j*v j))=_
    simp only [anticommute,Ring.neg_mul,negSum,Ring.mul_neg]; rfl
  have sym : realInner xs (fun i => V Q i ()) (fun i => V P i ())=realInner xs (fun i => V P i ()) (fun i => V Q i ()) := by
    apply sumOverCongr; intro i; simp only [re_mul,re_star,im_star]; grind only
  have t := congrArg ComplexScalar.re opp; rw [re_neg,realPart,realPart,sym] at t
  change realInner xs (fun i => V P i ()) (fun i => V Q i ())=0; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Homogeneous two-vector Bessel inequality. The state does not require
normalization, hence no square root of a Slater factorial is needed. -/
theorem homogeneousBessel {α : Type} (xs : List α) (z u v : α → ComplexScalar R) (m : R)
    (pos : 0<m) (nz : normSum xs z=m) (nu : normSum xs u=m) (nv : normSum xs v=m)
    (orth : realInner xs u v=0) :
    (realInner xs z u)^2+(realInner xs z v)^2≤m^2 := by
  let a := realInner xs z u
  let b := realInner xs z v
  let err i := ofReal m*z i-ofReal a*u i-ofReal b*v i
  have point (i : α) : normSq (err i)=m^2*normSq (z i)+a^2*normSq (u i)+b^2*normSq (v i)-
      (2*m*a)*(star (z i)*u i).re-(2*m*b)*(star (z i)*v i).re+(2*a*b)*(star (u i)*v i).re := by
    simp only [err,normSq,re_sub,im_sub,re_mul,im_mul,re_ofReal,im_ofReal,re_star,im_star]; grind only
  have p := Compression.sumOverNonnegative xs (fun i => normSq (err i)) (fun i _ => normSq_nonnegative _)
  rw [sumOverCongr xs point] at p
  simp only [sumOverAdd,Compression.sumOverSub,←sumOverMulLeft] at p
  change 0≤m^2*normSum xs z+a^2*normSum xs u+b^2*normSum xs v-
    2*m*a*a-2*m*b*b+2*a*b*realInner xs u v at p
  rw [nz,nu,nv,orth] at p
  change a^2+b^2≤m^2
  apply Classical.byContradiction; intro bad
  have e := OrderedRing.mul_pos pos (show 0<a^2+b^2-m^2 by grind only); grind only

def expectation {n : Nat} (r : Nat) (z : Sites (Basis n) r → ComplexScalar R) (p : Word n) :=
  let xs := indices (qubitIndices n) r
  realInner xs z (image xs (pauli r p) z)

/-- For every unnormalized state on an odd tensor power, the squared
expectations of the genuine repeated anticommuting Pauli matrices
sum to at most the squared state mass. -/
theorem pauliUncertainty {n : Nat} (r : Nat) (odd : r%2=1) (p q : Word n) (ant : SymmetricDefect.anti p q=true)
    (z : Sites (Basis n) r → ComplexScalar R) (pos : 0<normSum (indices (qubitIndices n) r) z) :
    (expectation r z p)^2+(expectation r z q)^2≤(normSum (indices (qubitIndices n) r) z)^2 :=
  homogeneousBessel _ z _ _ _ pos rfl (pauliIsometry r p z) (pauliIsometry r q z)
    (antiRealOrthogonal _ _ _ (pauliHerm r p) (pauliHerm r q) (pauliAnti r odd p q ant) z)

end Order

end RankSeven.OddTensorUncertainty

#print axioms RankSeven.OddTensorUncertainty.matrixComp
#print axioms RankSeven.OddTensorUncertainty.matrixDagger
#print axioms RankSeven.OddTensorUncertainty.pauliGram
#print axioms RankSeven.OddTensorUncertainty.pauliAnti
#print axioms RankSeven.OddTensorUncertainty.pauliIsometry
#print axioms RankSeven.OddTensorUncertainty.antiRealOrthogonal
#print axioms RankSeven.OddTensorUncertainty.homogeneousBessel
#print axioms RankSeven.OddTensorUncertainty.pauliUncertainty

