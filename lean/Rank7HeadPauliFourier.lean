import Rank7ThreeLegFourier
import Rank7SixPointRounding

/-! Pauli character transforms of the two physical head-label amplitudes. -/
namespace RankSeven.HeadPauliFourier
open Lean.Grind Pauli ComplexScalar SymmetricDefect
open PhysicalMixedFrame (pairs Pair)
open JointProbePayment (pairWeight pairAmplitude)
variable {R C α β : Type} [CommRing R] [CommRing C]

def element {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n) :=
  sumOver (pairs n) (fun e => (star (x e.1)*y e.2)*wordEntry imaginaryUnit p e.1 e.2)

private theorem sumPairs (xs : List α) (ys : List β) (f : α×β → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem cycle {n : Nat} (xs : List (Pair n)) (F : Word n → Pair n → Pair n → C) :
    sumOver (words n) (fun p => sumOver xs (fun e => sumOver xs (F p e)))=
      sumOver xs (fun e => sumOver xs (fun f => sumOver (words n) (fun p => F p e f))) := by
  rw [sumOverSwap]; apply sumOverCongr; intro e; rw [sumOverSwap]

private theorem crossed (xs : List α) (G H : α → α → C) :
    let ps := productIndices xs xs
    sumOver ps (fun e => sumOver ps (fun f => G e.1 f.2*H f.1 e.2))=
      sumOver ps (fun e => G e.1 e.2)*sumOver ps (fun e => H e.1 e.2) := by
  dsimp only; simp only [sumPairs]
  simp only [←sumOverMulRight]
  have h (a b) : sumOver xs (fun c => sumOver xs (G a)*H c b)=sumOver xs (G a)*sumOver xs (fun c => H c b) :=
    (sumOverMulLeft _ _ _).symm
  simp only [h,←sumOverMulLeft,←sumOverMulRight]
  rw [sumOverSwap xs xs (fun b c => H c b)]

theorem elementHermitian {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n) : star (element x y p)=element y x p := by
  unfold element; rw [ComplexExterior.starSumOver]
  unfold pairs; simp only [sumPairs]; rw [sumOverSwap]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b
  simp only [star_mul,star_star,ComplexPauliMoment.wordHermitian]; grind only

theorem elementFrame {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n) (i j : Fin m) :
    element (fun x => A x i) (fun x => A x j) p=PhysicalOddLeakage.compression A p i j := by
  unfold element pairs; rw [sumPairs]; apply sumOverCongr; intro a
  change _=star (A a i)*sumOver (qubitIndices n) (fun b => wordEntry imaginaryUnit p a b*A b j)
  rw [sumOverMulLeft]; apply sumOverCongr; intro b
  change star (A a i)*A b j*wordEntry imaginaryUnit p a b=star (A a i)*(wordEntry imaginaryUnit p a b*A b j)
  grind only

/-- Signed Pauli completeness polarized between arbitrary pure columns. -/
theorem mixedResolution {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n) :
    sumOver (words n) (fun v => chi p v*element x x v*element y y v)=
      (2:ComplexScalar R)^n*(element x y p*element y x p) := by
  let P (q : Word n) := wordEntry (imaginaryUnit (R:=R)) q
  let ps := pairs n
  let cx (e : Pair n) := star (x e.1)*x e.2
  let cy (e : Pair n) := star (y e.1)*y e.2
  let g a b := star (x a)*y b*P p a b
  let h a b := star (y a)*x b*P p a b
  let d := (2:ComplexScalar R)^n
  have expand (v : Word n) : chi p v*element x x v*element y y v =
      sumOver ps (fun e => sumOver ps (fun f => cx e*cy f*(chi p v*P v e.1 e.2*P v f.1 f.2))) := by
    unfold element
    change (chi p v*sumOver ps (fun e => cx e*P v e.1 e.2))*sumOver ps (fun f => cy f*P v f.1 f.2)=_
    rw [sumOverMulLeft ps (fun e => cx e*P v e.1 e.2) (chi p v),sumOverMulRight]; apply sumOverCongr; intro e; rw [sumOverMulLeft]; apply sumOverCongr; intro f; grind only
  have ft (e f : Pair n) := signedResolution (imaginaryUnit (R:=R)) imaginaryUnit_sq p e.1 e.2 f.1 f.2
  change sumOver _ _=d*(sumOver ps (fun e => g e.1 e.2)*sumOver ps (fun e => h e.1 e.2))
  have cr := crossed (qubitIndices n) g h
  change sumOver ps (fun e => sumOver ps (fun f => g e.1 f.2*h f.1 e.2))=sumOver ps (fun e => g e.1 e.2)*sumOver ps (fun e => h e.1 e.2) at cr
  rw [sumOverCongr _ expand,cycle,←cr]
  change _=d*sumOver ps (fun e => sumOver ps (fun f => g e.1 f.2*h f.1 e.2))
  rw [sumOverMulLeft]; apply sumOverCongr; intro e; rw [sumOverMulLeft]; apply sumOverCongr; intro f
  rw [←sumOverMulLeft]; have k := ft e f
  change sumOver _ (fun v => chi p v*P v e.1 e.2*P v f.1 f.2)=d*P p e.1 f.2*P p f.1 e.2 at k
  rw [k]; dsimp only [cx,cy,g,h]; grind only

theorem transposeExpectation {n : Nat} (x : Basis n → ComplexScalar R) (p : Word n) :
    element (fun i => star (x i)) (fun i => star (x i)) p=wordSign p*element x x p := by
  unfold element pairs; simp only [sumPairs,star_star]
  rw [sumOverSwap,sumOverMulLeft]; apply sumOverCongr; intro a; rw [sumOverMulLeft]; apply sumOverCongr; intro b
  rw [wordEntryTranspose imaginaryUnit p a b]; grind only

theorem physicalAntiAmplitude {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (i j : Fin 7) :
    element (fun a => star (A a j)) (fun a => A a i) p=pairAmplitude A p i j := by
  unfold element pairAmplitude pairs; simp only [sumPairs,star_star,PhysicalMixedFrame.dual]
  rw [sumOverSwap]; apply sumOverCongr; intro a; apply sumOverCongr; intro b; grind only

def expectation {n : Nat} (x : Basis n → ComplexScalar R) (p : Word n) := (element x x p).re

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem realExpect {n : Nat} (x : Basis n → ComplexScalar R) (p : Word n) : element x x p=ofReal (expectation x p) := by
  have h := congrArg ComplexScalar.im (elementHermitian x x p)
  rw [im_star] at h; apply ComplexScalar.ext
  · rfl
  · change (element x x p).im=0; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum {a : Type} (xs : List a) (f : a → ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=_; rw [re_add,ih]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem realChi {n : Nat} (p q : Word n) : (chi p q : ComplexScalar R)=ofReal (chi p q : R) := by
  unfold chi phase; cases anti p q <;> simp <;> apply ComplexScalar.ext <;> simp <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem castSign {n : Nat} (p : Word n) : (wordSign p : ComplexScalar R)=ofReal (wordSign p : R) := by
  induction p with
  | empty => rfl
  | cons a p ih =>
    cases a <;> simp only [wordSign,axisSign,ih]
    all_goals apply ComplexScalar.ext <;> simp <;> grind only

/-- Both ordinary and transpose-twisted transforms are actual physical
matrix-element probabilities. -/
theorem realResolution {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n) :
    sumOver (words n) (fun v => chi p v*expectation x v*expectation y v)=(2:R)^n*normSq (element x y p) := by
  have e := congrArg ComplexScalar.re (mixedResolution x y p)
  rw [reSum] at e
  have each (v : Word n) : ((chi p v:ComplexScalar R)*element x x v*element y y v).re=chi p v*expectation x v*expectation y v := by
    rw [realChi,realExpect x,realExpect y]
    simp only [re_mul,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,Semiring.mul_zero]; grind only
  rw [sumOverCongr _ each] at e
  have eq (z : ComplexScalar R) : z*star z=ofReal (normSq z) := by rw [←star_mul_self]; grind only
  rw [←elementHermitian x y p,eq] at e
  change _=((ofReal (2:R))^n*ofReal (normSq (element x y p))).re at e
  rw [←PhysicalPairedReduction.realEmbeddingPow] at e; simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul] at e; grind only

theorem signedResolutionOfFrame {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (i j : Fin 7) (p : Word n) :
    sumOver (words n) (fun v => chi p v*wordSign v*expectation (fun a => A a i) v*expectation (fun a => A a j) v)=
      (2:R)^n*pairWeight A p i j := by
  let x a := A a i
  let y a := A a j
  have e := realResolution (fun a => star (y a)) x p
  have each (v : Word n) : chi p v*expectation (fun a => star (y a)) v*expectation x v=
      chi p v*wordSign v*expectation x v*expectation y v := by
    unfold expectation; rw [transposeExpectation,castSign]; simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only
  rw [sumOverCongr _ each] at e
  change _=(2:R)^n*normSq (element (fun a => star (A a j)) (fun a => A a i) p) at e
  rw [physicalAntiAmplitude] at e; exact e

def fourier {n : Nat} (f : Word n → R) (p : Word n) := sumOver (words n) (fun v => chi p v*f v)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem oddIndicator {a : Type} (xs : List a) (flag : a → Bool) (f : a → R) :
    2*sumOver (xs.filter flag) f=sumOver xs f-sumOver xs (fun v => phase (flag v)*f v) := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons q xs ih => rw [List.filter_cons]; cases e : flag q <;> simp [e,phase,sumOver] at ih ⊢ <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sqSum {a : Type} (xs : List a) (f : a → R) :
    (sumOver xs f)^2=sumOver xs (fun u => sumOver xs (fun v => f u*f v)) := by
  rw [Semiring.pow_two,sumOverMulRight]; apply sumOverCongr; intro u; exact sumOverMulLeft _ _ _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- Signed Parseval for an arbitrary real Pauli coefficient product.
The transpose-Gauss correction is its ordinary Fourier quadratic form. -/
theorem oddTwistedParseval {n : Nat} (F : Word n → R) :
    2*sumOver (MixedDefect.oddWords n) (fun p => (fourier (fun v => wordSign v*F v) p)^2)=
      (4:R)^n*sumOver (words n) (fun v => (F v)^2)-(2:R)^n*sumOver (words n) (fun v => F v*fourier F v) := by
  let ws := words n
  let G v := wordSign v*F v
  have gs (v : Word n) : (G v)^2=(F v)^2 := by have e := wordSignSquare (C:=R) v; unfold G; grind only
  have full := fourierParseval G
  change sumOver ws (fun p => (fourier G p)^2)=(4:R)^n*sumOver ws (fun p => (G p)^2) at full
  change 2*sumOver (ws.filter MixedDefect.oddWord) (fun p => (fourier G p)^2)=_
  rw [oddIndicator,full,sumOverCongr _ gs]
  congr 1
  have factor (p : Word n) : phase (MixedDefect.oddWord p)*(fourier G p)^2=
      sumOver ws (fun a => sumOver ws (fun b => (wordSign p : R)*chi p a*chi p b*(G a*G b))) := by
    rw [←MixedDefect.oddWordTransposeSign]; unfold fourier; rw [sqSum,sumOverMulLeft]
    apply sumOverCongr; intro a; rw [sumOverMulLeft]; apply sumOverCongr; intro b; grind only
  rw [sumOverCongr _ factor,sumOverSwap ws ws]; unfold fourier; rw [sumOverMulLeft]; apply sumOverCongr; intro a
  rw [sumOverSwap,sumOverMulLeft,sumOverMulLeft]; apply sumOverCongr; intro b
  rw [←sumOverMulRight]
  have e := MixedDefect.transposeGauss (C:=R) a b
  rw [e]; have sa := wordSignSquare (C:=R) a; have sb := wordSignSquare (C:=R) b
  dsimp only [G]; grind only

def firstThree {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (x : Basis n) (i : Fin 3) := A x (PhysicalOddLeakage.sublabel 2 i)

def localH {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) := PhysicalOddLeakage.compression (firstThree A) p

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem diag (A : Basis n → Fin m → ComplexScalar R) (i : Fin m) (v : Word n) :
    (PhysicalOddLeakage.compression A v i i).re=expectation (fun a => A a i) v := congrArg ComplexScalar.re (elementFrame A v i i).symm

theorem ordinaryTransforms {n : Nat} (A : Basis n → Fin 3 → ComplexScalar R) (p : Word n) :
    let H v := PhysicalOddLeakage.compression A v
    let d := (2:R)^n
    fourier (fun v => ThreeLegFourier.head (H v)*ThreeLegFourier.middle (H v)) p=d*ThreeLegFourier.crossWeight (H p) ∧
    fourier (fun v => (ThreeLegFourier.head (H v))^2) p=d*(ThreeLegFourier.head (H p))^2 ∧
    fourier (fun v => (ThreeLegFourier.middle (H v))^2) p=d*(2-ThreeLegFourier.middleLoss (H p)) := by
  let H := PhysicalOddLeakage.compression A
  let a (i : Fin 3) v := expectation (fun x => A x i) v
  let d := (2:R)^n
  have f (i j : Fin 3) : fourier (fun v => a i v*a j v) p=d*normSq (H p i j) := by
    have e := realResolution (fun x => A x i) (fun x => A x j) p
    rw [elementFrame] at e
    unfold fourier; exact (sumOverCongr _ (fun v => by dsimp only [a]; grind only)).trans e
  have add (u v : Word n → R) : fourier (fun i => u i+v i) p=fourier u p+fourier v p := by
    unfold fourier; simp only [Semiring.left_distrib,sumOverAdd]
  have row (i : Fin 3) (p : Word n) : (H p i i).re=a i p := diag A i p
  have q (v : Word n) : a 0 v*(a 1 v+a 2 v)=a 1 v*a 0 v+a 2 v*a 0 v := by grind only
  have sq (v : Word n) : (a 1 v+a 2 v)^2=a 1 v*a 1 v+a 1 v*a 2 v+(a 2 v*a 1 v+a 2 v*a 2 v) := by grind only
  have real : normSq (H p 0 0)=(a 0 p)^2 := by
    have c := realExpect (fun x => A x 0) p; rw [elementFrame] at c
    change H p 0 0=ofReal (a 0 p) at c; rw [c,normSq_ofReal]
  dsimp only
  change fourier (fun v => (H v 0 0).re*((H v 1 1).re+(H v 2 2).re)) p=d*ThreeLegFourier.crossWeight (H p) ∧
    fourier (fun v => (H v 0 0).re^2) p=d*(H p 0 0).re^2 ∧
    fourier (fun v => ((H v 1 1).re+(H v 2 2).re)^2) p=d*(2-ThreeLegFourier.middleLoss (H p))
  simp only [row,q,sq,add,f,ThreeLegFourier.crossWeight,ThreeLegFourier.middleLoss,Semiring.pow_two]
  have h := f 0 0; rw [real] at h; grind only

theorem twistedHead {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    fourier (fun v => wordSign v*(ThreeLegFourier.head (localH A v)*ThreeLegFourier.middle (localH A v))) p=
      (2:R)^n*SixPointRounding.headWeight A p := by
  let a (i : Fin 7) v := expectation (fun x => A x i) v
  let H := localH A
  have f (v : Word n) : ThreeLegFourier.head (H v)=a 0 v ∧ ThreeLegFourier.middle (H v)=a 1 v+a 2 v := by
    have r (i : Fin 3) := diag (firstThree A) i v
    exact ⟨r 0,by change (PhysicalOddLeakage.compression (firstThree A) v 1 1).re+(PhysicalOddLeakage.compression (firstThree A) v 2 2).re=_; rw [r 1,r 2]; rfl⟩
  have s (i : Fin 7) := signedResolutionOfFrame A 0 i p
  let flag (i : Fin 7) v := (chi p v : R)*wordSign v*a 0 v*a i v
  have e (v : Word n) : chi p v*(wordSign v*(ThreeLegFourier.head (H v)*ThreeLegFourier.middle (H v)))=flag 1 v+flag 2 v := by
    rw [(f v).1,(f v).2]; dsimp only [flag]; grind only
  change sumOver (words n) _=_; rw [sumOverCongr _ e,sumOverAdd]
  change sumOver (words n) (flag 1)+sumOver (words n) (flag 2)=(2:R)^n*(pairWeight A p 0 1+pairWeight A p 0 2)
  have t (i : Fin 7) : sumOver (words n) (flag i)=(2:R)^n*pairWeight A p 0 i := s i
  rw [t,t]; grind only

end Order

end RankSeven.HeadPauliFourier

#print axioms RankSeven.HeadPauliFourier.mixedResolution
#print axioms RankSeven.HeadPauliFourier.transposeExpectation
#print axioms RankSeven.HeadPauliFourier.realResolution
#print axioms RankSeven.HeadPauliFourier.signedResolutionOfFrame
#print axioms RankSeven.HeadPauliFourier.oddTwistedParseval
#print axioms RankSeven.HeadPauliFourier.ordinaryTransforms
#print axioms RankSeven.HeadPauliFourier.twistedHead

