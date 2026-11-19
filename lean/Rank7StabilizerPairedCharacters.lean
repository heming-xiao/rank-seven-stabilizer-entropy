import Rank7StabilizerPopulationRounding

namespace RankSeven.StabilizerPairedCharacters

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform StabilizerPopulationRounding
open PhysicalCompressionEffect (OrthonormalFrame)
open HeadPauliFourier (localH)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

noncomputable def representative {n : Nat} {G : MaximalFamily n} (T : Transversal G) (v : Word n) : Word n :=
  (T.cover v).choose

theorem represents {n : Nat} {G : MaximalFamily n} (T : Transversal G) (v : Word n) :
    representative T v∈T.reps ∧ equiv G v (representative T v) := (T.cover v).choose_spec

theorem charConstant {n : Nat} {G : MaximalFamily n} {a b : Word n} (same : equiv G a b) (g : Word n) (hg : g∈G.labels) :
    (chi a g:R)=chi b g := by
  have h := (G.criterion _).mp same g hg; rw [antiAddLeft] at h
  cases x : anti a g <;> cases y : anti b g <;> simp [x,y,chi] at h ⊢

def transform {n : Nat} (half : R) (G : MaximalFamily n) (f : Word n → R) (a : Word n) :=
  half^n*sumOver G.labels (fun g => chi a g*f g)

theorem shifted {n : Nat} (half : R) {G : MaximalFamily n} (T : Transversal G) (f : Word n→R) (a t : Word n) :
    transform half G f (representative T (wordAdd a t))=transform half G (fun g => chi t g*f g) a := by
  unfold transform; congr 1; apply AnticommutingDefect.sumCongrMem; intro g hg
  rw [←charConstant (represents T _).2 g hg,chiSymm (wordAdd a t) g,characterAddRight g a t,chiSymm g a,chiSymm g t]
  grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem transformProduct {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f u : Word n → R) : sumOver T.reps (fun a => transform half G f a*transform half G u a)=
    half^n*sumOver G.labels (fun g => f g*u g) := by
  let F := transform half G f
  let U := transform half G u
  have add (a : Word n) : transform half G (fun g => f g+u g) a=F a+U a := by
    unfold F U transform; simp only [Semiring.left_distrib,sumOverAdd]
  have s := parseval half h2 T (fun g => f g+u g)
  change sumOver T.reps (fun a => (transform half G (fun g => f g+u g) a)^2)=_ at s
  have p (a : Word n) : (F a+U a)^2=(F a)^2+(U a)^2+2*(F a*U a) := by grind only
  have q (g : Word n) : (f g+u g)^2=(f g)^2+(u g)^2+2*(f g*u g) := by grind only
  simp only [add,p,q,sumOverAdd,←sumOverMulLeft] at s
  have fc : sumOver T.reps (fun a => (F a)^2)=_ := parseval half h2 T f
  have uc : sumOver T.reps (fun a => (U a)^2)=_ := parseval half h2 T u
  change sumOver T.reps (fun a => F a*U a)=half^n*sumOver G.labels (fun g => f g*u g)
  grind only

theorem inversion {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f : Word n → R) (g : Word n) (hg : g∈G.labels) :
    sumOver T.reps (fun a => chi a g*transform half G f a)=f g := by
  let point (p : Word n) := if g=p then (2:R)^n else 0
  have one (a : Word n) : transform half G point a=chi a g := by
    unfold transform
    have e (p : Word n) : chi a p*point p=if g=p then chi a p*(2:R)^n else 0 := by
      by_cases h : g=p <;> simp [point,h] <;> grind only
    rw [sumOverCongr _ e,ExteriorPauliBase.sumOnIndex G.labels g _ G.nodup hg]
    have inv := SectorDefectAccounting.dimensionInverse half h2 n; grind only
  have tr := transformProduct half h2 T point f
  rw [sumOverCongr T.reps (fun a => congrArg (fun z => z*transform half G f a) (one a))] at tr
  rw [tr]
  have e (p : Word n) : point p*f p=if g=p then (2:R)^n*f p else 0 := by by_cases h : g=p <;> simp [point,h] <;> grind only
  rw [sumOverCongr _ e,ExteriorPauliBase.sumOnIndex G.labels g _ G.nodup hg]
  have inv := SectorDefectAccounting.dimensionInverse half h2 n; grind only

theorem pairedSquare {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (t : Word n) (f : Word n→R) :
    sumOver T.reps (fun a => transform half G f a*(transform half G f a+transform half G f (representative T (wordAdd a t))))=
      2*half^n*sumOver G.labels (fun g => if anti t g then 0 else (f g)^2) := by
  let u g := chi t g*f g
  let F := transform half G f
  let U := transform half G u
  have entry (a : Word n) : F a*(F a+transform half G f (representative T (wordAdd a t)))=(F a)^2+F a*U a := by
    rw [shifted half T]; change F a*(F a+U a)=(F a)^2+F a*U a; grind only
  change sumOver T.reps (fun a => F a*(F a+transform half G f (representative T (wordAdd a t))))=_
  rw [sumOverCongr _ entry,sumOverAdd]
  have p : sumOver T.reps (fun a => (F a)^2)=half^n*sumOver G.labels (fun g => (f g)^2) := parseval half h2 T f
  have q : sumOver T.reps (fun a => F a*U a)=half^n*sumOver G.labels (fun g => f g*u g) := transformProduct half h2 T f u
  rw [p,q,←Semiring.left_distrib,←sumOverAdd]
  have e (g : Word n) : (f g)^2+f g*u g=2*(if anti t g then 0 else (f g)^2) := by
    cases h : anti t g <;> simp [u,chi,phase,h] <;> grind only
  rw [sumOverCongr _ e,←sumOverMulLeft]; grind only

attribute [local instance] Semiring.natCast

theorem halfGroup {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (t : Word n) (ht : t∉G.labels) :
    2*half^n*sumOver G.labels (fun g => if anti t g then (0:R) else 1)=1 := by
  have e := HeavyPauliGroup.characterSum (R:=R) G t; rw [ite_eq_right ht] at e
  have constant : sumOver G.labels (fun _ => (1:R))=(2:R)^n := by
    have s (xs : List (Word n)) : sumOver xs (fun _ => (1:R))=@Nat.cast R Semiring.natCast xs.length := by
      induction xs with
      | nil => change 0=Nat.cast 0; rw [Semiring.natCast_zero]
      | cons a xs ih => change 1+sumOver xs _=Nat.cast (xs.length+1); rw [ih,Semiring.natCast_succ]; grind only
    rw [s,cardinalCast (R:=R)]
  have a (g : Word n) : 1+(chi t g:R)=2*(if anti t g then 0 else 1) := by cases h : anti t g <;> simp [chi,phase,h] <;> grind only
  have eq := sumOverCongr G.labels a; rw [sumOverAdd,←sumOverMulLeft,constant,e] at eq
  have inv := SectorDefectAccounting.dimensionInverse half h2 n; grind only

/-- The coarse six-point rate uses only the off-group defect and the first
character region. No estimate on the centralizer complement is needed. -/
theorem coarseErrors (kappa D e f delta : R) (small : 200*kappa≤11) (fn : 0≤f)
    (off : 12*D+e≤60*kappa) (regions : e+4*(1-e)^2*f≤2*D) (angle : 2*delta≤3*(e+2*f)) :
    5*(e+2*f)<3 ∧ 411*delta<378 := by
  have m := OrderedRing.mul_nonneg (squareNonnegative (1-e)) fn
  have pos : 0≤1-2*e := by grind only
  have cubic := OrderedRing.mul_nonneg (squareNonnegative e) pos
  have sq := squareNonnegative (252*e-97)
  have cap : 5*(e+2*f)<3 := by
    apply Classical.byContradiction; intro no
    have excess := OrderedRing.mul_nonneg (squareNonnegative (1-e)) (show 0≤5*(e+2*f)-3 by grind only)
    grind only
  exact ⟨cap,by grind only⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem headFourier {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (A : Basis n→Fin 7→ComplexScalar R)
    (a : Word n) : pop half L a (fun i => A i 0)=transform half G (fun g => phase (L.sign g)*ThreeLegFourier.head (localH A g)) a := by
  rw [popFourier]; unfold transform; congr 1; apply sumOverCongr; intro g
  have e := congrArg ComplexScalar.re (HeadPauliFourier.elementFrame (HeadPauliFourier.firstThree A) g 0 0)
  change HeadPauliFourier.expectation (fun i => A i 0) g=ThreeLegFourier.head (localH A g) at e; rw [e]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem columnNorm {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (i : Fin 7) :
    PauliPairContraction.normSum (qubitIndices n) (fun x => A x i)=1 := by
  have eq := congrArg ComplexScalar.re (orth i i)
  have reSum {α : Type} (xs : List α) (f : α→ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun a => (f a).re) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => change (f a+sumOver xs f).re=_; rw [re_add,ih]; rfl
  unfold PauliPairContraction.normSum; simpa only [reSum,ite_true,re_one,re_star_mul_self] using eq

def headPop {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :=
  pop half L a (fun i => A i 0)
noncomputable def pairedHead {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (A : Basis n→Fin 7→ComplexScalar R)
    (t a : Word n) := headPop half L A a+headPop half L A (representative T (wordAdd a t))

private theorem maxOn {α : Type} (xs : List α) (f : α→R) (h : xs≠[]) : ∃x∈xs,∀y∈xs,f y≤f x := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases empty : xs=[]
    · subst xs; exact ⟨x,List.mem_cons_self,by simp⟩
    · obtain ⟨y,hy,large⟩ := ih empty
      by_cases le : f y≤f x
      · refine ⟨x,List.mem_cons_self,?_⟩; intro z hz
        cases List.mem_cons.mp hz with
        | inl e => rw [e]; exact Std.le_refl _
        | inr e => exact Std.le_trans (large z e) le
      · refine ⟨y,List.mem_cons_of_mem x hy,?_⟩; intro z hz
        cases List.mem_cons.mp hz with
        | inl e => rw [e]; grind only
        | inr e => exact large z e

private theorem sumLe {α : Type} (xs : List α) (f h : α→R) (e : ∀i∈xs,f i≤h i) : sumOver xs f≤sumOver xs h := by
  have q := Compression.sumOverNonnegative xs (fun i => h i-f i) (fun i hi => by have := e i hi; grind only)
  rw [Compression.sumOverSub] at q; grind only

theorem firstCharacterRegion {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (t : Word n) (ht : t∉G.labels) :
    ∃c∈T.reps,(∀a∈T.reps,pairedHead half L T A t a≤pairedHead half L T A t c) ∧
      1-pairedHead half L T A t c≤2*half^n*sumOver G.labels (fun g => if anti t g then 0 else 1-(ThreeLegFourier.head (localH A g))^2) := by
  let H := headPop half L A
  let V := pairedHead half L T A t
  let r g := ThreeLegFourier.head (localH A g)
  let f g := phase (L.sign g)*r g
  have tf : ∀a,H a=transform half G f a := headFourier half L A
  have one : sumOver T.reps H=1 := (popTotal half h2 L T _).trans (columnNorm A orth 0)
  have arg := (represents T t).1
  obtain ⟨c,hc,cap⟩ := maxOn T.reps V (by intro e; rw [e] at arg; contradiction)
  refine ⟨c,hc,cap,?_⟩
  have b := sumLe T.reps (fun a => H a*V a) (fun a => H a*V c) (fun a ha =>
    OrderedRing.mul_le_mul_of_nonneg_left (cap a ha) (popNonnegative half h2 L a _))
  rw [←sumOverMulRight,one,Semiring.one_mul] at b
  have p := pairedSquare half h2 T t f
  have fe (g : Word n) : (f g)^2=(r g)^2 := by cases e : L.sign g <;> simp [f,e,phase] <;> grind only
  rw [show transform half G f=H from (funext tf).symm] at p
  simp only [fe] at p
  change sumOver T.reps (fun a => H a*V a)=_ at p
  have s (g : Word n) : (if anti t g then 0 else 1-(r g)^2)=(if anti t g then 0 else 1)-(if anti t g then 0 else (r g)^2) := by
    cases anti t g <;> simp <;> grind only
  have oneH := halfGroup (R:=R) half h2 (G:=G) t ht
  change 1-V c≤2*half^n*sumOver G.labels (fun g => if anti t g then 0 else 1-(r g)^2)
  rw [sumOverCongr _ s,Compression.sumOverSub]; grind only

theorem mateDifferent {n : Nat} {G : MaximalFamily n} (T : Transversal G) (t : Word n) (ht : t∉G.labels) (a : Word n) :
    a≠representative T (wordAdd a t) := by
  intro e; have q := (represents T (wordAdd a t)).2; rw [←e] at q
  change wordAdd (wordAdd a t) a∈G.labels at q; rw [wordAddComm a t,wordAddCancel] at q; exact ht q

private theorem sumPairLe {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup) (a b : α)
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) (m : α→R) (nn : ∀i∈xs,0≤m i) : m a+m b≤sumOver xs m := by
  have p := sumLe xs (fun j => (if a=j then m j else 0)+(if b=j then m j else 0)) m (fun j hj => by
    have n := nn j hj; by_cases e : a=j <;> by_cases h : b=j <;> simp only [e,h,ite_true,ite_false] <;> grind only)
  rw [sumOverAdd,ExteriorPauliBase.sumOnIndex xs a m nd ha,ExteriorPauliBase.sumOnIndex xs b m nd hb] at p; exact p

theorem pairedHeadBounds {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (t a : Word n) (ht : t∉G.labels) (ha : a∈T.reps) :
    0≤pairedHead half L T A t a ∧ pairedHead half L T A t a≤1 := by
  let H := headPop half L A
  let b := representative T (wordAdd a t)
  have nn (p : Word n) : 0≤H p := popNonnegative half h2 L p _
  have bds := sumPairLe T.reps T.nodup a b ha (represents T _).1 (mateDifferent T t ht a) H (fun i _ => nn i)
  have total : sumOver T.reps H=1 := (popTotal half h2 L T _).trans (columnNorm A orth 0)
  have h := nn a; have j := nn b
  change 0≤H a+H b ∧ H a+H b≤1; grind only

theorem middleStable {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (a b : Word n) (ha : a∈T.reps) (hb : b∈T.reps)
    (ne : a≠b) (g : Word n) (hg : g∈G.labels) (ag : anti (wordAdd a b) g=false)
    (close : 1≤middlePop half L a A+middlePop half L b A) :
    4*(middlePop half L a A+middlePop half L b A-1)^2≤(ThreeLegFourier.middle (localH A g))^2 := by
  let m i := middlePop half L i A
  let u g := ThreeLegFourier.middle (localH A g)
  let tau (i : Word n) : R := chi i g
  let wt (i : Word n) := (if a=i then m i else 0)+(if b=i then m i else 0)
  have same : tau a=tau b := by
    rw [antiAddLeft] at ag; unfold tau chi; cases x : anti a g <;> cases y : anti b g <;> simp [x,y] at ag ⊢
  have val (i : Word n) : tau i=1 ∨ tau i= -1 := by cases h : anti i g <;> simp [tau,chi,phase,h]
  have point (i : Word n) : 2*wt i-m i≤tau a*(tau i*m i) := by
    have nn : 0≤m i := (middleBounds half h2 L i A orth).1
    by_cases eq : a=i
    · subst i; simp only [wt,ite_true,Ne.symm ne,ite_false]; rcases val a with h|h <;> rw [h] <;> grind only
    · by_cases eb : b=i
      · subst i; simp only [wt,ne,ite_false,ite_true]; rw [same]; rcases val b with h|h <;> rw [h] <;> grind only
      · simp only [wt,eq,eb,ite_false]; rcases val a with h|h <;> rcases val i with j|j <;> rw [h,j] <;> grind only
  have s := sumLe T.reps _ _ (fun i _ => point i)
  have v : sumOver T.reps wt=m a+m b := by
    unfold wt; rw [sumOverAdd,ExteriorPauliBase.sumOnIndex _ _ _ T.nodup ha,ExteriorPauliBase.sumOnIndex _ _ _ T.nodup hb]
  have total : sumOver T.reps m=2 := middleTotal half h2 L T A orth
  rw [Compression.sumOverSub,←sumOverMulLeft,←sumOverMulLeft,v,total] at s
  have inv := inversion half h2 T (fun p => phase (L.sign p)*u p) g hg
  have ft (p : Word n) : transform half G (fun p => phase (L.sign p)*u p) p=m p := (middleFourier half L p A).symm
  simp only [ft] at inv
  change sumOver T.reps (fun p => tau p*m p)=phase (L.sign g)*u g at inv; rw [inv] at s
  have ph : (phase (L.sign g):R)=1 ∨ (phase (L.sign g):R)= -1 := by cases L.sign g <;> simp [phase]
  have lo : 0≤2*(m a+m b-1) := by change 1≤m a+m b at close; grind only
  let z := tau a*(phase (L.sign g)*u g)
  have low : 2*(m a+m b-1)≤z := by dsimp only [z]; grind only
  have prod := OrderedRing.mul_nonneg (show 0≤z-2*(m a+m b-1) by grind only) (show 0≤z+2*(m a+m b-1) by grind only)
  have zz : z^2=(u g)^2 := by dsimp only [z]; rcases val a with h|h <;> rcases ph with q|q <;> rw [h,q] <;> grind only
  have finish (x y v : R) (p : 0≤(y-2*x)*(y+2*x)) (q : y^2=v^2) : 4*x^2≤v^2 := by grind only
  exact finish (m a+m b-1) z (u g) prod zz

end Order

end RankSeven.StabilizerPairedCharacters

#print axioms RankSeven.StabilizerPairedCharacters.inversion
#print axioms RankSeven.StabilizerPairedCharacters.pairedSquare
#print axioms RankSeven.StabilizerPairedCharacters.halfGroup
#print axioms RankSeven.StabilizerPairedCharacters.middleStable
#print axioms RankSeven.StabilizerPairedCharacters.firstCharacterRegion
#print axioms RankSeven.StabilizerPairedCharacters.coarseErrors

