import Rank7StabilizerCosetTransform

namespace RankSeven.StabilizerPopulationRounding

open Lean.Grind Pauli ComplexScalar SymmetricDefect HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open SlaterUnionBound (energy)
open HeadPauliFourier (expectation element firstThree localH)
open PhysicalPairedReduction (dagger)
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliPairContraction (normSum image)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def pop {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n) (x : Basis n→ComplexScalar R) :=
  energy (qubitIndices n) (block half L a) x

def middlePop {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) :=
  pop half L a (fun t => A t 1)+pop half L a (fun t => A t 2)

private theorem reSum {α : Type} (xs : List α) (f : α→ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=_; rw [re_add,ih]; rfl

private theorem elements {n : Nat} (x : Basis n→ComplexScalar R) (p : Word n) :
    element x x p=sumOver (qubitIndices n) (fun i => star (x i)*StabilizerCharacterBasis.act p x i) := by
  exact HeadPauliFourier.elementFrame (fun t (_ : Fin 1) => x t) p 0 0

theorem popFourier {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n) (x : Basis n→ComplexScalar R) :
    pop half L a x=half^n*sumOver G.labels (fun p => (chi a p:R)*(phase (L.sign p)*expectation x p)) := by
  let xs := qubitIndices n
  let h := (ofReal half)^n
  let c (p : Word n) : ComplexScalar R := chi a p*phase (L.sign p)
  have eq (i : Basis n) : sumOver xs (fun j => block half L a i j*x j)=
      h*sumOver G.labels (fun p => c p*StabilizerCharacterBasis.act p x i) := by
    unfold block raw lifted; simp only [h,Semiring.mul_assoc,sumOverMulRight,sumOverMulLeft]
    rw [sumOverSwap]; apply sumOverCongr; intro p
    unfold StabilizerCharacterBasis.act; simp only [sumOverMulLeft]; apply sumOverCongr; intro j; unfold c; grind only
  have ev : sumOver xs (fun i => star (x i)*sumOver xs (fun j => block half L a i j*x j))=
      h*sumOver G.labels (fun p => c p*element x x p) := by
    simp only [eq,elements,sumOverMulLeft]; rw [sumOverSwap]
    apply sumOverCongr; intro p; apply sumOverCongr; intro i; grind only
  change (sumOver xs (fun i => star (x i)*sumOver xs (fun j => block half L a i j*x j))).re=_
  rw [ev]; have ch : h=ofReal (half^n) := (PhysicalPairedReduction.realEmbeddingPow _ _).symm
  have sub0 (u : R) : u-0=u := by grind only
  rw [ch]; simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,sub0,reSum]
  congr 1; apply sumOverCongr; intro p
  unfold c chi expectation phase; cases anti a p <;> cases L.sign p <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,re_mul,im_mul,re_neg,im_neg,re_one,im_one] <;> grind only

private theorem unitExpect {n : Nat} (x : Basis n→ComplexScalar R) :
    expectation x (unitWord n)=normSum (qubitIndices n) x := by
  unfold expectation normSum; rw [elements]; simp only [actIdentity,reSum,re_star_mul_self]

theorem popTotal {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (x : Basis n→ComplexScalar R) [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] :
    sumOver T.reps (fun a => pop half L a x)=normSum (qubitIndices n) x := by
  simp only [popFourier]; rw [transformSum half h2 T,L.identity,unitExpect]; simp only [phase,Bool.false_eq_true,ite_false,Semiring.one_mul]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem popNonnegative {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n) (x : Basis n→ComplexScalar R) :
    0≤pop half L a x := SlaterUnionBound.energyNonnegative _ ⟨Basis n,qubitIndices n,block half L a,(blockIsometry half h2 L a).symm⟩ x

theorem populationBessel {n m : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→Fin m→ComplexScalar R) (orth : ∀ i j,sumOver (qubitIndices n) (fun x => star (A x i)*A x j)=if i=j then 1 else 0) :
    sumOver (List.finRange m) (fun j => pop half L a (fun x => A x j))≤1 := by
  let xs := qubitIndices n
  let B := block half L a
  let fs := List.finRange m
  have gram : matMul xs (dagger B) B=B := blockIsometry half h2 L a
  have herm (i j : Basis n) : star (B i j)=B j i := congrFun (congrFun (blockHerm (R:=R) half L a) j) i
  have pr (j : Fin m) : pop half L a (fun x => A x j)=sumOver xs (fun i => normSq (sumOver xs (fun t => B i t*A t j))) := by
    change energy xs B _=_
    conv => lhs; rw [←gram,SlaterUnionBound.energyGram]
    rfl
  have row (i : Basis n) :
      sumOver fs (fun j => normSq (sumOver xs (fun t => B i t*A t j)))≤sumOver xs (fun t => normSq (B t i)) := by
    have bb := PhysicalCutCapacities.frameBessel fs xs (List.nodup_finRange m) (fun j => List.mem_finRange j) A orth (fun t => B t i)
    have e (j : Fin m) : star (sumOver xs (fun t => star (A t j)*B t i))=sumOver xs (fun t => B i t*A t j) := by
      rw [ComplexExterior.starSumOver]; simp only [star_mul,star_star,herm]; apply sumOverCongr; intro t; grind only
    simp only [←e,normSq_star]; exact bb
  have col (i : Basis n) : sumOver xs (fun t => normSq (B t i))=(B i i).re := by
    have e := congrArg ComplexScalar.re (congrFun (congrFun gram i) i)
    change (sumOver xs (fun t => star (B t i)*B t i)).re=_ at e; simpa only [reSum,re_star_mul_self] using e
  rw [sumOverCongr _ pr,sumOverSwap]
  have b := Compression.sumOverNonnegative xs
    (fun i => sumOver xs (fun t => normSq (B t i))-sumOver fs (fun j => normSq (sumOver xs (fun t => B i t*A t j))))
    (fun i _ => by have := row i; grind only)
  rw [Compression.sumOverSub,sumOverCongr _ col,←reSum] at b
  have tr := blockTrace half h2 L a
  change sumOver xs (fun t => B t t)=1 at tr; rw [tr,re_one] at b; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem unitColumn {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (j : Fin 7) :
    normSum (qubitIndices n) (fun x => A x j)=1 := by
  have e := congrArg ComplexScalar.re (orth j j); simp only [ite_true,re_one,reSum,re_star_mul_self] at e; exact e

theorem middleTotal {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) : sumOver T.reps (fun a => middlePop half L a A)=2 := by
  unfold middlePop; rw [sumOverAdd,popTotal half h2 L T,popTotal half h2 L T,unitColumn A orth,unitColumn A orth]; grind only

theorem middleBounds {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) : 0≤middlePop half L a A ∧
      pop half L a (fun t => A t 0)+middlePop half L a A≤1 := by
  have fr (i j : Fin 3) := congrFun (congrFun (PhysicalFourierDefect.topThreeOrth A orth) i) j
  have b := populationBessel half h2 L a (firstThree A) fr
  have l : List.finRange 3=[0,1,2] := by decide
  rw [l] at b
  let v (j : Fin 7) := pop half L a (fun t => A t j)
  change v 0+(v 1+(v 2+0))≤1 at b
  have one : 0≤v 1 := popNonnegative half h2 L a _
  have two : 0≤v 2 := popNonnegative half h2 L a _
  change 0≤v 1+v 2 ∧ v 0+(v 1+v 2)≤1; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem middleFourier {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) :
    middlePop half L a A=half^n*sumOver G.labels (fun g => chi a g*(phase (L.sign g)*ThreeLegFourier.middle (localH A g))) := by
  unfold middlePop; rw [popFourier,popFourier]
  let v (j : Fin 7) g := expectation (fun t => A t j) g
  have e (g : Word n) (i : Fin 3) := congrArg ComplexScalar.re (HeadPauliFourier.elementFrame (firstThree A) g i i)
  have m (g : Word n) : ThreeLegFourier.middle (localH A g)=v 1 g+v 2 g := by
    have one : (localH A g 1 1).re=v 1 g := (e g 1).symm
    have two : (localH A g 2 2).re=v 2 g := (e g 2).symm
    exact congrArg (fun z => z+_) one |>.trans (congrArg (fun z => _+z) two)
  rw [←Semiring.left_distrib,←sumOverAdd]; congr 1; apply sumOverCongr; intro g; rw [m]; dsimp only [v]; grind only

theorem middleParseval {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) :
    sumOver T.reps (fun a => (middlePop half L a A)^2)=
    half^n*sumOver G.labels (fun g => (ThreeLegFourier.middle (localH A g))^2) := by
  simp only [middleFourier]; rw [parseval half h2 T]
  congr 1; apply sumOverCongr; intro g; cases L.sign g <;> simp [phase] <;> grind only

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

theorem topPair {α : Type} (xs : List α) (nd : xs.Nodup) (f : α→R) (bounds : ∀i∈xs,0≤f i ∧ f i≤1)
    (total : sumOver xs f=2) : ∃a∈xs,∃b∈xs,a≠b ∧ sumOver xs (fun i => (f i)^2)≤f a+f b := by
  classical
  have xn : xs≠[] := by intro eq; rw [eq] at total; change (0:R)=2 at total; grind only
  obtain ⟨a,ha,hmax⟩ := maxOn xs f xn
  let rest := xs.filter (fun i => decide (i≠a))
  have rem (i : α) : i∈rest ↔ i∈xs ∧ i≠a := by simp [rest]
  have rn : rest≠[] := by
    intro empty
    have onlyA (i : α) (hi : i∈xs) : i=a := by
      apply Classical.byContradiction; intro ne
      have bad := (rem i).mpr ⟨hi,ne⟩; rw [empty] at bad; contradiction
    have e (i : α) (hi : i∈xs) : f i=if a=i then f i else 0 := by rw [onlyA i hi]; simp
    rw [AnticommutingDefect.sumCongrMem xs _ _ e,ExteriorPauliBase.sumOnIndex xs a f nd ha] at total
    have h := (bounds a ha).2; grind only
  obtain ⟨b,hb,second⟩ := maxOn rest f rn
  obtain ⟨hb0,ne⟩ := (rem b).mp hb
  refine ⟨a,ha,b,hb0,Ne.symm ne,?_⟩
  let extra i := if a=i then (f a)^2-f b*f a else 0
  have elt (i : α) (hi : i∈xs) : (f i)^2≤f b*f i+extra i := by
    by_cases eq : a=i
    · subst i; simp only [extra,ite_true]; grind only
    · have h := OrderedRing.mul_le_mul_of_nonneg_right (second i ((rem i).mpr ⟨hi,Ne.symm eq⟩)) (bounds i hi).1
      simp only [extra,eq,ite_false]; grind only
  have e := Compression.sumOverNonnegative xs (fun i => (f b*f i+extra i)-(f i)^2) (fun i hi => by have := elt i hi; grind only)
  have ex : sumOver xs extra=(f a)^2-f b*f a :=
    ExteriorPauliBase.sumOnIndex xs a (fun _ => (f a)^2-f b*f a) nd ha
  rw [Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,total,ex] at e
  have g := OrderedRing.mul_nonneg (show 0≤1-f a by have := (bounds a ha).2; grind only)
    (show 0≤f a-f b by have := hmax b hb0; grind only)
  grind only

theorem twoLineLocalization {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    ∃a∈T.reps,∃b∈T.reps,a≠b ∧
      2-middlePop half L a A-middlePop half L b A≤
        half^n*sumOver (words n) (fun g => if g∈G.labels then 0 else (ThreeLegFourier.middle (localH A g))^2) := by
  let m a := middlePop half L a A
  let u g := (ThreeLegFourier.middle (localH A g))^2
  have bds (a : Word n) : 0≤m a ∧ m a≤1 := by
    have e := middleBounds half h2 L a A orth; have p := popNonnegative half h2 L a (fun t => A t 0)
    change 0≤m a ∧ pop half L a (fun t => A t 0)+m a≤1 at e
    grind only
  obtain ⟨a,ha,b,hb,ne,cap⟩ := topPair T.reps T.nodup m (fun i _ => bds i) (middleTotal half h2 L T A orth)
  refine ⟨a,ha,b,hb,ne,?_⟩
  have par := middleParseval half h2 L T A
  have tot := (PhysicalFourierDefect.totalMoments A orth).2
  have split (g : Word n) : u g=(if g∈G.labels then u g else 0)+(if g∈G.labels then 0 else u g) := by
    by_cases e : g∈G.labels <;> simp [e] <;> grind only
  change sumOver (words n) u=2*(2:R)^n at tot
  rw [sumOverCongr _ split,sumOverAdd,sumMembership G u] at tot
  change sumOver T.reps (fun a => (m a)^2)=half^n*sumOver G.labels u at par
  have inv := SectorDefectAccounting.dimensionInverse half h2 n
  have eq := congrArg (fun t : R => half^n*t) tot
  change 2-m a-m b≤half^n*sumOver (words n) (fun g => if g∈G.labels then 0 else u g)
  grind only

/-- Two distinct rank-one character projections capture the physical
middle two columns with error at most 60κ/7. -/
theorem physicalTwoLines [DecidableRel ((·≤·) : R→R→Prop)] (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (mu : Fin 7→R) (orth : OrthonormalFrame A) :
    ∃ (G : MaximalFamily (k+3)) (L : Lift G) (T : Transversal G),∃a∈T.reps,∃b∈T.reps,
      a≠b ∧ (∀g,1<2*(ThreeLegFourier.head (localH A g))^2 → g∈G.labels) ∧
      7*(2-middlePop half L a A-middlePop half L b A)≤60*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa := by
  obtain ⟨G,large,off⟩ := physicalFamily half h2 k A mu orth
  obtain ⟨L⟩ := liftExists G; obtain ⟨T⟩ := transversalExists G
  obtain ⟨a,ha,b,hb,ne,err⟩ := twoLineLocalization half h2 L T A orth
  exact ⟨G,L,T,a,ha,b,hb,ne,large,by grind only⟩

end Order

end RankSeven.StabilizerPopulationRounding

#print axioms RankSeven.StabilizerPopulationRounding.populationBessel
#print axioms RankSeven.StabilizerPopulationRounding.middleBounds
#print axioms RankSeven.StabilizerPopulationRounding.middleParseval
#print axioms RankSeven.StabilizerPopulationRounding.twoLineLocalization
#print axioms RankSeven.StabilizerPopulationRounding.physicalTwoLines

