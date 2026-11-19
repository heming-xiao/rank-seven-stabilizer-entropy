import Rank7StabilizerPairedCharacters

namespace RankSeven.StabilizerSmallCodes

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPopulationRounding StabilizerPairedCharacters ThreeLegFourier HeadPauliFourier PhysicalFourierDefect
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem sumLe {α : Type} (xs : List α) (f h : α→R) (e : ∀i∈xs,f i≤h i) : sumOver xs f≤sumOver xs h := by
  have q := Compression.sumOverNonnegative xs (fun i => h i-f i) (fun i hi => by have := e i hi; grind only)
  rw [Compression.sumOverSub] at q; grind only

private theorem halfPositive (half : R) (h2 : 2*half=1) (n : Nat) : 0≤half^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)

private theorem headLoss {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (p : Word n) :
    0≤1-(head (localH A p))^2 := by
  let H := localH A p
  have gn := PhysicalOddLeakage.compressionComplement (firstThree A) p (topThreeOrth A orth)
  have c := ThreeLegFourier.columnContraction H gn 0
  have L : List.finRange 3=[0,1,2] := by decide
  simp only [L,sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons] at c
  have a := normSq_nonnegative (H 1 0); have b := normSq_nonnegative (H 2 0)
  have sq : (head H)^2≤normSq (H 0 0) := by unfold head normSq; have := squareNonnegative (H 0 0).im; grind only
  change 0≤1-(head H)^2; grind only

noncomputable def outside {n : Nat} (half : R) (G : MaximalFamily n) (A : Basis n→Fin 7→ComplexScalar R) :=
  half^n*sumOver (words n) (fun g => if g∈G.labels then 0 else (middle (localH A g))^2)

theorem outsidePrice [DecidableRel ((·≤·) : R→R→Prop)] (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (mu : Fin 7→R) (orth : OrthonormalFrame A)
    (G : MaximalFamily (k+3)) (contains : ∀g,1<2*(head (localH A g))^2 → g∈G.labels) :
    12*diagonalDefect half A+outside half G A≤60*(physicalPayment half h2 k A mu).kappa := by
  let n := k+3
  let r g := head (localH A g)
  let u g := (middle (localH A g))^2
  have bound (g : Word n) : (if g∈G.labels then 0 else u g)≤(if 2*(r g)^2≤1 then u g else 0) := by
    have nn : 0≤u g := squareNonnegative _
    by_cases mem : g∈G.labels
    · simp only [mem,ite_true]; split <;> grind only
    · have sm : 2*(r g)^2≤1 := by apply Classical.byContradiction; intro no; exact mem (contains g (by change 1<2*(r g)^2; grind only))
      simp [mem,sm]
  have s := sumLe (words n) _ _ (fun g _ => bound g)
  have m := OrderedRing.mul_le_mul_of_nonneg_left s (halfPositive half h2 n)
  change outside half G A≤outsideMass half A at m
  have a := (weakMassLocalization half h2 k A mu orth).2.1
  have b := (physicalFourierBounds half h2 k A mu orth).2.2; grind only

theorem firstPlusOutside {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n}
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (contains : ∀g,1<2*(head (localH A g))^2 → g∈G.labels) (t : Word n) (e f : R)
    (off : e≤outside half G A)
    (stable : ∀g∈G.labels,anti t g=false → 4*(1-e)^2≤(middle (localH A g))^2)
    (first : f≤2*half^n*sumOver G.labels (fun g => if anti t g then 0 else 1-(head (localH A g))^2)) :
    e+4*(1-e)^2*f≤2*diagonalDefect half A := by
  let r g := (head (localH A g))^2
  let u g := (middle (localH A g))^2
  let out g := if g∈G.labels then 0 else u g
  let inside g := if g∈G.labels then (if anti t g then 0 else 1-r g) else 0
  let c := 4*(1-e)^2
  have cn : 0≤c := by have := squareNonnegative (1-e); dsimp only [c]; grind only
  have point (g : Word n) : out g+2*c*inside g≤2*(u g*(1-r g)) := by
    have u0 : 0≤u g := squareNonnegative _
    have r0 : 0≤1-r g := headLoss A orth g
    have positive := OrderedRing.mul_nonneg u0 r0
    by_cases mem : g∈G.labels
    · unfold out inside; simp only [mem,ite_true]
      cases a : anti t g with
      | true => simp only [ite_true]; grind only
      | false =>
        have st : c≤u g := stable g mem a
        have m := OrderedRing.mul_le_mul_of_nonneg_right st r0; simp only [Bool.false_eq_true,ite_false]; grind only
    · have small : 2*r g≤1 := by apply Classical.byContradiction; intro no; exact mem (contains g (by change 1<2*r g; grind only))
      have m := OrderedRing.mul_nonneg u0 (show 0≤1-2*r g by grind only)
      simp only [out,inside,mem,ite_false]; grind only
  have s := sumLe (words n) _ _ (fun g _ => point g)
  rw [sumOverAdd,←sumOverMulLeft,←sumOverMulLeft] at s
  have ins : sumOver (words n) inside=sumOver G.labels (fun g => if anti t g then 0 else 1-r g) :=
    sumMembership G _
  rw [ins] at s
  have m := OrderedRing.mul_le_mul_of_nonneg_left s (halfPositive half h2 n)
  have p := OrderedRing.mul_le_mul_of_nonneg_left first cn
  change e≤half^n*sumOver (words n) out at off
  change e+c*f≤2*(half^n*sumOver (words n) (fun g => u g*(1-r g)))
  change c*f≤c*(2*half^n*sumOver G.labels (fun g => if anti t g then 0 else 1-r g)) at p
  grind only

omit [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem repClass {n : Nat} {G : MaximalFamily n} (T : Transversal G) (p q : Word n) (hq : q∈T.reps) (eq : equiv G p q) :
    representative T p=q := T.separated _ (represents T p).1 q hq (StabilizerCosetTransform.trans (StabilizerCosetTransform.symm (represents T p).2) eq)

omit [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem mateSwaps {n : Nat} {G : MaximalFamily n} (T : Transversal G) (a b : Word n) (ha : a∈T.reps) (hb : b∈T.reps) :
    representative T (wordAdd a (wordAdd a b))=b ∧ representative T (wordAdd b (wordAdd a b))=a := by
  constructor
  · rw [←wordAddAssoc,wordAddSelf,wordAddComm,wordAddZero]; exact repClass T b b hb (StabilizerCosetTransform.refl G b)
  · rw [wordAddComm a b,←wordAddAssoc,wordAddSelf,wordAddComm,wordAddZero]; exact repClass T a a ha (StabilizerCosetTransform.refl G a)


omit [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem mateInvol {n : Nat} {G : MaximalFamily n} (T : Transversal G) (t c : Word n) (hc : c∈T.reps) :
    representative T (wordAdd (representative T (wordAdd c t)) t)=c := by
  let d := representative T (wordAdd c t)
  have h := (represents T (wordAdd c t)).2
  have e : wordAdd (wordAdd d t) c=wordAdd (wordAdd c t) d := by
    rw [wordAddComm (wordAdd c t) d,wordAddAssoc,wordAddComm t c]
  exact repClass T _ _ hc (show wordAdd (wordAdd d t) c∈G.labels by rw [e]; exact h)

structure SmallCodes (half : R) {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) where
  G : MaximalFamily n
  L : Lift G
  T : Transversal G
  a : Word n
  b : Word n
  c : Word n
  ha : a∈T.reps
  hb : b∈T.reps
  hc : c∈T.reps
  distinct : a≠b ∧ c≠a ∧ c≠b
  secondDistinct : ∀v, v=representative T (wordAdd c (wordAdd a b)) → v≠a ∧ v≠b ∧ v≠c
  error : 5*((2-middlePop half L a A-middlePop half L b A)+
      2*(1-pairedHead half L T A (wordAdd a b) c))<3
  errorNonnegative : 0≤2-middlePop half L a A-middlePop half L b A ∧
      0≤1-pairedHead half L T A (wordAdd a b) c

/-- The physical head column and middle pair concentrate on two distinct
parallel rank-two character codes. Their weighted leakage is below 3/5. -/
theorem physicalSmallCodes [DecidableRel ((·≤·) : R→R→Prop)] (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (mu : Fin 7→R) (orth : OrthonormalFrame A)
    (small : 200*(physicalPayment half h2 k A mu).kappa≤11) : Nonempty (SmallCodes half A) := by
  obtain ⟨G,contains,out⟩ := physicalFamily half h2 k A mu orth
  obtain ⟨L⟩ := liftExists G; obtain ⟨T⟩ := transversalExists G
  obtain ⟨a,ha,b,hb,ne,hOff⟩ := twoLineLocalization half h2 L T A orth
  let t := wordAdd a b
  have ht : t∉G.labels := fun mem => ne (T.separated a ha b hb mem)
  obtain ⟨c,hc,_,first⟩ := firstCharacterRegion half h2 L T A orth t ht
  let m p := middlePop half L p A
  let H := headPop half L A
  let e := 2-m a-m b
  let f := 1-pairedHead half L T A t c
  let D := diagonalDefect half A
  let K := (physicalPayment half h2 k A mu).kappa
  have ba (p : Word (k+3)) : H p+m p≤1 := (middleBounds half h2 L p A orth).2
  have nn (p : Word (k+3)) : 0≤H p := popNonnegative half h2 L p _
  have en : 0≤e := by have := ba a; have := ba b; have := nn a; have := nn b; unfold e; grind only
  have fn : 0≤f := by have v := (pairedHeadBounds half h2 L T A orth t c ht hc).2; unfold f; grind only
  have off : e≤outside half G A := hOff
  have joined := outsidePrice half h2 k A mu orth G contains
  change 12*D+outside half G A≤60*K at joined
  change 7*outside half G A≤60*K at out; change 200*K≤11 at small
  have close : 1≤m a+m b := by dsimp only [e] at off; grind only
  have stable (g : Word (k+3)) (hg : g∈G.labels) (ag : anti t g=false) : 4*(1-e)^2≤(middle (localH A g))^2 := by
    have s := middleStable half h2 L T A orth a b ha hb ne g hg ag close
    change 4*(m a+m b-1)^2≤_ at s
    have eq : 1-e=m a+m b-1 := by unfold e; grind only
    rw [eq]; exact s
  have regions := firstPlusOutside half h2 A orth contains t e f off stable first
  change e+4*(1-e)^2*f≤2*D at regions
  have cap : 5*(e+2*f)<3 := (coarseErrors K D e f 0 small fn (by grind only) regions (by grind only)).1
  have swaps := mateSwaps T a b ha hb
  have ab : representative T (wordAdd a t)=b := swaps.1
  have bb : representative T (wordAdd b t)=a := swaps.2
  have dist : c≠a ∧ c≠b := by
    have ca : f=1-(H c+H (representative T (wordAdd c t))) := rfl
    have x := ba a; have y := ba b
    dsimp only [e] at cap
    constructor
    · intro he; rw [he,ab] at ca; grind only
    · intro he; rw [he,bb] at ca; grind only
  refine ⟨⟨G,L,T,a,b,c,ha,hb,hc,⟨ne,dist⟩,?_,cap,⟨en,fn⟩⟩⟩
  intro v eq; subst v
  have inv := mateInvol T t c hc
  change representative T (wordAdd c t)≠a ∧ representative T (wordAdd c t)≠b ∧ representative T (wordAdd c t)≠c
  refine ⟨?_,?_,Ne.symm (mateDifferent T t ht c)⟩
  · intro h; rw [h,ab] at inv; exact dist.2 inv.symm
  · intro h; rw [h,bb] at inv; exact dist.1 inv.symm

end RankSeven.StabilizerSmallCodes

#print axioms RankSeven.StabilizerSmallCodes.outsidePrice
#print axioms RankSeven.StabilizerSmallCodes.firstPlusOutside
#print axioms RankSeven.StabilizerSmallCodes.mateInvol
#print axioms RankSeven.StabilizerSmallCodes.physicalSmallCodes

