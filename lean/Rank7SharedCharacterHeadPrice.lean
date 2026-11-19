import Rank7PhysicalProjectionAngles
import Rank7HighestCosetFourier
import Rank7HighestCodeTransport

namespace RankSeven.SharedCharacterHeadPrice

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis
open StabilizerPairedCharacters StabilizerPopulationRounding StabilizerCosetTransform CharacterFourOrbits
open HeadPauliFourier (localH firstThree)
open ThreeLegFourier (head)
open PhysicalCompressionEffect (OrthonormalFrame)

variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumLe (xs : List α) (v w : α → R) (bound : ∀ i∈xs, v i≤w i) :
    sumOver xs v≤sumOver xs w := by
  have each i hi := (show 0≤w i-v i by have := bound i hi; grind only)
  have pos := Compression.sumOverNonnegative xs (fun i => w i-v i) each
  rw [Compression.sumOverSub] at pos
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumTwo [DecidableEq α] (xs : List α) (nd : xs.Nodup) (a b : α)
    (ha : a∈xs) (hb : b∈xs) (ab : a≠b) (v : α→R) :
    sumOver xs (fun i => if i=a ∨ i=b then v i else 0)=v a+v b := by
  have atPoint (i : α) : (if i=a ∨ i=b then v i else 0)=(if a=i then v i else 0)+(if b=i then v i else 0) := by
    grind only
  rw [sumOverCongr _ atPoint, sumOverAdd, ExteriorPauliBase.sumOnIndex _ _ _ nd ha,
    ExteriorPauliBase.sumOnIndex _ _ _ nd hb]

/-- The second moment of all pair masses is at most the squared selected
pair mass plus the squared total mass outside that pair. -/
theorem pairedPopulation (xs : List α) (nd : xs.Nodup) (u : α → α)
    (closed : ∀ i∈xs, u i∈xs) (inv : ∀ i∈xs, u (u i)=i)
    (free : ∀ i∈xs, i≠u i) (v : α → R) (v0 : ∀ i∈xs, 0≤v i)
    (total : sumOver xs v=1) (a : α) (ha : a∈xs) :
    let s := v a+v (u a)
    sumOver xs (fun i => v i*(v i+v (u i))) ≤ s^2+(1-s)^2 ∧
      ∀ i∈xs, i≠a → i≠u a → v i+v (u i)≤1-s := by
  classical
  let s := v a+v (u a)
  let hit (i : α) := i=a ∨ i=u a
  let part (i : α) := if hit i then v i else 0
  let rest (i : α) := if hit i then 0 else v i
  have partSum : sumOver xs part=s := sumTwo xs nd a (u a) ha (closed a ha) (free a ha) v
  have splitSum : sumOver xs v=sumOver xs part+sumOver xs rest := by
    rw [←sumOverAdd]
    apply sumOverCongr
    intro i
    unfold part rest
    split <;> grind only
  have restSum : sumOver xs rest=1-s := by grind only
  have rest0 (i : α) (hi : i∈xs) : 0≤rest i := by
    unfold rest
    split
    · exact Std.le_refl _
    · exact v0 i hi
  have hitInvariant (i : α) (hi : i∈xs) : hit (u i) ↔ hit i := by
    change u i=a ∨ u i=u a ↔ i=a ∨ i=u a
    constructor
    · rintro (e|e)
      · exact Or.inr ((inv i hi) ▸ congrArg u e)
      · exact Or.inl (by simpa only [inv i hi,inv a ha] using congrArg u e)
    · rintro (e|e)
      · exact Or.inr (congrArg u e)
      · exact Or.inl (by rw [e,inv a ha])
  have outside (i : α) (hi : i∈xs) (h : ¬hit i) : v i+v (u i)≤1-s := by
    have nh : ¬hit (u i) := fun b => h ((hitInvariant i hi).mp b)
    have sub := sumLe xs (fun j => if j=i ∨ j=u i then rest j else 0) rest (fun j hj => by
      split
      · exact Std.le_refl _
      · exact rest0 j hj)
    rw [sumTwo xs nd i (u i) hi (closed i hi) (free i hi) rest, restSum] at sub
    simpa only [rest,h,nh,ite_false] using sub
  have pointwise (i : α) (hi : i∈xs) :
      v i*(v i+v (u i))≤s*part i+(1-s)*rest i := by
    by_cases h : hit i
    · have pair : v i+v (u i)=s := by
        rcases h with hi'|hi'
        · rw [hi']
        · rw [hi', inv a ha]; dsimp only [s]; grind only
      rw [pair]
      simp only [part,rest,h,ite_true,Semiring.mul_zero,Semiring.add_zero]
      grind only
    · have scaled := OrderedRing.mul_le_mul_of_nonneg_right (outside i hi h) (v0 i hi)
      simp only [part,rest,h,ite_false,Semiring.mul_zero]
      grind only
  have bound := sumLe xs _ _ pointwise
  rw [sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,partSum,restSum] at bound
  exact ⟨by grind only,
    fun i hi p q => outside i hi (fun h => h.elim p q)⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem unitHead {n : Nat} (A : Basis n→Fin 7→ComplexScalar R)
  (orth : OrthonormalFrame A) : PauliPairContraction.normSum (qubitIndices n) (fun i => A i 0)=1 := by
  have e := congrArg ComplexScalar.re (orth 0 0)
  rw [ite_eq_left rfl] at e
  change (sumOver (qubitIndices n) (fun i => star (A i 0)*A i 0)).re=1 at e
  rw [(HighestCosetFourier.realSum _ _).1] at e
  simp only [re_star_mul_self] at e
  exact e

def halfLoss {n : Nat} (half : R) (G : MaximalFamily n) (t : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) :=
  half^n*sumOver G.labels (fun p => if anti t p then 0 else 1-(head (localH A p))^2)

/-- Exact head-character collision bound on the commuting half-group. -/
theorem physicalHeadHalfPrice {n : Nat} (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (t c : Word n)
    (tf : t∉G.labels) (hc : c∈T.reps) (A : Basis n→Fin 7→ComplexScalar R)
    (orth : OrthonormalFrame A) :
    let f := 1-pairedHead half L T A t c
    f*(1-f)≤halfLoss half G t A := by
  let H := headPop half L A
  let u (i : Line T) := shift T t i
  let r p := head (localH A p)
  let F p := phase (L.sign p)*r p
  let a : Line T := ⟨c,hc⟩
  let b := pairedHead half L T A t c
  let f := 1-b
  have unit := unitHead A orth
  have mass : sumOver T.reps H=1 := (popTotal half h2 L T _).trans unit
  have ht (i : Word n) : H i=transform half G F i := by
    unfold H headPop
    rw [popFourier]
    unfold transform
    congr 1
    apply sumOverCongr
    intro g
    have e := congrArg ComplexScalar.re (HeadPauliFourier.elementFrame (firstThree A) g 0 0)
    change HeadPauliFourier.expectation (fun i => A i 0) g=r g at e
    rw [e]
  have sq (g : Word n) : (F g)^2=(r g)^2 := by
    cases e : L.sign g <;> simp [F,e,phase] <;> grind only
  have pairedBound := (pairedPopulation T.reps.attach (linesNodup T) u (fun i _ => List.mem_attach _ _)
    (fun i _ => shiftTwice T t i) (fun i _ => shiftFree T t tf i)
    (fun i => H i.val) (fun i _ => popNonnegative half h2 L i.val _)
    ((lineSum T H).trans mass) a (List.mem_attach _ _)).1
  change sumOver T.reps.attach (fun (i : Line T) => H i.val*(H i.val+H (u i).val))≤b^2+(1-b)^2 at pairedBound
  have linewise (i : Line T) : (u i).val=representative T (wordAdd i.val t) := rfl
  simp only [linewise] at pairedBound
  rw [lineSum T (fun j => H j*(H j+H (representative T (wordAdd j t))))] at pairedBound
  have identity := pairedSquare half h2 T t F
  rw [show transform half G F=H from (funext ht).symm] at identity
  simp only [sq] at identity
  have normal := halfGroup (R:=R) half h2 (G:=G) t tf
  have split (g : Word n) : (if anti t g then (0:R) else 1-(r g)^2)=
      (if anti t g then 0 else 1)-(if anti t g then 0 else (r g)^2) := by
    cases anti t g <;> simp <;> grind only
  rw [identity] at pairedBound
  change f*(1-f)≤halfLoss half G t A
  unfold halfLoss
  change _≤half^n*sumOver G.labels (fun g => if anti t g then 0 else 1-(r g)^2)
  rw [sumOverCongr _ split, Compression.sumOverSub]
  clear ht sq linewise identity
  grind only

def commutingDefect {n : Nat} (half : R) (G : MaximalFamily n) (t : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) :=
  half^n*sumOver G.labels (fun g => if anti t g then 0 else
    (ThreeLegFourier.middle (localH A g))^2*(1-(head (localH A g))^2))

private theorem headLossNonnegative {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (g : Word n) : 0≤1-(head (localH A g))^2 := by
  let H := localH A g
  have complement := PhysicalOddLeakage.compressionComplement (firstThree A) g
    (PhysicalFourierDefect.topThreeOrth A orth)
  have columns := ThreeLegFourier.columnContraction H complement 0
  have labels : List.finRange 3=[0,1,2] := by decide
  simp only [labels,sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons] at columns
  have rowOne := normSq_nonnegative (H 1 0)
  have rowTwo := normSq_nonnegative (H 2 0)
  have entry : (head H)^2≤normSq (H 0 0) := by
    unfold head normSq
    have := squareNonnegative (H 0 0).im
    grind only
  change 0≤1-(head H)^2
  grind only

/-- The actual diagonal Fourier defect on the commuting half-group alone
pays the sharp head leakage contribution. -/
theorem physicalCommutingPrice {n : Nat} (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (a b c : Word n)
    (ha : a∈T.reps) (hb : b∈T.reps) (hc : c∈T.reps) (different : a≠b)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (near : 1≤middlePop half L a A+middlePop half L b A) :
    let e := 2-middlePop half L a A-middlePop half L b A
    let f := 1-pairedHead half L T A (wordAdd a b) c
    4*(1-e)^2*f*(1-f)≤commutingDefect half G (wordAdd a b) A := by
  let t := wordAdd a b
  let e := 2-middlePop half L a A-middlePop half L b A
  let f := 1-pairedHead half L T A t c
  let loss (g : Word n) := if anti t g then 0 else 1-(head (localH A g))^2
  let rate := 4*(1-e)^2
  have t0 : t∉G.labels := fun h => different (T.separated a ha b hb h)
  have first : f*(1-f)≤halfLoss half G t A := physicalHeadHalfPrice half h2 L T t c t0 hc A orth
  have pow0 (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have rate0 : 0≤rate := by have := squareNonnegative (1-e); unfold rate; grind only
  have point (g : Word n) (hg : g∈G.labels) :
      rate*loss g ≤ if anti t g then 0 else
        (ThreeLegFourier.middle (localH A g))^2*(1-(head (localH A g))^2) := by
    cases h : anti t g with
    | true => simp only [loss,h,ite_true,Semiring.mul_zero]; exact Std.le_refl 0
    | false =>
      have middle := middleStable half h2 L T A orth a b ha hb different g hg h near
      have bound : rate≤(ThreeLegFourier.middle (localH A g))^2 := by
        have eq : 1-e=middlePop half L a A+middlePop half L b A-1 := by
          dsimp only [e]
          grind only
        unfold rate
        rw [eq]
        exact middle
      simpa only [loss,h,Bool.false_eq_true,ite_false] using
        OrderedRing.mul_le_mul_of_nonneg_right bound (headLossNonnegative A orth g)
  have summed := sumLe G.labels _ _ point
  rw [←sumOverMulLeft] at summed
  have actual := OrderedRing.mul_le_mul_of_nonneg_left summed (pow0 n)
  have paid := OrderedRing.mul_le_mul_of_nonneg_left first rate0
  change rate*(f*(1-f))≤rate*(half^n*sumOver G.labels loss) at paid
  change rate*f*(1-f)≤commutingDefect half G t A
  calc
    rate*f*(1-f) = rate*(f*(1-f)) := Semiring.mul_assoc _ _ _
    _ ≤ rate*(half^n*sumOver G.labels loss) := paid
    _ = half^n*(rate*sumOver G.labels loss) := by
      rw [←Semiring.mul_assoc,CommSemiring.mul_comm rate (half^n),Semiring.mul_assoc]
    _ ≤ commutingDefect half G t A := actual

section Outside

open FiniteProjectionAngles SlaterUnionBound
open HighestCodeLocalization (innerProduct)
open PhysicalProjectionAngles (code codeProjection)
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

/-- Away from the two character cosets preserving the head code, its
actual Pauli expectation is bounded by the head error alone. -/
theorem physicalHeadOutside {n : Nat} (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (t c q : Word n)
    (tf : t∉G.labels) (hc : c∈T.reps) (qf : q∉G.labels) (qt : wordAdd q t∉G.labels)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (small : 2*(1-pairedHead half L T A t c)≤1) :
    let f := 1-pairedHead half L T A t c
    (head (localH A q))^2≤4*f*(1-f) := by
  let a : Line T := ⟨c,hc⟩
  let m := shift T t
  let b := m a
  let h := headPop half L A
  let x := fun i => A i 0
  let y := act q x
  let xs := qubitIndices n
  let Q := code half L a.val b.val
  let f := 1-pairedHead half L T A t c
  have a_ne_b : a.val≠b.val := fun e => shiftFree T t tf a (Subtype.ext e)
  have apart : ¬equiv G a.val b.val := fun e => a_ne_b (T.separated _ a.property _ b.property e)
  have proj := codeProjection half h2 L a.val b.val apart
  have hMass : sumOver T.reps h=1 := (popTotal half h2 L T x).trans (unitHead A orth)
  have bound := (pairedPopulation T.reps.attach (linesNodup T) m (fun i _ => List.mem_attach _ _)
    (fun i _ => shiftTwice T t i) (fun i _ => shiftFree T t tf i)
    (fun i => h i.val) (fun i _ => popNonnegative half h2 L i.val x)
    ((lineSum T h).trans hMass) a (List.mem_attach _ _)).2
  have close : energy xs Q x=pairedHead half L T A t c := by
    unfold Q code
    rw [energyAdd]
    rfl
  have shifted (i : Line T) : pop half L i.val y=h (shift T q i).val := by
    unfold y
    rw [HighestCodeTransport.actPopulation half h2 L]
    exact HighestCodeTransport.classPopulation half L x (represents T _).2
  have commute : shift T q b=m (shift T q a) := by
    unfold b m
    rw [shiftSum,shiftSum,wordAddComm q t]
  have out : energy xs Q y≤f := by
    have value : energy xs Q y=pop half L a.val y+pop half L b.val y := by
      unfold Q code
      rw [energyAdd]
      rfl
    rw [value,shifted,shifted,commute]
    exact bound (shift T q a) (List.mem_attach _ _)
      (Ne.symm (shiftFree T q qf a)) (shiftDifferent T q t qt a)
  have yn : PauliPairContraction.normSum xs y=1 := (PauliPairContraction.wordIsometry q x).trans (unitHead A orth)
  have comparison := HighestAnchorMoments.projectionMismatch xs (HyperplaneIncidence.normalsNodup n)
    (@qubitIndicesComplete n) Q proj x y (unitHead A orth) yn
  have headAsInner : head (localH A q)=(innerProduct xs x y).re := by
    unfold head localH PhysicalOddLeakage.compression innerProduct y act
    rfl
  have entry := squareNonnegative (innerProduct xs x y).im
  have split : normSq (innerProduct xs x y)=(head (localH A q))^2+(innerProduct xs x y).im^2 := by
    unfold normSq
    rw [headAsInner]
  rw [split,close] at comparison
  let v := energy xs Q y
  change v≤f at out
  have corr : pairedHead half L T A t c=1-f := by
    dsimp only [f]
    grind only
  rw [corr] at comparison
  change (head (localH A q))^2+(innerProduct xs x y).im^2≤1-(1-f-v)^2 at comparison
  change 2*f≤1 at small
  have monotone := OrderedRing.mul_nonneg (show 0≤(1-f-v)-(1-2*f) by grind only)
    (show 0≤(1-f-v)+(1-2*f) by grind only)
  change (head (localH A q))^2≤4*f*(1-f)
  grind only

noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

noncomputable def complementaryMass {n : Nat} (half : R) (G : MaximalFamily n)
    (t : Word n) (A : Basis n→Fin 7→ComplexScalar R) :=
  half^n*sumOver (words n) (fun q => if q∈G.labels ∨ wordAdd q t∈G.labels then 0 else
    (ThreeLegFourier.middle (localH A q))^2)

set_option linter.constructorNameAsVariable false in
/-- The complementary cosets and the commuting subgroup occupy disjoint
terms of the exact diagonal Fourier defect. -/
theorem disjointRegions {n : Nat} (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (t c : Word n)
    (tf : t∉G.labels) (hc : c∈T.reps)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (small : 2*(1-pairedHead half L T A t c)≤1) :
    let f := 1-pairedHead half L T A t c
    commutingDefect half G t A + (1-2*f)^2*complementaryMass half G t A≤
      PhysicalFourierDefect.diagonalDefect half A := by
  classical
  let f := 1-pairedHead half L T A t c
  let w (q : Word n) := (ThreeLegFourier.middle (localH A q))^2
  let v (q : Word n) := 1-(head (localH A q))^2
  let stay (q : Word n) := if anti t q then 0 else w q*v q
  let central (q : Word n) := if q∈G.labels then stay q else 0
  let away (q : Word n) := if q∈G.labels ∨ wordAdd q t∈G.labels then 0 else w q
  let rate := (1-2*f)^2
  have pow0 (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have each (q : Word n) : central q+rate*away q≤w q*v q := by
    have wn : 0≤w q := squareNonnegative _
    have vn : 0≤v q := headLossNonnegative A orth q
    have nn := OrderedRing.mul_nonneg wn vn
    by_cases inG : q∈G.labels
    · have flag : q∈G.labels ∨ wordAdd q t∈G.labels := Or.inl inG
      simp only [central,stay,away,inG,ite_true]
      cases anti t q <;> simp <;> grind only
    · by_cases onMate : wordAdd q t∈G.labels
      · have flag : q∈G.labels ∨ wordAdd q t∈G.labels := Or.inr onMate
        simp only [central,away,inG,ite_false]
        grind only
      · have flag : ¬(q∈G.labels ∨ wordAdd q t∈G.labels) := fun h => h.elim inG onMate
        have headBound := physicalHeadOutside half h2 L T t c q tf hc inG onMate A orth small
        have price : rate≤v q := by dsimp only [rate,v]; grind only
        have prod := OrderedRing.mul_le_mul_of_nonneg_right price wn
        simp only [central,away,inG,ite_false]
        grind only
  have summed := sumLe (words n) _ _ (fun q _ => each q)
  rw [sumOverAdd,←sumOverMulLeft] at summed
  have centerSum : sumOver (words n) central=sumOver G.labels stay :=
    HeavyPauliGroup.sumMembership G stay
  rw [centerSum] at summed
  have paid := OrderedRing.mul_le_mul_of_nonneg_left summed (pow0 n)
  change half^n*sumOver G.labels stay+rate*(half^n*sumOver (words n) away)≤
    half^n*sumOver (words n) (fun q => w q*v q)
  have assoc (a b c d : R) : a*b+c*(a*d)=a*(b+c*d) := by grind only
  rw [assoc]
  exact paid

end Outside

end RankSeven.SharedCharacterHeadPrice

#print axioms RankSeven.SharedCharacterHeadPrice.pairedPopulation
#print axioms RankSeven.SharedCharacterHeadPrice.physicalHeadHalfPrice
#print axioms RankSeven.SharedCharacterHeadPrice.physicalCommutingPrice
#print axioms RankSeven.SharedCharacterHeadPrice.physicalHeadOutside
#print axioms RankSeven.SharedCharacterHeadPrice.disjointRegions
