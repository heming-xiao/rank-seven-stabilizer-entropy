import Rank7SharedSmallGramScalar

namespace RankSeven.SharedMiddleCosets

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCharacterBasis StabilizerCosetTransform StabilizerOddSector StabilizerExteriorTrace
open HeadPauliFourier (element elementHermitian expectation localH)
open PhysicalProjectionAngles (middleCols)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumCoordinates {n : Nat} (f : Basis n×Basis n→ComplexScalar R) :
    sumOver (PhysicalMixedFrame.pairs n) f=
      sumOver (qubitIndices n) (fun i => sumOver (qubitIndices n) (fun j => f (i,j))) := by
  unfold PhysicalMixedFrame.pairs productIndices
  rw [sumOverFlatMap]
  apply sumOverCongr
  intro i
  simp only [sumOver,List.map_map,Function.comp_def]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem diagonalAmplitude {n : Nat} (x : Basis n→ComplexScalar R) (p : Word n) :
    amplitude x (fun i => star (x i)) p=element x x p := by
  unfold amplitude element
  simp only [sumCoordinates]
  rw [sumOverSwap]
  apply sumOverCongr
  intro i
  apply sumOverCongr
  intro j
  grind only

private theorem diagonalElement {n : Nat} (x : Basis n→ComplexScalar R) (p : Word n) :
    element x x p=ofReal (expectation x p) := by
  apply ComplexScalar.ext
  · rfl
  · have h := congrArg ComplexScalar.im (elementHermitian x x p)
    rw [im_star] at h
    simp only [im_ofReal]
    grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem coordinateConjugation {n : Nat} (half : R) {G : MaximalFamily n}
    (L : Lift G) (z : TransposeOffset G) (a : Word n) (x y : Basis n→ComplexScalar R) :
    coordinate half L (wordAdd a z.offset) (fun i => star (y i)) (fun i => star (x i)) =
      coordinate half L a x y := by
  unfold coordinate
  simp only [sumCoordinates,star_star]
  rw [sumOverSwap]
  apply sumOverCongr
  intro i
  apply sumOverCongr
  intro j
  have eq : block half L (wordAdd a z.offset) j i=block half L a i j :=
    (congrFun (congrFun (conjugateBlock half L z a) j) i).symm
  rw [eq]
  grind only

/-- Ordinary Pauli coefficient products on a single coset equal the
overlap of the corresponding translated compressed character lines. -/
theorem cosetEntry {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n}
    (L : Lift G) (T : Transversal G) (z : TransposeOffset G) (t : Word n)
    (x y : Basis n→ComplexScalar R) :
    half^n*sumOver (words n) (fun p => if wordAdd p t∈G.labels then expectation x p*expectation y p else 0)=
      sumOver T.reps (fun a =>
        (coordinate half L (wordAdd a t) y x*coordinate half L a x y).re) := by
  have relation := amplitudeCoset half h2 L T z t x (fun i => star (x i)) y (fun i => star (y i))
  simp only [diagonalAmplitude,diagonalElement,star_ofReal,coordinateConjugation] at relation
  have projected := congrArg ComplexScalar.re relation
  rw [←PhysicalPairedReduction.realEmbeddingPow,re_mul,re_ofReal,im_ofReal,Semiring.zero_mul] at projected
  rw [(HighestCosetFourier.realSum _ _).1, (HighestCosetFourier.realSum _ _).1] at projected
  have point (p : Word n) :
      (if wordAdd p t∈G.labels then ofReal (expectation x p)*ofReal (expectation y p) else (0:ComplexScalar R)).re=
        if wordAdd p t∈G.labels then expectation x p*expectation y p else 0 := by
    by_cases h : wordAdd p t∈G.labels <;> simp only [h,ite_true,ite_false,re_zero,re_mul,re_ofReal,im_ofReal,Semiring.zero_mul] <;> grind only
  simp only [point] at projected
  have norm (a b : R) : a*b-0=a*b := by grind only
  simpa only [norm] using projected

variable {α : Type}

def blockCross {n : Nat} (xs : List α) (half : R) {G : MaximalFamily n}
    (L : Lift G) (A : Basis n→α→ComplexScalar R) (a b : Word n) :=
  sumOver xs (fun i => sumOver xs (fun j =>
    (compressed half L a A i j*compressed half L b A j i).re))

theorem blockCrossNonnegative {n : Nat} (xs : List α) (half : R)
    (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (A : Basis n→α→ComplexScalar R)
    (a b : Word n) : 0≤blockCross xs half L A a b := by
  have nonnegative := compressedCross xs half h2 L b a A
  unfold blockCross
  simp only [CommSemiring.mul_comm (compressed half L b A _ _) (compressed half L a A _ _)] at nonnegative
  exact nonnegative

noncomputable def cosetMass {n : Nat} (half : R) (G : MaximalFamily n)
    (t : Word n) (A : Basis n→Fin 7→ComplexScalar R) :=
  half^n*sumOver (words n) (fun p => if wordAdd p t∈G.labels then (ThreeLegFourier.middle (localH A p))^2 else 0)

theorem middleCoset {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n}
    (L : Lift G) (T : Transversal G) (z : TransposeOffset G) (t : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) :
    cosetMass half G t A=
      sumOver T.reps (fun a => blockCross [false,true] half L (middleCols A) a (wordAdd a t)) := by
  let I := [false,true]
  let M := middleCols A
  let r (i : Bool) := expectation (fun x => M x i)
  let D (i j : Bool) (p : Word n) := if wordAdd p t∈G.labels then r i p*r j p else 0
  let C (i j : Bool) (a : Word n) :=
    (compressed half L a M i j*compressed half L (wordAdd a t) M j i).re
  have each (i j : Bool) : half^n*sumOver (words n) (D i j)=sumOver T.reps (C i j) := by
    have eq := cosetEntry half h2 L T z t (fun x => M x i) (fun x => M x j)
    calc
      half^n*sumOver (words n) (D i j) = sumOver T.reps (fun a =>
          (coordinate half L (wordAdd a t) (fun x => M x j) (fun x => M x i)*
            coordinate half L a (fun x => M x i) (fun x => M x j)).re) := eq
      _ = sumOver T.reps (C i j) := by
        apply sumOverCongr
        intro a
        unfold C compressed
        rw [CommSemiring.mul_comm]
  have middle (p : Word n) : ThreeLegFourier.middle (localH A p)=r false p+r true p := by
    have first := congrArg ComplexScalar.re (HeadPauliFourier.elementFrame (HeadPauliFourier.firstThree A) p 1 1)
    have second := congrArg ComplexScalar.re (HeadPauliFourier.elementFrame (HeadPauliFourier.firstThree A) p 2 2)
    change r false p=(localH A p 1 1).re at first
    change r true p=(localH A p 2 2).re at second
    unfold ThreeLegFourier.middle
    rw [←first,←second]
  have combine (p : Word n) :
      sumOver I (fun i => sumOver I (fun j => D i j p))=
        if wordAdd p t∈G.labels then (ThreeLegFourier.middle (localH A p))^2 else 0 := by
    unfold I sumOver
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [middle]
    unfold D
    split <;> grind only
  have interchange (xs : List (Word n)) (f : Bool→Bool→Word n→R) :
      sumOver I (fun i => sumOver I (fun j => sumOver xs (f i j)))=
        sumOver xs (fun a => sumOver I (fun i => sumOver I (fun j => f i j a))) := by
    simp only [sumOverSwap I xs]
  unfold cosetMass
  rw [←sumOverCongr _ combine,←interchange (words n) D]
  simp only [sumOverMulLeft,each]
  rw [interchange T.reps C]
  rfl

open PhysicalPairedReduction (dagger)
open PauliPairContraction (normSum)
open HighestCodeLocalization (innerProduct innerBound)

private theorem gramCrossUpper {α β γ : Type} (rows : List α) (left : List β) (right : List γ)
    (F : β→α→ComplexScalar R) (V : γ→α→ComplexScalar R) :
    (trace rows (matMul rows (matMul left (dagger F) F) (matMul right (dagger V) V))).re≤
      sumOver left (fun i => normSum rows (F i))*sumOver right (fun j => normSum rows (V j)) := by
  let B := matMul rows F (dagger V)
  have eq : trace rows (matMul rows (matMul left (dagger F) F) (matMul right (dagger V) V))=
      trace left (matMul right B (dagger B)) := by
    unfold B
    rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerInvolution]
    rw [matMulAssoc left rows,traceMatMulSwap rows left (dagger F)]
    simp only [matMulAssoc]
  rw [eq]
  unfold trace
  rw [(HighestCosetFourier.realSum _ _).1]
  have diagonal (i : β) : (matMul right B (dagger B) i i).re=sumOver right (fun j => normSq (B i j)) := by
    unfold matMul
    rw [(HighestCosetFourier.realSum _ _).1]
    apply sumOverCongr
    intro j
    change (B i j*star (B i j)).re=normSq (B i j)
    rw [CommSemiring.mul_comm,re_star_mul_self]
  simp only [diagonal]
  have point (i : β) (j : γ) : normSq (B i j)≤normSum rows (F i)*normSum rows (V j) := by
    have id : B i j=innerProduct rows (V j) (F i) := by
      unfold B matMul innerProduct
      apply sumOverCongr
      intro a
      change F i a*star (V j a)=_
      rw [CommSemiring.mul_comm]
    rw [id,CommSemiring.mul_comm (normSum rows (F i))]
    exact innerBound rows (V j) (F i)
  have inner (i : β) : sumOver right (fun j => normSq (B i j))≤
      normSum rows (F i)*sumOver right (fun j => normSum rows (V j)) := by
    rw [sumOverMulLeft]
    have diff : 0≤sumOver right (fun j => normSum rows (F i)*normSum rows (V j)-normSq (B i j)) := by
      apply Compression.sumOverNonnegative
      intro j _
      have := point i j
      grind only
    rw [Compression.sumOverSub] at diff
    grind only
  rw [sumOverMulRight]
  have diff : 0≤sumOver left (fun i => normSum rows (F i)*sumOver right (fun j => normSum rows (V j))-
      sumOver right (fun j => normSq (B i j))) := by
    apply Compression.sumOverNonnegative
    intro i _
    have := inner i
    grind only
  rw [Compression.sumOverSub] at diff
  grind only

theorem blockCrossUpper {n : Nat} (rows : List α) (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (A : Basis n→α→ComplexScalar R) (a b : Word n) :
    blockCross rows half L A a b≤mass rows half L A a*mass rows half L A b := by
  let xs := qubitIndices n
  let F := matMul xs (block half L a) A
  let V := matMul xs (block half L b) A
  let G₁ := compressed half L a A
  let G₂ := compressed half L b A
  have qa : G₁=matMul xs (dagger F) F := compressedGram half h2 L a A
  have qb : G₂=matMul xs (dagger V) V := compressedGram half h2 L b A
  have traceValue : (trace rows (matMul rows G₁ G₂)).re=blockCross rows half L A a b := by
    unfold trace matMul blockCross
    rw [(HighestCosetFourier.realSum _ _).1]
    apply sumOverCongr
    intro i
    rw [(HighestCosetFourier.realSum _ _).1]
  have allMass (c : Word n) :
      sumOver xs (fun i => normSum rows (matMul xs (block half L c) A i))=mass rows half L A c := by
    unfold normSum mass
    rw [sumOverSwap]
    apply sumOverCongr
    intro i
    have diag := congrArg ComplexScalar.re (diagonalReal half h2 L c A i)
    rw [compressedGram half h2 L c A] at diag
    change (sumOver xs (fun j => star (matMul xs (block half L c) A j i)*
      matMul xs (block half L c) A j i)).re=_ at diag
    rw [(HighestCosetFourier.realSum _ _).1] at diag
    simpa only [re_star_mul_self,re_ofReal] using diag
  have bound := gramCrossUpper rows xs xs F V
  rw [←qa,←qb,traceValue] at bound
  change _≤sumOver xs (fun i => normSum rows (matMul xs (block half L a) A i))*
    sumOver xs (fun i => normSum rows (matMul xs (block half L b) A i)) at bound
  exact (allMass a ▸ allMass b ▸ bound)

open FiniteProjectionAngles SlaterUnionBound
open PhysicalCompressionEffect (OrthonormalFrame)
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem coordinateInner {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G)
    (a : Word n) (x y : Basis n→ComplexScalar R) :
    coordinate half L a x y=innerProduct (qubitIndices n) x
      (PauliPairContraction.image (qubitIndices n) (block half L a) y) := by
  unfold coordinate innerProduct PauliPairContraction.image
  rw [sumCoordinates]
  apply sumOverCongr
  intro i
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro j
  grind only

theorem pairBlockSquare {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n}
    (L : Lift G) (a b : Word n) (apart : ¬equiv G a b)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    let M := middleCols A
    let K := blockCross [false,true] half L M
    let e := 2-StabilizerPopulationRounding.middlePop half L a A-StabilizerPopulationRounding.middlePop half L b A
    K a a+K a b+K b a+K b b≤2-2*e+e^2 := by
  let M := middleCols A
  let xs := qubitIndices n
  let Q := PhysicalProjectionAngles.code half L a b
  let P := compl Q
  let x j := M j false
  let y j := M j true
  let X := energy xs Q x
  let Y := energy xs Q y
  let s := innerProduct xs x (PauliPairContraction.image xs Q y)
  let t := innerProduct xs x (PauliPairContraction.image xs P y)
  let C (i j : Bool) := compressed half L a M i j+compressed half L b M i j
  have project := PhysicalProjectionAngles.codeProjection half h2 L a b apart
  have complementP := complement xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) Q project
  have sx : normSum xs x=1 := by
    have e := congrArg ComplexScalar.re (orth 1 1)
    rw [ite_eq_left rfl] at e
    rw [(HighestCosetFourier.realSum _ _).1] at e
    simpa only [re_star_mul_self,re_one,x,M,middleCols,ite_false,Bool.false_eq_true,normSum,xs] using e
  have sy : normSum xs y=1 := by
    have e := congrArg ComplexScalar.re (orth 2 2)
    rw [ite_eq_left rfl] at e
    rw [(HighestCosetFourier.realSum _ _).1] at e
    simpa only [re_star_mul_self,re_one,y,M,middleCols,ite_true,normSum,xs] using e
  have xy : innerProduct xs x y=0 := by
    unfold innerProduct x y M middleCols xs
    simp only [Bool.false_eq_true,ite_false,ite_true]
    rw [orth 1 2,ite_eq_right (by decide : (1:Fin 7)≠2)]
  have sub : t= -s := by
    let U (i : Basis n) (_ : Unit) := x i
    let V (i : Basis n) (_ : Unit) := y i
    change matMul xs (dagger U) (matMul xs (compl Q) V) () ()=
      -(matMul xs (dagger U) (matMul xs Q V) () ())
    unfold compl
    rw [subLeft,idLeft xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n),subRight]
    change innerProduct xs x y-s= -s
    rw [xy]
    grind only
  have qx : energy xs P x=1-X := by
    unfold P compl
    rw [energySub,energyIdentity xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) x,sx]
  have qy : energy xs P y=1-Y := by
    unfold P compl
    rw [energySub,energyIdentity xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) y,sy]
  have cs := HighestCodeLocalization.projectedBound xs P complementP x y
  change normSq t≤energy xs P x*energy xs P y at cs
  have neg : normSq (-s)=normSq s := by
    unfold normSq
    simp only [re_neg,im_neg]
    grind only
  rw [sub,neg,qx,qy] at cs
  have Cxy (i j : Bool) : C i j=innerProduct xs (fun u => M u i)
      (PauliPairContraction.image xs Q (fun u => M u j)) := by
    let U (u : Basis n) (_ : Unit) := M u i
    let V (u : Basis n) (_ : Unit) := M u j
    unfold C compressed
    simp only [coordinateInner]
    change matMul xs (dagger U) (matMul xs (block half L a) V) () ()+
      matMul xs (dagger U) (matMul xs (block half L b) V) () ()=
      matMul xs (dagger U) (matMul xs Q V) () ()
    unfold Q PhysicalProjectionAngles.code
    rw [addLeft,addRight]
    rfl
  have cd (i : Bool) : C i i=ofReal (energy xs Q (fun u => M u i)) := by
    unfold C
    rw [diagonalReal half h2,diagonalReal half h2]
    unfold Q PhysicalProjectionAngles.code
    rw [energyAdd]
    apply ComplexScalar.ext <;> simp only [re_add, im_add,re_ofReal,im_ofReal]
    · rfl
    · grind only
  have swap : C true false=star s := by
    rw [Cxy true false]
    change innerProduct xs y (PauliPairContraction.image xs Q x)=
      star (innerProduct xs x (PauliPairContraction.image xs Q y))
    rw [←HighestCodeLocalization.projectedInner xs Q project x y,
      ←HighestCodeLocalization.projectedInner xs Q project y x]
    unfold innerProduct
    rw [ComplexExterior.starSumOver]
    apply sumOverCongr
    intro i
    rw [star_mul,star_star,CommSemiring.mul_comm]
  have e : 2-StabilizerPopulationRounding.middlePop half L a A-StabilizerPopulationRounding.middlePop half L b A=2-X-Y := by
    unfold X Y Q PhysicalProjectionAngles.code
    rw [energyAdd,energyAdd]
    unfold StabilizerPopulationRounding.middlePop StabilizerPopulationRounding.pop x y M middleCols
    simp only [ite_true]
    grind only
  have traceEq :
      blockCross [false,true] half L M a a+blockCross [false,true] half L M a b+
        blockCross [false,true] half L M b a+blockCross [false,true] half L M b b=
      sumOver [false,true] (fun i => sumOver [false,true] (fun j => (C i j*C j i).re)) := by
    unfold C blockCross sumOver
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,re_add,re_mul,im_add]
    grind only
  have norm : sumOver [false,true] (fun i => sumOver [false,true] (fun j => (C i j*C j i).re))=
      X^2+Y^2+2*normSq s := by
    unfold sumOver
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [cd false,cd true,swap]
    have entry : C false true=s := Cxy false true
    rw [entry,CommSemiring.mul_comm s (star s),re_star_mul_self]
    simp only [re_mul,re_ofReal,im_ofReal]
    dsimp only [X,Y,x,y]
    grind only
  dsimp only
  rw [traceEq,norm,e]
  have pure (u v w : R) (bound : w≤(1-u)*(1-v)) :
      u^2+v^2+2*w≤2-2*(2-u-v)+(2-u-v)^2 := by grind only
  exact pure X Y _ cs

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumTwo [DecidableEq α] (xs : List α) (nd : xs.Nodup) (a b : α)
    (ha : a∈xs) (hb : b∈xs) (ab : a≠b) (v : α→R) :
    sumOver xs (fun i => if i=a ∨ i=b then v i else 0)=v a+v b := by
  have pt (i : α) : (if i=a ∨ i=b then v i else 0)=(if a=i then v i else 0)+(if b=i then v i else 0) := by grind only
  rw [sumOverCongr _ pt,sumOverAdd,ExteriorPauliBase.sumOnIndex _ _ _ nd ha,ExteriorPauliBase.sumOnIndex _ _ _ nd hb]

private theorem pairedMatchingUpper (xs : List α) (nd : xs.Nodup) (m : α→α)
    (full : ∀i∈xs,m i∈xs) (involution : ∀i∈xs,m (m i)=i) (free : ∀i∈xs,i≠m i)
    (c : α→α→R) (v : α→R) (vpos : ∀i∈xs,0≤v i) (bound : ∀i j,c i j≤v i*v j)
    (total : sumOver xs v=2) (a : α) (ha : a∈xs) :
    let e := 2-v a-v (m a)
    sumOver xs (fun i => c i i+c i (m i))≤c a a+c a (m a)+c (m a) (m a)+c (m a) a+e^2 := by
  classical
  let chosen (i : α) := i=a ∨ i=m a
  let tail (w : α→R) (i : α) := if chosen i then 0 else w i
  let u (i : α) := c i i+c i (m i)
  let e := 2-v a-v (m a)
  have splitSum (w : α→R) : sumOver xs w=w a+w (m a)+sumOver xs (tail w) := by
    let select (i : α) := if chosen i then w i else 0
    have eq (i : α) : w i=select i+tail w i := by unfold select tail; split <;> grind only
    rw [sumOverCongr _ eq,sumOverAdd]
    rw [show sumOver xs select=w a+w (m a) from sumTwo xs nd a (m a) ha (full a ha) (free a ha) w]
  have budget : sumOver xs (tail v)=e := by have := splitSum v; unfold e; grind only
  have positive (i : α) (hi : i∈xs) : 0≤tail v i := by unfold tail; split; exact Std.le_refl _; exact vpos i hi
  have localBound (i : α) (hi : i∈xs) : tail u i≤e*tail v i := by
    by_cases h : chosen i
    · simp only [tail,h,ite_true,Semiring.mul_zero]; exact Std.le_refl _
    · have ht : ¬chosen (m i) := by
        rintro (eq|eq)
        · exact h (Or.inr ((involution i hi) ▸ congrArg m eq))
        · exact h (Or.inl (by simpa only [involution i hi,involution a ha] using congrArg m eq))
      have sum := Compression.sumOverNonnegative xs (fun j => tail v j-(if j=i ∨ j=m i then tail v j else 0))
        (fun j hj => by split <;> have := positive j hj <;> grind only)
      rw [Compression.sumOverSub,sumTwo xs nd i (m i) hi (full i hi) (free i hi),budget] at sum
      have cap : v i+v (m i)≤e := by simpa only [tail,h,ht,ite_false] using (show tail v i+tail v (m i)≤e by grind only)
      have multiplied := OrderedRing.mul_le_mul_of_nonneg_left cap (vpos i hi)
      have k := bound i i
      have l := bound i (m i)
      simp only [tail,h,ite_false,u]; grind only
  have tailBound := Compression.sumOverNonnegative xs (fun i => e*tail v i-tail u i)
    (fun i hi => by have := localBound i hi; grind only)
  rw [Compression.sumOverSub,←sumOverMulLeft,budget] at tailBound
  have sum := splitSum u
  dsimp only [u] at sum
  rw [involution a ha] at sum
  change sumOver xs u≤_
  grind only

open StabilizerPairedCharacters StabilizerPopulationRounding CharacterFourOrbits
open SharedCharacterHeadPrice (complementaryMass)

/-- The original physical middle columns contribute both directions of the
selected code-to-complement cross mass outside the two preserving cosets. -/
theorem complementaryMiddle {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n}
    (L : Lift G) (T : Transversal G) (a b : Word n) (ha : a∈T.reps) (hb : b∈T.reps) (ab : a≠b)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    let e := 2-middlePop half L a A-middlePop half L b A
    2*e*(1-e)≤complementaryMass half G (wordAdd a b) A := by
  let t := wordAdd a b
  let a' : Line T := ⟨a,ha⟩
  let b' : Line T := ⟨b,hb⟩
  let m := shift T t
  let I := [false,true]
  let K := blockCross I half L (middleCols A)
  let v (i : Word n) := middlePop half L i A
  let e := 2-v a-v b
  let W (p : Word n) := (ThreeLegFourier.middle (localH A p))^2
  have t0 : t∉G.labels := fun h => ab (T.separated a ha b hb h)
  have mate : m a'=b' := Subtype.ext (StabilizerSmallCodes.mateSwaps T a b ha hb).1
  have reflPart : ¬equiv G a b := t0
  obtain ⟨z⟩ := offsetExists half h2 T
  have pure := pairBlockSquare half h2 L a b reflPart A orth
  change K a a+K a b+K b a+K b b≤2-2*e+e^2 at pure
  have mTotal : sumOver T.reps v=2 := middleTotal half h2 L T A orth
  have cap (i j : Word n) : K i j≤v i*v j := by
    have fact (u : Word n) : mass I half L (middleCols A) u=v u := by
      unfold mass I sumOver middleCols v middlePop
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Bool.false_eq_true,ite_true,ite_false]
      grind only
    rw [←fact i,←fact j]
    exact blockCrossUpper I half h2 L (middleCols A) i j
  have matching := pairedMatchingUpper T.reps.attach (linesNodup T) m (fun i _ => List.mem_attach _ _)
    (fun i _ => shiftTwice T t i) (fun i _ => shiftFree T t t0 i) (fun i j => K i.val j.val)
    (fun i => v i.val) (fun i _ => (middleBounds half h2 L i.val A orth).1)
    (fun i j => cap i.val j.val) ((lineSum T v).trans mTotal) a' (List.mem_attach _ _)
  rw [mate] at matching
  have own (i : Line T) : (m i).val=representative T (wordAdd i.val t) := rfl
  simp only [own] at matching
  let V (j : Word n) := K j j+K j (representative T (wordAdd j t))
  change sumOver T.reps.attach (fun i : Line T => V i.val)≤K a a+K a b+K b b+K b a+e^2 at matching
  rw [lineSum T V] at matching
  have equalClass (i : Word n) : K i (wordAdd i t)=K i (representative T (wordAdd i t)) := by
    have same : block half L (wordAdd i t)=block half L (representative T (wordAdd i t)) := by
      funext x y
      unfold block
      rw [sameCoset (R:=R) L _ _ (represents T _).2]
    unfold K blockCross compressed coordinate
    rw [same]
  have sumCosets : cosetMass half G (unitWord n) A+cosetMass half G t A=sumOver T.reps V := by
    rw [middleCoset half h2 L T z, middleCoset half h2 L T z,←sumOverAdd]
    apply sumOverCongr
    intro i
    rw [wordAddZero]
    unfold V
    exact congrArg (fun q => K i i+q) (equalClass i)
  have split (p : Word n) :
      W p=(if wordAdd p (unitWord n)∈G.labels then W p else 0)+(if wordAdd p t∈G.labels then W p else 0)+
        (if p∈G.labels ∨ wordAdd p t∈G.labels then 0 else W p) := by
    rw [wordAddZero]
    by_cases x : p∈G.labels
    · have y : wordAdd p t∉G.labels := by
        intro h
        apply t0
        have z := addMem G p (wordAdd p t) x h
        rw [wordAddComm p (wordAdd p t),wordAddComm p t,wordAddCancel] at z
        exact z
      simp [x,y]
      grind only
    · by_cases y : wordAdd p t∈G.labels <;> simp [x,y] <;> grind only
  have both : cosetMass half G (unitWord n) A+cosetMass half G t A+complementaryMass half G t A=2 := by
    have total : sumOver (words n) W=2*(2:R)^n := (PhysicalFourierDefect.totalMoments A orth).2
    have full : half^n*sumOver (words n) W=2 := by
      rw [total]
      have inverse := SectorDefectAccounting.dimensionInverse half h2 n
      grind only
    unfold cosetMass complementaryMass
    rw [←Semiring.left_distrib,←Semiring.left_distrib,←sumOverAdd,←sumOverAdd]
    exact (congrArg (fun z => half^n*z) (sumOverCongr (words n) split)).symm.trans full
  rw [sumCosets] at both
  let r := complementaryMass half G t A
  change sumOver T.reps V+r=2 at both
  change 2*e*(1-e)≤r
  have scalar (e r a b c d s : R) (p : a+b+c+d≤2-2*e+e^2)
      (q : s≤a+b+d+c+e^2) (r1 : s+r=2) : 2*e*(1-e)≤r := by grind only
  exact scalar e r _ _ _ _ _ pure matching both

open SharedSmallGramScalar
open PhysicalFourierDefect (diagonalDefect physicalFourierBounds weakMassLocalization)

set_option linter.constructorNameAsVariable false in
/-- The selected parallel character codes have total weighted leakage below
one seventh throughout the physical small shared-Gram range. -/
theorem physicalSmallCodes (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (mu : Fin 7→R) (orth : OrthonormalFrame A)
    (small : 24*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa≤1) :
    ∃(G : MaximalFamily (k+3)) (L : Lift G) (T : Transversal G), ∃a∈T.reps, ∃b∈T.reps, ∃c∈T.reps,
      a≠b ∧
      let e := 2-middlePop half L a A-middlePop half L b A
      let f := 1-pairedHead half L T A (wordAdd a b) c
      0≤e ∧ 0≤f ∧ 7*(e+2*f)<1 := by
  classical
  obtain ⟨G,contains,outCap⟩ := HeavyPauliGroup.physicalFamily half h2 k A mu orth
  obtain ⟨L⟩ := liftExists G
  obtain ⟨T⟩ := transversalExists G
  obtain ⟨a,ha,b,hb,ne,off⟩ := twoLineLocalization half h2 L T A orth
  let t := wordAdd a b
  have no : t∉G.labels := fun he => ne (T.separated a ha b hb he)
  obtain ⟨c,hc,_,hprice⟩ := firstCharacterRegion half h2 L T A orth t no
  let e := 2-middlePop half L a A-middlePop half L b A
  let f := 1-pairedHead half L T A t c
  let d := diagonalDefect half A
  let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappa
  have e0 : 0≤e := by
    have p := middleBounds half h2 L a A orth
    have q := middleBounds half h2 L b A orth
    have u := popNonnegative half h2 L a (fun i => A i 0)
    have v := popNonnegative half h2 L b (fun i => A i 0)
    unfold e
    grind only
  have f0 : 0≤f := by have := (pairedHeadBounds half h2 L T A orth t c no hc).2; unfold f; grind only
  have o := StabilizerSmallCodes.outsidePrice half h2 k A mu orth G contains
  change e≤StabilizerSmallCodes.outside half G A at off
  change 12*d+StabilizerSmallCodes.outside half G A≤60*K at o
  have small' : 200*K≤11 := by change 24*K≤1 at small; grind only
  change 7*StabilizerSmallCodes.outside half G A≤60*K at outCap
  have near : 1≤middlePop half L a A+middlePop half L b A := by unfold e at off; grind only
  have stable (g : Word (k+3)) (hh : g∈G.labels) (anti0 : anti t g=false) : 4*(1-e)^2≤(ThreeLegFourier.middle (localH A g))^2 := by
    have s := middleStable half h2 L T A orth a b ha hb ne g hh anti0 near
    unfold e
    grind only
  have coarseRegion := StabilizerSmallCodes.firstPlusOutside half h2 A orth contains t e f off stable hprice
  change e+4*(1-e)^2*f≤2*d at coarseRegion
  have rough : e≤2*d := by
    have pos := OrderedRing.mul_nonneg (squareNonnegative (1-e)) f0
    grind only
  have coarse := (coarseErrors K d e f 0 small' f0 (by grind only) coarseRegion (by grind only)).1
  have fHalf : 2*f≤1 := by grind only
  have first := SharedCharacterHeadPrice.physicalCommutingPrice half h2 L T a b c ha hb hc ne A orth near
  have second := complementaryMiddle half h2 L T a b ha hb ne A orth
  have mixed := SharedCharacterHeadPrice.disjointRegions half h2 L T t c no hc A orth fHalf
  have prod := OrderedRing.mul_le_mul_of_nonneg_left second (squareNonnegative (1-2*f))
  change 4*(1-e)^2*f*(1-f)≤SharedCharacterHeadPrice.commutingDefect half G t A at first
  change SharedCharacterHeadPrice.commutingDefect half G t A+(1-2*f)^2*complementaryMass half G t A≤d at mixed
  change (1-2*f)^2*(2*e*(1-e))≤(1-2*f)^2*complementaryMass half G t A at prod
  have regions : 2*e*(1-e)*(1-2*f)^2+4*(1-e)^2*f*(1-f)≤d := by grind only
  have dcap : d≤5*K := (physicalFourierBounds half h2 k A mu orth).2.1
  exact ⟨G,L,T,a,ha,b,hb,c,hc,ne,e0,f0,smallError K d e f small dcap e0 f0 rough coarse regions⟩

end RankSeven.SharedMiddleCosets

#print axioms RankSeven.SharedMiddleCosets.cosetEntry
#print axioms RankSeven.SharedMiddleCosets.blockCrossNonnegative
#print axioms RankSeven.SharedMiddleCosets.middleCoset
#print axioms RankSeven.SharedMiddleCosets.blockCrossUpper
#print axioms RankSeven.SharedMiddleCosets.pairBlockSquare
#print axioms RankSeven.SharedMiddleCosets.complementaryMiddle
#print axioms RankSeven.SharedMiddleCosets.physicalSmallCodes

