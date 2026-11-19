import Rank7SharedUnionTransport
import Rank7HighestTailTransfer

namespace RankSeven.SharedOddLeakage

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks
open PhysicalMixedFrame (Pair pairs form dual skewReconstruct)
open MixedDefect (oddWords)
open HighestCodeLocalization (innerProduct)
open HighestTailTransfer (sumPairs)
open JointProbeGram (oddAverage)
open PauliPairContraction (image normSum)
open StabilizerExteriorTrace (amplitude amplitudeTranspose)
open StabilizerSmallCodes StabilizerOddSector SharedUnionTransport
open PhysicalProjectionAngles (test)
open SlaterUnionBound FiniteProjectionAngles

variable {R : Type} [CommRing R]

def coefficient {n : Nat} (F : Pair n → ComplexScalar R) (p : Word n) :=
  sumOver (pairs n) (fun x => dual p x*F x)

/-- The normalized odd Pauli transform preserves inner products on the skew sector. -/
theorem skewInner {n : Nat} (half : R) (unit : 2*half=1)
    (F G : Pair n → ComplexScalar R) (skew : ∀x, G x.swap= -G x) :
    ofReal half^n*sumOver (oddWords n) (fun p => star (coefficient F p)*coefficient G p)=
      innerProduct (pairs n) F G := by
  have starCoeff (p : Word n) :
      star (coefficient F p)=sumOver (pairs n) (fun x => form x p*star (F x)) := by
    rw [coefficient,ComplexExterior.starSumOver]
    apply sumOverCongr
    intro x
    rw [star_mul]
    congr 1
    exact ComplexPauliMoment.wordHermitian p x.2 x.1
  have swap :
      sumOver (oddWords n) (fun p => star (coefficient F p)*coefficient G p)=
        sumOver (pairs n) (fun x => star (F x)*sumOver (oddWords n) (fun p => form x p*coefficient G p)) := by
    simp only [starCoeff,sumOverMulRight,sumOverMulLeft]
    rw [sumOverSwap]
    apply sumOverCongr
    intro x
    apply sumOverCongr
    intro p
    grind only
  rw [swap,sumOverMulLeft]
  unfold innerProduct
  apply sumOverCongr
  intro x
  have r := skewReconstruct half unit G skew x
  change ofReal half^n*sumOver (oddWords n) (fun p => form x p*coefficient G p)=G x at r
  rw [←r]
  grind only

theorem skewNorm {n : Nat} (half : R) (unit : 2*half=1)
    (F : Pair n → ComplexScalar R) (skew : ∀x, F x.swap= -F x) :
    oddAverage half (fun p => normSq (coefficient F p))=2*normSum (pairs n) F := by
  have h := congrArg ComplexScalar.re (skewInner half unit F F skew)
  change (ofReal half^n*sumOver (oddWords n) _).re=(innerProduct (pairs n) F F).re at h
  rw [←PhysicalPairedReduction.realEmbeddingPow,re_mul,re_ofReal,im_ofReal] at h
  unfold innerProduct at h
  simp only [Semiring.zero_mul,(HighestCosetFourier.realSum _ _).1,re_star_mul_self] at h
  unfold oddAverage normSum
  grind only

private def tensor {α : Type} (x y : α → ComplexScalar R) (i : α×α) :=
  x i.1*y i.2

private def wedge {α : Type} (x y : α → ComplexScalar R) (i : α×α) :=
  tensor x y i-tensor y x i

private theorem wedgeSkew {α : Type} (x y : α → ComplexScalar R) (i : α×α) :
    wedge x y i.swap= -wedge x y i := by
  unfold wedge tensor
  change x i.2*y i.1-y i.2*x i.1= -(x i.1*y i.2-y i.1*x i.2)
  grind only

private theorem coefficientWedge {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n)
    (hp : p∈oddWords n) : coefficient (wedge x y) p=2*amplitude x y p := by
  have odd := (List.mem_filter.mp hp).2
  have sign : (wordSign p : ComplexScalar R)= -1 := by
    rw [MixedDefect.oddWordTransposeSign,odd]
    rfl
  have expand : coefficient (wedge x y) p=amplitude x y p-amplitude y x p := by
    unfold coefficient amplitude
    rw [←Compression.sumOverSub]
    apply sumOverCongr
    intro i
    unfold dual wedge tensor
    grind only
  rw [expand,amplitudeTranspose p x y,sign]
  grind only

private theorem coefficientAdd {n : Nat} (F G : Pair n → ComplexScalar R) (p : Word n) :
    coefficient (fun i => F i+G i) p=coefficient F p+coefficient G p := by
  unfold coefficient
  rw [←sumOverAdd]
  apply sumOverCongr
  intro i
  grind only

private theorem tensorInner {α : Type} (xs : List α) (x y u v : α → ComplexScalar R) :
    innerProduct (productIndices xs xs) (tensor x y) (tensor u v)=
      innerProduct xs x u*innerProduct xs y v := by
  unfold innerProduct
  rw [sumPairs,sumOverMulRight]
  apply sumOverCongr
  intro i
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro j
  unfold tensor
  simp only [star_mul]
  grind only

private theorem innerExpand {α : Type} (xs : List α) (a b c d : α → ComplexScalar R) :
    innerProduct xs (fun i => a i+b i) (fun i => c i+d i)=
      innerProduct xs a c+innerProduct xs a d+(innerProduct xs b c+innerProduct xs b d) := by
  unfold innerProduct
  simp only [←sumOverAdd]
  apply sumOverCongr
  intro i
  rw [star_add]
  grind only

private theorem starSub (a b : ComplexScalar R) : star (a-b)=star a-star b := by
  apply ComplexScalar.ext <;> simp only [re_star,im_star,re_sub,im_sub] <;> grind only

private theorem zeroStar : star (0 : ComplexScalar R)=0 := by
  apply ComplexScalar.ext <;> simp <;> grind only

private theorem innerDiff {α : Type} (xs : List α) (a b c d : α → ComplexScalar R) :
    innerProduct xs (fun i => a i-b i) (fun i => c i-d i)=
      innerProduct xs a c-innerProduct xs a d-(innerProduct xs b c-innerProduct xs b d) := by
  unfold innerProduct
  simp only [←Compression.sumOverSub]
  apply sumOverCongr
  intro i
  rw [starSub]
  grind only

private theorem wedgeInner {α : Type} (xs : List α) (x y u v : α → ComplexScalar R) :
    innerProduct (productIndices xs xs) (wedge x y) (wedge u v)=
      2*(innerProduct xs x u*innerProduct xs y v-innerProduct xs x v*innerProduct xs y u) := by
  unfold wedge
  rw [innerDiff,tensorInner,tensorInner,tensorInner,tensorInner]
  grind only

private theorem innerNorm {α : Type} (xs : List α) (F : α → ComplexScalar R) :
    (innerProduct xs F F).re=normSum xs F := by
  unfold innerProduct normSum
  rw [(HighestCosetFourier.realSum _ _).1]
  simp only [re_star_mul_self]

private theorem conjugateInner {α : Type} (xs : List α) (x y : α → ComplexScalar R) :
    innerProduct xs x y=star (innerProduct xs y x) := by
  unfold innerProduct
  rw [ComplexExterior.starSumOver]
  apply sumOverCongr
  intro i
  rw [star_mul,star_star,CommSemiring.mul_comm]


private def crossed {α : Type} (a b c d : α → ComplexScalar R) (i : α×α) :=
  wedge a b i-wedge c d i

private def parallel {α : Type} (a b c d : α → ComplexScalar R) (i : α×α) :=
  wedge a c i+wedge d b i

private theorem splitWedge {α : Type} (a b c d : α → ComplexScalar R) (i : α×α) :
    wedge (fun j => a j+d j) (fun j => c j+b j) i=crossed a b c d i+parallel a b c d i := by
  unfold crossed parallel wedge tensor
  grind only

private theorem parallelSkew {α : Type} (a b c d : α → ComplexScalar R) (i : α×α) :
    parallel a b c d i.swap= -parallel a b c d i := by
  unfold parallel
  rw [wedgeSkew,wedgeSkew]
  grind only

private theorem splitNorm {α : Type} (xs : List α) (a b c d : α → ComplexScalar R)
    (ab : innerProduct xs a b=0) (ad : innerProduct xs a d=0)
    (cb : innerProduct xs c b=0) (cd : innerProduct xs c d=0) :
    normSum (productIndices xs xs) (fun i => crossed a b c d i+parallel a b c d i)=
      normSum (productIndices xs xs) (parallel a b c d)+2*crossedMass xs a b c d := by
  let zs := productIndices xs xs
  let B := crossed a b c d
  let P := parallel a b c d
  have rev {x y : α → ComplexScalar R} (h : innerProduct xs x y=0) :
      innerProduct xs y x=0 := by rw [conjugateInner xs y x,h,zeroStar]
  have ba := rev ab
  have da := rev ad
  have bc := rev cb
  have dc := rev cd
  have crossZero : innerProduct zs B P=0 := by
    unfold zs B P crossed parallel innerProduct
    have eq : ∀i, star (wedge a b i-wedge c d i)*(wedge a c i+wedge d b i)=
        (star (wedge a b i)*wedge a c i+star (wedge a b i)*wedge d b i)-
          (star (wedge c d i)*wedge a c i+star (wedge c d i)*wedge d b i) := by
      intro i
      rw [starSub]
      grind only
    simp only [eq,Compression.sumOverSub,sumOverAdd]
    change innerProduct (productIndices xs xs) (wedge a b) (wedge a c)+
      innerProduct (productIndices xs xs) (wedge a b) (wedge d b)-
        (innerProduct (productIndices xs xs) (wedge c d) (wedge a c)+
          innerProduct (productIndices xs xs) (wedge c d) (wedge d b))=0
    simp only [wedgeInner,ab,ad,cb,cd,ba,da,bc,dc,Semiring.zero_mul,Semiring.mul_zero]
    grind only
  let X := fun i => tensor a b i-tensor c d i
  let Y := fun i => tensor b a i-tensor d c i
  have diff : B=(fun i => X i-Y i) := by
    funext i
    unfold B X Y crossed wedge
    grind only
  have xy : innerProduct zs X Y=0 := by
    unfold zs X Y
    rw [innerDiff]
    simp only [tensorInner,ab,ad,cb,cd,ba,da,bc,dc,Semiring.mul_zero]
    grind only
  have yx : innerProduct zs Y X=0 := by rw [conjugateInner zs Y X,xy,zeroStar]
  have xx : normSum zs X=crossedMass xs a b c d := by
    unfold zs X normSum crossedMass
    rw [sumPairs]
    rfl
  have yy : normSum zs Y=normSum zs X := by
    unfold zs X Y normSum
    rw [sumPairs,sumPairs,sumOverSwap]
    apply sumOverCongr
    intro i
    apply sumOverCongr
    intro j
    unfold tensor
    change normSq (b j*a i-d j*c i)=normSq (a i*b j-c i*d j)
    rw [CommSemiring.mul_comm (b j),CommSemiring.mul_comm (d j)]
  have bn : normSum zs B=2*crossedMass xs a b c d := by
    rw [←innerNorm,diff,innerDiff,xy,yx]
    simp only [re_sub,innerNorm,yy,xx,re_zero]
    grind only
  have crossZeroRev : innerProduct zs P B=0 := by
    rw [conjugateInner zs P B,crossZero,zeroStar]
  change normSum zs (fun i => B i+P i)=normSum zs P+2*crossedMass xs a b c d
  rw [←innerNorm,innerExpand,crossZero,crossZeroRev]
  simp only [re_add,re_zero,innerNorm,bn]
  grind only

private theorem amplitudeTest {n : Nat} (x y : Basis n → ComplexScalar R) (p : Word n) :
    amplitude x y p=star (innerProduct (qubitIndices n) y (test p x)) := by
  unfold amplitude pairs innerProduct
  rw [sumPairs,sumOverSwap,ComplexExterior.starSumOver]
  apply sumOverCongr
  intro j
  unfold test StabilizerCharacterBasis.act
  rw [star_mul,star_star,star_star,sumOverMulLeft]
  apply sumOverCongr
  intro i
  grind only


private theorem coefficientSub {n : Nat} (F G : Pair n → ComplexScalar R) (p : Word n) :
    coefficient (fun i => F i-G i) p=coefficient F p-coefficient G p := by
  unfold coefficient
  rw [←Compression.sumOverSub]
  apply sumOverCongr
  intro i
  grind only

private theorem imageSplit {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (all : ∀i,i∈xs) (Q : Mx α R) (x : α → ComplexScalar R) (i : α) :
    image xs Q x i+image xs (compl Q) x i=x i := by
  let X (j : α) (_ : Unit) := x j
  change matMul xs Q X i ()+matMul xs (compl Q) X i ()=x i
  unfold compl
  rw [subLeft,idLeft xs nd all]
  unfold subM
  grind only

private theorem insideOutsideOrth {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (all : ∀i,i∈xs) (Q : Mx α R) (proj : Projection xs Q) (x y : α → ComplexScalar R) :
    innerProduct xs (image xs Q x) (image xs (compl Q) y)=0 := by
  have cross : matMul xs Q (compl Q)=(fun _ _ => 0) := by
    unfold compl
    rw [subRight,idRight xs nd all,proj.square]
    funext i j
    unfold subM
    grind only
  let X (i : α) (_ : Unit) := x i
  let Y (i : α) (_ : Unit) := y i
  change matMul xs (PhysicalPairedReduction.dagger (matMul xs Q X))
    (matMul xs (compl Q) Y) () ()=0
  rw [PhysicalPairedReduction.daggerProduct,proj.herm,matMulAssoc,
    ←matMulAssoc xs xs Q (compl Q) Y,cross]
  have zeros {ι : Type} (is : List ι) : sumOver is (fun _ => (0:ComplexScalar R))=0 := by
    induction is with
    | nil => rfl
    | cons a as ih =>
      change 0+sumOver as (fun _ => (0:ComplexScalar R))=0
      rw [ih]
      grind only
  unfold matMul
  simp only [Semiring.zero_mul,zeros,Semiring.mul_zero]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

/-- Odd words outside the selected character cosets contain all of the mixed
inside-outside component of a two-vector exterior product. -/
theorem outsidePair {n : Nat} (half : R) (unit : 2*half=1)
    {A : Basis n → Fin 7 → ComplexScalar R} (C : SmallCodes half A)
    (z : TransposeOffset C.G) (x y : Basis n → ComplexScalar R) :
    let xs := qubitIndices n
    let Q := unionProjector C
    let V := compl Q
    crossedMass xs (image xs Q x) (image xs V y) (image xs Q y) (image xs V x)≤
      oddAverage half (fun p => if member z C.c C.a C.b p then 0 else normSq (amplitude x y p)) := by
  let xs := qubitIndices n
  let Q := unionProjector C
  let V := compl Q
  let a := image xs Q x
  let b := image xs V y
  let c := image xs Q y
  let d := image xs V x
  let P := parallel a b c d
  let F := wedge x y
  let flag := member z C.c C.a C.b
  have nd := HyperplaneIncidence.normalsNodup n
  have all := @qubitIndicesComplete n
  have q := unionIsProjection half unit C
  have orth := insideOutsideOrth xs nd all Q q
  have eq : F=(fun i => crossed a b c d i+P i) := by
    funext i
    have ex : (fun j => a j+d j)=x := funext (imageSplit xs nd all Q x)
    have ey : (fun j => c j+b j)=y := funext (imageSplit xs nd all Q y)
    rw [←splitWedge,ex,ey]
  have mass : normSum (pairs n) F=normSum (pairs n) P+2*crossedMass xs a b c d := by
    rw [eq]
    exact splitNorm xs a b c d (orth x y) (orth x x) (orth y y) (orth y x)
  have selected (p : Word n) (hp : p∈oddWords n) (sel : flag p=true) :
      coefficient F p=coefficient P p := by
    have odd := (List.mem_filter.mp hp).2
    have sign : (wordSign p : ComplexScalar R)= -1 := by
      rw [MixedDefect.oddWordTransposeSign,odd]
      rfl
    have off (u v : Basis n → ComplexScalar R) :
        amplitude (image xs Q u) (image xs V v) p=0 := by
      have t := selectedCrossZero half unit C z p sel u v
      change innerProduct xs (image xs Q u) (test p (image xs V v))=0 at t
      have e := amplitudeTest (image xs V v) (image xs Q u) p
      change _ = star (innerProduct xs (image xs Q u) (test p (image xs V v))) at e
      rw [t,zeroStar,amplitudeTranspose p (image xs Q u) (image xs V v),sign] at e
      grind only
    have abz := off x y
    have cdz := off y x
    change amplitude a b p=0 at abz
    change amplitude c d p=0 at cdz
    rw [eq,coefficientAdd]
    unfold crossed
    rw [coefficientSub,coefficientWedge a b p hp,coefficientWedge c d p hp,abz,cdz]
    grind only
  let out := oddAverage half (fun p => if flag p then 0 else normSq (amplitude x y p))
  have restricted (p : Word n) (hp : p∈oddWords n) :
      normSq (coefficient F p)≤normSq (coefficient P p)+
        4*(if flag p then 0 else normSq (amplitude x y p)) := by
    cases hm : flag p
    · simp only [Bool.false_eq_true,ite_false]
      change normSq (coefficient (wedge x y) p)≤_
      rw [coefficientWedge x y p hp,normSq_mul]
      have four : normSq (2:ComplexScalar R)=4 := by
        change normSq (ofReal (2:R))=4
        rw [normSq_ofReal]
        grind only
      rw [four]
      have h := normSq_nonnegative (coefficient P p)
      grind only
    · simp only [ite_true,Semiring.mul_zero]
      rw [selected p hp hm]
      grind only
  have ordered := Compression.sumOverNonnegative (oddWords n)
    (fun p => normSq (coefficient P p)+4*(if flag p then 0 else normSq (amplitude x y p))-
      normSq (coefficient F p))
    (fun p hp => by have h := restricted p hp; grind only)
  rw [Compression.sumOverSub,sumOverAdd,←sumOverMulLeft] at ordered
  have half0 : 0≤half := by
    have pos := OrderedRing.zero_lt_one (R:=R)
    grind only
  have scale0 : 0≤2*half^n := by
    have pow0 : ∀k : Nat, 0≤half^k := by
      intro k
      induction k with
      | zero => rw [Semiring.pow_zero]; have h := OrderedRing.zero_lt_one (R:=R); grind only
      | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih half0
    exact OrderedRing.mul_nonneg (by have h := OrderedRing.zero_lt_one (R:=R); grind only) (pow0 n)
  have scaled := OrderedRing.mul_nonneg scale0 ordered
  have df := skewNorm half unit F (wedgeSkew x y)
  have dp := skewNorm half unit P (parallelSkew a b c d)
  unfold oddAverage at df dp
  rw [mass] at df
  have h : 0≤2*half^n*sumOver (oddWords n) (fun p => normSq (coefficient P p))+
      4*out-2*half^n*sumOver (oddWords n) (fun p => normSq (coefficient F p)) := by
    have ident :
        2*half^n*sumOver (oddWords n) (fun p => normSq (coefficient P p))+
            4*out-2*half^n*sumOver (oddWords n) (fun p => normSq (coefficient F p))=
          2*half^n*(sumOver (oddWords n) (fun p => normSq (coefficient P p))+
            4*sumOver (oddWords n) (fun p => if flag p then 0 else normSq (amplitude x y p))-
            sumOver (oddWords n) (fun p => normSq (coefficient F p))) := by
      unfold out oddAverage
      grind only
    rw [ident]
    exact scaled
  rw [dp,df] at h
  change crossedMass xs a b c d≤out
  grind only


open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalProjectionAngles (code)
open StabilizerPopulationRounding (pop middlePop popNonnegative)
open StabilizerPairedCharacters (pairedHead representative)
open WeightedProbeShift (physicalPayment)

noncomputable def outsideEnergy {n : Nat} {half : R} {A : Basis n → Fin 7 → ComplexScalar R}
    (C : SmallCodes half A) (i : Fin 7) : R :=
  energy (qubitIndices n) (compl (unionProjector C)) (fun t => A t i)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem frameNorm {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (i : Fin 7) : normSum (qubitIndices n) (fun t => A t i)=1 := by
  have t := congrArg ComplexScalar.re (orth i i)
  change (innerProduct (qubitIndices n) (fun t => A t i) (fun t => A t i)).re=_ at t
  simpa only [innerNorm,ite_true,re_one] using t

theorem outsideEnergyBounds {n : Nat} (half : R) (unit : 2*half=1)
    {A : Basis n → Fin 7 → ComplexScalar R} (orth : OrthonormalFrame A) (C : SmallCodes half A) :
    (∀i, 0≤outsideEnergy C i) ∧
      outsideEnergy C 1+outsideEnergy C 2+2*outsideEnergy C 0≤SharedRoundedSector.error C := by
  let xs := qubitIndices n
  let Q := unionProjector C
  let d := representative C.T (wordAdd C.c (wordAdd C.a C.b))
  have nd := HyperplaneIncidence.normalsNodup n
  have all := @qubitIndicesComplete n
  have q := unionIsProjection half unit C
  have v := complement xs nd all Q q
  have expansion (i : Fin 7) : outsideEnergy C i=1-
      ((pop half C.L C.a (fun t => A t i)+pop half C.L C.b (fun t => A t i))+
        (pop half C.L C.c (fun t => A t i)+pop half C.L d (fun t => A t i))) := by
    change energy xs (compl Q) (fun t => A t i)=_
    unfold Q compl unionProjector code
    rw [energySub,energyIdentity xs nd all,frameNorm A orth i,energyAdd,energyAdd,energyAdd]
    rfl
  have nonnegative (i : Fin 7) : 0≤outsideEnergy C i := by
    change 0≤energy xs (compl Q) (fun t => A t i)
    rw [energyNorm _ _ v]
    exact Compression.sumOverNonnegative _ _ (fun _ _ => normSq_nonnegative _)
  have f : outsideEnergy C 0≤1-pairedHead half C.L C.T A (wordAdd C.a C.b) C.c := by
    rw [expansion]
    change _≤1-(pop half C.L C.c (fun t => A t 0)+pop half C.L d (fun t => A t 0))
    have a := popNonnegative half unit C.L C.a (fun t => A t 0)
    have b := popNonnegative half unit C.L C.b (fun t => A t 0)
    grind only
  have e : outsideEnergy C 1+outsideEnergy C 2≤2-middlePop half C.L C.a A-middlePop half C.L C.b A := by
    rw [expansion,expansion]
    have c1 := popNonnegative half unit C.L C.c (fun t => A t 1)
    have d1 := popNonnegative half unit C.L d (fun t => A t 1)
    have c2 := popNonnegative half unit C.L C.c (fun t => A t 2)
    have d2 := popNonnegative half unit C.L d (fun t => A t 2)
    unfold middlePop
    grind only
  refine ⟨nonnegative,?_⟩
  unfold SharedRoundedSector.error
  grind only

/-- The actual odd-Pauli leakage controls both head–middle crossed masses
on the same four-dimensional character union. -/
theorem outsideHeadPrice {n : Nat} (half : R) (unit : 2*half=1)
    {A : Basis n → Fin 7 → ComplexScalar R} (orth : OrthonormalFrame A) (C : SmallCodes half A)
    (z : TransposeOffset C.G) :
    let e := outsideEnergy C 1+outsideEnergy C 2
    let f := outsideEnergy C 0
    e+2*f-2*f*e≤oddAverage half (fun p =>
      if member z C.c C.a C.b p then 0 else SixPointRounding.headWeight A p) := by
  let xs := qubitIndices n
  let Q := unionProjector C
  let x (t : Basis n) := A t 0
  let flag := member z C.c C.a C.b
  let part (j : Fin 7) (p : Word n) := if flag p then 0 else normSq (amplitude x (fun t => A t j) p)
  let e := outsideEnergy C 1+outsideEnergy C 2
  let f := outsideEnergy C 0
  have each (j : Fin 7) (ne : 0≠j) :
      outsideEnergy C j+f-2*f*outsideEnergy C j≤oddAverage half (part j) := by
    have ot : innerProduct xs x (fun t => A t j)=0 := by
      have t := orth 0 j
      change innerProduct xs x (fun t => A t j)=(if 0=j then 1 else 0) at t
      rwa [ite_eq_right ne] at t
    have cut := crossedMassPrice xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
      Q (unionIsProjection half unit C) x (fun t => A t j) (frameNorm A orth 0) (frameNorm A orth j) ot
    exact Std.le_trans cut (outsidePair half unit C z x (fun t => A t j))
  have one := each 1 (by decide)
  have two := each 2 (by decide)
  have perWord (p : Word n) : (if flag p then 0 else SixPointRounding.headWeight A p)=part 1 p+part 2 p := by
    unfold part SixPointRounding.headWeight JointProbePayment.pairWeight
    rw [←StabilizerExteriorTrace.frameAmplitude,←StabilizerExteriorTrace.frameAmplitude]
    change (if flag p then 0 else normSq (amplitude x (fun t => A t 1) p)+
      normSq (amplitude x (fun t => A t 2) p))=_
    cases flag p <;> simp <;> grind only
  have sum : oddAverage half (fun p => if flag p then 0 else SixPointRounding.headWeight A p)=
      oddAverage half (part 1)+oddAverage half (part 2) := by
    unfold oddAverage
    rw [sumOverCongr _ perWord,sumOverAdd]
    grind only
  change e+2*f-2*f*e≤oddAverage half (fun p => if flag p then 0 else SixPointRounding.headWeight A p)
  rw [sum]
  unfold e
  grind only

/-- A true small physical shared Gram pays for the full weighted head and
middle mass outside the rounded four-dimensional character union. -/
theorem physicalLeakagePrice (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (m : Fin 7 → R)
    (orth : OrthonormalFrame A) (C : SmallCodes half A)
    (small : 7*SharedRoundedSector.error C≤1) (z : TransposeOffset C.G) :
    297*(outsideEnergy C 1+outsideEnergy C 2+2*outsideEnergy C 0)≤
      196*(physicalPayment half unit k A m).kappa := by
  let leak := oddAverage half (fun p => if member z C.c C.a C.b p then 0 else SixPointRounding.headWeight A p)
  let e := outsideEnergy C 1+outsideEnergy C 2
  let f := outsideEnergy C 0
  let E := e+2*f
  obtain ⟨nonnegative,cap⟩ := outsideEnergyBounds half unit orth C
  have E0 : 0≤E := by
    have p := nonnegative 0
    have q := nonnegative 1
    have r := nonnegative 2
    unfold E e f
    grind only
  have cap7 : 7*E≤1 := by
    change E≤SharedRoundedSector.error C at cap
    grind only
  have paid := (SharedRoundedSector.oddOutsidePrice half unit k A m orth C small z).2
  change 11*leak≤7*(physicalPayment half unit k A m).kappa at paid
  have crossed := outsideHeadPrice half unit orth C z
  change E-2*f*e≤leak at crossed
  have product := OrderedRing.mul_nonneg E0 (show 0≤1-7*E by grind only)
  have square := squareNonnegative (e-2*f)
  have debit : 27*E≤28*leak := by unfold E at product crossed ⊢; grind only
  change 297*E≤196*(physicalPayment half unit k A m).kappa
  grind only


/-- The four-character union and its energy price follow from the physical
small-Gram threshold alone. -/
theorem smallGramUnion (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (m : Fin 7 → R)
    (orth : OrthonormalFrame A) (small : 24*(physicalPayment half unit k A m).kappa≤1) :
    ∃C : SmallCodes half A, 7*SharedRoundedSector.error C<1 ∧
      297*(outsideEnergy C 1+outsideEnergy C 2+2*outsideEnergy C 0)≤
        196*(physicalPayment half unit k A m).kappa := by
  obtain ⟨C,error⟩ := SharedRoundedSector.physicalCodes half unit k A m orth small
  obtain ⟨z⟩ := offsetExists half unit C.T
  exact ⟨C,error,physicalLeakagePrice half unit k A m orth C (Std.le_of_lt error) z⟩

end RankSeven.SharedOddLeakage

#print axioms RankSeven.SharedOddLeakage.skewInner
#print axioms RankSeven.SharedOddLeakage.skewNorm

#print axioms RankSeven.SharedOddLeakage.outsidePair

#print axioms RankSeven.SharedOddLeakage.outsideEnergyBounds
#print axioms RankSeven.SharedOddLeakage.outsideHeadPrice
#print axioms RankSeven.SharedOddLeakage.physicalLeakagePrice
#print axioms RankSeven.SharedOddLeakage.smallGramUnion
