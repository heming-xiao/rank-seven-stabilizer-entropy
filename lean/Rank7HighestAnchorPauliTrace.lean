import Rank7HighestAnchorMetric

namespace RankSeven.HighestAnchorPauliTrace

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestExteriorOccupation
open HighestTailTransfer HighestCosetFourier FrameExteriorSector
open UpperPairLoss (rest)
open UpperPairCap (walls)
open PauliPairContraction (normSum)
open ExteriorCuts (Wedge7 wedges)
open PackingPolynomial (physicalWeights link)
open ExteriorPauliBase (permutations oddPermutation)
open GenericExteriorKernel (signed reorder)
open HyperplaneInduction (minor4 sourceSite)
open StabilizerCharacterBasis (act)
variable {R α : Type} [CommRing R]

def headFrame {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (s v : Basis n→ComplexScalar R)
    (t : Basis n) (j : Fin 7) := if j=0 then s t else if j=1 then v t else A t j

theorem sameTail {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (s v : Basis n→ComplexScalar R) (w : Basis n×Basis n→ComplexScalar R) :
    transfer half (headFrame A s v) w=transfer half A w := by
  have non (i : Fin 5) : rest i≠0 ∧ rest i≠1 := by revert i; decide
  funext r; unfold transfer tailColumn headFrame
  simp only [(non _).1,(non _).2,ite_false]

private theorem productIP {β : Type} (xs : List α) (ys : List β) (x u : α→ComplexScalar R) (y v : β→ComplexScalar R) :
    innerProduct (productIndices xs ys) (fun t => x t.1*y t.2) (fun t => u t.1*v t.2)=innerProduct xs x u*innerProduct ys y v := by
  unfold innerProduct
  rw [←factorProductSum]; apply sumOverCongr; intro t; rw [star_mul]; grind only

theorem frameTensorAction {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) (x y : Four (Fin 7)) :
    tensorFour (FrameExteriorSector.framedWord A p) x y=
      innerProduct (fourIndices (qubitIndices n)) (fun t => tensorFour A t x)
      (fun t => tensorFour (fun a j => act p (fun b => A b j) a) t y) := by
  let xs := qubitIndices n
  let F (j : Fin 7) (a : Basis n) := A a j
  let V (j : Fin 7) := act p (F j)
  have h (j k : Fin 7) : FrameExteriorSector.framedWord A p j k=innerProduct xs (F j) (V k) := rfl
  let f (j : Fin 7×Fin 7) (t : Basis n×Basis n) := F j.1 t.1*F j.2 t.2
  let v (j : Fin 7×Fin 7) (t : Basis n×Basis n) := V j.1 t.1*V j.2 t.2
  let ps := productIndices xs xs
  have split (j l : Fin 7×Fin 7) : innerProduct ps (f j) (v l)=innerProduct xs (F j.1) (V l.1)*innerProduct xs (F j.2) (V l.2) :=
    productIP xs xs _ _ _ _
  have full := productIP ps ps (f x.1) (v y.1) (f x.2) (v y.2)
  change _=innerProduct (productIndices ps ps) (fun t => f x.1 t.1*f x.2 t.2) (fun t => v y.1 t.1*v y.2 t.2)
  rw [full,split,split]; rfl

def wordExpectation {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) (w : Wedge7) :=
  sumOver permutations (fun σ => signed (oddPermutation σ)
    (innerProduct (fourIndices (qubitIndices n)) (fun t => tensorFour A t (FrameExteriorSector.sourceTuple w))
      (fun t => tensorFour (fun a j => act p (fun b => A b j) a) t (reorder (FrameExteriorSector.sourceTuple w) σ))))

theorem wordExpectationMinor {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) (w : Wedge7) :
    wordExpectation A p w=minor4 (FrameExteriorSector.framedWord A p) (sourceSite w) w := by
  rw [←FrameExteriorSector.tensorExteriorSector]; unfold wordExpectation FrameExteriorSector.exteriorSector
  apply sumOverCongr; intro σ; rw [frameTensorAction]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem wallSum (x : Wedge7→R) : link x 0 1=sumOver walls x := by
  have cut : wedges.filter (fun w => PackingDual.occupied w 0 && PackingDual.occupied w 1)=walls := by decide
  have select (xs : List Wedge7) (f : Wedge7→Bool) : sumOver xs (fun i => if f i then x i else 0)=sumOver (xs.filter f) x := by
    induction xs with | nil => rfl | cons i xs ih => cases e : f i <;> simp [sumOver,e] at ih ⊢ <;> grind only
  exact (select wedges _).trans (congrArg (fun ws => sumOver ws x) cut)

theorem anchorWordTrace (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R) (s v : Basis (k+3)→ComplexScalar R) :
    let n := k+3
    let H := headFrame A s v
    normSum (rows n) (transfer half A (exterior s v))=
      3*half^(n+n)*sumOver walls (fun w => sumOver (words n) (fun p => (wordExpectation H p w).re)) := by
  let n := k+3
  let H := headFrame A s v
  let q := 4*half^n
  let h := half^(n+n)
  have m := fullTransfer half h2 k H
  have f0 : (fun t => H t 0)=s := by funext t; rfl
  have f1 : (fun t => H t 1)=v := by funext t; rfl
  rw [f0,f1,sameTail,wallSum] at m
  let weights := physicalWeights half h2 k H
  have pt (w : Wedge7) : q*weights w=h*sumOver (words n) (fun p => (wordExpectation H p w).re) := by
    have e := FrameExteriorSector.sector_eq_weight_mul_physicalEntry half h2 k H w w
    rw [FrameExteriorSector.frameTwirl_exteriorSector,←PhysicalPairedReduction.realEmbeddingPow] at e
    have r := congrArg ComplexScalar.re e
    simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,(realSum _ _).1,←wordExpectationMinor] at r
    change h*(sumOver (words n) (fun p => (wordExpectation H p w).re))-0=q*weights w-0 at r
    grind only
  have scalar := sumOverCongr walls pt
  rw [←sumOverMulLeft,←sumOverMulLeft] at scalar
  change normSum (rows n) (transfer half A (exterior s v))=(3*q)*sumOver walls weights at m
  change normSum (rows n) (transfer half A (exterior s v))=3*h*sumOver walls (fun w => sumOver (words n) (fun p => (wordExpectation H p w).re))
  grind only

open HeavyPauliGroup StabilizerCharacterBasis
open PhysicalCompressionEffect (OrthonormalFrame)

theorem lineBoundFromWords (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    {G : MaximalFamily (k+3)} (L : Lift G) (c : Word (k+3))
    (bound : ∀i : Basis (k+3),0<(block half L c i i).re → ∀v : Basis (k+3)→ComplexScalar R,
      let s t := block half L c t i
      innerProduct (qubitIndices (k+3)) s v=0 →
      half^(k+3)*sumOver walls (fun w => sumOver (words (k+3)) (fun p => (wordExpectation (headFrame A s v) p w).re))≤
        8*((block half L c i i).re*normSum (qubitIndices (k+3)) v)) :
    HighestAnchorVectors.lineBound half A L c := by
  apply HighestAnchorMetric.lineBoundFromOrthogonal half h2 A L c
  intro i pos v
  dsimp only; intro orth
  let n := k+3
  let s t := block half L c t i
  let C := sumOver walls (fun w => sumOver (words n) (fun p => (wordExpectation (headFrame A s v) p w).re))
  let m := (block half L c i i).re*normSum (qubitIndices n) v
  have h := bound i pos v orth
  change half^n*C≤8*m at h
  have one := OrderedRing.zero_lt_one (R:=R)
  have pp (t : Nat) : 0≤half^t := by
    induction t with | zero => rw [Semiring.pow_zero]; grind only | succ t ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have sc := OrderedRing.mul_le_mul_of_nonneg_left h (pp n)
  have eq := anchorWordTrace half h2 k A s v
  change normSum (rows n) (transfer half A (exterior s v))=3*half^(n+n)*C at eq
  rw [Semiring.pow_add] at eq
  change normSum (rows n) (transfer half A (exterior s v))≤2*(3*(4*half^n))*m
  grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem physicalHighestFromWords (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A)
    (bound : ∀{G : MaximalFamily (k+3)} (L : Lift G) (c : Word (k+3)) (i : Basis (k+3)),
      0<(block half L c i i).re → ∀v : Basis (k+3)→ComplexScalar F,
      let s t := block half L c t i
      innerProduct (qubitIndices (k+3)) s v=0 →
      half^(k+3)*sumOver walls (fun w => sumOver (words (k+3)) (fun p => (wordExpectation (headFrame A s v) p w).re))≤
        8*((block half L c i i).re*normSum (qubitIndices (k+3)) v)) :
    2*UpperFrameTrace.highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne :=
  HighestAnchorVectors.physicalHighestFromLines half h2 k A mu orth (fun L c => lineBoundFromWords half h2 k A L c (bound L c))
end Field

end RankSeven.HighestAnchorPauliTrace

#print axioms RankSeven.HighestAnchorPauliTrace.frameTensorAction
#print axioms RankSeven.HighestAnchorPauliTrace.wordExpectationMinor
#print axioms RankSeven.HighestAnchorPauliTrace.anchorWordTrace
#print axioms RankSeven.HighestAnchorPauliTrace.physicalHighestFromWords

