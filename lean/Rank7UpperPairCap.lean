import Rank7UpperPairLoss
namespace RankSeven.UpperPairCap
open Lean.Grind Pauli ComplexScalar PhysicalCutCapacities AnticommutingDefect UpperPairPfaffian UpperPairLoss
open ExteriorCuts (Wedge7 wedges)
open PackingPolynomial (link physicalWeights)
variable {R : Type} [CommRing R]

def walls : List Wedge7 := [⟨0,1,2,3,by decide,by decide,by decide⟩,⟨0,1,2,4,by decide,by decide,by decide⟩,⟨0,1,2,5,by decide,by decide,by decide⟩,⟨0,1,2,6,by decide,by decide,by decide⟩,⟨0,1,3,4,by decide,by decide,by decide⟩,⟨0,1,3,5,by decide,by decide,by decide⟩,⟨0,1,3,6,by decide,by decide,by decide⟩,⟨0,1,4,5,by decide,by decide,by decide⟩,⟨0,1,4,6,by decide,by decide,by decide⟩,⟨0,1,5,6,by decide,by decide,by decide⟩]
private theorem wallList : wedges.filter (fun w => PackingDual.occupied w 0 && PackingDual.occupied w 1)=walls := by decide
private theorem filterSum {C α : Type} [CommRing C] (xs : List α) (h : α→Bool) (f : α→C) :
    sumOver xs (fun i => if h i then f i else 0)=sumOver (xs.filter h) f := by
  induction xs with
  | nil => rfl
  | cons a tail ih => cases b : h a <;> simp [sumOver,b] at ih ⊢ <;> grind only

private theorem zeros {C α : Type} [CommRing C] (xs : List α) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with
  | nil => rfl
  | cons a as ih => change 0+sumOver as _=0; rw [ih]; grind only
private theorem wallSum (x : Wedge7→R) : link x 0 1=sumOver walls x :=
  (filterSum wedges _ _).trans (congrArg (fun ws => sumOver ws x) wallList)

private theorem offDiagonal (g : Fin 5→Fin 5→R) (diag : ∀ i,g i i=0) (flip : ∀ i j,g j i=g i j) :
    sumOver (List.finRange 5) (fun j => sumOver (List.finRange 5) (fun i => g i j)) =
      2*(g 0 1+(g 0 2+(g 0 3+(g 0 4+(g 1 2+(g 1 3+(g 1 4+(g 2 3+(g 2 4+(g 3 4+(0))))))))))) := by
  change (g 0 0+(g 1 0+(g 2 0+(g 3 0+(g 4 0+(0))))))+((g 0 1+(g 1 1+(g 2 1+(g 3 1+(g 4 1+(0))))))+((g 0 2+(g 1 2+(g 2 2+(g 3 2+(g 4 2+(0))))))+((g 0 3+(g 1 3+(g 2 3+(g 3 3+(g 4 3+(0))))))+((g 0 4+(g 1 4+(g 2 4+(g 3 4+(g 4 4+(0))))))+(0))))) = _
  rw [diag 0,diag 1,diag 2,diag 3,diag 4,flip 0 1,flip 0 2,flip 0 3,flip 0 4,flip 1 2,flip 1 3,flip 1 4,flip 2 3,flip 2 4,flip 3 4]; grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem orderedColumns {n} (half : R) (unit : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R) :
    sumOver (List.finRange 5) (fun j => sumOver (List.finRange 5) (fun i => rowMass half A ((0,1),rest i,rest j)))=
      2*sumOver walls (fun w => rowMass half A (FrameExteriorSector.sourceTuple w)) := by
  let g i j := rowMass half A ((0,1),rest i,rest j)
  have flip (i j : Fin 5) : g j i=g i j := by
    apply sumCongrMem
    intro p hp
    change normSq (columnCoef half A ((0,1),rest j,rest i) p)=_
    rw [anchoredSkew half unit A p hp]
    simp only [normSq,re_neg,im_neg]; grind only
  have diag (i : Fin 5) : g i i=0 := by
    have zero (p : Word n) (hp : p∈MixedDefect.oddWords n) : columnCoef half A ((0,1),rest i,rest i) p=0 := by
      have skew := anchoredSkew half unit A p hp (rest i) (rest i)
      have re := congrArg ComplexScalar.re skew; have im := congrArg ComplexScalar.im skew
      apply ComplexScalar.ext <;> simp only [re_neg,im_neg,re_zero,im_zero] at * <;> grind only
    change sumOver (MixedDefect.oddWords n) _=0
    rw [sumCongrMem _ _ (fun _ => (0:R)) (fun p hp => by rw [zero p hp]; simp [normSq]; grind only),zeros]
  exact offDiagonal g diag flip

theorem physicalPairCap (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    3*link (physicalWeights half unit k A) 0 1≤7 := by
  let n := k+3
  let h := half^n
  let os := MixedDefect.oddWords n
  let Q := List.finRange 5
  let L := qubitIndices n
  let S := fun w => rowMass half A (FrameExteriorSector.sourceTuple w)
  let x := physicalWeights half unit k A
  have avg := JointProbeGram.pairWeightAverage half unit A orth 0 1 (by decide)
  change (2*h)*sumOver os (fun p => JointProbePayment.pairWeight A p 0 1)=1 at avg
  let gain (p : Word n) := (2*h)^2*JointProbePayment.pairWeight A p 0 1
  have paid : sumOver os gain=2*h := by
    unfold gain; rw [←sumOverMulLeft]; have m := congrArg (fun a : R => 2*h*a) avg; change 2*h*((2*h)*sumOver os (fun p => JointProbePayment.pairWeight A p 0 1))=2*h*1 at m; grind only
  let m j i (p : Word n) := normSq (columnCoef half A ((0,1),rest i,rest j) p)
  let l t i (p : Word n) := normSq (leg half A ((0,1),rest i) t p)
  have bound := UpperOddCut.sumLe os (fun p hp => perWordOddCut half unit A orth p hp)
  change sumOver os (fun p => gain p+sumOver Q (fun j => sumOver Q (fun i => m j i p)))≤
    sumOver os (fun p => sumOver L (fun t => sumOver Q (fun i => l t i p))) at bound
  rw [sumOverAdd,paid,sumOverSwap os Q] at bound
  have cols (j : Fin 5) : sumOver os (fun p => sumOver Q (fun i => m j i p))=sumOver Q (fun i => rowMass half A ((0,1),rest i,rest j)) := sumOverSwap _ _ _
  rw [sumOverCongr Q cols,orderedColumns half unit A] at bound
  have rows (p : Word n) : sumOver L (fun t => sumOver Q (fun i => l t i p))=sumOver Q (fun i => sumOver L (fun t => l t i p)) := sumOverSwap _ _ _
  rw [sumOverCongr os rows,sumOverSwap os Q] at bound
  have distinctFree : ∀ i : Fin 5, distinct ((0,1),rest i) := by unfold distinct; decide
  have each (i : Fin 5) : 2*sumOver os (fun p => sumOver L (fun t => l t i p))=3*(4*h) :=
    oneHoleFrameMass half unit A orth ((0,1),rest i) (distinctFree i)
  have total := (sumOverMulLeft Q (fun i => sumOver os (fun p => sumOver L (fun t => l t i p))) 2).trans (sumOverCongr Q each)
  change 2*sumOver Q (fun i => sumOver os (fun p => sumOver L (fun t => l t i p)))=
    (3*(4*h))+((3*(4*h))+((3*(4*h))+((3*(4*h))+((3*(4*h))+(0))))) at total
  have normalized (w : Wedge7) : 2*S w=(3*(4*h))*x w := coordinateMass half unit k A w
  have mass := (sumOverMulLeft walls S 2).trans ((sumOverCongr walls normalized).trans (sumOverMulLeft walls x (3*(4*h))).symm)
  rw [←wallSum x] at mass
  change 2*h+2*sumOver walls S≤sumOver Q (fun i => sumOver os (fun p => sumOver L (fun t => l t i p))) at bound
  have onePos : (0:R)<1 := OrderedRing.zero_lt_one
  have hp : 0<half := by grind only
  have pos (m : Nat) : 0<half^m := by
    induction m with
    | zero => simpa only [Semiring.pow_zero] using onePos
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih hp
  have hn : 0<h := pos n
  by_cases ok : 3*link x 0 1≤7
  · exact ok
  · have bad := OrderedRing.mul_pos hn (show 0<3*link x 0 1-7 by grind only)
    grind only
end RankSeven.UpperPairCap
#print axioms RankSeven.UpperPairCap.physicalPairCap
