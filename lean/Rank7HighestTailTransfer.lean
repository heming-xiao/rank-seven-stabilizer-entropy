import Rank7HighestExteriorComponents

namespace RankSeven.HighestTailTransfer

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestExteriorOccupation HighestExteriorComponents
open PhysicalCutCapacities UpperPairLoss UpperPairPfaffian AnticommutingDefect
open WedgeSquareIntertwiner (wedgeSquareColumn)
open HighestExteriorStability (output)
open MixedDefect (oddWords)
open PauliPairContraction (normSum)
open ExteriorCuts (Wedge7 wedges)
open PackingPolynomial (physicalWeights link)
open UpperPairCap (walls)
variable {R α β : Type} [CommRing R]

theorem sumPairs {C : Type} [CommRing C] (xs : List α) (ys : List β) (f : α×β→C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def tailColumn {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (w : Basis n×Basis n→ComplexScalar R)
    (i j : Fin 5) (p : Word n) :=
  ofReal half*sumOver (fourIndices (qubitIndices n)) (fun t =>
    star (w t.1*(A t.2.1 (rest i)*A t.2.2 (rest j)))*wedgeSquareColumn half p t)

def rows (n : Nat) := productIndices (productIndices (List.finRange 5) (List.finRange 5)) (oddWords n)

def transfer {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (w : Basis n×Basis n→ComplexScalar R)
    (i : (Fin 5×Fin 5)×Word n) := tailColumn half A w i.1.2 i.1.1 i.2

theorem linear {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (v : Fin 4→Basis n×Basis n→ComplexScalar R)
    (a b c d : R) (r : (Fin 5×Fin 5)×Word n) :
    transfer half A (output (fun t j => v j t) a b c d) r=output (fun t j => transfer half A (v j) t) a b c d r := by
  let xs := fourIndices (qubitIndices n)
  let K (t : Four (Basis n)) := star (A t.2.1 (rest r.1.2)*A t.2.2 (rest r.1.1))*wedgeSquareColumn half r.2 t
  let F (j : Fin 4) (t : Four (Basis n)) := star (v j t.1)*K t
  have re (u : R) : star (ofReal u)=ofReal u := by apply ComplexScalar.ext <;> simp <;> grind only
  have form (w : Basis n×Basis n→ComplexScalar R) : transfer half A w r=ofReal half*sumOver xs (fun t => star (w t.1)*K t) := by
    unfold transfer tailColumn K; congr 1; apply sumOverCongr; intro t; rw [star_mul]; grind only
  unfold output; simp only [form]
  have pt (t : Four (Basis n)) : star (ofReal a*v 0 t.1+ofReal b*v 1 t.1+ofReal c*v 2 t.1+ofReal d*v 3 t.1)*K t=
      ofReal a*F 0 t+ofReal b*F 1 t+ofReal c*F 2 t+ofReal d*F 3 t := by unfold F; simp only [star_add,star_mul,re]; grind only
  rw [sumOverCongr xs pt]; simp only [sumOverAdd,←sumOverMulLeft]; unfold F; grind only

theorem waveSwap {n : Nat} (half : R) (h2 : 2*half=1) (p : Word n) (hp : p∈oddWords n)
    (a b c d : Basis n) : wedgeSquareColumn half p ((b,a),c,d)= -wedgeSquareColumn half p ((a,b),c,d) := by
  rw [physicalColumnPfaffian half h2 p hp,physicalColumnPfaffian half h2 p hp,wordSkew p hp a b]; grind only

theorem fullColumn {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R)
    (i j : Fin 5) (p : Word n) (hp : p∈oddWords n) :
    tailColumn half A (exterior (fun t => A t 0) (fun t => A t 1)) i j p=columnCoef half A ((0,1),rest i,rest j) p := by
  let xs := qubitIndices n
  let K (t : Four (Basis n)) := star (A t.2.1 (rest i)*A t.2.2 (rest j))*wedgeSquareColumn half p t
  let f (t : Four (Basis n)) := star (A t.1.1 0*A t.1.2 1)*K t
  let g (t : Four (Basis n)) := star (A t.1.1 1*A t.1.2 0)*K t
  have ex : tailColumn half A (exterior (fun t => A t 0) (fun t => A t 1)) i j p=
      ofReal half*(sumOver (fourIndices xs) f-sumOver (fourIndices xs) g) := by
    unfold tailColumn; rw [←Compression.sumOverSub]; congr 1; apply sumOverCongr; intro t
    unfold exterior f g K
    have sub (a b : ComplexScalar R) : star (a-b)=star a-star b := by apply ComplexScalar.ext <;> simp <;> grind only
    rw [star_mul,sub]; grind only
  have swapped : sumOver (fourIndices xs) g= -(sumOver (fourIndices xs) f) := by
    have neg := sumOverMulLeft (fourIndices xs) f (-1)
    rw [show -(sumOver (fourIndices xs) f)=sumOver (fourIndices xs) (fun t => (-1)*f t) by rw [←neg]; grind only]
    unfold fourIndices; simp only [sumPairs]
    rw [sumOverSwap xs xs]
    apply sumOverCongr; intro a; apply sumOverCongr; intro b
    apply sumOverCongr; intro c; apply sumOverCongr; intro d
    change star (A b 1*A a 0)*(star (A c (rest i)*A d (rest j))*wedgeSquareColumn half p ((b,a),c,d))=_
    rw [waveSwap half h2 p hp,CommSemiring.mul_comm (A b 1)]; unfold f K; grind only
  have id : columnCoef half A ((0,1),rest i,rest j) p=sumOver (fourIndices xs) f := by
    change sumOver (fourIndices xs) (fun t => star (tensorFour A t ((0,1),rest i,rest j))*wedgeSquareColumn half p t)=_
    apply sumOverCongr; intro t; unfold tensorFour tensor f K; rw [star_mul]; grind only
  have h : 2*ofReal half=(1:ComplexScalar R) := by change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp [ofReal] <;> grind only
  rw [ex,id,swapped]; grind only

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


theorem fullTransfer (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R) :
    normSum (rows (k+3)) (transfer half A (exterior (fun t => A t 0) (fun t => A t 1)))=
      (3*(4*half^(k+3)))*link (physicalWeights half h2 k A) 0 1 := by
  let n := k+3
  let es := List.finRange 5
  let w := exterior (fun t => A t 0) (fun t => A t 1)
  have f (j i : Fin 5) : sumOver (oddWords n) (fun p => normSq (tailColumn half A w i j p))=rowMass half A ((0,1),rest i,rest j) := by
    apply sumCongrMem; intro p hp; rw [fullColumn half h2 A i j p hp]
  change sumOver (rows n) (fun r => normSq (transfer half A w r))=_
  unfold rows; simp only [sumPairs,transfer,f]
  rw [orderedColumns half h2 A,wallSum]
  have price (s : Wedge7) := coordinateMass half h2 k A s
  rw [sumOverMulLeft,sumOverMulLeft]
  apply sumOverCongr; intro s; exact price s

theorem componentTransfer (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    {G : HeavyPauliGroup.MaximalFamily (k+3)} (L : StabilizerCharacterBasis.Lift G) (c d : Word (k+3)) :
    let v := component (HighestExteriorComponents.split half L c d) (qubitIndices (k+3)) (fun t => A t 0) (fun t => A t 1)
    let z t i := transfer half A (v i) t
    normSum (rows (k+3)) (output z 1 1 1 1)=
      (3*(4*half^(k+3)))*link (physicalWeights half h2 k A) 0 1 := by
  let v := component (HighestExteriorComponents.split half L c d) (qubitIndices (k+3)) (fun t => A t 0) (fun t => A t 1)
  have e := (componentValues half L c d (fun t => A t 0) (fun t => A t 1)).2.2
  have eq := funext (linear half A v 1 1 1 1)
  rw [e] at eq
  dsimp only; rw [←eq]; exact fullTransfer half h2 k A

end RankSeven.HighestTailTransfer

#print axioms RankSeven.HighestTailTransfer.linear
#print axioms RankSeven.HighestTailTransfer.fullColumn
#print axioms RankSeven.HighestTailTransfer.fullTransfer
#print axioms RankSeven.HighestTailTransfer.componentTransfer

