import Rank7HighestStabilizerLine

namespace RankSeven.HighestAnchorVectors

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestExteriorOccupation HighestExteriorComponents
open FiniteProjectionAngles SlaterUnionBound HighestStabilizerLine HighestTailTransfer HighestExteriorStability
open HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliPairContraction (normSum image)
variable {R α : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def testSource (b : Bool) (u : Fin 4→α→ComplexScalar R) : α→ComplexScalar R :=
  if b then output (fun t i => u i t) 1 0 2 0 else output (fun t i => u i t) 1 2 0 0

theorem wedgeFactor (s x y u v : α→ComplexScalar R) (h l m : ComplexScalar R) (xl : ∀i,h*x i=s i*l) (yl : ∀i,h*y i=s i*m)
    (t : α×α) :
    h*(exterior x v t+exterior u y t)=exterior s (fun i => l*v i-m*u i) t := by
  let a := t.1
  let b := t.2
  have one := xl a; have two := xl b; have three := yl a; have four := yl b
  change h*(x a*v b-v a*x b+(u a*y b-y a*u b))=s a*(l*v b-m*u b)-(l*v a-m*u a)*s b
  grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem sourceShape {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (c d : Word n)
    (b : Bool) (x y : Basis n→ComplexScalar R) (t : Basis n×Basis n) :
    let xs := qubitIndices n
    let u := component (HighestExteriorComponents.split half L c d) xs x y
    let B := block half L (if b then d else c)
    let D := block half L (if b then c else d)
    let S := compl (PhysicalProjectionAngles.code half L c d)
    let tail (v : Basis n→ComplexScalar R) i := image xs D v i+2*image xs S v i
    testSource b u t=exterior (image xs B x) (tail y) t+exterior (tail x) (image xs B y) t := by
  let xs := qubitIndices n
  let C := block half L c
  let D := block half L d
  let S := compl (PhysicalProjectionAngles.code half L c d)
  let P := HighestExteriorComponents.split half L c d
  have null (i : Word n) : exterior (image xs (block half L i) x) (image xs (block half L i) y) t=0 :=
    congrFun (projectedExteriorZero half h2 xs qubitIndicesComplete (block half L i) (PhysicalProjectionAngles.lineProjection half h2 L i) (blockTrace half h2 L i) x y) t
  have n0 : exterior (image xs (P 0) x) (image xs (P 0) y) t=0 := null c
  have n1 : exterior (image xs (P 1) x) (image xs (P 1) y) t=0 := null d
  have scalar0 : ofReal (0:R)=(0:ComplexScalar R) := rfl
  have scalar1 : ofReal (1:R)=(1:ComplexScalar R) := rfl
  have scalar2 : ofReal (2:R)=(2:ComplexScalar R) := rfl
  change testSource b (component P xs x y) t=_
  cases b <;>
    simp (config:={decide:=true}) only [testSource,output,component,sectors,ite_true,ite_false,
      sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,n0,n1,scalar0,scalar1,scalar2,Semiring.one_mul,Semiring.zero_mul,Semiring.add_zero]
  all_goals
    unfold exterior
    simp only [P,HighestExteriorComponents.split]
    simp (config:={decide:=true}) only [ite_false,ite_true]
    grind only

theorem testHasPhysicalAnchor {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (c d : Word n)
    (b : Bool) (x y : Basis n→ComplexScalar R) :
    let xs := qubitIndices n
    let B := block half L (if b then d else c)
    let u := component (HighestExteriorComponents.split half L c d) xs x y
    ∃i∈xs, 0<(B i i).re ∧ ∃v : Basis n→ComplexScalar R, ∀t,
      ofReal (B i i).re*testSource b u t=exterior (fun a => B a i) v t := by
  let xs := qubitIndices n
  let B := block half L (if b then d else c)
  let D := block half L (if b then c else d)
  let S := compl (PhysicalProjectionAngles.code half L c d)
  let tail (v : Basis n→ComplexScalar R) i := image xs D v i+2*image xs S v i
  obtain ⟨i,hi,p,_,col⟩ := characterPivot half h2 L (if b then d else c)
  let u := component (HighestExteriorComponents.split half L c d) xs x y
  refine ⟨i,hi,p,fun j => image xs B x i*tail y j-image xs B y i*tail x j,?_⟩
  intro t
  have e := sourceShape half h2 L c d b x y t
  change testSource b u t=exterior (image xs B x) (tail y) t+exterior (tail x) (image xs B y) t at e
  change ofReal (B i i).re*testSource b u t=_
  rw [e]; exact wedgeFactor (fun a => B a i) (image xs B x) (image xs B y) (tail x) (tail y) _ _ _ (col x) (col y) t

def lineBound {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) {G : MaximalFamily n}
    (L : Lift G) (c : Word n) : Prop :=
  ∀i : Basis n, 0<(block half L c i i).re → ∀v : Basis n→ComplexScalar R,
    let w := exterior (fun a => block half L c a i) v
    normSum (rows n) (transfer half A w)≤2*(3*(4*half^n))*HighestExteriorOccupation.measure half (qubitIndices n) w

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem transferScale {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (w : Basis n×Basis n→ComplexScalar R) (s : R)
    (r : (Fin 5×Fin 5)×Word n) :
    transfer half A (fun t => ofReal s*w t) r=ofReal s*transfer half A w r := by
  have real : star (ofReal s)=ofReal s := by apply ComplexScalar.ext <;> simp <;> grind only
  let F (t : Four (Basis n)) := star (w t.1*(A t.2.1 (UpperPairLoss.rest r.1.2)*A t.2.2 (UpperPairLoss.rest r.1.1)))*WedgeSquareIntertwiner.wedgeSquareColumn half r.2 t
  have e (t : Four (Basis n)) : star (ofReal s*w t.1*(A t.2.1 (UpperPairLoss.rest r.1.2)*A t.2.2 (UpperPairLoss.rest r.1.1)))*
      WedgeSquareIntertwiner.wedgeSquareColumn half r.2 t=ofReal s*F t := by unfold F; simp only [star_mul,real]; grind only
  unfold transfer tailColumn; rw [sumOverCongr _ e,←sumOverMulLeft]; unfold F; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem normScale (xs : List α) (w : α→ComplexScalar R) (s : R) :
    normSum xs (fun i => ofReal s*w i)=s^2*normSum xs w := by unfold normSum; simp only [normSq_mul,normSq_ofReal,←sumOverMulLeft]

theorem anchorTransfer {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R)
    {G : MaximalFamily n} (L : Lift G) (c d : Word n) (b : Bool) (x y : Basis n→ComplexScalar R)
    (hyp : lineBound half A L (if b then d else c)) :
    let xs := qubitIndices n
    let u := component (HighestExteriorComponents.split half L c d) xs x y
    let t := testSource b u
    normSum (rows n) (transfer half A t)≤2*(3*(4*half^n))*HighestExteriorOccupation.measure half xs t := by
  let xs := qubitIndices n
  let B := block half L (if b then d else c)
  let u := component (HighestExteriorComponents.split half L c d) xs x y
  let w := testSource b u
  let q := 3*(4*half^n)
  obtain ⟨i,_,pos,v,e⟩ := testHasPhysicalAnchor half h2 L c d b x y
  let h := (B i i).re
  have eq : (fun j => ofReal h*w j)=exterior (fun a => B a i) v := funext e
  have bd := hyp i pos v
  change normSum (rows n) (transfer half A (exterior (fun a => B a i) v))≤2*q*HighestExteriorOccupation.measure half xs (exterior (fun a => B a i) v) at bd
  rw [←eq] at bd
  have moved : transfer half A (fun i => ofReal h*w i)=fun r => ofReal h*transfer half A w r := funext (transferScale half A w h)
  rw [moved,normScale] at bd
  unfold HighestExteriorOccupation.measure at bd
  rw [normScale] at bd
  change 0<h at pos
  change normSum (rows n) (transfer half A w)≤2*q*(half*normSum (productIndices xs xs) w)
  by_cases ok : normSum (rows n) (transfer half A w)≤2*q*(half*normSum (productIndices xs xs) w)
  · exact ok
  · have bad := OrderedRing.mul_pos (OrderedRing.mul_pos pos pos)
      (show 0<normSum (rows n) (transfer half A w)-2*q*(half*normSum (productIndices xs xs) w) by grind only)
    grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem testsFromLines {n : Nat} (half : F) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar F)
    {G : MaximalFamily n} (L : Lift G) (c d : Word n) (dif : ¬equiv G c d)
    (first : lineBound half A L c) (second : lineBound half A L d) : HighestAnchorReduction.anchorTests half A L c d := by
  let xs := qubitIndices n
  let P := HighestExteriorComponents.split half L c d
  let x i := A i 0
  let y i := A i 1
  let u := component P xs x y
  let m i := HighestExteriorOccupation.measure half xs (u i)
  let z t i := transfer half A (u i) t
  let D := diagonal (m 0) (m 1) (m 2) (m 3)
  let q := 3*(4*half^n)
  have v (a b c' d' : F) : HighestExteriorOccupation.measure half xs (output (fun t i => u i t) a b c' d')=D a b c' d' :=
    componentMass half h2 xs P (splitOrthogonal half h2 L c d dif) x y a b c' d'
  have l (a b c' d' : F) : transfer half A (output (fun t i => u i t) a b c' d')=output z a b c' d' :=
    funext (linear half A u a b c' d')
  have f := anchorTransfer half h2 A L c d false x y first
  have s := anchorTransfer half h2 A L c d true x y second
  change normSum (rows n) (transfer half A (output (fun t i => u i t) 1 2 0 0))≤2*q*HighestExteriorOccupation.measure half xs (output (fun t i => u i t) 1 2 0 0) at f
  change normSum (rows n) (transfer half A (output (fun t i => u i t) 1 0 2 0))≤2*q*HighestExteriorOccupation.measure half xs (output (fun t i => u i t) 1 0 2 0) at s
  rw [l,v] at f s
  exact ⟨f,s⟩

theorem physicalHighestFromLines (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A)
    (anchors : ∀{G : MaximalFamily (k+3)} (L : Lift G) (c : Word (k+3)),lineBound half A L c) :
    2*UpperFrameTrace.highExcess (PackingPolynomial.physicalWeights half h2 k A)≤
      5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne :=
  HighestAnchorReduction.physicalHighest half h2 k A mu orth
    (fun L c d dif => testsFromLines half h2 A L c d dif (anchors L c) (anchors L d))

end Field

end RankSeven.HighestAnchorVectors

#print axioms RankSeven.HighestAnchorVectors.testHasPhysicalAnchor
#print axioms RankSeven.HighestAnchorVectors.anchorTransfer
#print axioms RankSeven.HighestAnchorVectors.testsFromLines
#print axioms RankSeven.HighestAnchorVectors.physicalHighestFromLines

