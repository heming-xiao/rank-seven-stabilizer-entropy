import Rank7HighestExteriorOccupation

namespace RankSeven.HighestExteriorComponents

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestCosetFourier HighestExteriorOccupation
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
variable {R α : Type} [CommRing R]

def sectors (i : Fin 4) : List (Fin 3×Fin 3) :=
  if i=0 then [(0,0),(0,1),(1,0),(1,1)] else if i=1 then [(0,2),(2,0)] else if i=2 then [(1,2),(2,1)] else [(2,2)]

private theorem differentSectors : ∀i j : Fin 4, i≠j → ∀a∈sectors i,∀b∈sectors j,
    (a.1≠b.1 ∨ a.2≠b.2) ∧ (a.1≠b.2 ∨ a.2≠b.1) := by decide

def component (P : Fin 3→Mx α R) (xs : List α) (x y : α→ComplexScalar R) (i : Fin 4) (e : α×α) :=
  sumOver (sectors i) (fun a => exterior (image xs (P a.1) x) (image xs (P a.2) y) e)

def orthogonalRanges (xs : List α) (P : Fin 3→Mx α R) : Prop :=
  ∀i j, i≠j → ∀u v,innerProduct xs (image xs (P i) u) (image xs (P j) v)=0

private theorem innerSums {β γ : Type} (xs : List α) (us : List β) (vs : List γ) (x : β→α→ComplexScalar R) (y : γ→α→ComplexScalar R) :
    innerProduct xs (fun i => sumOver us (fun j => x j i)) (fun i => sumOver vs (fun j => y j i))=
    sumOver us (fun j => sumOver vs (fun k => innerProduct xs (x j) (y k))) := by
  unfold innerProduct; simp only [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap xs vs,sumOverSwap us vs]; apply sumOverCongr; intro j; rw [sumOverSwap xs us]

private theorem zeros {β C : Type} [CommRing C] (xs : List β) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with | nil => rfl | cons i is ih => change 0+sumOver is _=0; rw [ih]; grind only

theorem componentOrthogonal (half : R) (h2 : 2*half=1) (xs : List α) (P : Fin 3→Mx α R) (o : orthogonalRanges xs P)
    (x y : α→ComplexScalar R) (i j : Fin 4) (ne : i≠j) :
    innerProduct (productIndices xs xs) (component P xs x y i) (component P xs x y j)=0 := by
  let es := productIndices xs xs
  let w (a : Fin 3×Fin 3) := exterior (image xs (P a.1) x) (image xs (P a.2) y)
  have hh : 2*ofReal half=(1:ComplexScalar R) := by
    have two : (2:ComplexScalar R)=1+1 := by grind only
    rw [two]; apply ComplexScalar.ext <;> simp only [re_mul,re_add,im_mul,im_add,re_ofReal,im_ofReal,re_one,im_one] <;> grind only
  have sep (a : Fin 3×Fin 3) (ha : a∈sectors i) (b : Fin 3×Fin 3) (hb : b∈sectors j) : innerProduct es (w a) (w b)=0 := by
    have e := exteriorGram half h2 xs (image xs (P a.1) x) (image xs (P a.2) y) (image xs (P b.1) x) (image xs (P b.2) y)
    have splits := differentSectors i j ne a ha b hb
    change ofReal half*innerProduct es (w a) (w b)=_ at e
    rcases splits.1 with h|h <;> rcases splits.2 with l|l <;> rw [o _ _ h,o _ _ l] at e <;> grind only
  change innerProduct es (fun t => sumOver (sectors i) (fun a => w a t)) (fun t => sumOver (sectors j) (fun b => w b t))=0
  rw [innerSums]
  have row (a : Fin 3×Fin 3) (ha : a∈sectors i) : sumOver (sectors j) (fun b => innerProduct es (w a) (w b))=0 := by
    rw [AnticommutingDefect.sumCongrMem _ _ (fun _ => 0) (sep a ha),zeros]
  rw [AnticommutingDefect.sumCongrMem _ _ (fun _ => 0) row,zeros]

theorem componentMass (half : R) (h2 : 2*half=1) (xs : List α) (P : Fin 3→Mx α R) (o : orthogonalRanges xs P)
    (x y : α→ComplexScalar R) (a b c d : R) :
    let u := component P xs x y
    let m i := HighestExteriorOccupation.measure half xs (u i)
    HighestExteriorOccupation.measure half xs (HighestExteriorStability.output (fun t i => u i t) a b c d)=HighestExteriorStability.diagonal (m 0) (m 1) (m 2) (m 3) a b c d := by
  let es := productIndices xs xs
  let u := component P xs x y
  have off (i j : Fin 4) (ne : i≠j) : sumOver es (fun t => (star (u i t)*u j t).re)=0 := by
    have h := congrArg ComplexScalar.re (componentOrthogonal half h2 xs P o x y i j ne)
    simpa only [innerProduct,(realSum _ _).1,re_zero] using h
  dsimp only; unfold HighestExteriorOccupation.measure
  rw [←HighestExteriorStability.columnValue]
  unfold HighestExteriorStability.value HighestExteriorStability.columnForm HighestExteriorStability.diagonal
  dsimp only
  dsimp only [es,u] at off
  rw [off 0 1 (by decide),off 0 2 (by decide),off 0 3 (by decide),off 1 2 (by decide),off 1 3 (by decide),off 2 3 (by decide)]
  simp only [Semiring.mul_zero,Semiring.zero_mul,Semiring.add_zero]; rfl

open HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def split {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (c d : Word n) (i : Fin 3) :=
  if i=0 then block half L c else if i=1 then block half L d else compl (PhysicalProjectionAngles.code half L c d)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem orthProduct (xs : List α) (P Q : Mx α R) (hp : dagger P=P) (null : matMul xs P Q=fun _ _ => 0)
    (u v : α→ComplexScalar R) : innerProduct xs (image xs P u) (image xs Q v)=0 := by
  let U (i : α) (_ : Unit) := u i
  let V (i : α) (_ : Unit) := v i
  change matMul xs (dagger (matMul xs P U)) (matMul xs Q V) () ()=0
  rw [PhysicalPairedReduction.daggerProduct,hp,matMulAssoc,←matMulAssoc xs xs P Q V,null]
  unfold matMul; simp only [Semiring.zero_mul,zeros,Semiring.mul_zero]

theorem splitOrthogonal {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (c d : Word n)
    (apart : ¬equiv G c d) : orthogonalRanges (qubitIndices n) (split half L c d) := by
  let xs := qubitIndices n
  let P := block (R:=R) half L c
  let D := block half L d
  let Q := addM P D
  let S := compl Q
  have cp := PhysicalProjectionAngles.lineProjection half h2 L c
  have dp := PhysicalProjectionAngles.lineProjection half h2 L d
  have cd : matMul xs P D=fun _ _ => 0 := (blockProduct half h2 L c d).trans (ite_eq_right apart)
  have dc : matMul xs D P=fun _ _ => 0 := (blockProduct half h2 L d c).trans (ite_eq_right (fun h => apart (StabilizerCosetTransform.symm h)))
  have com (T : Mx (Basis n) R) (idem : matMul xs T Q=T) : matMul xs T S=fun _ _ => 0 := by
    unfold S compl; rw [subRight,idRight xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete,idem]
    funext i j; unfold subM; grind only
  have ps := com P (by unfold Q; rw [addRight,cp.square,cd]; funext i j; unfold addM; grind only)
  have ds := com D (by unfold Q; rw [addRight,dc,dp.square]; funext i j; unfold addM; grind only)
  have flip (T V : Mx (Basis n) R) (h : ∀u v,innerProduct xs (image xs T u) (image xs V v)=0) (u v : Basis n→ComplexScalar R) :
      innerProduct xs (image xs V u) (image xs T v)=0 := by
    rw [conjugateProduct xs (image xs T v),h]; apply ComplexScalar.ext <;> simp <;> grind only
  have h01 := orthProduct xs P D cp.herm cd
  have h02 := orthProduct xs P S cp.herm ps
  have h12 := orthProduct xs D S dp.herm ds
  intro i j ne u v
  have cases3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by revert i; decide
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl <;> first
    | exact False.elim (ne rfl)
    | exact h01 u v
    | exact h02 u v
    | exact h12 u v
    | exact flip _ _ h01 u v
    | exact flip _ _ h02 u v
    | exact flip _ _ h12 u v

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem addImage (xs : List α) (P Q : Mx α R) (u : α→ComplexScalar R) (i : α) :
    image xs (addM P Q) u i=image xs P u i+image xs Q u i := by
  unfold image addM; simp only [Semiring.right_distrib,sumOverAdd]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem splitSum {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (c d : Word n)
    (v : Basis n→ComplexScalar R) (i : Basis n) :
    let xs := qubitIndices n
    let P := split half L c d
    image xs (P 0) v i+image xs (P 1) v i+image xs (P 2) v i=v i := by
  let xs := qubitIndices n
  let Q := PhysicalProjectionAngles.code half L c d
  let V (i : Basis n) (_ : Unit) := v i
  have rem : image xs (compl Q) v i=v i-image xs Q v i := by
    change matMul xs (compl Q) V i ()=_
    unfold compl; rw [subLeft,idLeft xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete]; rfl
  change image xs (block half L c) v i+image xs (block half L d) v i+image xs (compl Q) v i=v i
  rw [←addImage,rem]; change image xs Q v i+(v i-image xs Q v i)=v i; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem componentValues {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (c d : Word n)
    (x y : Basis n→ComplexScalar R) :
    let xs := qubitIndices n
    let P := split half L c d
    let Q := PhysicalProjectionAngles.code half L c d
    let v := component P xs x y
    v 0=exterior (image xs Q x) (image xs Q y) ∧ v 3=exterior (image xs (compl Q) x) (image xs (compl Q) y) ∧
      HighestExteriorStability.output (fun t i => v i t) 1 1 1 1=exterior x y := by
  let xs := qubitIndices n
  let P := split half L c d
  let Q := PhysicalProjectionAngles.code half L c d
  let v := component P xs x y
  have cs (e : Basis n×Basis n) : v 0 e+v 1 e+v 2 e+v 3 e=exterior x y e := by
    have xx (i : Basis n) := (splitSum half L c d x i).symm
    have yy (i : Basis n) := (splitSum half L c d y i).symm
    conv => rhs; unfold exterior; rw [xx,yy,yy,xx]
    unfold v component
    simp (config:={decide:=true}) only [sectors,ite_true,ite_false,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,exterior]
    grind only
  refine ⟨?_,?_,?_⟩
  · funext e
    change v 0 e=exterior (image xs Q x) (image xs Q y) e
    unfold v component Q PhysicalProjectionAngles.code
    simp (config:={decide:=true}) only [sectors,ite_true,ite_false,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,exterior,addImage]
    change _=(image xs (P 0) x e.1+image xs (P 1) x e.1)*(image xs (P 0) y e.2+image xs (P 1) y e.2)-
      (image xs (P 0) y e.1+image xs (P 1) y e.1)*(image xs (P 0) x e.2+image xs (P 1) x e.2)
    grind only
  · funext e; change v 3 e=_; unfold v component
    simp (config:={decide:=true}) only [sectors,ite_false,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Semiring.add_zero]
    rfl
  · funext e
    have one : ofReal (1:R)=(1:ComplexScalar R) := by apply ComplexScalar.ext <;> simp
    change ofReal 1*v 0 e+ofReal 1*v 1 e+ofReal 1*v 2 e+ofReal 1*v 3 e=_
    rw [one]; simpa only [Semiring.one_mul] using cs e

theorem physicalSourceMass {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (c d : Word n) (apart : ¬equiv G c d) (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let xs := qubitIndices n
    let Q := PhysicalProjectionAngles.code half L c d
    let x i := A i 0
    let y i := A i 1
    let e := 1-half*(energy xs Q x+energy xs Q y)
    let v := component (split half L c d) xs x y
    let m i := HighestExteriorOccupation.measure half xs (v i)
    m 0+m 1+m 2+m 3=1 ∧ 0≤m 3 ∧ m 1+m 2≤2*e ∧ m 3≤e^2 ∧ 0≤e := by
  let xs := qubitIndices n
  let Q := PhysicalProjectionAngles.code half L c d
  let P := split half L c d
  let x i := A i 0
  let y i := A i 1
  let e := 1-half*(energy xs Q x+energy xs Q y)
  let v := component P xs x y
  let m i := HighestExteriorOccupation.measure half xs (v i)
  have un (i : Fin 7) : normSum xs (fun j => A j i)=1 := by
    have h := orth i i
    change innerProduct xs (fun j => A j i) (fun j => A j i)=_ at h
    rw [selfProduct,ite_eq_left rfl] at h
    simpa only [re_ofReal,re_one] using congrArg ComplexScalar.re h
  have xy : innerProduct xs x y=0 := (orth 0 1).trans (ite_eq_right (by decide))
  have full : HighestExteriorOccupation.measure half xs (exterior x y)=1 := by
    rw [exteriorMass half h2,un 0,un 1,xy]; simp only [normSq,re_zero,im_zero]; grind only
  have vals := componentValues half L c d x y
  have sums := componentMass half h2 xs P (splitOrthogonal half h2 L c d apart) x y 1 1 1 1
  change HighestExteriorOccupation.measure half xs (HighestExteriorStability.output (fun t i => v i t) 1 1 1 1)=HighestExteriorStability.diagonal (m 0) (m 1) (m 2) (m 3) 1 1 1 1 at sums
  change _=_ ∧ _=_ ∧ HighestExteriorStability.output (fun t i => v i t) 1 1 1 1=exterior x y at vals
  rw [vals.2.2,full] at sums
  unfold HighestExteriorStability.diagonal at sums
  have input := projectedMasses half h2 xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete Q
    (PhysicalProjectionAngles.codeProjection half h2 L c d apart) x y (un _) (un _) xy
  change 0≤_ ∧ 0≤_ ∧ 0≤e ∧ _≤e^2 ∧ _+2*_=2*e at input
  rw [←vals.1,←vals.2.1] at input
  change 0≤m 3 ∧ 0≤m 0 ∧ 0≤e ∧ m 3≤e^2 ∧ 1-m 0-m 3+2*m 3=2*e at input
  change m 0+m 1+m 2+m 3=1 ∧ 0≤m 3 ∧ m 1+m 2≤2*e ∧ m 3≤e^2 ∧ 0≤e
  exact ⟨by grind only,input.1,by grind only,input.2.2.2.1,input.2.2.1⟩

end RankSeven.HighestExteriorComponents

#print axioms RankSeven.HighestExteriorComponents.componentOrthogonal
#print axioms RankSeven.HighestExteriorComponents.componentMass
#print axioms RankSeven.HighestExteriorComponents.splitOrthogonal
#print axioms RankSeven.HighestExteriorComponents.componentValues
#print axioms RankSeven.HighestExteriorComponents.physicalSourceMass

