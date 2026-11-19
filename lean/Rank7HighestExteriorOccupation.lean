import Rank7HighestExteriorStability

namespace RankSeven.HighestExteriorOccupation

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestCosetFourier
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
variable {R α : Type} [CommRing R]

def exterior (x y : α→ComplexScalar R) (p : α×α) := x p.1*y p.2-y p.1*x p.2

def measure (half : R) (xs : List α) (w : α×α→ComplexScalar R) := half*normSum (productIndices xs xs) w

private theorem prodSum {β C : Type} [CommRing C] (xs : List α) (ys : List β) (F : α×β→C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem productMetric (xs : List α) (x y u v : α→ComplexScalar R) :
    sumOver (productIndices xs xs) (fun p => star (x p.1*y p.2)*(u p.1*v p.2))=
      innerProduct xs x u*innerProduct xs y v := by
  rw [prodSum]
  unfold innerProduct; rw [sumOverMulRight]
  apply sumOverCongr; intro i; rw [sumOverMulLeft]; apply sumOverCongr; intro j; rw [star_mul]; grind only

theorem exteriorGram (half : R) (h2 : 2*half=1) (xs : List α) (x y u v : α→ComplexScalar R) :
    ofReal half*innerProduct (productIndices xs xs) (exterior x y) (exterior u v)=
    innerProduct xs x u*innerProduct xs y v-innerProduct xs x v*innerProduct xs y u := by
  let es := productIndices xs xs
  let f (x y u v : α→ComplexScalar R) (p : α×α) := star (x p.1*y p.2)*(u p.1*v p.2)
  have row (p : α×α) : star (exterior x y p)*exterior u v p=
    f x y u v p-f x y v u p-f y x u v p+f y x v u p := by
    unfold f exterior
    have ss (a b : ComplexScalar R) : star (a-b)=star a-star b := by apply ComplexScalar.ext <;> simp <;> grind only
    rw [ss]; grind only
  have sum := sumOverCongr es row
  simp only [sumOverAdd,Compression.sumOverSub,f,productMetric,es] at sum
  have ch : (2:ComplexScalar R)*ofReal half=1 := by
    have two : (2:ComplexScalar R)=1+1 := by grind only
    rw [two]; apply ComplexScalar.ext <;> simp only [re_mul,re_add,im_mul,im_add,re_ofReal,im_ofReal,re_one,im_one] <;> grind only
  change ofReal half*(sumOver es (fun p => star (exterior x y p)*exterior u v p))=_
  rw [sum]; grind only

theorem selfProduct (xs : List α) (x : α→ComplexScalar R) :
    innerProduct xs x x=ofReal (normSum xs x) := by
  apply ComplexScalar.ext
  · unfold innerProduct normSum; rw [(realSum _ _).1]; simp only [re_star_mul_self,re_ofReal]
  · unfold innerProduct; rw [(realSum _ _).2]; simp only [im_star_mul_self,im_ofReal]
    induction xs with | nil => rfl | cons i is ih => change 0+sumOver is (fun _ => (0:R))=0; rw [ih]; grind only

theorem conjugateProduct (xs : List α) (x y : α→ComplexScalar R) : innerProduct xs y x=star (innerProduct xs x y) := by
  unfold innerProduct; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro j; rw [star_mul,star_star]; grind only

theorem exteriorMass (half : R) (h2 : 2*half=1) (xs : List α) (x y : α→ComplexScalar R) :
    measure half xs (exterior x y)=normSum xs x*normSum xs y-normSq (innerProduct xs x y) := by
  have gram := exteriorGram half h2 xs x y x y
  rw [selfProduct,selfProduct,selfProduct,conjugateProduct xs x y,
    CommSemiring.mul_comm (innerProduct xs x y),star_mul_self] at gram
  have e := congrArg ComplexScalar.re gram
  simp only [re_mul,re_sub,re_ofReal,im_ofReal,Semiring.mul_zero] at e
  unfold measure; grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem complInner [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (Q : Mx α R)
    (x y : α→ComplexScalar R) :
    innerProduct xs x (image xs (compl Q) y)=innerProduct xs x y-innerProduct xs x (image xs Q y) := by
  let X (i : α) (_ : Unit) := x i
  let Y (i : α) (_ : Unit) := y i
  change matMul xs (dagger X) (matMul xs (compl Q) Y) () ()=_
  unfold compl; rw [subLeft,idLeft xs nd full,subRight]; rfl

theorem projectedMasses [DecidableEq α] (half : R) (h2 : 2*half=1) (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs)
    (Q : Mx α R) (q : Projection xs Q) (x y : α→ComplexScalar R) (ux : normSum xs x=1) (uy : normSum xs y=1)
    (xy : innerProduct xs x y=0) :
    let S := compl Q
    let w := exterior (image xs Q x) (image xs Q y)
    let z := exterior (image xs S x) (image xs S y)
    let e := 1-half*(energy xs Q x+energy xs Q y)
    let m := measure half xs
    0≤m z ∧ 0≤m w ∧ 0≤e ∧ m z≤e^2 ∧ (1-m w-m z)+2*m z=2*e := by
  let S := compl Q
  let w := exterior (image xs Q x) (image xs Q y)
  let z := exterior (image xs S x) (image xs S y)
  let U := energy xs Q x
  let V := energy xs Q y
  let C := innerProduct xs x (image xs Q y)
  let e := 1-half*(U+V)
  have hon : 0≤half := by have := OrderedRing.zero_lt_one (R:=R); grind only
  have sn (v : α×α→ComplexScalar R) : 0≤measure half xs v :=
    OrderedRing.mul_nonneg hon (Compression.sumOverNonnegative _ _ (fun i _ => normSq_nonnegative _))
  have qs := complement xs nd full Q q
  have eQ (u : α→ComplexScalar R) : normSum xs (image xs Q u)=energy xs Q u := (energyNorm xs Q q u).symm
  have eS (u : α→ComplexScalar R) : normSum xs (image xs S u)=normSum xs u-energy xs Q u := by
    rw [←energyNorm xs S qs]; unfold S compl; rw [energySub,energyIdentity xs nd full]
  have zGram : innerProduct xs (image xs S x) (image xs S y) = -C := by
    rw [projectedInner xs S qs,complInner xs nd full,xy]; grind only
  have nw : measure half xs w=U*V-normSq C := by
    unfold w; rw [exteriorMass half h2,eQ,eQ,projectedInner xs Q q]
  have nz : measure half xs z=(1-U)*(1-V)-normSq C := by
    unfold z; rw [exteriorMass half h2,eS,eS,ux,uy,zGram]
    simp only [normSq,re_neg,im_neg]; grind only
  have eq : 2*e=2-U-V := by unfold e; grind only
  have uSum := contract xs nd full Q q x
  have vSum := contract xs nd full Q q y
  rw [eQ,ux] at uSum; rw [eQ,uy] at vSum
  change U≤1 at uSum; change V≤1 at vSum
  have s := squareNonnegative (U-V)
  have ee := congrArg (fun c : R => c^2) eq
  change (2*e)^2=(2-U-V)^2 at ee
  have cn := normSq_nonnegative C
  change 0≤measure half xs z ∧ 0≤measure half xs w ∧ 0≤e ∧ measure half xs z≤e^2 ∧ (1-measure half xs w-measure half xs z)+2*measure half xs z=2*e
  refine ⟨sn z,sn w,by grind only,?_,by grind only⟩
  rw [nz]
  simp only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] at s ee ⊢
  grind only

section Field
open PhysicalCompressionEffect (OrthonormalFrame)
open HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

theorem physicalOccupation (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A) (small : 15*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne≤2) :
    ∃G : MaximalFamily (k+3),∃L : Lift G,∃c d : Word (k+3), ¬equiv G c d ∧
      let xs := qubitIndices (k+3)
      let Q := PhysicalProjectionAngles.code half L c d
      let x i := A i 0
      let y i := A i 1
      let e := 1-half*(energy xs Q x+energy xs Q y)
      let m0 := measure half xs (exterior (image xs Q x) (image xs Q y))
      let m3 := measure half xs (exterior (image xs (compl Q) x) (image xs (compl Q) y))
      0≤e ∧ 20*e<1 ∧ 6137*e≤2000*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne ∧
        0≤m0 ∧ 0≤m3 ∧ m3≤e^2 ∧ (1-m0-m3)+2*m3=2*e := by
  obtain ⟨G,L,c,d,dif,unit,near,bound⟩ := HighestPhysicalConcentration.physicalStabilizerPlane half h2 k A mu orth small
  refine ⟨G,L,c,d,dif,?_⟩
  let xs := qubitIndices (k+3)
  let x i := A i 0
  let y i := A i 1
  let Q := PhysicalProjectionAngles.code half L c d
  let E := energy xs Q x+energy xs Q y
  let e := 1-half*E
  have un (i : Fin 7) : normSum xs (fun j => A j i)=1 := by
    have h := orth i i
    change innerProduct xs (fun j => A j i) (fun j => A j i)=_ at h
    rw [selfProduct,ite_eq_left rfl] at h
    simpa only [re_ofReal,re_one] using congrArg ComplexScalar.re h
  have xy : innerProduct xs x y=0 := by exact (orth 0 1).trans (ite_eq_right (by decide))
  have qty := projectedMasses half h2 xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete Q
    (PhysicalProjectionAngles.codeProjection half h2 L c d dif) x y (un _) (un _) xy
  have eq : 2*e=2-E := by unfold e; grind only
  change E≤2 at unit; change 19<10*E at near; change 6137*(2-E)≤_ at bound
  exact ⟨qty.2.2.1,show 20*e<1 by grind only,show 6137*e≤_ by grind only,qty.2.1,qty.1,qty.2.2.2.1,qty.2.2.2.2⟩

end Field

end RankSeven.HighestExteriorOccupation

#print axioms RankSeven.HighestExteriorOccupation.exteriorGram
#print axioms RankSeven.HighestExteriorOccupation.projectedMasses
#print axioms RankSeven.HighestExteriorOccupation.physicalOccupation

