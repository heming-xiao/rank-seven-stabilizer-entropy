import Rank7CharacterFourOrbits

namespace RankSeven.FiniteProjectionAngles

open Lean.Grind Pauli ComplexScalar SlaterUnionBound
open PhysicalPairedReduction (dagger)
open PauliPairContraction (image normSum)
variable {R α β γ : Type} [CommRing R]

def addM (A B : α→β→ComplexScalar R) (i : α) (j : β) := A i j+B i j
def subM (A B : α→β→ComplexScalar R) (i : α) (j : β) := A i j-B i j
def compl [DecidableEq α] (P : Mx α R) := subM ident P

structure Projection (xs : List α) (P : Mx α R) : Prop where
  herm : dagger P=P
  square : matMul xs P P=P

theorem addLeft (xs : List β) (A B : α→β→ComplexScalar R) (M : β→γ→ComplexScalar R) :
    matMul xs (addM A B) M=addM (matMul xs A M) (matMul xs B M) := by
  funext i j; unfold matMul addM; simp only [Semiring.right_distrib,sumOverAdd]

theorem subLeft (xs : List β) (A B : α→β→ComplexScalar R) (M : β→γ→ComplexScalar R) :
    matMul xs (subM A B) M=subM (matMul xs A M) (matMul xs B M) := by
  funext i j; unfold matMul subM; rw [←Compression.sumOverSub]; apply sumOverCongr; intro k; grind only

theorem addRight (xs : List β) (M : α→β→ComplexScalar R) (A B : β→γ→ComplexScalar R) :
    matMul xs M (addM A B)=addM (matMul xs M A) (matMul xs M B) := by
  funext i j; unfold matMul addM; simp only [Semiring.left_distrib,sumOverAdd]

theorem subRight (xs : List β) (M : α→β→ComplexScalar R) (A B : β→γ→ComplexScalar R) :
    matMul xs M (subM A B)=subM (matMul xs M A) (matMul xs M B) := by
  funext i j; unfold matMul subM; rw [←Compression.sumOverSub]; apply sumOverCongr; intro k; grind only

theorem idLeft [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (A : α→β→ComplexScalar R) : matMul xs ident A=A := by
  funext i j; change sumOver xs (fun k => ident i k*A k j)=A i j
  conv => rhs; rw [←ExteriorPauliBase.sumOnIndex xs i (fun k => A k j) nd (full i)]
  apply sumOverCongr; intro k; by_cases eq : i=k <;> simp [ident,eq] <;> grind only

theorem idRight [DecidableEq β] (xs : List β) (nd : xs.Nodup) (full : ∀i,i∈xs) (A : α→β→ComplexScalar R) : matMul xs A ident=A := by
  funext i j; change sumOver xs (fun k => A i k*ident k j)=A i j
  conv => rhs; rw [←ExteriorPauliBase.sumOnIndex xs j (fun k => A i k) nd (full j)]
  apply sumOverCongr; intro k; by_cases eq : k=j <;> simp [ident,eq,Eq.comm] <;> grind only

theorem dagAdd (A B : α→β→ComplexScalar R) : dagger (addM A B)=addM (dagger A) (dagger B) := by
  funext i j; exact star_add _ _
theorem dagSub (A B : α→β→ComplexScalar R) : dagger (subM A B)=subM (dagger A) (dagger B) := by
  funext i j; change star (A j i-B j i)=star (A j i)-star (B j i)
  apply ComplexScalar.ext <;> simp <;> grind only
theorem dagId [DecidableEq α] : dagger (ident (R:=R) (α:=α))=ident := by
  funext i j; change star (ident j i)=ident i j
  by_cases e : i=j <;> simp [ident,e,Eq.comm] <;> apply ComplexScalar.ext <;> simp <;> grind only

theorem complement [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (P : Mx α R) (p : Projection xs P) :
    Projection xs (compl P) := by
  constructor
  · unfold compl; rw [dagSub,dagId,p.herm]
  · unfold compl; rw [subLeft,subRight,subRight,idLeft xs nd full,idLeft xs nd full,idRight xs nd full,p.square]
    funext i j; unfold subM; grind only

theorem energySub (xs : List α) (A B : Mx α R) (z : α→ComplexScalar R) : energy xs (subM A B) z=energy xs A z-energy xs B z := by
  let Z (i : α) (_ : Unit) := z i
  change (matMul xs (dagger Z) (matMul xs (subM A B) Z) () ()).re=_
  rw [subLeft,subRight]; exact re_sub _ _

theorem energyAdd (xs : List α) (A B : Mx α R) (z : α→ComplexScalar R) : energy xs (addM A B) z=energy xs A z+energy xs B z := by
  let Z (i : α) (_ : Unit) := z i
  change (matMul xs (dagger Z) (matMul xs (addM A B) Z) () ()).re=_
  rw [addLeft,addRight]; exact re_add _ _

theorem energyNorm (xs : List α) (P : Mx α R) (p : Projection xs P) (z : α→ComplexScalar R) :
    energy xs P z=normSum xs (image xs P z) := by
  have e : matMul xs (dagger P) P=P := by rw [p.herm,p.square]
  conv => lhs; rw [←e]
  exact energyGram xs xs P z

theorem imageComp (xs : List β) (ys : List γ) (A : α→β→ComplexScalar R) (B : β→γ→ComplexScalar R) (z : γ→ComplexScalar R) :
    image xs A (image ys B z)=image ys (matMul xs A B) z := by
  let Z (i : γ) (_ : Unit) := z i
  funext i; exact (congrFun (congrFun (matMulAssoc xs ys A B Z).symm i) ())

private theorem reSum {δ : Type} (xs : List δ) (f : δ→ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=_; rw [re_add,ih]; rfl

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem contract [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (P : Mx α R) (p : Projection xs P) (z : α→ComplexScalar R) :
    normSum xs (image xs P z)≤normSum xs z := by
  have q := complement xs nd full P p
  have non := energyNonnegative xs (show Gram (compl P) from ⟨α,xs,compl P,by rw [q.herm,q.square]⟩) z
  rw [compl,energySub,energyIdentity xs nd full,energyNorm xs P p] at non; grind only

theorem frobeniusBound (xs : List α) (P : Mx α R) (z : α→ComplexScalar R) (unit : normSum xs z=1) :
    normSum xs (image xs P z)≤(trace xs (matMul xs (dagger P) P)).re := by
  let A (i : α) (_ : Unit) := star (z i)
  have orth (i j : Unit) : sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0 := by
    cases i; cases j; simp only [A,star_star,ite_true]
    have eq (a : α) : z a*star (z a)=ofReal (normSq (z a)) := by rw [CommSemiring.mul_comm,star_mul_self]
    rw [sumOverCongr _ eq]; apply ComplexScalar.ext
    · rw [reSum]; simp only [re_ofReal,re_one]; exact unit
    · have zero (ys : List α) : (sumOver ys (fun a => ofReal (normSq (z a)))).im=0 := by
        induction ys with | nil => rfl | cons i ys ih => change (ofReal (normSq (z i))+sumOver ys (fun a => ofReal (normSq (z a)))).im=0; rw [im_add,im_ofReal,ih]; grind only
      exact zero _
  have row (i : α) : normSq (image xs P z i)≤sumOver xs (fun j => normSq (P i j)) := by
    have b := PhysicalCutCapacities.frameBessel [()] xs (by simp) (by intro x; cases x; simp) A orth (fun j => P i j)
    have eq (j : α) : star (A j ())*P i j=P i j*z j := by unfold A; rw [star_star,CommSemiring.mul_comm]
    simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Semiring.add_zero] at b
    change normSq (sumOver xs (fun j => star (A j ())*P i j))≤_ at b; rw [sumOverCongr _ eq] at b; exact b
  have pos := Compression.sumOverNonnegative xs (fun i => sumOver xs (fun j => normSq (P i j))-normSq (image xs P z i))
    (fun i _ => by have := row i; grind only)
  rw [Compression.sumOverSub,sumOverSwap] at pos
  change sumOver xs (fun i => normSq (image xs P z i))≤(sumOver xs (fun j => sumOver xs (fun i => star (P i j)*P i j))).re
  simp only [reSum,re_star_mul_self]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem traceSub (xs : List α) (P Q : Mx α R) : trace xs (subM P Q)=trace xs P-trace xs Q := Compression.sumOverSub xs _ _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem traceAdd (xs : List α) (P Q : Mx α R) : trace xs (addM P Q)=trace xs P+trace xs Q := sumOverAdd xs _ _

theorem normWeighted (xs : List α) (u v : α→ComplexScalar R) :
    2*normSum xs (fun i => u i+v i)≤3*normSum xs u+6*normSum xs v := by
  have point (i : α) : 0≤(3*normSq (u i)+6*normSq (v i))-2*normSq (u i+v i) := by
    have k := normSq_nonnegative (u i-(v i+v i))
    simp only [normSq,re_add,im_add,re_sub,im_sub] at k ⊢; grind only
  have s := Compression.sumOverNonnegative xs _ (fun i _ => point i)
  rw [Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,←sumOverMulLeft] at s
  unfold normSum; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem productTrace (xs : List α) (P Q : Mx α R) (p : Projection xs P) (q : Projection xs Q) :
    trace xs (matMul xs (dagger (matMul xs P Q)) (matMul xs P Q))=trace xs (matMul xs P Q) := by
  rw [PhysicalPairedReduction.daggerProduct,p.herm,q.herm,matMulAssoc,←matMulAssoc xs xs P P Q,p.square]
  rw [traceMatMulSwap xs xs Q (matMul xs P Q),matMulAssoc,q.square]

theorem oneSided [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (P Q : Mx α R)
    (p : Projection xs P) (q : Projection xs Q) (z : α→ComplexScalar R) (unit : normSum xs z=1) :
    2*energy xs P z≤3*((trace xs P).re-(trace xs (matMul xs P Q)).re)+6*energy xs Q z := by
  let C := compl Q
  let H := matMul xs P C
  let B := matMul xs P Q
  have comp : Projection xs C := complement xs nd full Q q
  have split : P=addM H B := by
    unfold H B C compl; rw [subRight,idRight xs nd full]; funext i j; unfold addM subM; grind only
  have imageP : image xs P z=fun i => image xs H z i+image xs B z i := by
    conv => lhs; rw [split]
    funext i; unfold image addM; simp only [Semiring.right_distrib,sumOverAdd]
  have t := normWeighted xs (image xs H z) (image xs B z)
  have h := frobeniusBound xs H z unit
  have tr : trace xs (matMul xs (dagger H) H)=trace xs P-trace xs (matMul xs P Q) := by
    rw [productTrace xs P C p comp]; unfold C compl; rw [subRight,idRight xs nd full,traceSub]
  rw [tr,re_sub] at h
  have b := contract xs nd full P p (image xs Q z)
  rw [imageComp] at b; change normSum xs (image xs B z)≤normSum xs (image xs Q z) at b
  rw [energyNorm xs P p,imageP,energyNorm xs Q q]; grind only

/-- The two transfer estimates between equal-trace projections P and Q,
with all coefficients cleared and no square roots. -/
theorem projectionAngles [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (P Q : Mx α R)
    (p : Projection xs P) (q : Projection xs Q) (same : trace xs P=trace xs Q) (z : α→ComplexScalar R) (unit : normSum xs z=1) :
    let e := (trace xs P).re-(trace xs (matMul xs P Q)).re
    2*energy xs P z≤3*e+6*energy xs Q z ∧ 2*(1-energy xs P z)≤3*e+6*(1-energy xs Q z) := by
  refine ⟨oneSided xs nd full P Q p q z unit,?_⟩
  have s := oneSided xs nd full (compl P) (compl Q) (complement xs nd full P p) (complement xs nd full Q q) z unit
  have tr : trace xs (matMul xs (compl P) (compl Q))=trace xs (compl P)-trace xs Q+trace xs (matMul xs P Q) := by
    unfold compl; rw [subLeft,subRight,subRight,idLeft xs nd full,idLeft xs nd full,idRight xs nd full,traceSub,traceSub,traceSub,traceSub]
    grind only
  rw [tr,re_add,re_sub,compl,compl,energySub,energySub,energyIdentity xs nd full,unit] at s
  have equal := congrArg ComplexScalar.re same
  change 2*(1-energy xs P z)≤3*((trace xs P).re-(trace xs (matMul xs P Q)).re)+6*(1-energy xs Q z); grind only

end RankSeven.FiniteProjectionAngles

#print axioms RankSeven.FiniteProjectionAngles.frobeniusBound
#print axioms RankSeven.FiniteProjectionAngles.oneSided
#print axioms RankSeven.FiniteProjectionAngles.projectionAngles

