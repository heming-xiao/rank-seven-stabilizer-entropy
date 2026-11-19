import Rank7LowerSignedPrices
namespace RankSeven.LowerExteriorScale
open Lean.Grind UpperEndpoint LowerNormalizedSigned LowerCorner
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem minScale (a b t : R) (tp : 0<t) :
    t*smaller a b=smaller (t*a) (t*b) := by
  unfold smaller
  by_cases h : a≤b
  · have v := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt tp)
    simp [h,v]
  · have v := OrderedRing.mul_lt_mul_of_pos_left (show b<a by grind only) tp
    have nv : ¬t*a≤t*b := by grind only
    simp [h,nv]

theorem orderedRatios (b c : R) (cb : 1≤c ∧ c≤b) :
    0≤1/b ∧ 1/b≤c/b ∧ c/b≤1 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have bp : 0<b := by grind only
  have e := UpperContractor.quotientEq c bp
  have d := UpperContractor.quotientEq (1:R) bp
  exact ⟨UpperContractor.cancelLe bp (by rw [Semiring.mul_zero,d]; grind only),
    UpperContractor.cancelLe bp (by rw [e,d]; exact cb.1),UpperContractor.cancelLe bp (by rw [e,Semiring.mul_one]; exact cb.2)⟩

private theorem scaleFactors (b c : R) (bp : 0<b) :
    let C := c/b; let D := 1/b; let B := b*b
    B*(C*D)=c ∧ B*(D*D)=1 ∧ B*((1-D)*(C-D))=(b-1)*(c-1) ∧
    B*D^4=D*D ∧ B*D^3=D ∧ B*C=c*b := by
  let D := (1:R)/b; let C := c/b
  have e : b*C=c := UpperContractor.quotientEq c bp
  have t : b*D=1 := UpperContractor.quotientEq (1:R) bp
  have edge : b*(1-D)=b-1 := by grind only
  have spread : b*(C-D)=c-1 := by grind only
  change b*b*(C*D)=c ∧ b*b*(D*D)=1 ∧ b*b*((1-D)*(C-D))=(b-1)*(c-1) ∧
    b*b*D^4=D*D ∧ b*b*D^3=D ∧ b*b*C=c*b
  have sq : b*b*(D*D)=1 := by rw [show b*b*(D*D)=(b*D)*(b*D) by grind only,t]; grind only
  refine ⟨?_,sq,?_,?_,?_,?_⟩
  · rw [show b*b*(C*D)=(b*C)*(b*D) by grind only,e,t]; grind only
  · rw [show b*b*((1-D)*(C-D))=(b*(1-D))*(b*(C-D)) by grind only,edge,spread]
  · rw [show b*b*D^4=(b*b*(D*D))*(D*D) by grind only,sq]; grind only
  · rw [show b*b*D^3=(b*b*(D*D))*D by grind only,sq]; grind only
  · rw [show b*b*C=(b*C)*b by grind only,e]

noncomputable def lowerSplit (z y x b c l m : R) (r : RayData R) : R :=
  c*(z*(x-1)-3*x-5/2-l)*r.n+(y*(z+y+x)-m)*(r.v-(b-1)*(c-1)*r.tail)-c*y*r.v
noncomputable def lowerSingle (z y x b c l m : R) (r : RayData R) : R :=
  let C := (z+y+x)*(y+x)*x-l*((y+x)+x)-m*x
  c*(z*x-l)*r.n+(y*(z+y+x)-m)*(r.v-(b-1)*(c-1)*r.tail)-c*(z+2*y+3*x)*r.m-r.constant/(b*b)-
      smaller (x/b) (c*b*C)*r.improvement

theorem rescaleBounds (z y x b c l m : R) (r : RayData R) (bp : 0<b) :
    b*b*splitPrice z y x (c/b) (1/b) l m r=lowerSplit z y x b c l m r ∧
    b*b*single z y x (c/b) (1/b) l m r=lowerSingle z y x b c l m r := by
  let C := c/b; let D := (1:R)/b; let B := b*b
  let g := z*x; let delta := y*(z+y+x)-m
  let J := (z+y+x)*(y+x)*x-l*((y+x)+x)-m*x
  obtain ⟨td,dd,pre,q4,q3,tc⟩ := scaleFactors b c bp
  change B*(C*D)=c at td; change B*(D*D)=1 at dd
  change B*((1-D)*(C-D))=(b-1)*(c-1) at pre
  change B*D^4=D*D at q4; change B*D^3=D at q3; change B*C=c*b at tc
  have Bpos := OrderedRing.mul_pos bp bp
  have constantEq : (D*D)*r.constant=r.constant/(b*b) := by
    have e := UpperContractor.quotientEq r.constant Bpos
    have eq : B*((D*D)*r.constant)=r.constant := by rw [← Semiring.mul_assoc,dd]; grind only
    apply Std.le_antisymm <;> apply UpperContractor.cancelLe Bpos <;> grind only
  have qdiv : D*x=x/b := by
    have inv := UpperContractor.quotientEq (1:R) bp
    have e := UpperContractor.quotientEq x bp
    have eq : b*(D*x)=x := by change b*((1/b)*x)=x; rw [← Semiring.mul_assoc,inv]; grind only
    apply Std.le_antisymm <;> apply UpperContractor.cancelLe bp <;> grind only
  have priced : B*smaller (D^3*x) (C*J)=smaller (x/b) (c*b*J) := by
    rw [minScale _ _ _ Bpos,← Semiring.mul_assoc B (D^3),q3,qdiv,← Semiring.mul_assoc B C,tc]
  have common : B*(delta*(D*D*r.v-(1-D)*(C-D)*r.tail))=delta*(r.v-(b-1)*(c-1)*r.tail) := by
    rw [show B*(delta*(D*D*r.v-(1-D)*(C-D)*r.tail))=delta*((B*(D*D))*r.v-(B*((1-D)*(C-D)))*r.tail) by grind only,dd,pre]; grind only
  have first (a t : R) : B*(C*D*a*t)=c*a*t := by rw [show B*(C*D*a*t)=(B*(C*D))*a*t by grind only,td]
  have distribute (p q : R) : B*(p-q)=B*p-B*q := by grind only
  have adding (p q : R) : B*(p+q)=B*p+B*q := by grind only
  constructor
  · unfold splitPrice lowerSplit
    change B*(C*D*(g-z-3*x-5/2-l)*r.n+delta*(D*D*r.v-(1-D)*(C-D)*r.tail)-C*D*y*r.v)=_
    rw [distribute,adding,common,first,first]
    dsimp only [g,delta]; grind only
  · unfold single lowerSingle
    change B*(C*D*(g-l)*r.n+delta*(D*D*r.v-(1-D)*(C-D)*r.tail)-C*D*(z+2*y+3*x)*r.m-D^4*r.constant-smaller (D^3*x) (C*J)*r.improvement)=_
    rw [distribute,distribute,distribute,adding,common,first,first,
      ← Semiring.mul_assoc B (D^4),q4,constantEq,← Semiring.mul_assoc B (smaller _ _),priced]

end RankSeven.LowerExteriorScale
#print axioms RankSeven.LowerExteriorScale.rescaleBounds