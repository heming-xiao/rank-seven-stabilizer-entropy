import Rank7HighestCodeLocalization

namespace RankSeven.HighestAnchorMoments

open Lean.Grind Pauli ComplexScalar SymmetricDefect
variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem squareRootOrder (x y : R) (hy : 0≤y) (s : x^2≤y^2) : x≤y := by
  by_cases h : x≤y
  · exact h
  · have mul := OrderedRing.mul_pos (show 0<x-y by grind only) (show 0<x+y by grind only)
    grind only

theorem fourthDeviation (a z : ComplexScalar R) (b e : R) (bn : 0≤b) (en : 0≤e)
    (ac : normSq a≤b^2) (zc : normSq z≤e^2) :
    (normSq (a+z))^2≤(normSq a)^2+4*normSq a*(star a*z).re+(6*normSq a+4*b*e+e^2)*normSq z := by
  let C := normSq a
  let t := normSq z
  let s := (star a*z).re
  have sn : s^2≤C*t := by
    have n := normSq_mul (star a) z
    rw [normSq_star] at n
    change (star a*z).re^2+(star a*z).im^2=C*t at n
    have pos := squareNonnegative (star a*z).im
    change (star a*z).re^2≤C*t; grind only
  have d : C*t≤b^2*e^2 := Std.le_trans (OrderedRing.mul_le_mul_of_nonneg_right ac (normSq_nonnegative z))
    (OrderedRing.mul_le_mul_of_nonneg_left zc (squareNonnegative b))
  have sb := squareRootOrder s (b*e) (OrderedRing.mul_nonneg bn en)
    (show s^2≤(b*e)^2 by
      have eq : b^2*e^2=(b*e)^2 := by grind only
      rw [←eq]; exact Std.le_trans sn d)
  have ee := OrderedRing.mul_le_mul_of_nonneg_right zc (normSq_nonnegative z)
  have se := OrderedRing.mul_le_mul_of_nonneg_right sb (normSq_nonnegative z)
  have add : normSq (a+z)=C+t+2*s := by simp only [C,t,s,normSq,re_add,im_add,re_mul,re_star,im_star]; grind only
  change normSq (a+z)^2≤C^2+4*C*s+(6*C+4*b*e+e^2)*t
  change t*t≤e^2*t at ee
  change s*t≤b*e*t at se
  rw [add]; grind only

theorem averagedFourth (xs : List α) (h : R) (hn : 0≤h) (unit : h*sumOver xs (fun _ => (1:R))=1)
    (a : ComplexScalar R) (r : α→ComplexScalar R) (b e : R) (bn : 0≤b) (en : 0≤e)
    (ac : normSq a≤b^2) (rc : ∀i∈xs,normSq (r i)≤e^2)
    (center : sumOver xs (fun i => (star a*r i).re)=0) :
    h*sumOver xs (fun i => (normSq (a+r i))^2)≤
      (normSq a)^2+(6*normSq a+4*b*e+e^2)*(h*sumOver xs (fun i => normSq (r i))) := by
  let C := normSq a
  let M := 6*C+4*b*e+e^2
  let u (i : α) := normSq (a+r i)^2
  let v (i : α) := C^2*(1:R)+4*C*(star a*r i).re+M*normSq (r i)
  have pt (i : α) (hi : i∈xs) : u i≤v i := by
    unfold u v; rw [Semiring.mul_one]; exact fourthDeviation a (r i) b e bn en ac (rc i hi)
  have sum := Compression.sumOverNonnegative xs (fun i => v i-u i) (fun i hi => by have := pt i hi; grind only)
  rw [Compression.sumOverSub] at sum
  have price := OrderedRing.mul_le_mul_of_nonneg_left (show sumOver xs u≤sumOver xs v by grind only) hn
  unfold v at price
  rw [sumOverAdd,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,←sumOverMulLeft,center] at price
  have cnt := congrArg (fun x : R => C^2*x) unit
  change h*sumOver xs u≤C^2+M*(h*sumOver xs (fun i => normSq (r i)))
  grind only

theorem fourthMomentDeficit (b C rho kappa : R) (bLarge : 3≤4*b) (bUnit : b≤1)
    (cLarge : 9≤16*C) (cBound : C≤b^2) (resid : rho-C≤(1-b)^2)
    (rv : 0≤rho-C)
    (mom : 1-kappa≤C^2+(6*C+4*b*(1-b)+(1-b)^2)*(rho-C)+4*b*(1-b)*(1-rho)) :
    4*b^2*(1-b)*(3*b-2)≤kappa := by
  let e := 1-b
  have ee : 0≤e := by unfold e; grind only
  have bb : 0≤b := by grind only
  have sq := squareNonnegative b
  have q := squareNonnegative e
  have bend := OrderedRing.mul_nonneg (show 0≤4*b-3 by grind only) (show 0≤4*b-1 by grind only)
  have ce : 0≤b^2+C-4*b*e := by unfold e; grind only
  have co := OrderedRing.mul_nonneg (show 0≤b^2-C by grind only) ce
  have grow := OrderedRing.mul_nonneg (show 0≤b^2-C by grind only) rv
  have re := OrderedRing.mul_le_mul_of_nonneg_left resid (show 0≤6*b^2+(1-b)^2 by have := squareNonnegative (1-b); grind only)
  unfold e at co
  grind only

theorem smallDeficit (b kappa : R) (bLarge : 3≤4*b) (bUnit : b≤1) (small : 15*kappa≤2)
    (fourth : 4*b^2*(1-b)*(3*b-2)≤kappa) :
    19<20*b ∧ 6137*(1-b)≤2000*kappa := by
  have b0 : 0≤b := by grind only
  have sq := squareNonnegative b
  have near : 19<20*b := by
    by_cases done : 19<20*b
    · exact done
    · have pe := OrderedRing.mul_nonneg (show 0≤4*b-3 by grind only) (show 0≤19-20*b by grind only)
      have s := OrderedRing.mul_nonneg pe (show 0≤1200*b^2+40*b+13 by grind only)
      grind only
  let t := 20*b-19
  have tn : 0≤t := by unfold t; grind only
  have t2 := squareNonnegative t
  have t3 := OrderedRing.mul_nonneg tn t2
  have low : 6137≤2000*(4*b^2*(3*b-2)) := by unfold t at tn t2 t3; grind only
  have scale := OrderedRing.mul_le_mul_of_nonneg_right low (show 0≤1-b by grind only)
  exact ⟨near,by grind only⟩

open HighestCodeLocalization FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (image normSum)
open PhysicalPairedReduction (dagger)

theorem projectionMismatch [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs)
    (Q : Mx α R) (q : Projection xs Q) (x y : α→ComplexScalar R)
    (ux : normSum xs x=1) (uy : normSum xs y=1) :
    normSq (innerProduct xs x y)≤1-(energy xs Q x-energy xs Q y)^2 := by
  let S := compl Q
  let a := innerProduct xs x (image xs Q y)
  let b := innerProduct xs x (image xs S y)
  let U := energy xs Q x
  let V := energy xs Q y
  have qS := complement xs nd full Q q
  have cs : normSq a≤U*V := projectedBound xs Q q x y
  have ds : normSq b≤(1-U)*(1-V) := by
    have bound := projectedBound xs S qS x y
    have energyS (w : α→ComplexScalar R) : energy xs S w=normSum xs w-energy xs Q w := by
      unfold S compl; rw [energySub,energyIdentity xs nd full]
    rw [energyS,energyS,ux,uy] at bound; exact bound
  have eq : innerProduct xs x y=a+b := by
    let X (i : α) (_ : Unit) := x i
    let Y (i : α) (_ : Unit) := y i
    change matMul xs (dagger X) Y () ()=_+matMul xs (dagger X) (matMul xs (compl Q) Y) () ()
    unfold compl; rw [subLeft,idLeft xs nd full,subRight]
    change matMul xs (dagger X) Y () ()=a+(matMul xs (dagger X) Y () ()-a); grind only
  have c0 (w : α→ComplexScalar R) : 0≤energy xs Q w := by
    rw [energyNorm xs Q q]; exact Compression.sumOverNonnegative _ _ (fun i _ => normSq_nonnegative _)
  have ub (w : α→ComplexScalar R) : energy xs Q w≤normSum xs w := by
    rw [energyNorm xs Q q]; exact contract xs nd full Q q w
  have un : 0≤U := c0 x
  have vn : 0≤V := c0 y
  have uu : U≤1 := (ux ▸ ub x)
  have vv : V≤1 := (uy ▸ ub y)
  let m := (star a*b).re
  have ms : m^2≤normSq a*normSq b := by
    have s := normSq_mul (star a) b; rw [normSq_star] at s
    change m^2+(star a*b).im^2=_ at s; have pos := squareNonnegative (star a*b).im; grind only
  have big := Std.le_trans (OrderedRing.mul_le_mul_of_nonneg_right cs (normSq_nonnegative b))
    (OrderedRing.mul_le_mul_of_nonneg_left ds (OrderedRing.mul_nonneg un vn))
  let l := U*(1-U)
  let r := V*(1-V)
  have ln : 0≤l := OrderedRing.mul_nonneg un (by grind only)
  have rn : 0≤r := OrderedRing.mul_nonneg vn (by grind only)
  have sq := squareNonnegative (l-r)
  have prod : U*V*((1-U)*(1-V))=l*r := by unfold l r; grind only
  rw [prod] at big
  have proj := squareRootOrder (2*m) (l+r) (by grind only) (by grind only)
  have e : normSq (a+b)=normSq a+normSq b+2*m := by unfold m normSq; simp only [re_add,im_add,re_mul,re_star,im_star]; grind only
  rw [eq,e]; change normSq a+normSq b+2*m≤1-(U-V)^2
  unfold l r at proj; grind only

end RankSeven.HighestAnchorMoments

#print axioms RankSeven.HighestAnchorMoments.averagedFourth
#print axioms RankSeven.HighestAnchorMoments.fourthMomentDeficit
#print axioms RankSeven.HighestAnchorMoments.smallDeficit
#print axioms RankSeven.HighestAnchorMoments.projectionMismatch

