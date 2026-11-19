import Rank7UpperWeighted
import Rank7UpperOldRegions

namespace RankSeven.UpperResidual

open Lean.Grind UpperWeighted UpperContractor

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

private theorem cancelPositive {a b c : R} (hc : 0<c) (less : c*a<c*b) : a<b := by
  by_cases ordered : a<b
  · exact ordered
  · have opposite := OrderedRing.mul_le_mul_of_nonneg_left
      (show b≤a by grind only) (Std.le_of_lt hc)
    grind only

/-- The two strict reserve bounds obtained when the unit weighted test
fails, with positive completion. The coefficients are cleared exactly. -/
theorem polynomialLimits {D delta g q : R} (d0 : 0<delta) (nonnegD : 0<D)
    (gBound : 2928*delta^2+25*g^2<86400*D*delta)
    (qBound : 8784*delta^2+25*q^4<259200*D*delta) :
    61*delta<1800*D ∧ g<160*D ∧ q^4<17^4*D^2 := by
  have completion := RankSeven.squareNonnegative (61*delta-900*D)
  have gOnSquare := OrderedRing.mul_lt_mul_of_pos_left gBound (show (0:R)<61 by grind only)
  have qOnSquare := OrderedRing.mul_lt_mul_of_pos_left qBound (show (0:R)<61 by grind only)
  have gained : 1525*g^2<38880000*D^2 := by
    have floor := OrderedRing.mul_le_mul_of_nonneg_left completion (show (0:R)≤48 by grind only)
    grind only
  have reserved : 1525*q^4<116640000*D^2 := by
    have floor := OrderedRing.mul_le_mul_of_nonneg_left completion (show (0:R)≤144 by grind only)
    grind only
  have dsq := RankSeven.squareNonnegative D
  have gsq := RankSeven.squareNonnegative g
  refine ⟨cancelPositive d0 (by grind only),?_,?_⟩
  · by_cases small : g<160*D
    · exact small
    · have mono := OrderedRing.mul_nonneg (show 0≤g-160*D by grind only)
        (show 0≤g+160*D by grind only)
      have bound : g^2≥25600*D^2 := by grind only
      have scaled := OrderedRing.mul_le_mul_of_nonneg_left bound (show (0:R)≤1525 by grind only)
      grind only
  · have grow := OrderedRing.mul_le_mul_of_nonneg_right
      (show (116640000:R)≤1525*17^4 by grind only) dsq
    apply cancelPositive (c:=(1525:R)) (by grind only)
    grind only

/-- The C++ box caps for k and q follow without a square-root witness
from the residual inequalities and the ordered last two probabilities. -/
theorem tailHeadCaps {h k q c d : R} (h0 : 0≤h) (k0 : 0≤k) (q0 : 0≤q)
    (d0 : 0<d) (ordered : d≤c) (unit : c≤1)
    (D0 : 0<discount c d)
    (delta : 61*(k*(h+k+q))<1800*discount c d)
    (qBound : q^4<17^4*(discount c d)^2) :
    2*k<11*d ∧ q<17*d := by
  let D := discount c d
  have cap : D≤d*d := by
    have loss := OrderedRing.mul_nonneg (show 0≤1-d by grind only) (show 0≤c-d by grind only)
    unfold D discount
    grind only
  have kk : k*k≤k*(h+k+q) := by
    have := OrderedRing.mul_nonneg k0 (show 0≤h+q by grind only)
    grind only
  have kkScaled := OrderedRing.mul_le_mul_of_nonneg_left kk (show (0:R)≤61 by grind only)
  have capScaled := OrderedRing.mul_le_mul_of_nonneg_left cap (show (0:R)≤1800 by grind only)
  have dSq := RankSeven.squareNonnegative d
  constructor
  · by_cases small : 2*k<11*d
    · exact small
    · have mono := OrderedRing.mul_nonneg (show 0≤2*k-11*d by grind only)
        (show 0≤2*k+11*d by grind only)
      have weak : 121*d*d≤4*k*k := by grind only
      have strong := OrderedRing.mul_le_mul_of_nonneg_left weak (show (0:R)≤61 by grind only)
      grind only
  · have d4 : D^2≤(d*d)^2 := by
      have grow := OrderedRing.mul_nonneg (show 0≤d*d-D by grind only)
        (show 0≤d*d+D by grind only)
      grind only
    have limit := OrderedRing.mul_le_mul_of_nonneg_left d4
      (show (0:R)≤17^4 by grind only)
    by_cases small : q<17*d
    · exact small
    · have diff := OrderedRing.mul_nonneg (show 0≤q-17*d by grind only)
        (show 0≤q+17*d by grind only)
      have qSq := RankSeven.squareNonnegative q
      have fourth := OrderedRing.mul_nonneg (show 0≤q*q-17^2*d*d by grind only)
        (show 0≤q*q+17^2*d*d by grind only)
      grind only

/-- The real unit-shift failure, with a nonzero middle gap and ordered
positive tails, implies the exact strict residual products and ordered
head caps used by the upper checker. -/
theorem failureDomain {h k q c d : R}
    (h0 : 0≤h) (k0 : 0<k) (q0 : 0≤q) (d0 : 0<d)
    (ordered : d≤c) (unit : c≤1)
    (failed : margin h k q c d 1≤0) :
    0<discount c d ∧ h*q<160*discount c d ∧
    61*(k*(h+k+q))<1800*discount c d ∧ 2*k<11*d ∧ q<17*d := by
  have c0 : 0<c := Std.lt_of_lt_of_le d0 ordered
  obtain ⟨D0,deltaPos,gb,qb⟩ := failedUnitPolynomialBounds h0 k0 q0 c0 d0 failed
  obtain ⟨delta,g,qFourth⟩ := polynomialLimits deltaPos D0 gb qb
  obtain ⟨kk,qq⟩ := tailHeadCaps h0 (Std.le_of_lt k0) q0 d0 ordered unit D0 delta qFourth
  exact ⟨D0,g,delta,kk,qq⟩ 


/-- A point outside the normalized analytic comparison regions, whose
real unit-shift margin is nonpositive, has the residual required by
the C++ contractor. The open near/far cuts are geometric branch conditions. -/
theorem contractResidualOfTests {h k q c d : R}
    (h0 : 0≤h) (k0 : 0<k) (q0 : 1≤2*q) (d0 : 0<d)
    (ordered : d≤c) (unit : c≤1) (slab : 4*d≤3)
    (near : 101*d<100*c) (far : 5*c<9*d)
    (survives : ¬UpperOldRegions.OldCondition h k q c d)
    (failed : margin h k q c d 1≤0) : Residual h k q c d := by
  obtain ⟨_,g,delta,_,_⟩ := failureDomain h0 k0 (by grind only) d0 ordered unit failed
  have lowHead : c-c*q-2*d*k<0 := by
    by_cases pos : 0≤c-c*q-2*d*k
    · exact False.elim (survives (Or.inr (Or.inl pos)))
    · grind only
  have share : ¬((1+(h+k+q))*(1+q)*d ≤ 1+(h+k+q) ∨
      (1+(h+k+q))*(1+q)*d ≤ (1+(k+q))*(1+q)) := by
    intro bad
    exact survives (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad)))))))
  have sharedA : 1+h+k+q<(1+h+k+q)*(1+q)*d := by grind only
  have sharedB : (1+k+q)*(1+q)<(1+h+k+q)*(1+q)*d := by grind only
  exact ⟨h0,Std.le_of_lt k0,by grind only,d0,ordered,unit,near,far,
    sharedA,sharedB,lowHead,g,delta,twoThirdsFloor slab q0⟩

end RankSeven.UpperResidual

#print axioms RankSeven.UpperResidual.polynomialLimits
#print axioms RankSeven.UpperResidual.tailHeadCaps
#print axioms RankSeven.UpperResidual.failureDomain

#print axioms RankSeven.UpperResidual.contractResidualOfTests
