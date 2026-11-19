import Rank7UpperPhysicalInterior
namespace RankSeven.UpperCornerCompletion
open Lean.Grind
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Two independently priced inequalities interpolate by the actual missing
triple mass, with no choice of a completion basis. -/
theorem minimumCompletion {F base x a b J price improvement : R} (xn : 0≤x)
    (bn : 0≤b) (priceSmall : price≤a ∧ price≤b) (pn : 0≤price)
    (pos : (0≤J → improvement=J) ∧ (J≤0 → improvement=0))
    (low : F≤base-b*x) (high : F≤base-b*x-a*(J-x)) :
    F≤base-price*improvement := by
  by_cases jp : 0≤J
  · rw [pos.1 jp]
    by_cases inside : J≤x
    · have bx := OrderedRing.mul_le_mul_of_nonneg_right priceSmall.2 xn
      have jx := OrderedRing.mul_le_mul_of_nonneg_left inside pn
      grind only
    · have bj := OrderedRing.mul_le_mul_of_nonneg_right priceSmall.2 xn
      have aj := OrderedRing.mul_le_mul_of_nonneg_right priceSmall.1 (show 0≤J-x by grind only)
      grind only
  · rw [pos.2 (by grind only)]
    have charge := OrderedRing.mul_nonneg bn xn; grind only

/-- Nonnegativity of the exact completion price at all permitted shift
fractions; 2λ≤hq and 2μ≤k(h+k+q) suffice. -/
theorem completionPriceNonnegative {h k q lambda mu : R} (hn : 0≤h) (kn : 0≤k) (qn : 0≤q)
    (ls : 2*lambda≤h*q) (ms : 2*mu≤k*(h+k+q)) :
    0≤(h+k+q)*(k+q)*q-lambda*((k+q)+q)-mu*q := by
  have l := OrderedRing.mul_le_mul_of_nonneg_right ls (show 0≤(k+q)+q by grind only)
  have m := OrderedRing.mul_le_mul_of_nonneg_right ms qn
  have hkk := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hn kn) qn
  have kkk := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg kn kn) qn
  have kqq := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg kn qn) qn
  have qqq := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg qn qn) qn
  grind only
end RankSeven.UpperCornerCompletion
#print axioms RankSeven.UpperCornerCompletion.minimumCompletion
#print axioms RankSeven.UpperCornerCompletion.completionPriceNonnegative
