import Rank7Interval
import Rank7PauliReduction

namespace RankSeven.JointTracePrices

open Lean.Grind Interval

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def variance (u : R) : R := u*(1-u)

theorem sharedVarianceLower (n x : R) (xNonnegative : 0 ≤ x) (capacity : 2*n+x ≤ 1) :
    variance n ≤ variance (n+x) := by
  have payment := OrderedRing.mul_nonneg xNonnegative (show 0 ≤ 1-2*n-x by grind)
  unfold variance
  grind

/-- Below the 2/3 breakpoint, the shared capacity bounds the trace
remainder by one half and produces the quadratic highest-cut price. -/
theorem lowerRatioPrices (half n r x : R) (halfUnit : 2*half=1)
    (nn : 0 ≤ n) (xn : 0 ≤ x) (capacity : 2*n+x ≤ 1) :
    n*(r-half*r^2) ≤ variance (r*n) ∧ half*n ≤ variance (n+x) := by
  have nBound : n ≤ half := by grind
  have p := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg nn (squareNonnegative r))
    (show 0 ≤ half-n by grind)
  have shared := sharedVarianceLower n x xn capacity
  have q := OrderedRing.mul_nonneg nn (show 0 ≤ half-n by grind)
  constructor
  · unfold variance
    grind only
  · calc
      _ ≤ variance n := by
        have identity := congrArg (fun z => z*n) halfUnit
        unfold variance
        grind only
      _ ≤ _ := shared

/-- Above the breakpoint the highest-cut capacity controls the remainder.
The reciprocal of the ratio is specified by its multiplication identity. -/
theorem upperRatioPrices (third n r reciprocal x : R) (thirdUnit : 3*third=1)
    (nn : 0 ≤ n) (rp : 0 < r) (xn : 0 ≤ x) (sharedCapacity : 2*n+x ≤ 1)
    (highestCapacity : 3*(r*n) ≤ 1) (reciprocalUnit : 3*r*reciprocal = 1) :
    (2*third)*r*n ≤ variance (r*n) ∧ n*(1-reciprocal) ≤ variance (n+x) := by
  have vBound : r*n ≤ third := by grind
  have nBound : n ≤ reciprocal := by
    by_cases le : n ≤ reciprocal
    · exact le
    · have positive : 0 < 3*r := OrderedRing.mul_pos (by grind : 0 < (3:R)) rp
      have opposite := OrderedRing.mul_lt_mul_of_pos_left (show reciprocal < n by grind) positive
      grind
  have vp := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (show 0 ≤ r by grind) nn)
    (show 0 ≤ third-r*n by grind)
  have np := OrderedRing.mul_nonneg nn (show 0 ≤ reciprocal-n by grind)
  have shared := sharedVarianceLower n x xn sharedCapacity
  constructor
  · have identity := congrArg (fun z => z*(r*n)) thirdUnit
    unfold variance
    grind only
  · calc
      _ ≤ variance n := by unfold variance; grind only
      _ ≤ _ := shared

def lowPrice (half r : R) : R := r-half*r^2

theorem lowPriceConcave (half a b t : R) (halfNonnegative : 0 ≤ half) (tLo : 0 ≤ t) (tHi : t ≤ 1) :
    lerp t (lowPrice half a) (lowPrice half b) ≤ lowPrice half (lerp t a b) := by
  have simplex := OrderedRing.mul_nonneg tLo (show 0 ≤ 1-t by grind)
  have gap := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg halfNonnegative simplex)
    (squareNonnegative (b-a))
  unfold lowPrice lerp
  grind

theorem reciprocalConvex (a b t ai bi ri : R) (ap : 0 < a) (bp : 0 < b)
    (tLo : 0 ≤ t) (tHi : t ≤ 1) (aiUnit : a*ai=1) (biUnit : b*bi=1)
    (riUnit : lerp t a b*ri=1) : ri ≤ lerp t ai bi := by
  let r := lerp t a b
  have rp : 0 < r := lerpPositive tLo tHi ap bp
  have scale : 0 < a*b*r := OrderedRing.mul_pos (OrderedRing.mul_pos ap bp) rp
  have one : a*b*r*(lerp t ai bi-ri) = r*((1-t)*b+t*a)-a*b := by
    change r*ri=1 at riUnit
    unfold lerp
    grind only
  have two : r*((1-t)*b+t*a)-a*b = t*(1-t)*(b-a)^2 := by
    unfold r lerp
    grind only
  have p := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg tLo (show 0 ≤ 1-t by grind))
    (squareNonnegative (b-a))
  rw [←two,←one] at p
  by_cases le : ri ≤ lerp t ai bi
  · exact le
  · have opposite := OrderedRing.mul_pos scale (show 0 < ri - lerp t ai bi by grind)
    grind

theorem highSharedConcave (third a b t ai bi ri : R) (thirdNonnegative : 0 ≤ third)
    (ap : 0 < a) (bp : 0 < b) (tLo : 0 ≤ t) (tHi : t ≤ 1)
    (aiUnit : a*ai=1) (biUnit : b*bi=1) (riUnit : lerp t a b*ri=1) :
    lerp t (1-third*ai) (1-third*bi) ≤ 1-third*ri := by
  have j := reciprocalConvex a b t ai bi ri ap bp tLo tHi aiUnit biUnit riUnit
  have p := OrderedRing.mul_nonneg thirdNonnegative (show 0 ≤ lerp t ai bi-ri by grind)
  unfold lerp at *
  grind

/-- The unbounded last ratio interval uses the v-axis slope and the
value at the last finite ray. The shared price increases with the ratio. -/
theorem lastRayPositive (r₀ r inv₀ inv intercept slope shared : R) (start : 0 < r₀) (order : r₀ ≤ r)
    (inv₀Unit : r₀*inv₀=1) (invUnit : r*inv=1) (slopeNonnegative : 0 ≤ slope)
    (sharedNonnegative : 0 ≤ shared) (firstPositive : 0 < intercept+slope*r₀+shared*(1-inv₀)) :
    0 < intercept+slope*r+shared*(1-inv) := by
  have invPositive : 0 < inv := by
    by_cases pos : 0 < inv
    · exact pos
    · have product := OrderedRing.mul_nonneg (show 0 ≤ r by grind) (show 0 ≤ -inv by grind)
      grind
  have nonneg := OrderedRing.mul_nonneg (show 0 ≤ r-r₀ by grind) (show 0 ≤ inv by grind)
  have compare : inv ≤ inv₀ := by
    by_cases le : inv ≤ inv₀
    · exact le
    · have opposite := OrderedRing.mul_lt_mul_of_pos_left (show inv₀ < inv by grind) start
      grind
  have gainOne := OrderedRing.mul_nonneg slopeNonnegative (show 0 ≤ r-r₀ by grind)
  have gainShared := OrderedRing.mul_nonneg sharedNonnegative (show 0 ≤ inv₀-inv by grind)
  grind

end RankSeven.JointTracePrices

#print axioms RankSeven.JointTracePrices.lowerRatioPrices
#print axioms RankSeven.JointTracePrices.upperRatioPrices
#print axioms RankSeven.JointTracePrices.reciprocalConvex
#print axioms RankSeven.JointTracePrices.lastRayPositive
