import Rank7PauliReduction

namespace RankSeven.UpperCorner

open Lean.Grind

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The global 1/13 floor on the tail part of Ψ, with denominators cleared.
    The three gaps are c-d, 1-c, and d. -/
theorem psiTailFloor (c d : R) :
    6 ≤ 13 * (6 * (c - d)^2 + (1 - c)^2 + d^2) := by
  let first := c - d
  let second := 1 - c
  have a := squareNonnegative (6*first - second)
  have b := squareNonnegative (6*first - d)
  have e := squareNonnegative (second - d)
  grind

/-- The two reserve terms admit the affine tangent actually evaluated by
    the C++ box checker. -/
theorem oddReserveTangent (c d cUpper dLower : R) :
    (1-cUpper) * (1+cUpper-2*c) + dLower * (2*d-dLower) ≤ (1-c)^2 + d^2 := by
  have a := squareNonnegative (cUpper - c)
  have b := squareNonnegative (d - dLower)
  grind

theorem oddReserveTangentNonnegative (c d cUpper dLower : R)
    (hc : c ≤ cUpper) (hUnit : cUpper ≤ 1) (hd : dLower ≤ d) (hLower : 0 ≤ dLower) :
    0 ≤ (1-cUpper) * (1+cUpper-2*c) + dLower * (2*d-dLower) := by
  have a := OrderedRing.mul_nonneg (show 0 ≤ 1-cUpper by grind) (show 0 ≤ 1+cUpper-2*c by grind)
  have b := OrderedRing.mul_nonneg hLower (show 0 ≤ 2*d-dLower by grind)
  grind

/-- Twice the multiaffine supporting price for an active trace cut. -/
def twiceSupport (inside outside weight : R) : R :=
  2 * weight * (inside - outside) - weight^2 * (inside + outside)

/-- Completing the square gives a lower price for the positive-part width
    term. Denominator 2*(inside+outside) has been cleared. -/
theorem supportWidthBound (inside outside weight gap : R)
    (weightNonnegative : 0 ≤ weight) (sumNonnegative : 0 ≤ inside + outside)
    (positivePart : (outside ≤ inside ∧ gap = inside - outside) ∨ (inside ≤ outside ∧ gap = 0)) :
    (inside + outside) * twiceSupport inside outside weight ≤ gap^2 := by
  unfold twiceSupport
  rcases positivePart with ⟨_, rfl⟩ | ⟨order, rfl⟩
  · have square := squareNonnegative (inside - outside - weight * (inside + outside))
    grind
  · have lin := OrderedRing.mul_nonneg weightNonnegative (show 0 ≤ outside - inside by grind)
    have quad := OrderedRing.mul_nonneg (squareNonnegative weight) sumNonnegative
    have priceNonpositive :
        0 ≤ -(2 * weight * (inside - outside) - weight^2 * (inside + outside)) := by grind
    have signed := OrderedRing.mul_nonneg sumNonnegative priceNonpositive
    grind

/-- The lower-left support weight remains eligible as the inside endpoint
    grows with the outside endpoint held fixed. -/
theorem supportConditionMonotone (initialInside inside outside weight : R)
    (weightAtMostOne : weight ≤ 1) (insideGrows : initialInside ≤ inside)
    (initialCut : weight * (initialInside + outside) ≤ initialInside - outside) :
    weight * (inside + outside) ≤ inside - outside := by
  have step := OrderedRing.mul_nonneg (show 0 ≤ 1-weight by grind) (show 0 ≤ inside-initialInside by grind)
  grind

theorem supportNonnegative (inside outside weight : R) (weightNonnegative : 0 ≤ weight)
    (sumNonnegative : 0 ≤ inside + outside)
    (eligible : weight = 0 ∨ weight * (inside + outside) ≤ inside - outside) :
    0 ≤ twiceSupport inside outside weight := by
  unfold twiceSupport
  rcases eligible with rfl | base
  · grind
  · have a := OrderedRing.mul_nonneg weightNonnegative
      (show 0 ≤ inside - outside - weight * (inside + outside) by grind)
    have b := OrderedRing.mul_nonneg (squareNonnegative weight) sumNonnegative
    grind

end RankSeven.UpperCorner

#print axioms RankSeven.UpperCorner.psiTailFloor
#print axioms RankSeven.UpperCorner.oddReserveTangent
#print axioms RankSeven.UpperCorner.supportWidthBound
#print axioms RankSeven.UpperCorner.supportConditionMonotone
#print axioms RankSeven.UpperCorner.supportNonnegative
