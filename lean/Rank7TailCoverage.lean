import Init.Grind

namespace RankSeven

open Lean.Grind

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- A comparison holds throughout an inclusive interval. -/
def OnClosed (P : R → Prop) (lo hi : R) : Prop :=
  ∀ x, lo ≤ x → x ≤ hi → P x

/-- Adjacent inclusively certified cells glue, including their common endpoint. -/
theorem glueClosed {P : R → Prop} {a b c : R}
    (left : OnClosed P a b) (right : OnClosed P b c) : OnClosed P a c := by
  intro x lower upper
  by_cases side : x ≤ b
  · exact left x lower side
  · exact right x (by grind) upper

/-- The thirteen C++ replay intervals, written in the scaled variable
    \(x=256(d/b)\). The hypotheses here are the mathematical comparisons
    within the cells. -/
theorem mainTailCoverage (P : R → Prop)
    (c01 : OnClosed P 144 145) (c02 : OnClosed P 145 148)
    (c03 : OnClosed P 148 152) (c04 : OnClosed P 152 156)
    (c05 : OnClosed P 156 160) (c06 : OnClosed P 160 164)
    (c07 : OnClosed P 164 168) (c08 : OnClosed P 168 172)
    (c09 : OnClosed P 172 176) (c10 : OnClosed P 176 180)
    (c11 : OnClosed P 180 184) (c12 : OnClosed P 184 188)
    (c13 : OnClosed P 188 192) : OnClosed P 144 192 := by
  have a := glueClosed c01 c02
  have b := glueClosed c03 c04
  have c := glueClosed c05 c06
  have d := glueClosed c07 c08
  have e := glueClosed c09 c10
  have f := glueClosed c11 c12
  exact glueClosed (glueClosed (glueClosed a b) (glueClosed c d))
    (glueClosed (glueClosed e f) c13)

/-- Glue every tail-ratio region of the rank-seven proof in the same
    scaled variable. This covers every \(0<d/b\le 1\).
    Each regional comparison still enters as a hypothesis. -/
theorem allTailRatios (P : R → Prop)
    (largeFifth : ∀ x, 0 < x → x ≤ 128 → P x)
    (upperAnchor : OnClosed P 128 144)
    (mainBand : OnClosed P 144 192)
    (lowerBand : ∀ x, 192 ≤ x → 101 * x ≤ 25600 → P x)
    (closeBottom : ∀ x, 25600 ≤ 101 * x → x ≤ 256 → P x) :
    ∀ x, 0 < x → x ≤ 256 → P x := by
  intro x positive inRange
  by_cases small : x ≤ 128
  · exact largeFifth x positive small
  by_cases anchor : x ≤ 144
  · exact upperAnchor x (by grind) anchor
  by_cases middle : x ≤ 192
  · exact mainBand x (by grind) middle
  by_cases lower : 101 * x ≤ 25600
  · exact lowerBand x (by grind) lower
  · exact closeBottom x (by grind) inRange

end RankSeven

#print axioms RankSeven.mainTailCoverage
#print axioms RankSeven.allTailRatios
