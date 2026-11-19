import Init.Grind

namespace RankSeven

open Lean.Grind

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The square-root bound used to replace \(\zeta=4-2\sqrt{3}\) by \(27/50\). -/
theorem sqrtThreeLowerBound (s : R) (nonnegative : 0 ≤ s) (square : s * s = 3) :
    173 ≤ 100 * s := by
  by_cases smaller : 100 * s < 173
  · have first : 0 ≤ 173 - 100 * s := by grind
    have second : 0 ≤ 173 + 100 * s := by grind
    have product := OrderedRing.mul_nonneg first second
    grind
  · grind

/-- At the largest allowed shifts, the two debits in the cubic coefficient
    of equation (4) are together at most \(78XYq\). -/
theorem mixedCutExteriorDebit (h k q : R)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hq : 0 ≤ q) :
    let Y := k + q
    let X := h + Y
    36 * h * q * (Y + q) + 42 * k * X * q ≤ 78 * X * Y * q := by
  dsimp
  have hhq := OrderedRing.mul_nonneg hh hq
  have hk2 := OrderedRing.mul_nonneg hk hk
  have hkq := OrderedRing.mul_nonneg hk hq
  have hq2 := OrderedRing.mul_nonneg hq hq
  have budget : 0 ≤ 6 * (h * q) + 36 * (k * k) + 114 * (k * q) + 78 * (q * q) := by
    grind
  have paid := OrderedRing.mul_nonneg budget hq
  grind

/-- Equation (5) in the mixed-cut transfer note after replacing the radical
    by its rational upper bound, setting \(w=S/b\), and clearing
    the positive denominator \(25(b+q)\). -/
theorem mixedCutRate (b d q k w : R)
    (hd : 0 ≤ d) (hk : 0 ≤ k) (hdq : 2 * d ≤ 3 * q)
    (hb : d ≤ b) (hw : w ≤ d) :
    (1296 * w * k + 1200 * d * q) * (b + q) + 600 * w * q * q
      ≤ 2292 * (k + q) * q * (b + q) := by
  have hq : 0 ≤ q := by grind
  have hsum : 0 ≤ b + q := by grind
  have hcoeff : 0 ≤ 2292 * q - 1296 * d := by grind
  have hhighest := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hcoeff hk) hsum
  let tailGap := b - d
  let headGap := 3 * q - 2 * d
  have ht : 0 ≤ tailGap := by grind
  have hh : 0 ≤ headGap := by grind
  have hd2 := OrderedRing.mul_nonneg hd hd
  have hdt := OrderedRing.mul_nonneg hd ht
  have hdh := OrderedRing.mul_nonneg hd hh
  have hht := OrderedRing.mul_nonneg hh ht
  have hh2 := OrderedRing.mul_nonneg hh hh
  have expansion :
      9 * ((2292 * q - 1200 * d) * (b + q) - 600 * d * q) =
        1320 * (d * d) + 2952 * (d * tailGap) + 10644 * (d * headGap)
          + 6876 * (headGap * tailGap) + 2292 * (headGap * headGap) := by
    grind
  have hshared : 0 ≤ (2292 * q - 1200 * d) * (b + q) - 600 * d * q := by grind
  have hsharedWeighted := OrderedRing.mul_nonneg hq hshared
  have hslack : 0 ≤ d - w := by grind
  have hksum := OrderedRing.mul_nonneg hk hsum
  have hq2 := OrderedRing.mul_nonneg hq hq
  have htransport : 0 ≤ 1296 * (k * (b + q)) + 600 * (q * q) := by grind
  have htransportWeighted := OrderedRing.mul_nonneg hslack htransport
  grind

/-- Equation (5) with the square-root expression retained and its positive
    denominator cleared. The variables \(w\) and \(s\) represent \(S/b\)
    and the nonnegative square root of three. -/
theorem mixedCutRateWithRadical
    (b d q k w s : R) (hd : 0 ≤ d) (hk : 0 ≤ k)
    (hdq : 2 * d ≤ 3 * q) (hb : d ≤ b) (hw0 : 0 ≤ w) (hw : w ≤ d)
    (hs : 0 ≤ s) (hsq : s * s = 3) :
    (2400 * (4 - 2 * s) * w * k + 1200 * d * q) * (b + q) + 600 * w * q * q
      ≤ 2292 * (k + q) * q * (b + q) := by
  have hsbound := sqrtThreeLowerBound s hs hsq
  have hcoeff : 0 ≤ 1296 - 2400 * (4 - 2 * s) := by grind
  have hsum : 0 ≤ b + q := by grind
  have hdifference := OrderedRing.mul_nonneg
    (OrderedRing.mul_nonneg hcoeff (OrderedRing.mul_nonneg hw0 hk)) hsum
  have hmajorant := mixedCutRate b d q k w hd hk hdq hb hw
  grind

/-- The final bookkeeping on the fourth-gap ray. The analytic width
    and crossing estimates supply the hypothesis called drift. -/
theorem mixedCutSeedConclusion
    (rate F0 Fp Q W10 W1p WS0 WSp T1 TS D0 Dp : R)
    (seed : rate * F0 + 96 * D0 ≤ Q + 96 * (W10 * T1 + WS0 * TS))
    (drift : 96 * ((W10 - W1p) * T1 + (WS0 - WSp) * TS + (Dp - D0))
      ≤ rate * (F0 - Fp)) :
    rate * Fp ≤ Q + 96 * (W1p * T1 + WSp * TS - Dp) := by
  grind

end RankSeven

#print axioms RankSeven.sqrtThreeLowerBound
#print axioms RankSeven.mixedCutExteriorDebit
#print axioms RankSeven.mixedCutRate
#print axioms RankSeven.mixedCutRateWithRadical
#print axioms RankSeven.mixedCutSeedConclusion
