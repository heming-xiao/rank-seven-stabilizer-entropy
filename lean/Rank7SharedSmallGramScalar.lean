import Rank7SharedCharacterHeadPrice

namespace RankSeven.SharedSmallGramScalar

open Lean.Grind Pauli ComplexScalar
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The two independent Fourier regions force the 1/7 localization
threshold for the sum of weighted head and middle errors. -/
theorem smallError (kappa d e f : R) (small : 24*kappa≤1) (control : d≤5*kappa)
    (e0 : 0≤e) (f0 : 0≤f) (rough : e≤2*d) (coarse : 5*(e+2*f)<3)
    (regions : 2*e*(1-e)*(1-2*f)^2+4*(1-e)^2*f*(1-f)≤d) :
    7*(e+2*f)<1 := by
  have dcap : 24*d≤5 := by grind only
  have ecol : 12*e≤5 := by grind only
  have one : 0≤1-e := by grind only
  have fHalf : 2*f≤1 := by grind only
  have ff := OrderedRing.mul_nonneg f0 (show 0≤1-f by grind only)
  have squareF := squareNonnegative (1-2*f)
  have regroup :
      2*e*(1-e)*(1-2*f)^2+4*(1-e)^2*f*(1-f)=
        2*e*(1-e)+4*(1-e)*(1-3*e)*f*(1-f) := by grind only
  rw [regroup] at regions
  have eThird : 3*e<1 := by
    apply Classical.byContradiction
    intro conflict
    have term := OrderedRing.mul_nonneg
      (OrderedRing.mul_nonneg one (show 0≤3*e-1 by grind only)) squareF
    have cut : (1-e)^2≤d := by grind only
    have squareE := OrderedRing.mul_nonneg
      (show 0≤12*(1-e)-7 by grind only) (show 0≤12*(1-e)+7 by grind only)
    grind only
  have eEighth : 8*e<1 := by
    have g := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg one (show 0≤1-3*e by grind only)) ff
    have low : 2*e*(1-e)≤d := by grind only
    apply Classical.byContradiction
    intro conflict
    have term := OrderedRing.mul_nonneg (show 0≤8*e-1 by grind only) (show 0≤7-8*e by grind only)
    grind only
  have fTwelfth : 12*f<1 := by
    apply Classical.byContradiction
    intro conflict
    have fterm := OrderedRing.mul_nonneg
      (show 0≤12*f-1 by grind only) (show 0≤11-12*f by grind only)
    have eterm := OrderedRing.mul_nonneg
      (show 0≤8*(1-e)-7 by grind only) (show 0≤8*(1-e)+7 by grind only)
    have scale := OrderedRing.mul_nonneg ff (show 0≤64*(1-e)^2-49 by grind only)
    have tail := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg e0 one) squareF
    rw [←regroup] at regions
    grind only
  let E := e+2*f
  have E0 : 0≤E := by unfold E; grind only
  have upper : 24*E<7 := by unfold E; grind only
  have sumNonnegative : 0≤1-E := by grind only
  have product e' (lo : 1-E≤e') : (1-E)^2≤(e')^2 := by
    have q := OrderedRing.mul_nonneg (show 0≤e'-(1-E) by grind only)
      (show 0≤e'+(1-E) by grind only)
    grind only
  have ef := OrderedRing.mul_nonneg e0 f0
  have pm := product ((1-e)*(1-2*f)) (by unfold E; grind only)
  have pf := product ((1-e)*(1-f)) (by unfold E; grind only)
  have extraM := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg e0 one) squareF
  have extraF := OrderedRing.mul_nonneg ff (squareNonnegative (1-e))
  have paidM := OrderedRing.mul_nonneg e0
    (show 0≤(1-e)*(1-2*f)^2-(1-E)^2 by grind only)
  have paidF := OrderedRing.mul_nonneg f0
    (show 0≤(1-e)^2*(1-f)-(1-E)^2 by grind only)
  have cubic : 2*E*(1-E)^2≤d := by
    rw [←regroup] at regions
    dsimp only [E] at paidM paidF ⊢
    grind only
  change 7*E<1
  apply Classical.byContradiction
  intro conflict
  have p := OrderedRing.mul_nonneg (show 0≤7*E-1 by grind only)
    (show 0≤49*E^2-91*E+36 by have := squareNonnegative E; grind only)
  grind only

/-- From the exact cut leakage lower bound and rounded head error, the
physical Gram pays at least 297/196 times the weighted exterior leakage. -/
theorem leakagePrice (kappa e f outsideE outsideF delta leak : R)
    (small : 7*(e+2*f)≤1)
    (e0 : 0≤outsideE) (f0 : 0≤outsideF)
    (eCap : outsideE≤e) (fCap : outsideF≤f)
    (angle : 2*delta≤3*(e+2*f)) (leak0 : 0≤leak)
    (crossed : outsideE+2*outsideF-2*outsideF*outsideE≤leak)
    (gram : 2*(1-delta)*leak≤kappa) :
    297*(outsideE+2*outsideF)≤196*kappa := by
  let E := outsideE+2*outsideF
  have E0 : 0≤E := by unfold E; grind only
  have cap : 7*E≤1 := by unfold E; grind only
  have square := squareNonnegative (outsideE-2*outsideF)
  have r := OrderedRing.mul_nonneg E0 (show 0≤1-7*E by grind only)
  have leakBound : 27*E≤28*leak := by unfold E at r ⊢; grind only
  have paid := OrderedRing.mul_nonneg leak0 (show 0≤14*(1-delta)-11 by grind only)
  change 297*E≤196*kappa
  grind only

theorem exteriorPrice (kappa E excess : R) (k0 : 0≤kappa)
    (leakage : 297*E≤196*kappa) (stability : excess≤18*E) : excess≤12*kappa := by
  grind only

end RankSeven.SharedSmallGramScalar

#print axioms RankSeven.SharedSmallGramScalar.smallError
#print axioms RankSeven.SharedSmallGramScalar.leakagePrice
#print axioms RankSeven.SharedSmallGramScalar.exteriorPrice

