import Rank7LowerPhysicalRay

namespace RankSeven.LowerAffinePayment
open Lean.Grind Interval UpperEndpoint UpperEndpointPrices LowerCorner LowerSignedExterior UpperPhysicalInterior UpperFrameGain
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def bonusSlope (z x b f u : R) : R :=
  let tax := (1-f)*(200/11)
  let norm := z*z+x*x
  let G := UpperPrices.positivePart (z*x-tax*(1-1/b))
  let s := u*(G*(norm/(norm+72*(f*f))))
  2*s*tax*b*invRate

def physicalPayment (b c slope : R) (p : Prices R) (r : RealRay R) : R :=
  (p.shared+slope*(b-c))*r.peak+p.high*r.v+c*p.cut*r.traceShared

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem endpoints (z y x b f u w wa wb : R) (r : RealRay R) (right : Bool) :
    let p := realPrices z y x b f u w wa wb
    physicalPayment b (endpoint b right) (bonusSlope z x b f u) p r=payment b p right r := by
  let p := realPrices z y x b f u w wa wb
  have slope : p.leftBonus=bonusSlope z x b f u*(b-1) := by
    change 2*_ * _ * b * (b-1)*invRate=(2*_ * _ * b*invRate)*(b-1)
    grind only
  change physicalPayment b (endpoint b right) _ p r=payment b p right r
  cases right <;> dsimp only [physicalPayment,payment,endpoint,Bool.false_eq_true,↓reduceIte] <;> grind only

private theorem insidePositive (b c left right middle : R) (cb : 1≤c ∧ c≤b) (bl : b≠1)
    (eq : (b-1)*middle=(b-c)*left+(c-1)*right) (positive : 0<left ∧ 0<right) : 0<middle := by
  have bp : 0<b-1 := by grind only
  by_cases yes : 0<middle
  · exact yes
  · have bad := OrderedRing.mul_le_mul_of_nonneg_left (show middle≤0 by grind only) (Std.le_of_lt bp)
    by_cases lt : c<b
    · have g := OrderedRing.mul_pos (show 0<b-c by grind only) positive.1
      have h := OrderedRing.mul_nonneg (show 0≤c-1 by grind only) (Std.le_of_lt positive.2)
      grind only
    · have g := OrderedRing.mul_nonneg (show 0≤b-c by grind only) (Std.le_of_lt positive.1)
      have h := OrderedRing.mul_pos (show 0<c-1 by grind only) positive.2
      grind only

/-- The same f,u,w and physical frame are held fixed between the two endpoints. -/
theorem interpolate (z y x b c f u w wa wb : R) (weights : ExteriorCuts.Wedge7→R) (r : RealRay R)
    (cb : 1≤c ∧ c≤b)
    (positive : ∀ right : Bool,let p := realPrices z y x b f u w wa wb
      gainAt z y x b (endpoint b right) w p weights<payment b p right r) :
    let p := realPrices z y x b f u w wa wb
    gainAt z y x b c w p weights<physicalPayment b c (bonusSlope z x b f u) p r := by
  let p := realPrices z y x b f u w wa wb
  let slope := bonusSlope z x b f u
  let F := correctedPoly (spectrum z y x) weights p.lambda (LowerSignedPrices.mu z y x w) (LowerSignedPrices.cross z x)
  let margin := fun h : R => physicalPayment b h slope p r-gainAt z y x b h w p weights
  have corners (right : Bool) : 0<margin (endpoint b right) := by
    have actual := positive right
    change gainAt z y x b _ w p weights<payment b p right r at actual
    change 0<physicalPayment b _ slope p r-gainAt z y x b _ w p weights
    rw [endpoints z y x b f u w wa wb r right]; grind only
  have cs : 0<margin 1 ∧ 0<margin b := ⟨corners false,corners true⟩
  have result : 0<margin c := by
    by_cases bz : b=1
    · have c1 : c=1 := by grind only
      rw [c1]; exact cs.1
    · apply insidePositive b c (margin 1) (margin b) _ cb bz _ cs
      have atVal (h : R) : gainAt z y x b h w p weights=(b*b)*F.eval (h/b) (1/b) := by
        unfold gainAt; rw [correctedPolyEval]
      dsimp only [margin,physicalPayment]; rw [atVal,atVal,atVal]
      unfold Bilinear.eval
      simp only [Field.div_eq_mul_inv]; grind only
  change gainAt z y x b c w p weights<physicalPayment b c slope p r
  change 0<physicalPayment b c slope p r-gainAt z y x b c w p weights at result
  grind only

theorem actualCutNonnegative (z y x b f u w : R) (roots : Roots z y x b)
    (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) :
    0≤(realPrices z y x b f u w ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)).cut := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have nn (a b : R) : 0≤gap a b := by
    have sq := squareNonnegative (UpperPrices.positivePart (a-b)); unfold gap; grind only
  have a := OrderedRing.mul_nonneg (show 0≤1+(z+y+x) by grind only) (nn roots.gamma roots.fifth)
  have g := OrderedRing.mul_nonneg (show 0≤1+x by grind only) (nn roots.alpha roots.betaFifth)
  have rt := UpperContractor.quotientEq (4242:R) (show (0:R)<25 by grind only)
  have den : (0:R)<4242/25 := by grind only
  have nonnegative : 0≤(invRate (R:=R)) := by
    apply UpperContractor.cancelLe den
    change (4242/25:R)*0≤(4242/25)*(1/(4242/25:R))
    rw [Semiring.mul_zero,UpperContractor.quotientEq _ den]; grind only
  change 0≤(96*invRate)*UpperEndpoint.smaller ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)
  apply OrderedRing.mul_nonneg (show 0≤96*(invRate (R:=R)) by grind only)
  unfold UpperEndpoint.smaller; split <;> assumption

end RankSeven.LowerAffinePayment
#print axioms RankSeven.LowerAffinePayment.interpolate
#print axioms RankSeven.LowerAffinePayment.actualCutNonnegative