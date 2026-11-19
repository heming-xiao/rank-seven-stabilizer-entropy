import Rank7RealLowerWeightedFourth
namespace RankSeven.RealLowerWeighted
open LowerLeaves RealLowerPauliPrice
noncomputable section

def fullMargin (z y x b w : ℝ) : ℝ :=
  let D:=y*(z+y+x); let G:=z*x
  b^2*(G^2/12+(12*w*(2-w)*D^2+antiPrice z y x)/(5/2))+168*y-(168-24*w)*D

private theorem headFloor (z y x : ℝ) (hy : 0≤y) (xh : 1≤2*x) (head : z+2*y+3*x≤5*z*x) :
    22≤15*(z+y+x) := by
  by_contra! bad
  have prod:=mul_neg_of_pos_of_neg (show 0<5*x-1 by linarith only [xh])
    (show 15*(z+x)-22<0 by linarith only [hy,bad])
  nlinarith only [prod,head,hy,sq_nonneg (15*x-8)]

theorem fourthFullMargin (z y x b : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x)
    (head : z+2*y+3*x≤5*z*x) (reserve : x^2≤5*z^2) (accepted : 0<weightedMargin z y x b (7/4)) :
    0<fullMargin z y x b (1225/707) := by
  let D:=y*(z+y+x); let G:=z*x; let A:=antiPrice z y x
  let maxR:=UpperWeighted.larger (G*G/24) ((x*x)*(x*x)/72)
  let w:=(1225/707:ℝ)
  have xp : 0≤x:=by linarith only [xh]
  have d0 : 0≤D:=by dsimp only [D]; positivity
  have scale : 6*maxR≤5*(G^2/12) := by
    dsimp only [maxR,UpperWeighted.larger]; split
    · nlinarith only [sq_nonneg G]
    · dsimp only [G]; nlinarith only [mul_le_mul_of_nonneg_left reserve (sq_nonneg x)]
  have full : maxR≤G^2/12 := by nlinarith only [scale,sq_nonneg G]
  by_cases big : 14140≤4193*b^2*D
  · have raw:=accepted.trans_le (fourthWitnessMargin z y x b d0 big)
    change 0<b*b*((12*w*(2-w)*(D*D)+A)*(1/(5/2))+maxR)+168*y-(168-24*w)*D at raw
    change 0<b^2*(G^2/12+(12*w*(2-w)*D^2+A)/(5/2))+168*y-(168-24*w)*D
    linarith only [raw,mul_le_mul_of_nonneg_left full (sq_nonneg b)]
  have ycap:=mul_le_mul_of_nonneg_right (headFloor z y x hy xh head) hy
  have lowD : b^2*D≤7/2 := by linarith only [not_le.mp big]
  have bA : A≤D^2 := by
    have step : y^2+(z^2+x^2)/2≤(z+y+x)^2 := by
      nlinarith only [mul_nonneg hz hy,mul_nonneg hz xp,mul_nonneg hy xp,sq_nonneg z,sq_nonneg x]
    dsimp only [A,D,antiPrice]
    nlinarith only [mul_le_mul_of_nonneg_left step (sq_nonneg y)]
  have dlow:=mul_le_mul_of_nonneg_right lowD d0
  have ap:=mul_le_mul_of_nonneg_left bA (sq_nonneg b)
  change 0<b*b*((12*(7/4)*(2-7/4)*(D*D)+A)*(1/(5/2))+maxR)+168*y-(168-24*(7/4))*D at accepted
  have ysmall : 22*y≤15*D := by dsimp only [D]; linarith only [ycap]
  have has : (5/2)*D<b^2*maxR := by linarith only [accepted,dlow,ap,ysmall,d0]
  have surplus : D/2<b^2*(G^2/12-maxR) := by
    linarith only [has,mul_le_mul_of_nonneg_left scale (sq_nonneg b)]
  have strength : (7/4:ℝ)*(2-7/4)≤w*(2-w) := by norm_num [w]
  have prices:=mul_le_mul_of_nonneg_right strength (show 0≤b^2*D^2 by positivity)
  have cutoff : 24*((7/4:ℝ)-w)≤1/2 := by norm_num [w]
  have diff:=mul_le_mul_of_nonneg_right cutoff d0
  change 0<b^2*(G^2/12+(12*w*(2-w)*D^2+A)/(5/2))+168*y-(168-24*w)*D
  linarith only [accepted,surplus,prices,diff]

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.fourthFullMargin