import Rank7RealLowerPhysicalComparison
namespace RankSeven.RealLowerWeighted
open Pauli ExteriorCuts PackingDual PackingInterpolation UpperPhysicalInterior UpperFrameGain LowerCorner LowerPhysicalGainScale
open UpperFrameTrace (sharedExcess highExcess)
open RealLowerPauliPrice (antiPrice)
noncomputable section
attribute [local irreducible] gain amplitude sharedExcess highExcess corrected rawProbe

theorem exteriorDebit (a : Wedge7→ℝ) (an : ∀i,0≤a i) (rows : RowsHold a) (hn : 0≤sharedExcess a) (hv : 0≤highExcess a)
    (z y x b c w : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (w0 : 0≤w) (wc : 707*w≤1225) (H : z*(x-1)-3*x-5/2≤0) :
    let D:=y*(z+y+x)
    let s:=rawSpectrum z y x b c
    168*gain a (amplitude s)-24*(b^2*w*D)*rawProbe s a 1≤
      b^2*((168-24*w)*D-168*y)*highExcess a := by
  let D:=y*(z+y+x); let m:=w*D/7
  let cross:=LowerSignedPrices.cross z x; let v:=highExcess a; let n:=sharedExcess a
  let r:=trueRay n v 0 0; let s:=rawSpectrum z y x b c
  let F:=corrected (spectrum z y x) a 0 m cross (c/b) (1/b)
  have xp : 0≤x := by linarith only [xh]
  have bp : 0<b := by linarith only [cb.1,cb.2]
  have D0 : 0≤D := by dsimp only [D]; positivity
  have m0 : 0≤m := by dsimp only [m]; positivity
  have cap : 707*m≤175*D := by dsimp only [m]; nlinarith only [mul_le_mul_of_nonneg_right wc D0]
  have ac : 707*cross=200*((1+x)*z) := by norm_num [cross,LowerSignedPrices.cross,UpperEndpointPrices.invRate]; ring
  have sig:=(LowerNormalizedSigned.normalizedBounds z y x 0 m cross a (c/b) (1/b) hz hy xh (LowerExteriorScale.orderedRatios b c cb)
    an rows hn hv ⟨le_rfl,by simp only [mul_zero]; positivity⟩ ⟨m0,cap⟩ ac).1
  change F≤LowerNormalizedSigned.splitPrice z y x (c/b) (1/b) 0 m r at sig
  have bnd:=mul_le_mul_of_nonneg_left sig (mul_self_nonneg b)
  rw [(LowerExteriorScale.rescaleBounds z y x b c 0 m r bp).1] at bnd
  change b*b*F≤c*(z*(x-1)-3*x-5/2-0)*n+(D-m)*(v-(b-1)*(c-1)*r.tail)-c*y*v at bnd
  have rn : 0≤r.tail := by
    change 0≤UpperWeighted.larger v (n/2)
    unfold UpperWeighted.larger; split <;> linarith only [hv,hn]
  have cp : 0≤c := by linarith only [cb.1]
  have head:=mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos cp H) hn
  have md : 0≤D-m := by linarith only [cap,D0]
  have pre:=mul_nonneg md (mul_nonneg (mul_nonneg (by linarith only [cb.1,cb.2] : 0≤b-1)
    (sub_nonneg.mpr cb.1)) rn)
  have tail:=mul_nonneg (mul_nonneg (sub_nonneg.mpr cb.1) hy) hv
  have raw : b*b*F≤((D-m)-y)*v := by
    change 0≤(D-m)*((b-1)*(c-1)*r.tail) at pre
    change 0≤(c-1)*y*v at tail
    change c*(z*(x-1)-3*x-5/2)*n≤0 at head
    linarith only [bnd,head,pre,tail]
  let w':=(707/700:ℝ)*w; let p:Prices ℝ:={realPrices z y x b 0 1 w 0 0 with lambda:=0}
  have mm : LowerSignedPrices.mu z y x w'=m := by
    norm_num [LowerSignedPrices.mu,UpperEndpointPrices.invRate,w',D,m]; ring
  have num:=physicalNumerator z y x b c w' p a bp
  change b*b*(b*b*corrected (spectrum z y x) a 0 (LowerSignedPrices.mu z y x w') cross (c/b) (1/b))=
    gain a (amplitude s)-(b*b*0)*(rawProbe s a 1+rawProbe s a 2)-(b*b*LowerSignedPrices.mu z y x w')*rawProbe s a 1+
    cross*(b*b)*(b-c)*a entering at num
  rw [mm] at num
  change b*b*(b*b*F)=_ at num
  have applied:=mul_le_mul_of_nonneg_left raw (mul_self_nonneg b)
  have cross0 : 0≤cross := by linarith only [ac,mul_nonneg (by linarith only [xp] : 0≤1+x) hz]
  have fee:=mul_nonneg (mul_nonneg (mul_nonneg cross0 (mul_self_nonneg b)) (sub_nonneg.mpr cb.2)) (an entering)
  change 168*gain a (amplitude s)-24*(b^2*w*D)*rawProbe s a 1≤b^2*((168-24*w)*D-168*y)*v
  dsimp only [m] at num applied
  linarith only [num,applied,fee]

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.exteriorDebit