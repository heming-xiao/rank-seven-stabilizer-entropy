import Rank7RealLowerPauliPrice
import Rank7EndpointLargeGrams
namespace RankSeven.RealLowerPhysicalPrice
open Pauli ExteriorCuts PhysicalCompressionEffect LowerCorner LowerSignedPrices LowerAffinePayment LowerPhysicalGainScale
open RealLowerPauliPrice PhysicalDefectAssembly PhysicalTailBlend JointProbeGram
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (sharedExcess highExcess sharedFraction)
open UpperEndpointPrices (invRate invGeom)
noncomputable section

private theorem subProbe (head : Fin 7→ℝ) (c d : ℝ) (diag : Wedge7→ℝ) (i : Fin 7) (hi : i=1∨i=2) :
    rawProbe (UpperFrameGain.tail head c d) diag i=UpperFrameGain.weightedProbe head diag i c d := by
  have sites : UpperFrameGain.pairSpectrum (UpperFrameGain.tail head c d) i=
      UpperFrameGain.tail (UpperFrameGain.pairSpectrum head i) c d := by
    funext j
    rcases hi with rfl|rfl <;> fin_cases j <;> rfl
  unfold rawProbe UpperFrameGain.weightedProbe; rw [sites]

private theorem coefficientNonneg (z y x b c f u w wa wb : ℝ) (cb : 1≤c ∧ c≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4)
    (sp : 0≤shift z x b f u) :
    let p := realPrices z y x b f u w wa wb
    0≤p.shared+bonusSlope z x b f u*(b-c) ∧ 0≤p.high := by
  have u0 : 0≤u ∧ u≤2 := by rcases us with e|e|e|e <;> rw [e] <;> norm_num
  have w0 : 0≤w ∧ w≤2 := by rcases ws with e|e|e|e <;> rw [e] <;> norm_num
  have f1 : f≤1 := by rcases fs with e|e|e <;> rw [e] <;> norm_num
  have tax0 : 0≤tax f := by dsimp [tax]; positivity [sub_nonneg.mpr f1]
  have b0 : 0≤b := by linarith only [cb.1,cb.2]
  have N : 0≤headNorm z x := by dsimp [headNorm]; nlinarith only [sq_nonneg z,sq_nonneg x]
  have inv0 : 0≤ inversePenalty z x f := by
    unfold inversePenalty
    apply div_nonneg N
    nlinarith only [N,sq_nonneg f]
  have j0 : (0:ℝ)≤ invRate := by norm_num [invRate]
  have l0 : (0:ℝ)≤ invGeom := by norm_num [invGeom]
  have ua : 0≤u*(2-u) := mul_nonneg u0.1 (by linarith only [u0.2])
  have wA : 0≤w*(2-w) := mul_nonneg w0.1 (by linarith only [w0.2])
  have pre : 0≤b-c := sub_nonneg.mpr cb.2
  let g:=z*x; let d:=y*(z+y+x); let G:=clipped z x b f; let i:=inversePenalty z x f
  change 0≤(g*g/12+u*(2-u)*(G*G*i))*(b*b)*invRate+2*shift z x b f u*tax f*b*invRate*(b-c) ∧
    0≤b*b*(12*w*(2-w)*(d*d)+y*y*(y*y+(z*z+x*x)/2))*invGeom*invRate
  constructor
  · have g0 := mul_self_nonneg g; have gg := mul_self_nonneg G
    have ig := mul_nonneg ua (mul_nonneg gg inv0)
    positivity
  · have d0 := mul_self_nonneg d
    have num : 0≤12*w*(2-w)*(d*d) := by nlinarith only [mul_nonneg wA d0]
    have ys := mul_self_nonneg y; have zs := mul_self_nonneg z; have xs := mul_self_nonneg x
    positivity

/-- The part of the real checker payment supplied by the actual Pauli defects.
Both Gram-to-excess conversions are stated on the very same physical frame. -/
theorem physicalPrice (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c f u w wa wb : ℝ) (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (chart : (fun i => (mu i)^2)=rawSpectrum z y x b c)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4)
    (shared : let diag := physicalWeights half h2 k A
      (realRay (sharedExcess diag) (highExcess diag) 0).peak≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne) :
    let diag := physicalWeights half h2 k A
    let n := sharedExcess diag; let v := highExcess diag; let peak := (realRay n v 0).peak
    let p := realPrices z y x b f u w wa wb
    let U := rawProbe (rawSpectrum z y x b c) diag
    b^2*((p.shared+bonusSlope z x b f u*(b-c))*peak+p.high*v)+
      b^2*p.lambda*(U 1+U 2)+b^2*LowerSignedPrices.mu z y x w*U 1≤
      invRate*(frameDefects half inv24 k A mu-unshiftedDefects half inv24 k A mu) := by
  let r := fun i => (mu i)^2
  let M := WeightedProbeShift.physicalPayment half h2 k A mu
  let diag := physicalWeights half h2 k A
  let G := z*x; let D := y*(z+y+x)
  let s := b^2*shift z x b f u; let t := b^2*highestShift z y x w
  let U := rawProbe (rawSpectrum z y x b c) diag
  let Q := 1+12*f^2*b^2/rawPsi z x b c
  let S := (b*z)^2*(b*x)^2+12*s*(2*(b^2*G-tax f*(b*(c-1)))-Q*s)
  let H := 12*t*(2*(b^2*D)-t)+b^4*antiPrice z y x
  let p := realPrices z y x b f u w wa wb
  let sp := p.shared+bonusSlope z x b f u*(b-c)
  let v := highExcess diag
  let peak := (realRay (sharedExcess diag) v 0).peak
  let all := frameDefects half inv24 k A mu; let base := unshiftedDefects half inv24 k A mu
  have parts := chartParts z y x b c half third h2 h3
  change r=rawSpectrum z y x b c at chart
  rw [←chart] at parts
  obtain ⟨gg,dd,tt,four,g0,g2,psi,lead⟩ := parts
  obtain ⟨f0,f1,s0,sc,t0,tc⟩ := shiftRanges z y x b f u w z0 y0 xh (le_trans cb.1 cb.2) fs us ws
  have boundS := mul_le_mul_of_nonneg_left sc (sq_nonneg b)
  have boundT := mul_le_mul_of_nonneg_left tc (sq_nonneg b)
  have x0 : 0≤x := by linarith only [xh]
  have ord : PauliMatchingPrices.SortedSpectrum r := chart ▸ ordered z y x b c z0 y0 x0 cb
  have hp : 0<spectralPsi half third r := by
    rw [psi]; unfold rawPsi; nlinarith only [sq_nonneg (c-1),sq_nonneg (b*z),sq_nonneg (b*x),sq_nonneg (b-c)]
  have raw := LowerPhysicalPauliSlots.fullLeading half inv24 third h2 h24 h3 k A mu orth ord s t f
    (mul_nonneg (sq_nonneg b) s0) (mul_nonneg (sq_nonneg b) t0) f0 f1
    (by rw [gg]; dsimp only [s]; linarith only [boundS])
    (by rw [dd]; dsimp only [t]; linarith only [boundT]) hp
  let W j := ProjectedProbeOverlap.weightedFourWedge 0 j r diag
  let head := fun i => b*UpperPhysicalInterior.spectrum z y x i
  have probes := PhysicalEndpointPrice.weightedChartProbes head diag c 1
  change UpperFrameGain.weightedProbe head diag 1 c 1=ProjectedProbeOverlap.weightedFourWedge 0 1 (rawSpectrum z y x b c) diag-
    referencePair (rawSpectrum z y x b c) ∧ UpperFrameGain.weightedProbe head diag 1 c 1+UpperFrameGain.weightedProbe head diag 2 c 1=
    ProjectedProbeOverlap.weightedFourWedge 0 1 (rawSpectrum z y x b c) diag+ProjectedProbeOverlap.weightedFourWedge 0 2 (rawSpectrum z y x b c) diag-referenceShared (rawSpectrum z y x b c) at probes
  rw [←subProbe head c 1 diag 1 (Or.inl rfl),←subProbe head c 1 diag 2 (Or.inr rfl)] at probes
  change U 1=_ ∧ U 1+U 2=_ at probes
  rw [←chart] at probes
  change U 1=W 1-referencePair r ∧ U 1+U 2=W 1+W 2-referenceShared r at probes
  have qeq : quadraticPenalty half third r f=Q := by unfold quadraticPenalty; rw [four,psi]
  change base+24*s*(W 1+W 2-referenceShared r)+24*t*(W 1-referencePair r)+
    ((PauliReserveSlots.gap r 0)^2*(PauliReserveSlots.gap r 2)^2+12*s*(2*(sharedGap r-(1-f)*(200/11)*tailGap r)-quadraticPenalty half third r f*s))*M.kappa+
    (12*t*(2*leadingGap r-t)+leadingCoefficient half third r)*M.kappaOne≤all at raw
  rw [←probes.1,←probes.2,gg,dd,tt,g0,g2,qeq,lead] at raw
  change base+24*s*(U 1+U 2)+24*t*U 1+S*M.kappa+H*M.kappaOne≤all at raw
  have jr : (0:ℝ)≤ invRate := by norm_num [invRate]
  have weighted := mul_le_mul_of_nonneg_left raw jr
  have scalar := sharedScaled z y x b c f u w wa wb xh cb
  change 12*b^2*sp≤ invRate*S at scalar
  have kg := WeightedProbeShift.physicalMomentOrder half h2 k A mu orth
  change 0≤M.cross ∧ M.cross≤M.kappa ∧ M.cross≤M.kappaOne ∧ _ at kg
  have combined := mul_le_mul_of_nonneg_right scalar (le_trans kg.1 kg.2.1)
  obtain ⟨sp0,high0⟩ := coefficientNonneg z y x b c f u w wa wb cb fs us ws s0
  change peak≤12*M.kappa at shared
  change 2*v≤5*M.kappaOne at highest
  have b1 := mul_le_mul_of_nonneg_left shared (mul_nonneg (sq_nonneg b) sp0)
  have b2 := mul_le_mul_of_nonneg_left highest (mul_nonneg (sq_nonneg b) high0)
  have highEq : 5*b^2*p.high=2*invRate*H := by
    change 5*b^2*((b*b)*(12*w*(2-w)*(D*D)+antiPrice z y x)*invGeom*invRate)=_
    dsimp only [H,t,highestShift,D]; norm_num [invGeom,invRate]; ring
  have highPay := congrArg (fun s : ℝ => s*M.kappaOne) highEq
  have lm : b^2*p.lambda=24*invRate*s := by change b^2*(24*invRate*shift z x b f u)=_; dsimp only [s]; ring
  have ym : b^2*LowerSignedPrices.mu z y x w=24*invRate*t := by dsimp only [LowerSignedPrices.mu,t,highestShift]; ring
  change b^2*(sp*peak+p.high*v)+b^2*p.lambda*(U 1+U 2)+b^2*LowerSignedPrices.mu z y x w*U 1≤ invRate*(all-base)
  rw [lm,ym]; linarith only [weighted,combined,b1,b2,highPay]

end
end RankSeven.RealLowerPhysicalPrice
#print axioms RankSeven.RealLowerPhysicalPrice.physicalPrice