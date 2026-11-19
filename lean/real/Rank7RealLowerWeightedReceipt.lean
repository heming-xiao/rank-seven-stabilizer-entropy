import Rank7RealLowerPhysicalComparison
namespace RankSeven.RealLowerWeighted
open Pauli ExteriorCuts PackingDual PackingInterpolation UpperFrameGain LowerPhysicalGainScale
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalDefectAssembly (frameDefects)
open PhysicalTailBlend (unshiftedDefects spectralPsi leadingCoefficient)
open JointProbeGram WeightedProbeShift RealLowerPauliPrice
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (highExcess)
noncomputable section
attribute [local irreducible] physicalWeights frameDefects unshiftedDefects highExcess rawProbe

private theorem rawOne (z y x b c : ℝ) (a : Wedge7→ℝ) :
    let s:=rawSpectrum z y x b c
    rawProbe s a 1=ProjectedProbeOverlap.weightedFourWedge 0 1 s a-referencePair s := by
  let h:=fun i=>b*UpperPhysicalInterior.spectrum z y x i
  have parts:=(PhysicalEndpointPrice.weightedChartProbes h a c 1).1
  unfold rawProbe
  have equal : pairSpectrum (tail h c 1) 1=tail (pairSpectrum h 1) c 1 := by
    funext i; fin_cases i <;> rfl
  change gain a (fun j=>if occupied j 0 && occupied j 1 then amplitude (pairSpectrum (tail h c 1) 1) j else 0)=_
  rw [equal]; exact parts

/-- A zero shared shift keeps all the shared anticommuting reserve for the
weighted highest excess. Both Gram comparisons concern the actual Pauli frame. -/
theorem pauliReceipt (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c w : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b) (w0 : 0≤w) (wc : 4*w≤7)
    (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (shared : highExcess (physicalWeights half h2 k A)≤12*(physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(physicalPayment half h2 k A mu).kappaOne) :
    let a:=physicalWeights half h2 k A; let v:=highExcess a; let s:=rawSpectrum z y x b c
    let D:=y*(z+y+x); let G:=z*x
    24*(b^2*w*D)*rawProbe s a 1+b^4*(G^2/12+(12*w*(2-w)*D^2+antiPrice z y x)/(5/2))*v≤
      frameDefects half inv24 k A mu := by
  let a:=physicalWeights half h2 k A; let v:=highExcess a; let s:=rawSpectrum z y x b c
  let D:=y*(z+y+x); let G:=z*x; let t:=b^2*w*D
  let P:=physicalPayment half h2 k A mu
  let hi:=12*w*(2-w)*D^2+antiPrice z y x
  let r:=fun i=>(mu i)^2
  let base:=unshiftedDefects half inv24 k A mu; let all:=frameDefects half inv24 k A mu
  have xp : 0≤x := by linarith only [xh]
  have d0 : 0≤D := by dsimp only [D]; positivity
  have g0 : 0≤G:=mul_nonneg hz xp
  have t0 : 0≤t := by dsimp only [t]; positivity
  have parts:=chartParts z y x b c half third h2 h3
  change r=rawSpectrum z y x b c at chart
  rw [←chart] at parts
  change r=s at chart
  obtain ⟨gg,dd,_tt,_four,g0x,g2x,psi,lead⟩:=parts
  have sorted : PauliMatchingPrices.SortedSpectrum r:=chart ▸ ordered z y x b c hz hy xp cb
  have pos : 0<spectralPsi half third r:=by
    rw [psi]; unfold rawPsi; nlinarith only [sq_nonneg (c-1),sq_nonneg (b*z),sq_nonneg (b*x),sq_nonneg (b-c)]
  have raw:=LowerPhysicalPauliSlots.fullLeading half inv24 third h2 h24 h3 k A mu orth sorted 0 t 0
    (le_refl _) t0 (le_refl _) (by norm_num) (by rw [gg]; nlinarith only [mul_nonneg (sq_nonneg b) g0])
    (by rw [dd]; dsimp only [t]; nlinarith only [mul_le_mul_of_nonneg_right wc (mul_nonneg (sq_nonneg b) d0)]) pos
  change base+24*0*(_)+24*t*(ProjectedProbeOverlap.weightedFourWedge 0 1 r a-referencePair r)+
    ((PauliReserveSlots.gap r 0)^2*(PauliReserveSlots.gap r 2)^2+12*0*_)*P.kappa+
    (12*t*(2*leadingGap r-t)+leadingCoefficient half third r)*P.kappaOne≤all at raw
  rw [g0x,g2x,dd,lead] at raw
  have probe:=rawOne z y x b c a
  change rawProbe s a 1=ProjectedProbeOverlap.weightedFourWedge 0 1 s a-referencePair s at probe
  rw [←chart] at probe
  rw [←probe,chart] at raw
  have pre : 0≤hi := by
    dsimp only [hi,antiPrice]
    have wz : 0≤2-w:=by linarith only [wc]
    positivity
  have base0 : 0≤base:=UnshiftedDefects.nonnegative half inv24 h2 h24 k A mu orth
  have low:=mul_le_mul_of_nonneg_left shared (show 0≤b^4*G^2 by positivity)
  have top:=mul_le_mul_of_nonneg_left highest (show 0≤b^4*hi from mul_nonneg (by positivity) pre)
  change b^4*G^2*v≤b^4*G^2*(12*P.kappa) at low
  change b^4*hi*(2*v)≤b^4*hi*(5*P.kappaOne) at top
  change 24*t*rawProbe s a 1+b^4*(G^2/12+hi/(5/2))*v≤all
  dsimp only [t,G,hi] at *
  linarith only [raw,base0,low,top]

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.pauliReceipt