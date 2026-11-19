import Rank7RealLowerWeighted
namespace RankSeven.RealLowerWeighted
open LowerLeaves Pauli ExteriorCuts UpperFrameTrace LowerPhysicalGainScale
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalDefectAssembly (PairedDefectBound)
open PackingPolynomial (physicalWeights)
noncomputable section

/-- The price is quadratic in the shift. At a fourth-witness leaf above this
threshold, the available continuous exterior certificate pays a larger margin. -/
theorem fourthWitnessMargin (z y x b : ℝ) (dn : 0≤y*(z+y+x))
    (threshold : 14140≤4193*b^2*(y*(z+y+x))) :
    weightedMargin z y x b (7/4)≤weightedMargin z y x b (1225/707) := by
  let D:=y*(z+y+x)
  have xn : 0≤D:=dn
  have q : 0≤D*(4193*b^2*D-14140):=mul_nonneg xn (sub_nonneg.mpr threshold)
  have formula : weightedMargin z y x b (1225/707)-weightedMargin z y x b (7/4)=
      (3/102010)*D*(4193*b^2*D-14140) := by
    unfold weightedMargin; dsimp only [D]; ring
  linarith only [formula,q]

theorem weightedFourth (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (threshold : 14140≤4193*b^2*(y*(z+y+x))) (H : z*(x-1)-3*x-5/2≤0) (reserve : x^2≤6*z^2)
    (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (hn : 0≤sharedExcess (physicalWeights half h2 k A)) (hv : 0≤highExcess (physicalWeights half h2 k A))
    (shared : highExcess (physicalWeights half h2 k A)≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (accepted : 0<weightedMargin z y x b (7/4)) : PairedDefectBound half inv24 h2 k A mu := by
  have xp : 0≤x:=by linarith only [xh]
  apply weightedPhysical half inv24 third h2 h24 h3 k A mu orth z y x b c (1225/707) hz hy xh cb
    (by norm_num) (by norm_num) H reserve chart hn hv shared highest
  exact accepted.trans_le (fourthWitnessMargin z y x b (by positivity) threshold)

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.fourthWitnessMargin
#print axioms RankSeven.RealLowerWeighted.weightedFourth