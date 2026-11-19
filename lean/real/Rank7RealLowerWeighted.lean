import Rank7RealLowerWeightedDebit
import Rank7RealLowerWeightedReceipt
namespace RankSeven.RealLowerWeighted
open Pauli ExteriorCuts UpperFrameGain LowerPhysicalGainScale LowerCorner
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (PairedDefectBound frameDefects)
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (sharedExcess highExcess)
open RealLowerPauliPrice (antiPrice)
noncomputable section
attribute [local irreducible] rawProbe PackingInterpolation.gain physicalEntries physicalWeights frameDefects SectorDefectAccounting.compressionLoss

/-- On this subcone the full retained shared reserve dominates both alternatives
in the replay's maximum. The choice of highest shift is continuous up to 1225/707. -/
theorem weightedPhysical (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c w : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b) (w0 : 0≤w) (wc : 707*w≤1225)
    (H : z*(x-1)-3*x-5/2≤0) (reserve : x^2≤6*z^2)
    (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (hn : 0≤sharedExcess (physicalWeights half h2 k A)) (hv : 0≤highExcess (physicalWeights half h2 k A))
    (shared : highExcess (physicalWeights half h2 k A)≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (accepted : 0<LowerLeaves.weightedMargin z y x b w) : PairedDefectBound half inv24 h2 k A mu := by
  let a:=physicalWeights half h2 k A; let v:=highExcess a; let s:=rawSpectrum z y x b c
  let D:=y*(z+y+x); let G:=z*x
  let hi:=(12*w*(2-w)*D^2+antiPrice z y x)/(5/2)
  let maxR:=UpperWeighted.larger (G*G/24) ((x*x)*(x*x)/72)
  have xp : 0≤x := by linarith only [xh]
  have rows:=PackingPolynomial.physicalRows half h2 k A orth
  have debit:=exteriorDebit a rows.1 rows.2 hn hv z y x b c w hz hy xh cb w0 wc H
  change 168*PackingInterpolation.gain a (amplitude s)-24*(b^2*w*D)*rawProbe s a 1≤b^2*((168-24*w)*D-168*y)*v at debit
  have pay:=pauliReceipt half inv24 third h2 h24 h3 k A mu orth z y x b c w hz hy xh cb w0 (by linarith only [wc]) chart shared highest
  change 24*(b^2*w*D)*rawProbe s a 1+b^4*(G^2/12+hi)*v≤frameDefects half inv24 k A mu at pay
  have maxBound : maxR≤G^2/12 := by
    dsimp only [maxR,UpperWeighted.larger]; split
    · nlinarith only [sq_nonneg G]
    · dsimp only [G]; nlinarith only [mul_le_mul_of_nonneg_left reserve (sq_nonneg x)]
  change 0<b*b*((12*w*(2-w)*(D*D)+antiPrice z y x)*(1/(5/2))+maxR)+168*y-(168-24*w)*D at accepted
  have scalar : (168-24*w)*D-168*y≤b^2*(G^2/12+hi) := by
    dsimp only [hi]; linarith only [accepted,mul_le_mul_of_nonneg_left maxBound (sq_nonneg b)]
  have applied:=mul_le_mul_of_nonneg_left scalar (mul_nonneg (sq_nonneg b) hv)
  have exactGain:=physicalGain half h2 k A mu (fun i=>b*UpperPhysicalInterior.spectrum z y x i) c 1 (fun i=>congrFun chart i)
  rw [gainPolyEval] at exactGain
  change SectorDefectAccounting.exteriorGain (amplitude mu) (physicalEntries half h2 k A)=PackingInterpolation.gain a (amplitude s) at exactGain
  have loss:=SectorDefectAccounting.physicalLossNonnegative half h2 k A orth (amplitude mu)
  unfold PairedDefectBound
  linarith only [debit,pay,applied,exactGain,loss]

theorem weightedLarge (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c w : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (witness : w=1 ∨ w=5/4 ∨ w=3/2) (H : z*(x-1)-3*x-5/2≤0) (reserve : x^2≤6*z^2)
    (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (hn : 0≤sharedExcess (physicalWeights half h2 k A)) (hv : 0≤highExcess (physicalWeights half h2 k A))
    (large : 1≤24*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (largeOne : 2≤15*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (accepted : 0<LowerLeaves.weightedMargin z y x b w) : PairedDefectBound half inv24 h2 k A mu := by
  have geom:=RealLowerPhysicalComparison.largeGrams half h2 k A mu orth hn large largeOne
  let a:=physicalWeights half h2 k A
  have peak : highExcess a≤(realRay (sharedExcess a) (highExcess a) 0).peak := by
    change _≤UpperWeighted.larger _ _; unfold UpperWeighted.larger; split <;> linarith
  exact weightedPhysical half inv24 third h2 h24 h3 k A mu orth z y x b c w hz hy xh cb
    (by rcases witness with rfl|rfl|rfl <;> norm_num) (by rcases witness with rfl|rfl|rfl <;> norm_num)
    H reserve chart hn hv (peak.trans geom.1) geom.2 accepted

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.weightedPhysical
#print axioms RankSeven.RealLowerWeighted.weightedLarge