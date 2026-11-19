import Rank7RealLowerWeightedFullMargin
namespace RankSeven.RealLowerWeighted
open Pauli ExteriorCuts LowerLeaves LowerPhysicalGainScale UpperFrameGain RealLowerPauliPrice
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (PairedDefectBound frameDefects)
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (sharedExcess highExcess)
noncomputable section
attribute [local irreducible] physicalWeights physicalEntries frameDefects rawProbe PackingInterpolation.gain SectorDefectAccounting.compressionLoss

private theorem fullPhysical (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c w : ℝ) (hz : 0≤z) (hy : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b) (w0 : 0≤w) (wc : 707*w≤1225)
    (H : z*(x-1)-3*x-5/2≤0) (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (hn : 0≤sharedExcess (physicalWeights half h2 k A)) (hv : 0≤highExcess (physicalWeights half h2 k A))
    (shared : highExcess (physicalWeights half h2 k A)≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (accepted : 0<fullMargin z y x b w) : PairedDefectBound half inv24 h2 k A mu := by
  let a:=physicalWeights half h2 k A; let v:=highExcess a; let s:=rawSpectrum z y x b c
  let D:=y*(z+y+x); let G:=z*x; let hi:=(12*w*(2-w)*D^2+antiPrice z y x)/(5/2)
  have rows:=PackingPolynomial.physicalRows half h2 k A orth
  have debit:=exteriorDebit a rows.1 rows.2 hn hv z y x b c w hz hy xh cb w0 wc H
  change 168*PackingInterpolation.gain a (amplitude s)-24*(b^2*w*D)*rawProbe s a 1≤b^2*((168-24*w)*D-168*y)*v at debit
  have pay:=pauliReceipt half inv24 third h2 h24 h3 k A mu orth z y x b c w hz hy xh cb w0 (by linarith only [wc]) chart shared highest
  change 24*(b^2*w*D)*rawProbe s a 1+b^4*(G^2/12+hi)*v≤frameDefects half inv24 k A mu at pay
  change 0<b^2*(G^2/12+hi)+168*y-(168-24*w)*D at accepted
  have scaled:=mul_nonneg (le_of_lt accepted) (mul_nonneg (sq_nonneg b) hv)
  have g:=physicalGain half h2 k A mu (fun i=>b*UpperPhysicalInterior.spectrum z y x i) c 1 (fun i=>congrFun chart i)
  rw [gainPolyEval] at g
  change SectorDefectAccounting.exteriorGain (amplitude mu) (physicalEntries half h2 k A)=PackingInterpolation.gain a (amplitude s) at g
  have loss:=SectorDefectAccounting.physicalLossNonnegative half h2 k A orth (amplitude mu)
  unfold PairedDefectBound; linarith only [debit,pay,scaled,g,loss]

/-- All weighted witnesses accepted by the actual lower replay are paid on
the nonpositive-head subcone when the full anticommuting reserve is sufficient. -/
theorem allWeightedWitnesses (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c : ℝ) (res : LowerContractor.Residual z y x b) (cb : 1≤c ∧ c≤b)
    (H : z*(x-1)-3*x-5/2≤0) (reserve : x^2≤5*z^2)
    (chart : (fun i=>(mu i)^2)=rawSpectrum z y x b c)
    (hn : 0≤sharedExcess (physicalWeights half h2 k A)) (hv : 0≤highExcess (physicalWeights half h2 k A))
    (shared : highExcess (physicalWeights half h2 k A)≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (highest : 2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (accepted : ∃w : ℝ,(w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ 0<weightedMargin z y x b w) :
    PairedDefectBound half inv24 h2 k A mu := by
  obtain ⟨w,valid,yes⟩:=accepted
  have sz : x^2≤6*z^2:=by nlinarith only [reserve,sq_nonneg z]
  have small (wp : 0≤w) (wc : 707*w≤1225) := weightedPhysical half inv24 third h2 h24 h3 k A mu orth
    z y x b c w res.zNonnegative res.yNonnegative res.xHead cb wp wc H sz chart hn hv shared highest yes
  rcases valid with e|e|e|e
  · exact small (by rw [e]; norm_num) (by rw [e]; norm_num)
  · exact small (by rw [e]; norm_num) (by rw [e]; norm_num)
  · exact small (by rw [e]; norm_num) (by rw [e]; norm_num)
  · rw [e] at yes
    exact fullPhysical half inv24 third h2 h24 h3 k A mu orth z y x b c (1225/707)
      res.zNonnegative res.yNonnegative res.xHead cb (by norm_num) (by norm_num) H chart hn hv shared highest
      (fourthFullMargin z y x b res.zNonnegative res.yNonnegative res.xHead res.headWeight reserve yes)

end
end RankSeven.RealLowerWeighted
#print axioms RankSeven.RealLowerWeighted.allWeightedWitnesses