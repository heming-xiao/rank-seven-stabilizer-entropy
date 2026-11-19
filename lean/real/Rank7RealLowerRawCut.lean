import Rank7RealLowerCutPrice
namespace RankSeven.RealLowerRawCut
open Pauli ExteriorCuts Compression RealTiedCutPrice LowerPhysicalGainScale

theorem scaleLoss (m : ℝ) (a : Wedge7→ℝ) (E : HermitianEntries Wedge7 ℝ) :
    SectorDefectAccounting.compressionLoss (fun w => m*a w) E=m^2*SectorDefectAccounting.compressionLoss a E := by
  have d : diagonalLoss wedges (fun w => m*a w) (fun w => E.realPart w w)=m^2*diagonalLoss wedges a (fun w => E.realPart w w) := by
    unfold diagonalLoss; rw [sumOverMulLeft]; apply sumOverCongr; intro i; ring
  have q : E.realQuadraticTrace wedges (fun w => m*a w)=m^2*E.realQuadraticTrace wedges a := by
    unfold HermitianEntries.realQuadraticTrace; rw [sumOverMulLeft]; apply sumOverCongr; intro i
    rw [sumOverMulLeft]; apply sumOverCongr; intro j; ring
  change diagonalLoss _ _ _-E.realQuadraticTrace _ _=_*(_-_)
  rw [d,q]; unfold SectorDefectAccounting.normOverlap SectorDefectAccounting.normAlt; ring

theorem rawCut (half : ℝ) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤UpperFrameTrace.sharedExcess (PackingPolynomial.physicalWeights half unit k A))
    (v0 : 0≤UpperFrameTrace.highExcess (PackingPolynomial.physicalWeights half unit k A))
    (z y x b c : ℝ) (roots : LowerCorner.Roots z y x b) (cb : 1≤c ∧ c≤b)
    (z0 : 0≤z) (y0 : 0≤y) (x0 : 0≤x) (mu : Fin 7→ℝ) (nonneg : ∀i,0≤mu i)
    (chart : (fun i => (mu i)^2)=rawSpectrum z y x b c) :
    let α := 1+(z+y+x); let γ := 1+x
    let V := min (α*LowerCorner.gap roots.gamma roots.fifth) (γ*LowerCorner.gap roots.alpha roots.betaFifth)
    let diag := PackingPolynomial.physicalWeights half unit k A
    let s := UpperFrameTrace.sharedFraction diag
    let E := PhysicalCompressionEffect.physicalEntries half unit k A
    b^2*c*V*(s*(1-s))-b^2*γ*z*(b-c)/2*diag UpperFrameGain.entering≤
      SectorDefectAccounting.compressionLoss (amplitude mu) E := by
  let α := 1+(z+y+x); let β := 1+(y+x); let γ := 1+x
  let V := min (α*LowerCorner.gap roots.gamma roots.fifth) (γ*LowerCorner.gap roots.alpha roots.betaFifth)
  let E := PhysicalCompressionEffect.physicalEntries half unit k A
  let diag := PackingPolynomial.physicalWeights half unit k A
  let s := UpperFrameTrace.sharedFraction diag
  let T := s*(1-s)
  let norm := weights α β γ (c/b) (1/b)
  let amp := amplitude (fun i => Real.sqrt (norm i))
  have bp : 0<b := by linarith only [cb.1,cb.2]
  have scale (i : Fin 7) : (mu i)^2=b*norm i := by
    have atI := congrFun chart i
    change (mu i)^2=rawSpectrum z y x b c i at atI
    rw [atI]
    fin_cases i <;> norm_num [rawSpectrum,UpperFrameGain.tail,UpperPhysicalInterior.spectrum,α,β,γ,norm,weights] <;> field_simp
  have rootsEq (i : Fin 7) : mu i=Real.sqrt b*Real.sqrt (norm i) := by
    rw [← Real.sqrt_mul (le_of_lt bp),←scale,Real.sqrt_sq (nonneg _)]
  have amplitudes : amplitude mu=fun w => b^2*amp w := by
    funext w; dsimp only [amp,amplitude,product4]
    rw [rootsEq w.i,rootsEq w.j,rootsEq w.k,rootsEq w.m]
    have unit := Real.sq_sqrt (le_of_lt bp)
    calc
      _ = ((Real.sqrt b)^2)^2*(Real.sqrt (norm w.i)*Real.sqrt (norm w.j)*Real.sqrt (norm w.k)*Real.sqrt (norm w.m)) := by ring
      _ = _ := by rw [unit]
  have priced := RealLowerCutPrice.actualShared half unit k A orth n0 v0 z y x b c roots cb z0 y0 x0
  change c*V*T-γ*z*(b-c)/2*diag UpperFrameGain.entering≤b^2*SectorDefectAccounting.compressionLoss amp E at priced
  have paid := mul_le_mul_of_nonneg_left priced (sq_nonneg b)
  change b^2*c*V*T-b^2*γ*z*(b-c)/2*diag UpperFrameGain.entering≤SectorDefectAccounting.compressionLoss (amplitude mu) E
  rw [amplitudes,scaleLoss]; linarith only [paid]

end RankSeven.RealLowerRawCut
#print axioms RankSeven.RealLowerRawCut.rawCut