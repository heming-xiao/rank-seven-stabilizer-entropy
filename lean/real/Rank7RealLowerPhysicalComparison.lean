import Rank7RealLowerPhysicalPrice
import Rank7RealLowerRawCut
import Rank7EndpointCornerGram
import Rank7UnshiftedDefects

set_option maxHeartbeats 450000
set_option maxRecDepth 2048
namespace RankSeven.RealLowerPhysicalComparison
open Pauli ExteriorCuts UpperFrameGain LowerPhysicalGainScale LowerSignedExterior LowerAffinePayment LowerCorner
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (PairedDefectBound frameDefects)
open SectorDefectAccounting (exteriorGain compressionLoss)
open PhysicalTailBlend (unshiftedDefects)
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (sharedExcess highExcess sharedFraction)
open UpperEndpointPrices (invRate)
noncomputable section

def SharedGeometry (half : ℝ) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) : Prop :=
  let diag := physicalWeights half h2 k A
  (realRay (sharedExcess diag) (highExcess diag) 0).peak≤12*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa

def HighestGeometry (half : ℝ) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) : Prop :=
  2*highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne

private theorem cutEq (z y x b f u w a e : ℝ) :
    (realPrices z y x b f u w a e).cut=96*invRate*min a e := by
  change 96*invRate*UpperEndpoint.smaller a e=_
  have m : UpperEndpoint.smaller a e=min a e := by unfold UpperEndpoint.smaller; split <;> simp_all [min_def]
  rw [m]

attribute [local irreducible] physicalWeights physicalEntries frameDefects unshiftedDefects
  compressionLoss exteriorGain amplitude LowerSignedExterior.gainAt PackingInterpolation.gain rawProbe
  LowerCorner.realPrices sharedExcess highExcess sharedFraction

theorem sharedComparison (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (nonneg : ∀i,0≤mu i) (orth : OrthonormalFrame A)
    (z y x b c : ℝ) (roots : Roots z y x b) (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (chart : (fun i => (mu i)^2)=rawSpectrum z y x b c)
    (n0 : 0≤sharedExcess (physicalWeights half h2 k A)) (v0 : 0≤highExcess (physicalWeights half h2 k A))
    (sharedGeom : SharedGeometry half h2 k A mu) (highestGeom : HighestGeometry half h2 k A mu)
    (accepted : LowerCertifiedFrameReplay.Shared z y x b c roots (physicalWeights half h2 k A)) :
    PairedDefectBound half inv24 h2 k A mu := by
  let diag := physicalWeights half h2 k A
  let E := physicalEntries half h2 k A
  let G := exteriorGain (amplitude mu) E; let D := frameDefects half inv24 k A mu
  let base := unshiftedDefects half inv24 k A mu
  let L := compressionLoss (amplitude mu) E
  change 168*G≤D+96*L
  by_cases gain0 : 0≤G
  · obtain ⟨f,u,w,fs,us,ws,paid⟩ := accepted
    let wa := (1+(z+y+x))*LowerCorner.gap roots.gamma roots.fifth
    let wb := (1+x)*LowerCorner.gap roots.alpha roots.betaFifth
    let p := realPrices z y x b f u w wa wb
    let U := rawProbe (rawSpectrum z y x b c) diag
    let n := sharedExcess diag; let v := highExcess diag; let sf := sharedFraction diag
    let T := sf*(1-sf); let peak := (realRay n v 0).peak
    let S := p.shared+bonusSlope z x b f u*(b-c)
    let jr := invRate (R:=ℝ)
    let F := gainAt z y x b c w p diag
    let G' := PackingInterpolation.gain diag (amplitude (rawSpectrum z y x b c))
    have x0 : 0≤x := by linarith only [xh]
    have bp : 0<b := by linarith only [cb.1,cb.2]
    have pcd := RealLowerPhysicalPrice.physicalPrice half inv24 third h2 h24 h3 k A mu orth z y x b c f u w wa wb z0 y0 xh cb chart fs us ws sharedGeom highestGeom
    change b^2*(S*peak+p.high*v)+b^2*p.lambda*(U 1+U 2)+b^2*LowerSignedPrices.mu z y x w*U 1≤jr*(D-base) at pcd
    have cut := RealLowerRawCut.rawCut half h2 k A orth n0 v0 z y x b c roots cb z0 y0 x0 mu nonneg chart
    change b^2*c*min wa wb*T-b^2*(1+x)*z*(b-c)/2*diag entering≤L at cut
    have gEq := physicalGain half h2 k A mu (fun i => b*UpperPhysicalInterior.spectrum z y x i) c 1 (fun i => congrFun chart i)
    rw [gainPolyEval] at gEq
    change G=G' at gEq
    have num := physicalNumerator z y x b c w p diag bp
    change b*b*F=G'-(b*b*p.lambda)*(U 1+U 2)-(b*b*LowerSignedPrices.mu z y x w)*U 1+
      LowerSignedPrices.cross z x*(b*b)*(b-c)*diag entering at num
    change F<S*peak+p.high*v+c*p.cut*T at paid
    have width : p.cut=96*jr*min wa wb := cutEq z y x b f u w wa wb
    rw [width] at paid
    have strictPaid := mul_lt_mul_of_pos_left paid (sq_pos_of_pos bp)
    have positive : 0≤96*jr := by norm_num [jr,invRate]
    have cf := mul_le_mul_of_nonneg_left cut positive
    have cross : LowerSignedPrices.cross z x=96*jr*((1+x)*z/2) := rfl
    rw [cross,←gEq] at num
    have all : G<jr*(D-base)+96*jr*L := by linear_combination strictPaid + pcd + cf - num
    have base0 : 0≤base := UnshiftedDefects.nonnegative half inv24 h2 h24 k A mu orth
    norm_num [jr,invRate] at all
    linarith only [all,base0,gain0]
  · have dn : 0≤D := PhysicalComparison.frameDefectsNonnegative half inv24 h2 h24 k A mu orth
    have ln : 0≤L := SectorDefectAccounting.physicalLossNonnegative half h2 k A orth (amplitude mu)
    linarith only [le_of_not_ge gain0,dn,ln]

/-- A replayed lower slab retains the two earlier exits; its accepted shared exit now supplies the actual paired defect bound. -/
theorem checkedSlab (slab : Fin 6) (t : Fin 4→ℝ) (c : ℝ) (roots : Roots (t 0) (t 1) (t 2) (t 3))
    (res : LowerContractor.Residual (t 0) (t 1) (t 2) (t 3)) (cb : 1≤c ∧ c≤t 3)
    (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (nonneg : ∀i,0≤mu i) (orth : OrthonormalFrame A)
    (chart : (fun i => (mu i)^2)=rawSpectrum (t 0) (t 1) (t 2) (t 3) c)
    (n0 : 0≤sharedExcess (physicalWeights half h2 k A)) (v0 : 0≤highExcess (physicalWeights half h2 k A))
    (nz : 0<sharedExcess (physicalWeights half h2 k A)+highExcess (physicalWeights half h2 k A))
    (sharedGeom : SharedGeometry half h2 k A mu) (highestGeom : HighestGeometry half h2 k A mu)
    (inside : (LowerReplay.toBox (LowerContractor.initial slab)).Contains Interval.cppGrid t) (pass : LowerReplay.replay slab=true) :
    LowerLeaves.OldCondition (t 0) (t 1) (t 2) (t 3) ∨
    (∃ w : ℝ,(w=5/4∨w=3/2∨w=1∨w=7/4) ∧ 0<LowerLeaves.weightedMargin (t 0) (t 1) (t 2) (t 3) w) ∨
    PairedDefectBound half inv24 h2 k A mu := by
  rcases LowerCertifiedFrameReplay.checkedSlab slab t c roots res cb half h2 k A orth n0 v0 nz inside pass with old|weighted|shared
  · exact Or.inl old
  · exact Or.inr (Or.inl weighted)
  · exact Or.inr (Or.inr (sharedComparison half inv24 third h2 h24 h3 k A mu nonneg orth _ _ _ _ c roots
      res.zNonnegative res.yNonnegative res.xHead cb chart n0 v0 sharedGeom highestGeom shared))

theorem largeGrams (half : ℝ) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ)
    (orth : OrthonormalFrame A) (n0 : 0≤sharedExcess (physicalWeights half h2 k A))
    (large : 1≤24*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (largeOne : 2≤15*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne) :
    SharedGeometry half h2 k A mu ∧ HighestGeometry half h2 k A mu :=
  ⟨EndpointLargeGrams.largeSharedOnCorner half h2 k A mu orth n0 large,
    HighestAnchorSelection.largeGram half h2 k A mu orth largeOne⟩

def rootsOfDomain (z y x b : ℝ) (z0 : 0≤z) (y0 : 0≤y) (x0 : 0≤x) (b0 : 0≤b) : Roots z y x b :=
  ⟨Real.sqrt (1+(z+y+x)),Real.sqrt (1+x),Real.sqrt b,Real.sqrt (b*(1+(y+x))),
    Real.sqrt_nonneg _,Real.sqrt_nonneg _,Real.sqrt_nonneg _,Real.sqrt_nonneg _,
    Real.mul_self_sqrt (by positivity),Real.mul_self_sqrt (by positivity),Real.mul_self_sqrt b0,
    Real.mul_self_sqrt (by positivity)⟩

/-- A real six-slab replay wrapper on the branch where both Gram entries clear their checked thresholds. -/
theorem checkedSlabLarge (slab : Fin 6) (t : Fin 4→ℝ) (c : ℝ)
    (res : LowerContractor.Residual (t 0) (t 1) (t 2) (t 3)) (cb : 1≤c ∧ c≤t 3)
    (half inv24 third : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (nonneg : ∀i,0≤mu i) (orth : OrthonormalFrame A)
    (chart : (fun i => (mu i)^2)=rawSpectrum (t 0) (t 1) (t 2) (t 3) c)
    (n0 : 0≤sharedExcess (physicalWeights half h2 k A)) (v0 : 0≤highExcess (physicalWeights half h2 k A))
    (nz : 0<sharedExcess (physicalWeights half h2 k A)+highExcess (physicalWeights half h2 k A))
    (large : 1≤24*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa)
    (largeOne : 2≤15*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne)
    (inside : (LowerReplay.toBox (LowerContractor.initial slab)).Contains Interval.cppGrid t) (pass : LowerReplay.replay slab=true) :
    LowerLeaves.OldCondition (t 0) (t 1) (t 2) (t 3) ∨
    (∃ w : ℝ,(w=5/4∨w=3/2∨w=1∨w=7/4) ∧ 0<LowerLeaves.weightedMargin (t 0) (t 1) (t 2) (t 3) w) ∨
    PairedDefectBound half inv24 h2 k A mu := by
  let roots := rootsOfDomain (t 0) (t 1) (t 2) (t 3) res.zNonnegative res.yNonnegative
    (by linarith only [res.xHead]) (by linarith only [cb.1,cb.2])
  have geometry := largeGrams half h2 k A mu orth n0 large largeOne
  exact checkedSlab slab t c roots res cb half inv24 third h2 h24 h3 k A mu nonneg orth chart n0 v0 nz geometry.1 geometry.2 inside pass

end
end RankSeven.RealLowerPhysicalComparison
#print axioms RankSeven.RealLowerPhysicalComparison.sharedComparison
#print axioms RankSeven.RealLowerPhysicalComparison.checkedSlab
#print axioms RankSeven.RealLowerPhysicalComparison.largeGrams
#print axioms RankSeven.RealLowerPhysicalComparison.checkedSlabLarge