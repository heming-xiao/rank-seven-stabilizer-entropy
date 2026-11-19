import Rank7RealTiedCutPrice
import Rank7EndpointCornerGram
import Rank7UpperCertifiedFrameReplay
import Rank7PhysicalComparison
import Rank7UnshiftedDefects
import Rank7UpperDomainFrontier

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace RankSeven.RealUpperPhysicalComparison

open Pauli ExteriorCuts UpperContractor UpperCorner UpperEndpoint UpperEndpointPrices
open UpperPhysicalInterior UpperFrameTrace UpperFrameGain UpperReplay
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (PairedDefectBound frameDefects)
open PackingPolynomial (physicalWeights physicalRows)
open SectorDefectAccounting (compressionLoss exteriorGain)
open PhysicalTailBlend (unshiftedDefects)
open WeightedProbeShift (physicalPayment)

private theorem chartEq (h k q c d : ℝ) :
    tail (UpperPhysicalInterior.spectrum h k q) c d =
      RealTiedCutPrice.weights (1+(h+k+q)) (1+(k+q)) (1+q) c d := by
  funext i
  fin_cases i <;> norm_num [tail, UpperPhysicalInterior.spectrum, RealTiedCutPrice.weights]

private theorem largerEqMax (a b : ℝ) : UpperWeighted.larger a b=max a b := by
  unfold UpperWeighted.larger
  split
  · exact (max_eq_left ‹_›).symm
  · exact (max_eq_right (le_of_not_ge ‹_›)).symm

private theorem chartSupports (p : Inputs ℝ) (wh ws c d : ℝ) :
    let a := 1+(p.h+p.k+p.q)
    let b := 1+(p.k+p.q)
    let g := 1+p.q
    (K p wh ws c d).one=UpperPrices.supportValue (a*b*c*d) (a*g) wh ∧
      (K p wh ws c d).shared=c*UpperPrices.supportValue (a*g*d) (max a (b*g)) ws := by
  let a := 1+(p.h+p.k+p.q)
  let b := 1+(p.k+p.q)
  let g := 1+p.q
  change UpperPrices.supportValue ((a*b)*(c*d)) (a*g) wh = _ ∧
    c*UpperPrices.supportValue ((a*g)*d) (UpperWeighted.larger a (b*g)) ws = _
  rw [largerEqMax, show (a*b)*(c*d)=a*b*c*d by ring]
  exact ⟨rfl,rfl⟩

attribute [local irreducible] physicalWeights physicalEntries frameDefects unshiftedDefects
  compressionLoss exteriorGain amplitude corrected gainPoly weightedProbe physicalPrice
  PairedDefectBound

private theorem admittedParameters {f u w : ℝ} (s : ShiftValues f u w) :
    0 ≤ f ∧ f ≤ 1 ∧ 0 ≤ u ∧ 2*u ≤ 3 ∧ 0 ≤ w ∧ 4*w ≤ 7 := by
  obtain ⟨f0,u0,w0⟩ := s
  have ff : 0 ≤ f ∧ f ≤ 1 := by rcases f0 with h|h|h|h|h <;> rw [h] <;> norm_num
  have uu : 0 ≤ u ∧ 2*u ≤ 3 := by rcases u0 with h|h|h|h <;> rw [h] <;> norm_num
  have ww : 0 ≤ w ∧ 4*w ≤ 7 := by rcases w0 with h|h|h|h <;> rw [h] <;> norm_num
  exact ⟨ff.1,ff.2,uu.1,uu.2,ww.1,ww.2⟩

private theorem scalarComparison (gain shiftShared shiftHigh tax price defect unshifted support loss : ℝ)
    (nonneg : 0 ≤ gain) (unused : 0 ≤ unshifted)
    (corner : gain-shiftShared-shiftHigh+96*invRate*tax<price)
    (pauli : price+shiftShared+shiftHigh ≤ invRate*(defect-unshifted)+96*invRate*support)
    (cuts : support-tax ≤ loss) : 168*gain<defect+96*loss := by
  norm_num [invRate] at corner pauli
  linarith only [corner,pauli,cuts,unused,nonneg]

private theorem priceComparison (p : Inputs ℝ) (x : Wedge7→ℝ)
    (wh ws c d gain D D₀ comp : ℝ)
    (gainEq : gain = (gainPoly (UpperPhysicalInterior.spectrum p.h p.k p.q) x).eval c d)
    (D₀0 : 0 ≤ D₀) (gain0 : 0 ≤ gain) :
    let v := highExcess x
    let s := sharedFraction x
    let U i := weightedProbe (UpperPhysicalInterior.spectrum p.h p.k p.q) x i c d
    let price := physicalPrice p wh ws c d (trueRay (sharedExcess x) v (v*(1-v)) (s*(1-s)))
    let support := (K p wh ws c d).one*(v*(1-v))+(K p wh ws c d).shared*(s*(1-s))
    let crossing := ((1+p.q)*p.h*d*(1-c)/2)*x entering
    corrected (UpperPhysicalInterior.spectrum p.h p.k p.q) x (P p).lambda (UpperPhysicalInterior.mu p) (cross p) c d < price →
    price+(P p).lambda*(U 1+U 2)+UpperPhysicalInterior.mu p*U 1 ≤ invRate*(D-D₀)+96*invRate*support →
    support-crossing ≤ comp →
    168*gain<D+96*comp := by
  dsimp only
  intro strict paid cuts
  have compGain := gainPolyEval (UpperPhysicalInterior.spectrum p.h p.k p.q) x c d
  rw [←gainEq] at compGain
  have eq : corrected (UpperPhysicalInterior.spectrum p.h p.k p.q) x (P p).lambda (UpperPhysicalInterior.mu p) (cross p) c d =
      gain-(P p).lambda*(weightedProbe (UpperPhysicalInterior.spectrum p.h p.k p.q) x 1 c d+
        weightedProbe (UpperPhysicalInterior.spectrum p.h p.k p.q) x 2 c d) -
        UpperPhysicalInterior.mu p*weightedProbe (UpperPhysicalInterior.spectrum p.h p.k p.q) x 1 c d+
        96*invRate*(((1+p.q)*p.h*d*(1-c)/2)*x entering) := by
    unfold corrected cross
    rw [←compGain]
    ring
  rw [eq] at strict
  exact scalarComparison _ _ _ _ _ _ _ _ _ gain0 D₀0 strict paid cuts

set_option maxHeartbeats 280000 in
set_option linter.constructorNameAsVariable false in
private theorem chartCompression (half : ℝ) (unit : 2*half=1) (n : Nat)
    (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (m0 : ∀ i,0 ≤ m i) (p : Inputs ℝ) (wh ws c d : ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum p.h p.k p.q) c d)
    (h0 : 0 ≤ p.h) (k0 : 0 ≤ p.k) (q0 : 0 ≤ p.q) (d0 : 0 ≤ d) (dc : d ≤ c) (c1 : c ≤ 1)
    (weights : WeightLimits p wh ws)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A)) :
    let x := physicalWeights half unit n A
    let v := highExcess x
    let s := sharedFraction x
    (K p wh ws c d).one*(v*(1-v))+(K p wh ws c d).shared*(s*(1-s))-
      ((1+p.q)*p.h*d*(1-c)/2)*x entering ≤ compressionLoss (amplitude m) (physicalEntries half unit n A) := by
  let a := 1+(p.h+p.k+p.q)
  let b := 1+(p.k+p.q)
  let g := 1+p.q
  have ga : 1 ≤ g := by dsimp only [g]; linarith only [q0]
  have gb : g ≤ b := by dsimp only [g,b]; linarith only [k0]
  have ba : b ≤ a := by dsimp only [b,a]; linarith only [h0]
  have cut := RealTiedCutPrice.physicalTiedCompression half unit n A orth n0 v0
    a b g c d ws wh ga gb ba d0 dc c1 weights.sharedNonnegative weights.highNonnegative
  have rootEq : (fun i => Real.sqrt (RealTiedCutPrice.weights a b g c d i))=m := by
    funext i
    have definition := chartEq p.h p.k p.q c d
    change tail (UpperPhysicalInterior.spectrum p.h p.k p.q) c d=RealTiedCutPrice.weights a b g c d at definition
    rw [←definition, ←congrFun chart i, Real.sqrt_sq (m0 i)]
  have gap : a-b=p.h := by unfold a b; ring
  have support := chartSupports p wh ws c d
  change (K p wh ws c d).one=UpperPrices.supportValue (a*b*c*d) (a*g) wh ∧
      (K p wh ws c d).shared=c*UpperPrices.supportValue (a*g*d) (max a (b*g)) ws at support
  let x := physicalWeights half unit n A
  let v := highExcess x
  let s := sharedFraction x
  dsimp only at cut
  rw [rootEq, gap, ←support.1, ←support.2] at cut
  rw [add_comm ((K p wh ws c d).shared*(s*(1-s))) ((K p wh ws c d).one*(v*(1-v)))] at cut
  change (K p wh ws c d).one*(v*(1-v))+(K p wh ws c d).shared*(s*(1-s))-
      (g*p.h*d*(1-c)/2)*x entering ≤ compressionLoss (amplitude m) (physicalEntries half unit n A)
  exact cut

set_option maxHeartbeats 280000 in
set_option linter.constructorNameAsVariable false in
/-- An actual strict replay corner price pays the full physical exterior gain
on the normalized tie. The only Pauli geometry inputs are the two anchor bounds. -/
theorem strictCornerPaid (half inv24 third : ℝ) (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7→ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀i,0 ≤ m i)
    (p : Inputs ℝ) (wh ws c d : ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum p.h p.k p.q) c d)
    (cl : p.cl ≤ c) (cu : c ≤ p.ch) (du : d ≤ p.dh) (dl : p.dl ≤ d) (dl0 : 0 ≤ p.dl)
    (cu1 : p.ch ≤ 1) (ordered : d ≤ c) (cornerOrder : p.dl ≤ p.cl)
    (h0 : 0 ≤ p.h) (k0 : 0 ≤ p.k) (q0 : 0 ≤ p.q)
    (shifts : ShiftValues p.f p.u p.w) (weights : WeightLimits p wh ws)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (sharedGeometry :
      let x := physicalWeights half unit n A
      (trueRay (sharedExcess x) (highExcess x) 0 0).peak ≤ 12*(physicalPayment half unit n A m).kappa)
    (highestGeometry : 2*highExcess (physicalWeights half unit n A) ≤ 5*(physicalPayment half unit n A m).kappaOne)
    (accepted :
      let x := physicalWeights half unit n A
      let v := highExcess x
      let s := sharedFraction x
      corrected (UpperPhysicalInterior.spectrum p.h p.k p.q) x (P p).lambda (UpperPhysicalInterior.mu p) (cross p) c d <
        physicalPrice p wh ws c d (trueRay (sharedExcess x) v (v*(1-v)) (s*(1-s)))) :
    PairedDefectBound half inv24 unit n A m := by
  let E := physicalEntries half unit n A
  let x := physicalWeights half unit n A
  let G := exteriorGain (amplitude m) E
  let D := frameDefects half inv24 n A m
  let L := compressionLoss (amplitude m) E
  unfold PairedDefectBound
  change 168*G ≤ D+96*L
  by_cases gain0 : 0 ≤ G
  · let v := highExcess x
    let s := sharedFraction x
    obtain ⟨f0,f1,u0,uc,w0,wc⟩ := admittedParameters shifts
    have pauli := PhysicalEndpointPrice.physicalPriceOnFrame half inv24 third unit unit24 unit3
      n A m orth p wh ws c d chart cl cu du dl dl0 cu1 ordered cornerOrder h0 k0 q0 f0 f1 u0 uc w0 wc
      sharedGeometry highestGeometry (v*(1-v)) (s*(1-s))
    have cmp := chartCompression half unit n A m orth m0 p wh ws c d chart h0 k0 q0
      (dl0.trans dl) ordered (cu.trans cu1) weights n0 v0
    have balance := UpperFrameGain.physicalGain half unit n A m
      (UpperPhysicalInterior.spectrum p.h p.k p.q) c d (fun i => congrFun chart i)
    have unshifted0 := UnshiftedDefects.nonnegative half inv24 unit unit24 n A m orth
    let D₀ := unshiftedDefects half inv24 n A m
    have paid : 168*G<D+96*L := priceComparison p x wh ws c d G D D₀ L
      balance unshifted0 gain0 accepted pauli cmp
    exact le_of_lt paid
  · have defect0 := PhysicalComparison.frameDefectsNonnegative half inv24 unit unit24 n A m orth
    have loss0 := SectorDefectAccounting.physicalLossNonnegative half unit n A orth (amplitude m)
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_lt (lt_of_not_ge gain0)))
      (add_nonneg defect0 (mul_nonneg (by norm_num) loss0))

private theorem orderedWitness (box : TailBox) (witness : Witnesses box) : box.d.hi ≤ box.c.lo := by
  obtain ⟨s,_,rows,comp,_⟩ := witness 0
  rw [UpperEndpoint.originalMargins] at comp
  unfold UpperEndpoint.preparedMargins at comp
  split at comp <;> first | contradiction | omega

set_option maxHeartbeats 280000 in
set_option linter.constructorNameAsVariable false in
/-- Physical upper corner implication of either exact traversal, using
the signed corner bounds internally. -/
theorem cornerWitnessComparison (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7→ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀i,0 ≤ m i)
    (box : TailBox) (h k q c d : ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum h k q) c d)
    (res : Residual h k q c d) (headFloor : 1 ≤ 2*q)
    (inside : Inside Interval.cppGrid box h k q c d) (domain : TailRectangle box) (witness : Witnesses box)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0<sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedGeometry :
      let x := physicalWeights half unit n A
      (trueRay (sharedExcess x) (highExcess x) 0 0).peak ≤ 12*(physicalPayment half unit n A m).kappa)
    (highestGeometry : 2*highExcess (physicalWeights half unit n A) ≤ 5*(physicalPayment half unit n A m).kappaOne) :
    PairedDefectBound half inv24 unit n A m := by
  obtain ⟨nx,rows⟩ := physicalRows half unit n A orth
  obtain ⟨f,u,w,wh,ws,shifts,weights,strict⟩ := UpperFrameTrace.actualFrameInterior
    half unit n A orth inside domain witness res.hNonnegative res.kNonnegative res.qNonnegative
    n0 v0 positive (UpperPairCap.physicalPairCap half unit n A orth)
    (UpperCertifiedExterior.exteriorEstimates res headFloor inside domain _ nx rows n0 v0)
  let p := realInputs box h k q f u w
  obtain ⟨cl,ch⟩ := insideEndpoints.mp inside.cInside
  obtain ⟨dl,dh⟩ := insideEndpoints.mp inside.dInside
  have dl0 : 0 ≤ p.dl := lowerEndpointNonnegative (pointSound (R:=ℝ) Interval.cppGrid box.d.lo) domain.1
  have cu1 : p.ch ≤ 1 := by
    change value Interval.cppGrid box.c.hi ≤ 1
    rw [←scaleValue (R:=ℝ) Interval.cppGrid]
    exact valueLe _ domain.2
  have order : p.dl ≤ p.cl := le_trans dl (le_trans dh (valueLe _ (orderedWitness box witness)))
  exact strictCornerPaid half inv24 third unit unit24 unit3 n A m orth m0 p wh ws c d chart
    cl ch dh dl dl0 cu1 res.ordered order res.hNonnegative res.kNonnegative res.qNonnegative
    shifts weights n0 v0 sharedGeometry highestGeometry strict

open UpperDomainFrontier (Here Accounts OpenPoint)

/-- The checked scalar branches are retained, and a signed corner branch yields the
physical paired-defect bound. -/
def PhysicalOutcome (z : Fin 5 → ℝ) (half inv24 : ℝ) (unit : 2*half=1) (n : Nat)
    (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ) : Prop :=
  UpperOldRegions.OldCondition (z 0) (z 1) (z 2) (z 3) (z 4) ∨
    (∃ u : ℝ, (u=1 ∨ u=5/4 ∨ u=3/2) ∧ 0 < UpperWeighted.margin (z 0) (z 1) (z 2) (z 3) (z 4) u) ∨
    PairedDefectBound half inv24 unit n A m

set_option linter.constructorNameAsVariable false in
/-- Every covered corner reaches the physical comparison; the unresolved
frontier and the other scalar branches are preserved. -/
theorem frontierComparison (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀i,0 ≤ m i)
    (z : Fin 5 → ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum (z 0) (z 1) (z 2)) (z 3) (z 4))
    (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4)) (headFloor : 1 ≤ 2*z 2)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0 < sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedGeometry :
      let x := physicalWeights half unit n A
      (trueRay (sharedExcess x) (highExcess x) 0 0).peak ≤ 12*(physicalPayment half unit n A m).kappa)
    (highestGeometry : 2*highExcess (physicalWeights half unit n A) ≤ 5*(physicalPayment half unit n A m).kappaOne)
    {root : TailBox} {front : List TailBox} (cert : Accounts ℝ root front)
    (valid : Valid Interval.cppGrid root) (domain : TailRectangle root) (inside : Here root z) :
    PhysicalOutcome z half inv24 unit n A m ∨ OpenPoint front z := by
  rcases cert z res valid domain inside with covered|pending
  · apply Or.inl
    rcases covered with old|weighted|⟨region,rect,contained,witness⟩
    · exact Or.inl old
    · exact Or.inr (Or.inl weighted)
    · exact Or.inr (Or.inr (cornerWitnessComparison half inv24 third unit unit24 unit3 n A m orth m0
        region (z 0) (z 1) (z 2) (z 3) (z 4) chart res headFloor contained rect witness n0 v0
        positive sharedGeometry highestGeometry))
  · exact Or.inr pending

set_option linter.constructorNameAsVariable false in
/-- When both Gram parameters are large, the Pauli geometry follows directly
from the physical frame and the two scalar range conditions. -/
theorem frontierComparisonLarge (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀i,0 ≤ m i)
    (z : Fin 5 → ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum (z 0) (z 1) (z 2)) (z 3) (z 4))
    (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4)) (headFloor : 1 ≤ 2*z 2)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0 < sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedLarge : 1 ≤ 24*(physicalPayment half unit n A m).kappa)
    (highestLarge : 2 ≤ 15*(physicalPayment half unit n A m).kappaOne)
    {root : TailBox} {front : List TailBox} (cert : Accounts ℝ root front)
    (valid : Valid Interval.cppGrid root) (domain : TailRectangle root) (inside : Here root z) :
    PhysicalOutcome z half inv24 unit n A m ∨ OpenPoint front z :=
  frontierComparison half inv24 third unit unit24 unit3 n A m orth m0 z chart res headFloor n0 v0 positive
    (EndpointLargeGrams.largeSharedOnCorner half unit n A m orth n0 sharedLarge)
    (HighestAnchorSelection.largeGram half unit n A m orth highestLarge) cert valid domain inside

end RankSeven.RealUpperPhysicalComparison

#print axioms RankSeven.RealUpperPhysicalComparison.strictCornerPaid
#print axioms RankSeven.RealUpperPhysicalComparison.cornerWitnessComparison
#print axioms RankSeven.RealUpperPhysicalComparison.frontierComparison
#print axioms RankSeven.RealUpperPhysicalComparison.frontierComparisonLarge
