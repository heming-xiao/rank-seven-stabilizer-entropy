import Rank7HighestAnchorCoefficient
import Rank7RealUpperPhysicalComparison
import Rank7RealLowerPhysicalComparison
import Rank7RealLowerAllWeighted

namespace RankSeven.RealPhysicalHighest

open Pauli
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalDefectAssembly (PairedDefectBound)
open PackingPolynomial (physicalWeights)
open UpperFrameTrace (sharedExcess highExcess)
open WeightedProbeShift (physicalPayment)

attribute [local irreducible] physicalWeights physicalPayment

section Upper

open UpperContractor (Residual Valid)
open UpperCorner (TailBox)
open UpperDomainFrontier (Accounts Here OpenPoint)
open UpperPhysicalInterior (TailRectangle)
open UpperFrameGain (tail)
open RealUpperPhysicalComparison (PhysicalOutcome)

set_option linter.constructorNameAsVariable false in
/-- For covered signed upper corners the highest-pair payment follows from
the physical frame. The shared payment is supplied by its large-Gram bound. -/
theorem upperFrontier (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀ i,0 ≤ m i) (z : Fin 5 → ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum (z 0) (z 1) (z 2)) (z 3) (z 4))
    (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4)) (headFloor : 1 ≤ 2*z 2)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0 < sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedLarge : 1 ≤ 24*(physicalPayment half unit n A m).kappa)
    {root : TailBox} {front : List TailBox} (cert : Accounts ℝ root front)
    (valid : Valid Interval.cppGrid root) (domain : TailRectangle root) (inside : Here root z) :
    PhysicalOutcome z half inv24 unit n A m ∨ OpenPoint front z :=
  RealUpperPhysicalComparison.frontierComparison half inv24 third unit unit24 unit3 n A m orth m0
    z chart res headFloor n0 v0 positive
    (EndpointLargeGrams.largeSharedOnCorner half unit n A m orth n0 sharedLarge)
    (HighestAnchorCoefficient.physicalHighest half unit n A m orth) cert valid domain inside

end Upper

section Lower

open LowerPhysicalGainScale (rawSpectrum)
open LowerLeaves (OldCondition weightedMargin)

set_option linter.constructorNameAsVariable false in
/-- The shared exit of a successful lower slab replay supplies the paired
defect inequality for every highest-pair Gram value. -/
theorem lowerSlab (slab : Fin 6) (t : Fin 4 → ℝ) (c : ℝ)
    (res : LowerContractor.Residual (t 0) (t 1) (t 2) (t 3)) (cb : 1 ≤ c ∧ c ≤ t 3)
    (half inv24 third : ℝ) (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ)
    (m0 : ∀ i,0 ≤ m i) (orth : OrthonormalFrame A)
    (chart : (fun i => (m i)^2)=rawSpectrum (t 0) (t 1) (t 2) (t 3) c)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0 < sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedLarge : 1 ≤ 24*(physicalPayment half unit n A m).kappa)
    (inside : (LowerReplay.toBox (LowerContractor.initial slab)).Contains Interval.cppGrid t)
    (pass : LowerReplay.replay slab=true) :
    OldCondition (t 0) (t 1) (t 2) (t 3) ∨
    (∃ w : ℝ, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ 0 < weightedMargin (t 0) (t 1) (t 2) (t 3) w) ∨
    PairedDefectBound half inv24 unit n A m := by
  let roots := RealLowerPhysicalComparison.rootsOfDomain (t 0) (t 1) (t 2) (t 3)
    res.zNonnegative res.yNonnegative (by linarith only [res.xHead]) (by linarith only [cb.1,cb.2])
  exact RealLowerPhysicalComparison.checkedSlab slab t c roots res cb half inv24 third unit unit24 unit3
    n A m m0 orth chart n0 v0 positive
    (EndpointLargeGrams.largeSharedOnCorner half unit n A m orth n0 sharedLarge)
    (HighestAnchorCoefficient.physicalHighest half unit n A m orth) inside pass

private theorem highLeLarger (a b : ℝ) : b ≤ UpperWeighted.larger a b := by
  unfold UpperWeighted.larger
  split
  · assumption
  · exact le_refl _

set_option linter.constructorNameAsVariable false in
/-- All four accepted lower weighted shifts on the certified nonpositive-head
subregion, for every highest-pair Gram value. -/
theorem lowerWeighted (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ) (orth : OrthonormalFrame A)
    (z y x b c : ℝ) (res : LowerContractor.Residual z y x b) (cb : 1 ≤ c ∧ c ≤ b)
    (head : z*(x-1)-3*x-5/2 ≤ 0) (reserve : x^2 ≤ 5*z^2)
    (chart : (fun i => (m i)^2)=rawSpectrum z y x b c)
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (sharedLarge : 1 ≤ 24*(physicalPayment half unit n A m).kappa)
    (accepted : ∃ w : ℝ, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ 0 < weightedMargin z y x b w) :
    PairedDefectBound half inv24 unit n A m := by
  have shared := EndpointLargeGrams.largeSharedOnCorner half unit n A m orth n0 sharedLarge
  let E := physicalWeights half unit n A
  change UpperWeighted.larger (sharedExcess E) (highExcess E) ≤ 12*(physicalPayment half unit n A m).kappa at shared
  exact RealLowerWeighted.allWeightedWitnesses half inv24 third unit unit24 unit3 n A m orth z y x b c res cb
    head reserve chart n0 v0 ((highLeLarger _ _).trans shared)
    (HighestAnchorCoefficient.physicalHighest half unit n A m orth) accepted

end Lower

end RankSeven.RealPhysicalHighest

#print axioms RankSeven.RealPhysicalHighest.upperFrontier
#print axioms RankSeven.RealPhysicalHighest.lowerSlab
#print axioms RankSeven.RealPhysicalHighest.lowerWeighted
