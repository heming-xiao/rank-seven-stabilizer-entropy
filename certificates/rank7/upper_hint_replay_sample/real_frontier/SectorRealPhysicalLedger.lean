import SectorDomainLedger
import Rank7RealPhysicalHighest

namespace RankSeven.SectorDomainLedger

open Pauli UpperContractor UpperCorner UpperReplay UpperDomainFrontier
open UpperFrameTrace UpperFrameGain RealUpperPhysicalComparison RealPhysicalHighest
open PackingPolynomial (physicalWeights)
open WeightedProbeShift (physicalPayment)
open PhysicalCompressionEffect (OrthonormalFrame)

attribute [local irreducible] physicalWeights physicalPayment PhysicalOutcome

set_option maxHeartbeats 300000 in
set_option linter.constructorNameAsVariable false in
/-- Every covered signed upper corner on this slab gives the paired-defect
comparison when the shared Gram meets its large-branch threshold. The
other scalar classifications and the nine unreplayed boxes remain explicit alternatives. -/
theorem physicalCornerOrFrontier (half inv24 third : ℝ)
    (unit : 2*half=1) (unit24 : 24*inv24=1) (unit3 : 3*third=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar ℝ) (m : Fin 7 → ℝ)
    (orth : OrthonormalFrame A) (m0 : ∀ i,0 ≤ m i) (z : Fin 5 → ℝ)
    (chart : (fun i => (m i)^2)=tail (UpperPhysicalInterior.spectrum (z 0) (z 1) (z 2)) (z 3) (z 4))
    (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (n0 : 0 ≤ sharedExcess (physicalWeights half unit n A))
    (v0 : 0 ≤ highExcess (physicalWeights half unit n A))
    (positive : 0 < sharedExcess (physicalWeights half unit n A)+highExcess (physicalWeights half unit n A))
    (sharedLarge : 1 ≤ 24*(physicalPayment half unit n A m).kappa)
    (inside : Here (initial 144 145) z) :
    PhysicalOutcome z half inv24 unit n A m ∨ OpenPoint remaining z := by
  have membership : (TailBox.toBox (initial 144 145)).Contains Interval.cppGrid z := by
    intro i
    have indices : ∀ j : Fin 5, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by decide
    rcases indices i with rfl|rfl|rfl|rfl|rfl
    · exact inside.hInside
    · exact inside.kInside
    · exact inside.qInside
    · exact inside.cInside
    · exact inside.dInside
  exact upperFrontier half inv24 third unit unit24 unit3 n A m orth m0 z chart res
    (UpperCertifiedFrameReplay.initialHeadFloor z membership)
    n0 v0 positive sharedLarge refined DomainSlab.initialValid DomainSlab.initialTail inside

end RankSeven.SectorDomainLedger

#print axioms RankSeven.SectorDomainLedger.physicalCornerOrFrontier
