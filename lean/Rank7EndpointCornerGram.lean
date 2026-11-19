import Rank7EndpointLargeGrams

namespace RankSeven.EndpointLargeGrams

open Lean.Grind Pauli PackingPolynomial UpperFrameTrace
open PhysicalCompressionEffect (OrthonormalFrame)
open UpperEndpoint UpperPhysicalInterior
open WeightedProbeShift (physicalPayment)

variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

/-- The physical shared-trace cap reaches the sharp large-branch threshold
used for nonnegative shared excess on the corner chart. -/
theorem largeSharedOnCorner (half : F) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar F) (mu : Fin 7 → F) (orth : OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half h2 k A))
    (large : 1≤24*(physicalPayment half h2 k A mu).kappa) :
    let x := physicalWeights half h2 k A
    (trueRay (sharedExcess x) (highExcess x) 0 0).peak≤12*(physicalPayment half h2 k A mu).kappa := by
  let x := physicalWeights half h2 k A
  have shared := (physicalSharedTrace half h2 k A orth n0).1
  have high := UpperPairCap.physicalPairCap half h2 k A orth
  change 3*link x 0 1≤7 at high
  have cap : 3*highExcess x≤1 := by unfold highExcess; grind only
  change UpperWeighted.larger (sharedExcess x) (highExcess x)≤_
  unfold UpperWeighted.larger
  split <;> grind only

end RankSeven.EndpointLargeGrams

#print axioms RankSeven.EndpointLargeGrams.largeSharedOnCorner
