import Rank7PhysicalExteriorPositivity
import Rank7ExteriorIsometry
import Rank7ExteriorCompressionEffect

namespace RankSeven.PhysicalCompressionEffect

open Lean.Grind Pauli Compression HyperplaneInduction PhysicalWedges
open ExteriorCuts (Wedge7 wedges product4 sharedLower amplitude error cutCost pos)
open ExteriorCompressionEffect (normalizedEntries normalizedExteriorEffect)
open PhysicalChartRestriction (weight)
open PhysicalExteriorCompression (physicalKernel inverseWeight inverseWeight_mul_weight)
open PhysicalExteriorCompression (wedgeRows)

variable {R : Type} [CommRing R]

/-- Orthonormality of the seven physical Schmidt columns in computational coordinates. -/
def OrthonormalFrame {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) : Prop :=
  ∀ i j, sumOver (qubitIndices n) (fun site => ComplexScalar.star (A site i) * A site j) =
    if i=j then 1 else 0

/-- The Hermitian matrix obtained directly from the physical Pauli kernel
and the signed minors of the seven input columns. -/
def physicalEntries (half : R) (halfUnit : 2*half = 1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) : HermitianEntries Wedge7 R :=
  normalizedEntries (coords (k+3)) (physicalKernel half)
    (PhysicalExteriorPositivity.physicalKernel_symmetric half halfUnit)
    (fun a w => minor4 A (wedgeRows a) w) (inverseWeight R k)

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem inverseWeightNonnegative (k : Nat) : 0 ≤ inverseWeight R k := by
  have two : 0 ≤ (2:R) := by grind
  have power (j : Nat) : 0 ≤ (2:R)^j := by
    induction j with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ j ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih two
  exact power (k+1)

/-- The normalized four-exterior compression in every dimension is a positive
contraction for any orthonormal seven-column frame. -/
theorem rankSevenPhysicalEffect (half : R) (halfUnit : 2*half = 1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    (physicalEntries half halfUnit k A).IsCoordinateEffect wedges := by
  apply normalizedExteriorEffect (coords (k+3)) wedgeRows (physicalKernel half)
    (PhysicalExteriorPositivity.physicalKernel_symmetric half halfUnit) A (inverseWeight R k)
    (weight half (k+3))
    (inverseWeightNonnegative k) (inverseWeight_mul_weight half halfUnit k)
  · intro v
    exact ExteriorIsometry.physicalNormIsometry (k+3) A orth v
  · intro v
    exact PhysicalExteriorPositivity.physicalKernel_nonnegative half halfUnit _ _
  · exact PhysicalExteriorCompression.rankSevenPauliKernelUpper half halfUnit k A

/-- The crossed spectral-cut loss inequality for the physical compression,
with no assumed positive-effect or row-slack inequality. -/
theorem rankSevenPhysicalCrossedCuts [DecidableRel (α := R) (· ≤ ·)]
    (half : R) (halfUnit : 2*half = 1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (s : Fin 7 → R) (nonnegative : ∀ i, 0 ≤ s i) (sorted : ∀ i j, i ≤ j → s j ≤ s i) :
    let entries := physicalEntries half halfUnit k A
    let sharedLo := sharedLower s
    let sharedHi := product4 s 0 2 5 6
    let fourthLo := product4 s 0 2 4 5
    let fourthHi := product4 s 0 1 5 6
    let a := amplitude s
    let w i := entries.realPart i i
    let slack := rowSlack wedges w entries.mass
    (pos (sharedHi-sharedLo))^2 * cutCost wedges (fun i => i.level.low) slack entries.mass +
    (pos (fourthHi-fourthLo))^2 * cutCost wedges (fun i => i.level.high) slack entries.mass -
      sumOver wedges (fun i =>
        ((if i.lowBad then error sharedLo sharedHi (a i) else 0) +
         (if i.highBad then error fourthLo fourthHi (a i) else 0)) * (w i*(1-w i))) ≤
      diagonalLoss wedges a w - entries.realQuadraticTrace wedges a :=
  effectRealLossControlsRankSevenCuts _ s half halfUnit nonnegative sorted
    (rankSevenPhysicalEffect half halfUnit k A orth)

end Order
end RankSeven.PhysicalCompressionEffect

#print axioms RankSeven.PhysicalCompressionEffect.rankSevenPhysicalEffect
#print axioms RankSeven.PhysicalCompressionEffect.rankSevenPhysicalCrossedCuts
