import Rank7PhysicalMixedDefect
import Rank7AntiDefectTransport

namespace RankSeven.PhysicalComparison

open Lean.Grind Pauli
open ExteriorCuts (amplitude)
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (physicalSectorTerms pairedState frameDefects PairedDefectBound)
open SectorDefectAccounting (exteriorGain compressionLoss)

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem frameDefectsNonnegative (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) : 0 ≤ frameDefects half inv24 k A mu := by
  have sym := PhysicalDefectAssembly.physicalSymmetricDefectNonnegative half inv24 unit unit24 k A mu orth
  have mixed := PhysicalMixedDefect.physicalMixedDefectNonnegative half inv24 unit unit24 k A mu orth
  have anti := AntiDefectTransport.physicalAnticommutingDefectNonnegative half inv24 unit unit24 k A mu orth
  have half0 : 0 ≤ half := by grind
  have power (n : Nat) : 0 ≤ half^n := by
    induction n with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih half0
  have symPaid := OrderedRing.mul_nonneg (squareNonnegative ((2:R)^(k+3))) sym
  have mixedPaid := OrderedRing.mul_nonneg (squareNonnegative ((2:R)^(k+3))) mixed
  have antiPaid := OrderedRing.mul_nonneg (power (k+3)) anti
  unfold frameDefects SectorDefectAccounting.totalDefect
  dsimp only
  grind only

/-- A paired frame with nonpositive exterior gain satisfies the full
comparison against the computational representative. This uses actual
nonnegativity of all three Pauli defects and the compression loss. -/
theorem pairedPurityLeOfNonpositiveGain (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (gain : exteriorGain (amplitude mu) (physicalEntries half unit k A) ≤ 0) :
    PhysicalPairedReduction.purity half (pairedState A mu) ≤
      PhysicalPairedReduction.purity half (RectangularPairedReduction.computationalCoefficients k k mu) := by
  have diff := PhysicalDefectAssembly.pairedPurityComputationalDifference half inv24 unit unit24 k A mu
  dsimp only at diff
  have defect := frameDefectsNonnegative half inv24 unit unit24 k A mu orth
  have exteriorLoss := SectorDefectAccounting.physicalLossNonnegative half unit k A orth (amplitude mu)
  grind only

/-- When the exterior compression already pays the gain, the three
nonnegative Pauli defects complete the exact scalar comparison. -/
theorem compareOfCompression (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A)
    (paid : 168*exteriorGain (amplitude mu) (physicalEntries half unit k A) ≤
      96*compressionLoss (amplitude mu) (physicalEntries half unit k A)) :
    PairedDefectBound half inv24 unit k A mu := by
  have rest := frameDefectsNonnegative half inv24 unit unit24 k A mu orth
  unfold PairedDefectBound
  grind only

end RankSeven.PhysicalComparison

#print axioms RankSeven.PhysicalComparison.frameDefectsNonnegative
#print axioms RankSeven.PhysicalComparison.pairedPurityLeOfNonpositiveGain
#print axioms RankSeven.PhysicalComparison.compareOfCompression
