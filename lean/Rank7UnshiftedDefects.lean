import Rank7PhysicalTailBlend

namespace RankSeven.UnshiftedDefects
open Lean.Grind Pauli
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalDefectAssembly (pairedState)
open PhysicalTailBlend (unshiftedDefects)

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

private theorem addNN (a b : R) (ha : 0≤a) (hb : 0≤b) : 0≤a+b := by grind only

theorem nonnegative (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (n : Nat) (A : Basis (n+3) → Fin 7 → ComplexScalar R) (m : Fin 7 → R)
    (orth : OrthonormalFrame A) : 0≤unshiftedDefects half inv24 n A m := by
  classical
  let S := pairedState A m
  let W := MixedDefect.oddWords (n+3)
  let K := PhysicalMixedFrame.K half S
  have herm : MixedDefect.Hermitian S := by
    intro i j
    exact (congrFun (congrFun (PhysicalDefectAssembly.pairedStateHermitian A m) j) i).symm
  have curvature (inst : DecidableEq (Word (n+3))) :
      letI := inst
      0≤MixedDefect.curvature W SymmetricDefect.anti K := by
    letI := inst
    rw [MixedDefect.curvatureEqSOS W (MixedDefect.oddWordsNodup _)
      SymmetricDefect.anti (fun i j => PauliEdgeBlocks.antiSymm j i) K
      (PhysicalMixedFrame.KHermitian half S herm)]
    exact OrderedRing.mul_nonneg (by grind only) (MixedDefect.edgeTriangleNonnegative W SymmetricDefect.anti K)
  have symm := PhysicalDefectAssembly.physicalSymmetricDefectNonnegative half inv24 unit unit24 n A m orth
  have power (j : Nat) : 0≤(2:R)^j := by
    induction j with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ j ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have lhs := OrderedRing.mul_nonneg (squareNonnegative ((2:R)^(n+3))) symm
  unfold unshiftedDefects
  dsimp only
  exact addNN _ _ lhs (OrderedRing.mul_nonneg
    (OrderedRing.mul_nonneg (show 0≤(4:R) by grind only) (power (n+3))) (curvature _))

end RankSeven.UnshiftedDefects

#print axioms RankSeven.UnshiftedDefects.nonnegative

