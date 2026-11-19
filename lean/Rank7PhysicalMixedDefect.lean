import Rank7PhysicalMixedSpectrum
import Rank7PauliEdgeBlocks
import Rank7MixedTransport

namespace RankSeven.PhysicalMixedDefect

open Lean.Grind Pauli
open SymmetricDefect (anti)
open PauliEdgeBlocks (antiSymm)
open PhysicalDefectAssembly (pairedState physicalSectorTerms rawSectorTrace wedgeSectorTrace rawAlternatingTransport)
open PhysicalCompressionEffect (OrthonormalFrame)
open MixedDefect (oddWords frameProjection realTrace square hadamard)

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem physicalMixedTraceSum (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let s := physicalSectorTerms half inv24 k A mu
    let xs := oddWords (k+3)
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    s.mixed+s.alternating = realTrace xs (square xs (hadamard K)) := by
  let n := k+3
  let xs := oddWords n
  let K := PhysicalMixedFrame.K half (pairedState A mu)
  let traceB := realTrace xs (square xs (hadamard K))
  have sum := PhysicalMixedFrame.physicalMixedPlusAlternating half inv24 unit24 A mu
  change (half^n)^2*(rawSectorTrace half A mu .antisymmetric + rawSectorTrace half A mu .mixedEven) =
    24*traceB at sum
  rw [rawAlternatingTransport half unit] at sum
  change half^(n+n)*inv24*rawSectorTrace half A mu .mixedEven + half^(n+n)*wedgeSectorTrace half A mu = traceB
  rw [Semiring.pow_add]
  have scaled := congrArg (fun x => inv24*x) sum
  change inv24*((half^n)^2*(24*wedgeSectorTrace half A mu + rawSectorTrace half A mu .mixedEven)) =
    inv24*(24*traceB) at scaled
  grind only

theorem physicalMixedCertificateFromTraces (half inv24 third : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (unit3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A)
    (alternating :
      let n := k+3
      let xs := oddWords n
      let K := PhysicalMixedFrame.K half (pairedState A mu)
      let P := frameProjection ((2:R)^n) (half^n) third anti
      realTrace xs (matMul xs P (square xs (hadamard K))) =
        (physicalSectorTerms half inv24 k A mu).alternating)
    (overlap :
      let n := k+3
      let xs := oddWords n
      let K := PhysicalMixedFrame.K half (pairedState A mu)
      let P := frameProjection ((2:R)^n) (half^n) third anti
      realTrace xs (matMul xs P (hadamard (square xs K))) =
        (physicalSectorTerms half inv24 k A mu).overlap) :
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let xs := oddWords (k+3)
    SectorDefectAccounting.mixedDefect (half^(k+3)) (physicalSectorTerms half inv24 k A mu) =
      4*half^(k+3)*MixedDefect.curvature xs anti K +
        32*(half^(k+3))^2*MixedDefect.linearResidual xs anti K := by
  let n := k+3
  let d := (2:R)^n
  let di := half^n
  let xs := oddWords n
  let K := PhysicalMixedFrame.K half (pairedState A mu)
  let P := frameProjection d di third (anti (n:=n))
  let s := physicalSectorTerms half inv24 k A mu
  have hs : MixedDefect.Hermitian (pairedState A mu) := by
    intro i j
    exact (congrFun (congrFun (PhysicalDefectAssembly.pairedStateHermitian A mu) j) i).symm
  have herm := PhysicalMixedFrame.KHermitian half (pairedState A mu) hs
  have inverse := SectorDefectAccounting.dimensionInverse half unit n
  have core := MixedDefect.mixedDefectEqSOS xs (MixedDefect.oddWordsNodup n) d di third inverse unit3
    anti (fun i j => antiSymm j i) K herm s
  change SectorDefectAccounting.mixedDefect di s =
    4*di*MixedDefect.curvature xs anti K+32*di^2*MixedDefect.linearResidual xs anti K
  change realTrace xs (matMul xs P (square xs (hadamard K)))=s.alternating at alternating
  change realTrace xs (matMul xs P (hadamard (square xs K)))=s.overlap at overlap
  have wedge : realTrace xs (square xs (square xs K))=s.wedgeFourth :=
    PhysicalMixedSpectrum.fourthTraceEqSpectrum half unit A mu orth
  have mix := physicalMixedTraceSum half inv24 unit unit24 k A mu
  change s.mixed+s.alternating=realTrace xs (square xs (hadamard K)) at mix
  unfold SectorDefectAccounting.mixedDefect MixedDefect.frameTerms at core
  dsimp only at core
  rw [alternating,overlap,wedge,←mix] at core
  unfold SectorDefectAccounting.mixedDefect
  grind only

/-- Physical mixed-sector defect, with every matrix trace identified on
the actual Pauli frame and no transport premises. -/
theorem physicalMixedDefectEqSquares (half inv24 : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let xs := oddWords (k+3)
    SectorDefectAccounting.mixedDefect (half^(k+3)) (physicalSectorTerms half inv24 k A mu) =
      4*half^(k+3)*MixedDefect.curvature xs anti K +
        32*(half^(k+3))^2*MixedDefect.linearResidual xs anti K := by
  let third := 8*inv24
  have unit3 : 3*third=1 := by unfold third; grind only
  exact physicalMixedCertificateFromTraces half inv24 third unit unit24 unit3 k A mu orth
    (MixedTransport.physicalAlternatingPrice half inv24 third unit unit24 unit3 k A mu)
    (MixedTransport.physicalOverlapPrice half inv24 third unit unit24 unit3 k A mu orth)

theorem physicalMixedDefectNonnegative (half inv24 : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    0 ≤ SectorDefectAccounting.mixedDefect (half^(k+3)) (physicalSectorTerms half inv24 k A mu) := by
  rw [physicalMixedDefectEqSquares half inv24 unit unit24 k A mu orth]
  have nonnegativeHalf : 0 ≤ half := by grind
  have power (j : Nat) : 0 ≤ half^j := by
    induction j with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ j ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih nonnegativeHalf
  let K := PhysicalMixedFrame.K half (pairedState A mu)
  let xs := oddWords (k+3)
  have herm : MixedDefect.Hermitian (pairedState A mu) := by
    intro i j
    exact (congrFun (congrFun (PhysicalDefectAssembly.pairedStateHermitian A mu) j) i).symm
  rw [MixedDefect.curvatureEqSOS xs (MixedDefect.oddWordsNodup _) anti (fun i j => antiSymm j i)
    K (PhysicalMixedFrame.KHermitian half _ herm)]
  have first := OrderedRing.mul_nonneg (power (k+3)) (MixedDefect.edgeTriangleNonnegative xs anti K)
  have second := OrderedRing.mul_nonneg (squareNonnegative (half^(k+3)))
    (MixedDefect.linearResidualNonnegative xs anti K)
  grind only

end RankSeven.PhysicalMixedDefect

#print axioms RankSeven.PhysicalMixedDefect.physicalMixedTraceSum
#print axioms RankSeven.PhysicalMixedDefect.physicalMixedCertificateFromTraces
#print axioms RankSeven.PhysicalMixedDefect.physicalMixedDefectEqSquares
#print axioms RankSeven.PhysicalMixedDefect.physicalMixedDefectNonnegative
