import AxisPhysicalLedger
import Rank7UpperCertifiedFrameReplay

namespace RankSeven.AxisDomainLedger

open Lean.Grind Interval UpperContractor UpperReplay UpperCorner
open UpperDomainFrontier DomainFrontierFrame UpperFrameTrace
open PackingPolynomial (physicalWeights physicalRows)

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

theorem certifiedSlabOrFrontier (z : Fin 5→R)
    (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A))
    (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (inside : Here (initial 144 145) z) : FrameOutcome z half unit k A ∨ OpenPoint remaining z := by
  have inBox : (TailBox.toBox (initial 144 145)).Contains cppGrid z := by
    intro i
    have cases : ∀ j : Fin 5, j=0∨j=1∨j=2∨j=3∨j=4 := by decide
    rcases cases i with rfl|rfl|rfl|rfl|rfl
    · exact inside.hInside
    · exact inside.kInside
    · exact inside.qInside
    · exact inside.cInside
    · exact inside.dInside
  have qFloor := UpperCertifiedFrameReplay.initialHeadFloor z inBox
  obtain ⟨nx,rows⟩ := physicalRows half unit k A orth
  exact actualSlabOrFrontier z res half unit k A orth n0 v0 positive
    (fun _ contained domain => UpperCertifiedExterior.exteriorEstimates res qFloor contained domain _ nx rows n0 v0)
    inside

end RankSeven.AxisDomainLedger

#print axioms RankSeven.AxisDomainLedger.certifiedSlabOrFrontier
