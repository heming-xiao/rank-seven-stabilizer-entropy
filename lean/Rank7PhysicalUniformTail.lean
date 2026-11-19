import Rank7PhysicalProjectionAngles
import Rank7PhysicalOddTail

namespace RankSeven.PhysicalUniformTail
open Lean.Grind Pauli ComplexScalar JointProbeGram WeightedProbeShift PauliReserveSlots PhysicalTailBlend
open PhysicalDefectAssembly (frameDefects)
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliMatchingPrices (SortedSpectrum)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The denominator-cleared normalized blend for every orthonormal frame and sorted spectrum. -/
theorem uniformBlend (half inv24 third rate : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t f : R) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1) :
    let w := fun i => (mu i)^2
    let psi := sixCoefficient half third w
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W))-
      144*(s*(f*tail))^2*M.kappa≤psi*frameDefects half inv24 k A mu := by
  apply PhysicalOddTail.sameFrameBlend half inv24 third h2 h24 h3 k A mu orth sorted s t f rate s0 t0 f1
  let M := physicalPayment half h2 k A mu
  have q := PhysicalProjectionAngles.uniformPhysicalSixPrice half h2 k A mu orth
  change 11*M.sixMass≤55+200*M.kappa at q
  have scaled := congrArg (fun r : R => r*M.kappa) price200
  change M.sixMass-5≤rate*M.kappa; grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

/-- The corresponding physical quadratic penalty at a positive spectral denominator. -/
theorem uniformPenaltyReceipt (half inv24 third rate : F)
    (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t f : F) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1) (positive : 0<spectralPsi half third (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    unshiftedDefects half inv24 k A mu+(headReceipt half h2 k A mu s t+12*s^2*M.kappa)+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W)-
      12*s^2*quadraticPenalty half third w f*M.kappa≤frameDefects half inv24 k A mu :=
  PhysicalOddTail.penaltyReceiptOfRounding half inv24 third rate h2 h24 h3 price200 k A mu orth sorted
    (fun small => PhysicalProjectionAngles.physicalRoundedSector half h2 k A mu orth (Std.le_of_lt small)) s t f s0 t0 f1 positive

end Field

end RankSeven.PhysicalUniformTail

#print axioms RankSeven.PhysicalUniformTail.uniformBlend
#print axioms RankSeven.PhysicalUniformTail.uniformPenaltyReceipt

