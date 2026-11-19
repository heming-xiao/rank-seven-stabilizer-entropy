import Rank7PhysicalOddLeakage
import Rank7PhysicalTailBlend

/-! The actual anticommuting cut reserve and blended tail payment after
closing every odd-dimensional leakage condition. -/
namespace RankSeven.PhysicalOddTail
open Lean.Grind Pauli ComplexScalar JointProbeGram WeightedProbeShift PauliReserveSlots PhysicalTailBlend
open PhysicalDefectAssembly (frameDefects)
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliMatchingPrices (SortedSpectrum)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem rankSixCrossEveryOdd {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (r : Fin 7) (odd : (r.val+1)%2=1) :
    reserve half A (cut 5) (cut 5)≤12*reserve half A (cut 5) (cut r) :=
  OddCutReserve.rankSixCross half A orth r (PhysicalOddLeakage.physicalOddCut A orth r odd)

/-- Both cut reserves are paid on every orthonormal physical frame, with
no additional assumption on the Pauli words. -/
theorem physicalReserve (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    leadingCoefficient half third w*M.kappaOne+sixCoefficient half third w*betaSix half A≤2*reserve half A w w := by
  obtain ⟨h,j,l⟩ := PhysicalOddLeakage.physicalOddCuts A orth
  exact jointReserve half inv24 third h2 h24 h3 k A mu orth sorted h j l

/-- The signed tail alone admits the full six-mode coefficient on all
spectra, including arbitrarily small shared Gram, without rounding. -/
theorem fullySignedTail (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2)) (s t : R) (s0 : 0≤s) (t0 : 0≤t) :
    let w := fun i => (mu i)^2
    let psi := sixCoefficient half third w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+
      leadingCoefficient half third w*M.kappaOne+24*s*tailGap w*(3-W))-
      144*(s*tailGap w)^2*M.kappa≤psi*frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let tail := tailGap w
  let psi := sixCoefficient half third w
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let J := leadingCoefficient half third w*M.kappaOne
  let W := SixModeProbe.sixWedge half h2 A
  let F := frameDefects half inv24 k A mu
  have pos : 0≤psi := by
    have g (i : Fin 7) : 0≤(gap w i)^2 := squareNonnegative _
    have inner : 0≤6*(gap w 5)^2+(gap w 0)^2+(gap w 2)^2+(gap w 4)^2+(gap w 6)^2 := by
      have := g 0; have := g 2; have := g 4; have := g 5; have := g 6; grind only
    exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (show 0≤half by grind only) (show 0≤third by grind only))
      (OrderedRing.mul_nonneg (g 5) inner)
  have p := physicalBlend half inv24 third h2 h24 h3 k A mu orth sorted s t tail psi J 0 s0 t0 pos
    (physicalReserve half inv24 third h2 h24 h3 k A mu orth sorted) (show (tail-tail)*(M.sixMass-5)≤0 by grind only)
  change psi*(D+H+J-24*s*0+24*s*tail*(3-W))-144*(s*tail)^2*M.kappa≤psi*F at p
  change psi*(D+H+J+24*s*tail*(3-W))-144*(s*tail)^2*M.kappa≤psi*F; grind only

/-- A maximally general direct/signed blend from the direct linear
price on the same physical frame. -/
theorem sameFrameBlend (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t f rate : R) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1)
    (linear : (physicalPayment half h2 k A mu).sixMass-5≤rate*(physicalPayment half h2 k A mu).kappa) :
    let w := fun i => (mu i)^2
    let psi := sixCoefficient half third w
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W))-
      144*(s*(f*tail))^2*M.kappa≤psi*frameDefects half inv24 k A mu := by
  obtain ⟨h,j,l⟩ := PhysicalOddLeakage.physicalOddCuts A orth
  exact blendedTail half inv24 third h2 h24 h3 k A mu orth sorted h j l s t f rate s0 t0 f1 linear

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

/-- With all odd leakage proved, only the small-Gram sector witness is
needed for the normalized 200/11 blended tail. -/
theorem penaltyReceiptOfRounding (half inv24 third rate : F)
    (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (small : 200*(physicalPayment half h2 k A mu).kappa<11 →
      ∃ delta, Nonempty (SixPointRounding.RoundedSector half A delta) ∧ 411*delta≤378)
    (s t f : F) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1) (positive : 0<spectralPsi half third (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    unshiftedDefects half inv24 k A mu+(headReceipt half h2 k A mu s t+12*s^2*M.kappa)+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W)-
      12*s^2*quadraticPenalty half third w f*M.kappa≤frameDefects half inv24 k A mu := by
  obtain ⟨h,j,l⟩ := PhysicalOddLeakage.physicalOddCuts A orth
  exact physicalPenaltyReceipt half inv24 third rate h2 h24 h3 price200 k A mu orth sorted h j l small s t f s0 t0 f1 positive

/-- All blend fractions are certified on the large-Gram branch, without
a stabilizer-sector witness. -/
theorem largeGramPenaltyReceipt (half inv24 third rate : F)
    (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2)) (large : 11≤200*(physicalPayment half h2 k A mu).kappa)
    (s t f : F) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1) (positive : 0<spectralPsi half third (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    unshiftedDefects half inv24 k A mu+(headReceipt half h2 k A mu s t+12*s^2*M.kappa)+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W)-
      12*s^2*quadraticPenalty half third w f*M.kappa≤frameDefects half inv24 k A mu :=
  penaltyReceiptOfRounding half inv24 third rate h2 h24 h3 price200 k A mu orth sorted
    (fun h => False.elim (by grind only)) s t f s0 t0 f1 positive

end Field

end RankSeven.PhysicalOddTail

#print axioms RankSeven.PhysicalOddTail.rankSixCrossEveryOdd
#print axioms RankSeven.PhysicalOddTail.physicalReserve
#print axioms RankSeven.PhysicalOddTail.fullySignedTail
#print axioms RankSeven.PhysicalOddTail.sameFrameBlend
#print axioms RankSeven.PhysicalOddTail.penaltyReceiptOfRounding
#print axioms RankSeven.PhysicalOddTail.largeGramPenaltyReceipt

