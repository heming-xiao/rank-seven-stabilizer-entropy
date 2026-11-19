import Rank7OddCutReserve
import Rank7SixPointRounding

/-! The six-mode blend on the physical frame, including the common Pauli
Gram, anticommuting reserve, and the full S4 defect. -/
namespace RankSeven.PhysicalTailBlend
open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram WeightedProbeShift PauliReserveSlots
open SymmetricDefect (anti)
open PhysicalDefectAssembly (frameDefects pairedState physicalSectorTerms)
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliMatchingPrices (SortedSpectrum)
open OddCutReserve (PairLeakage)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def betaSix {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :=
  let z := densityCoordinates half A (cut 5)
  2*hs (MixedDefect.oddWords n) z z

noncomputable def unshiftedDefects (half inv24 : R) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :=
  let d := (2:R)^(k+3)
  d^2*SectorDefectAccounting.symmetricDefect (half^(k+3)) (physicalSectorTerms half inv24 k A mu)+
    4*d*MixedDefect.curvature (MixedDefect.oddWords (k+3)) anti (PhysicalMixedFrame.K half (pairedState A mu))

/-- Shared/highest matching receipt before charging the six-point excess. -/
def headReceipt (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (s t : R) :=
  let w := fun i => (mu i)^2
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w (fun j => E.realPart j j)
  let M := physicalPayment half h2 k A mu
  24*s*(W 1+W 2-referenceShared w+sharedGap w*M.kappa+leadingGap w*M.cross+emptyGap w*M.emptyMass)+
    24*t*M.highest-12*s^2*M.kappa-12*t^2*M.kappaOne-24*s*t*M.cross

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem headReceiptIdentity (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (s t : R) :
    let M := physicalPayment half h2 k A mu
    headReceipt half h2 k A mu s t=M.receipt s t+24*s*tailGap (fun i => (mu i)^2)*(M.sixMass-5) := by
  dsimp only [headReceipt,physicalPayment,Payment.receipt]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem gramSquare {α : Type} (xs : List α) (U Z : α×α → R) (a b : R) :
    hs xs (fun e => a*U e+b*Z e) (fun e => a*U e+b*Z e)=
    a^2*hs xs U U+b^2*hs xs Z Z+2*a*b*hs xs U Z := by
  unfold hs; have add (e : α×α) : (a*U e+b*Z e)*(a*U e+b*Z e)=
      a^2*(U e*U e)+b^2*(Z e*Z e)+(2*a*b)*(U e*Z e) := by grind only
  rw [sumOverCongr _ add]; simp only [sumOverAdd,←sumOverMulLeft]; grind only

/-- The physical rank-six square pays the shared matching excess. Its
exact remainder is a single nonnegative Hilbert–Schmidt norm. -/
theorem signedPrice (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (v psi : R) :
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(24*v*(M.sixMass-2-W))≤psi^2*betaSix half A+144*v^2*M.kappa := by
  let M := physicalPayment half h2 k A mu
  let W := SixModeProbe.sixWedge half h2 A
  let xs := MixedDefect.oddWords (k+3)
  let U := sharedProbe half A
  let Z := densityCoordinates half A (cut 5)
  have square := hsNonnegative xs (fun e => (12*v)*U e+psi*Z e)
  rw [gramSquare] at square
  have gram := (physicalJointGram half third h2 h3 k A orth).1
  change 2*hs xs U U=M.kappa at gram
  have pol := SixModeProbe.sixPolarization half third h2 h3 k A mu orth
  change 2*hs xs U Z=2+W-M.sixMass at pol
  have gp := congrArg (fun z => 144*v^2*z) gram
  have pp := congrArg (fun z => 24*v*psi*z) pol
  change psi*(24*v*(M.sixMass-2-W))≤psi^2*(2*hs xs Z Z)+144*v^2*M.kappa
  grind only

/-- One physical defect, one allocation of the Pauli reserve, and a split
of the shared tail between the direct price and the signed rank-six Gram. -/
theorem physicalBlend (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t K psi retained directPrice : R) (s0 : 0≤s) (t0 : 0≤t) (p0 : 0≤psi)
    (reservePay : retained+psi*betaSix half A≤2*reserve half A (fun i => (mu i)^2) (fun i => (mu i)^2))
    (direct : (tailGap (fun i => (mu i)^2)-K)*((physicalPayment half h2 k A mu).sixMass-5)≤directPrice) :
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+retained-
      24*s*directPrice+24*s*K*(3-W))-144*(s*K)^2*M.kappa ≤ psi*frameDefects half inv24 k A mu := by
  let M := physicalPayment half h2 k A mu
  let w := fun i => (mu i)^2
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let W := SixModeProbe.sixWedge half h2 A
  let F := frameDefects half inv24 k A mu
  let J := reserve half A w w
  let B := betaSix half A
  have recpt := physicalDefectReceipt half inv24 third h2 h24 h3 k A mu orth sorted s t s0 t0
  rw [sameSlot] at reservePay
  change D+2*(half^(k+3))^2*(PhysicalAntiQuartic.antiMass
    (SymmetricDefect.traceWord imaginaryUnit (pairedState A w))).re+M.receipt s t≤F at recpt
  change retained+psi*B≤2*((half^(k+3))^2*(PhysicalAntiQuartic.antiMass
    (SymmetricDefect.traceWord imaginaryUnit (pairedState A w))).re) at reservePay
  have lower : D+retained+psi*B+M.receipt s t≤F := by grind only
  have pay := OrderedRing.mul_le_mul_of_nonneg_left lower p0
  have hd := headReceiptIdentity half h2 k A mu s t
  change H=M.receipt s t+24*s*tailGap w*(M.sixMass-5) at hd
  have hd' := congrArg (fun y => psi*y) hd
  have sq := signedPrice half third h2 h3 k A mu orth (s*K) psi
  change psi*(24*(s*K)*(M.sixMass-2-W))≤psi^2*B+144*(s*K)^2*M.kappa at sq
  have price := OrderedRing.mul_le_mul_of_nonneg_left direct
    (OrderedRing.mul_nonneg p0 (show 0≤24*s by grind only))
  change (psi*(24*s))*((tailGap w-K)*(M.sixMass-5))≤psi*(24*s)*directPrice at price
  change psi*(D+H+retained-24*s*directPrice+24*s*K*(3-W))-144*(s*K)^2*M.kappa≤psi*F
  grind only

def leadingCoefficient (half third : R) (w : Fin 7 → R) :=
  let g := gap w
  half*third*(6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2))

def sixCoefficient (half third : R) (w : Fin 7 → R) :=
  let g := gap w
  half*third*((g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2))

private theorem sixCoefficientNonnegative (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (w : Fin 7 → R) :
    0≤sixCoefficient half third w := by
  let g := gap w
  have z (i : Fin 7) : 0≤(g i)^2 := squareNonnegative _
  have term := OrderedRing.mul_nonneg (z 5) (show 0≤6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2 by
    have := z 0; have := z 2; have := z 4; have := z 5; have := z 6; grind only)
  exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (show 0≤half by grind only) (show 0≤third by grind only)) term

/-- Leading-pair and six-mode prices use the same anticommuting mass. -/
theorem jointReserve (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    leadingCoefficient half third w*M.kappaOne+sixCoefficient half third w*betaSix half A≤2*reserve half A w w := by
  let w := fun i => (mu i)^2
  let g := gap w
  let m := (physicalPayment half h2 k A mu).kappaOne
  let b := betaSix half A
  let j := reserve half A w w
  let c := 6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2)
  let d := (g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)
  have h := OddCutReserve.physicalOddPayments half inv24 third h2 h24 h3 k A mu orth sorted three five seven
  change c*m+d*b≤12*j at h
  have h6 := congrArg (fun x => x*(3*third)) h2
  have norm : 6*(half*third)=1 := by grind only
  have v := OrderedRing.mul_le_mul_of_nonneg_left h (OrderedRing.mul_nonneg (show 0≤half by grind only) (show 0≤third by grind only))
  have pay := congrArg (fun x => 2*j*x) norm
  change half*third*c*m+half*third*d*b≤2*j; grind only

private theorem tailNonnegative (mu : Fin 7 → R) (sort : SortedSpectrum (fun i => (mu i)^2)) :
    0≤tailGap (fun i => (mu i)^2) := by
  apply OrderedRing.mul_nonneg (squareNonnegative _)
  have e := sort.2.2.2.2.2.1
  change (mu 6)^2≤(mu 5)^2 at e; grind only

/-- Denominator-cleared physical receipt. The tail shift fT retains the
six-mode wedge slack. The direct fraction 1-f uses the same frame's
linear six-point price. -/
theorem blendedTail (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6)
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
  let w := fun i => (mu i)^2
  let tail := tailGap w
  let M := physicalPayment half h2 k A mu
  have c := OrderedRing.mul_nonneg (show 0≤1-f by grind only) (tailNonnegative mu sorted)
  have v := OrderedRing.mul_le_mul_of_nonneg_left linear c
  change ((1-f)*tail)*(M.sixMass-5)≤((1-f)*tail)*(rate*M.kappa) at v
  apply physicalBlend half inv24 third h2 h24 h3 k A mu orth sorted s t (f*tail) (sixCoefficient half third w)
    (leadingCoefficient half third w*M.kappaOne) ((1-f)*tail*rate*M.kappa) s0 t0 (sixCoefficientNonnegative half third h2 h3 w)
    (jointReserve half inv24 third h2 h24 h3 k A mu orth sorted three five seven)
  change (tail-f*tail)*(M.sixMass-5)≤(1-f)*tail*rate*M.kappa; grind only

/-- The manuscript's uniform 200/11 version. The only remaining physical
inputs are unit leakage on the three odd cuts of rank greater than one
and the existence of the weakly rounded odd-Pauli sector for small κ. -/
theorem physicalBlendedTailReceipt (half inv24 third rate : R)
    (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6)
    (small : 200*(physicalPayment half h2 k A mu).kappa<11 →
      ∃ delta, Nonempty (SixPointRounding.RoundedSector half A delta) ∧ 411*delta≤378)
    (s t f : R) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1) :
    let w := fun i => (mu i)^2
    let psi := sixCoefficient half third w
    let tail := tailGap w
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+
      leadingCoefficient half third w*M.kappaOne-24*s*((1-f)*tail*rate*M.kappa)+24*s*(f*tail)*(3-W))-
      144*(s*(f*tail))^2*M.kappa≤psi*frameDefects half inv24 k A mu := by
  apply blendedTail half inv24 third h2 h24 h3 k A mu orth sorted three five seven s t f rate s0 t0 f1
  let M := physicalPayment half h2 k A mu
  have e := SixPointRounding.uniformSixPriceCoarse half h2 k A mu orth small
  change 11*M.sixMass≤55+200*M.kappa at e
  have r := congrArg (fun a => a*M.kappa) price200
  change M.sixMass-5≤rate*M.kappa; grind only

/-- A fully physical signed-tail receipt using the two diagonal cut slots.
It applies to every sorted spectrum and has no rounding or odd-cut premise. -/
theorem unconditionalSignedTail (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t : R) (s0 : 0≤s) (t0 : 0≤t) :
    let w := fun i => (mu i)^2
    let psi := (gap w 5)^4
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    psi*(unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+
      (gap w 1)^4*M.kappaOne+24*s*tailGap w*(3-W))-
      144*(s*tailGap w)^2*M.kappa≤psi*frameDefects half inv24 k A mu := by
  let M := physicalPayment half h2 k A mu
  let w := fun i => (mu i)^2
  let T := tailGap w
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let L := (gap w 1)^4*M.kappaOne
  let psi := (gap w 5)^4
  let W := SixModeProbe.sixWedge half h2 A
  let F := frameDefects half inv24 k A mu
  have pos : 0≤psi := by have r := squareNonnegative ((gap w 5)^2); unfold psi; grind only
  have h := physicalBlend half inv24 third h2 h24 h3 k A mu orth sorted s t T psi L 0 s0 t0 pos
    (ReserveMixedNorm.twoDiagonalPayments half inv24 third h2 h24 h3 k A mu orth sorted)
    (show (T-T)*(M.sixMass-5)≤0 by grind only)
  change psi*(D+H+L-24*s*0+24*s*T*(3-W))-144*(s*T)^2*M.kappa≤psi*F at h
  change psi*(D+H+L+24*s*T*(3-W))-144*(s*T)^2*M.kappa≤psi*F; grind only

/-- The exact linear receipt when the spectral tail is flat. -/
theorem flatTailReceipt (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (s t retained : R) (s0 : 0≤s) (t0 : 0≤t) (flat : tailGap (fun i => (mu i)^2)=0)
    (reservePay : retained≤2*reserve half A (fun i => (mu i)^2) (fun i => (mu i)^2)) :
    unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+retained≤frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let F := frameDefects half inv24 k A mu
  let c := (PhysicalAntiQuartic.antiMass (SymmetricDefect.traceWord imaginaryUnit (pairedState A w))).re
  have a := headReceiptIdentity half h2 k A mu s t
  change H=M.receipt s t+24*s*tailGap w*(M.sixMass-5) at a
  change tailGap w=0 at flat; rw [flat] at a
  rw [sameSlot] at reservePay
  change retained≤2*((half^(k+3))^2*c) at reservePay
  have d := physicalDefectReceipt half inv24 third h2 h24 h3 k A mu orth sorted s t s0 t0
  change D+2*(half^(k+3))^2*c+M.receipt s t≤F at d
  change D+H+retained≤F; grind only

def spectralPsi (half third : R) (w : Fin 7 → R) :=
  let g := gap w
  (g 5)^2+half*third*((g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem spectralFactor (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (w : Fin 7 → R) :
    sixCoefficient half third w=(gap w 5)^2*spectralPsi half third w ∧ tailGap w=w 4*gap w 5 := by
  have h := congrArg (fun z => z*(3*third)) h2
  have n : 6*(half*third)=1 := by grind only
  have m := congrArg (fun z => z*(gap w 5)^4) n
  exact ⟨by unfold sixCoefficient spectralPsi; grind only,rfl⟩

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

def quadraticPenalty (half third : F) (w : Fin 7 → F) (f : F) :=
  1+12*f^2*(w 4)^2/spectralPsi half third w

/-- Field form of the physical four-tuple blend, including a flat sixth
gap. The shared Gram debit is exactly 12 s² Q κ. -/
theorem physicalPenaltyReceipt (half inv24 third rate : F)
    (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (price200 : 11*rate=200)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F)
    (orth : OrthonormalFrame A) (sorted : SortedSpectrum (fun i => (mu i)^2))
    (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6)
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
  let w := fun i => (mu i)^2
  let e := gap w 5
  let tail := tailGap w
  let cap := spectralPsi half third w
  let psi := sixCoefficient half third w
  let m := physicalPayment half h2 k A mu
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let L := leadingCoefficient half third w*m.kappaOne
  let W := SixModeProbe.sixWedge half h2 A
  let T := frameDefects half inv24 k A mu
  let B := betaSix half A
  let Q := quadraticPenalty half third w f
  let V := D+(H+12*s^2*m.kappa)+L-24*s*((1-f)*tail*rate*m.kappa)+24*s*(f*tail)*(3-W)-12*s^2*Q*m.kappa
  change V≤T
  have unit := Field.mul_inv_cancel (show cap≠0 by change 0<cap at positive; grind only)
  have factor := spectralFactor half third h2 h3 w
  change psi=e^2*cap ∧ tail=w 4*e at factor
  have product : cap*(Q-1)=12*f^2*(w 4)^2 := by
    unfold Q quadraticPenalty; change cap*((1+12*f^2*(w 4)^2/cap)-1)=_
    rw [Field.div_eq_mul_inv]; grind only
  have nQ : 0≤Q-1 := by
    have n := OrderedRing.mul_nonneg (squareNonnegative f) (squareNonnegative (w 4))
    apply Classical.byContradiction; intro no
    have a := OrderedRing.mul_pos positive (show 0< -(Q-1) by grind only)
    grind only
  have gm := (physicalJointGram half third h2 h3 k A orth).1
  let xs := MixedDefect.oddWords (k+3)
  let U := sharedProbe half A
  change 2*hs xs U U=m.kappa at gm
  have kp : 0≤m.kappa := by have z := hsNonnegative xs U; grind only
  by_cases ze : e=0
  · have flat : tail=0 := by rw [factor.2,ze]; grind only
    have paid := jointReserve half inv24 third h2 h24 h3 k A mu orth sorted three five seven
    change L+psi*B≤2*reserve half A w w at paid
    have zpsi : psi=0 := by rw [factor.1,ze]; grind only
    rw [zpsi] at paid
    have r := flatTailReceipt half inv24 third h2 h24 h3 k A mu orth sorted s t L s0 t0 flat (by grind only)
    change D+H+L≤T at r
    have m' := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (squareNonnegative s) nQ) kp
    unfold V; rw [flat]; grind only
  · have ep : 0<e^2 := by
      have pos := squareNonnegative e
      by_cases g : 0<e
      · have z := OrderedRing.mul_pos g g; grind only
      · have neg : 0< -e := by grind only
        have z := OrderedRing.mul_pos neg neg; grind only
    have pp : 0<psi := factor.1 ▸ OrderedRing.mul_pos ep positive
    have paid := physicalBlendedTailReceipt half inv24 third rate h2 h24 h3 price200 k A mu orth sorted three five seven small s t f s0 t0 f1
    change psi*(D+H+L-24*s*((1-f)*tail*rate*m.kappa)+24*s*(f*tail)*(3-W))-
      144*(s*(f*tail))^2*m.kappa≤psi*T at paid
    have id : psi*(Q-1)=12*(f*tail)^2 := by rw [factor.1,factor.2]; grind only
    have eq := congrArg (fun z => 12*s^2*m.kappa*z) id
    have v : psi*V≤psi*T := by unfold V; grind only
    apply Classical.byContradiction; intro no
    have h := OrderedRing.mul_lt_mul_of_pos_left (show T<V by grind only) pp; grind only
end Field

end RankSeven.PhysicalTailBlend

#print axioms RankSeven.PhysicalTailBlend.headReceiptIdentity
#print axioms RankSeven.PhysicalTailBlend.signedPrice
#print axioms RankSeven.PhysicalTailBlend.physicalBlend
#print axioms RankSeven.PhysicalTailBlend.jointReserve
#print axioms RankSeven.PhysicalTailBlend.blendedTail
#print axioms RankSeven.PhysicalTailBlend.physicalBlendedTailReceipt
#print axioms RankSeven.PhysicalTailBlend.unconditionalSignedTail
#print axioms RankSeven.PhysicalTailBlend.flatTailReceipt
#print axioms RankSeven.PhysicalTailBlend.spectralFactor
#print axioms RankSeven.PhysicalTailBlend.physicalPenaltyReceipt

