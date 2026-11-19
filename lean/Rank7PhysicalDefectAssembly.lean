import Rank7FourCopySectors
import Rank7FrameExteriorSector
import Rank7SectorDefectAccounting
import Rank7AlternatingTrace
import Rank7ComputationalPurity
import Rank7ComputationalExterior
import Rank7SymmetricDefect

namespace RankSeven.PhysicalDefectAssembly

open Lean.Grind Pauli PhysicalPairedReduction RectangularPairedReduction
open ExteriorCuts (Wedge7 wedges amplitude)
open ComplexScalar (ofReal imaginaryUnit)
open FourCopySectors (Sector rawBlock)
open SectorDefectAccounting (SectorTerms normOverlap normAlt)
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open FrameExteriorSector (exteriorSector effectEntry)
open ComplexPauliMoment (conjugate)

variable {R : Type} [CommRing R]

def pairedState {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    Basis n → Basis n → ComplexScalar R :=
  rankSevenCoefficients A (conjugate A) mu

/-- The density used by the fourth Pauli moment, with eigenvalues μ². -/
def pairedDensity {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    Basis n → Basis n → ComplexScalar R :=
  pairedState A (fun i => (mu i)^2)

def pauliDensityFourth {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) : R :=
  sumOver (words n) (fun p =>
    (trace (qubitIndices n) (matMul (qubitIndices n) (wordEntry imaginaryUnit p) (pairedDensity A mu))).re^4)

def rawSectorTrace {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (s : Sector) : R :=
  let H := tensorFour (diagonal mu)
  let F := normalizedFrame half A
  (pairedFrameTrace (fourIndices (List.finRange 7)) H (rawBlock s F) F).re

def wedgeSectorTrace {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) : R :=
  let H := diagonal (amplitude mu)
  let F := exteriorSector (normalizedFrame half A)
  (pairedFrameTrace wedges H F F).re

def wedgeOverlapTrace {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) : R :=
  let F := exteriorSector (normalizedFrame half A)
  sumOver wedges (fun w => (amplitude mu w)^2 * (F w w).re)

/-- The exact sector quantities, with their ambient-dimension factors. -/
def physicalSectorTerms (half invTwentyFour : R) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) : SectorTerms R where
  symmetric := half^((k+3)+(k+3)) * invTwentyFour * rawSectorTrace half A mu .symmetric
  mixed := half^((k+3)+(k+3)) * invTwentyFour * rawSectorTrace half A mu .mixedEven
  alternating := half^((k+3)+(k+3)) * wedgeSectorTrace half A mu
  overlap := half^(k+3) * wedgeOverlapTrace half A mu
  pauliFourth := pauliDensityFourth A mu
  wedgeFourth := sumOver (SectorDefectAccounting.wedgePairs (List.finRange 7))
    (fun ij => (mu ij.1 * mu ij.2)^4)

theorem pairedStateHermitian {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    dagger (pairedState A mu) = pairedState A mu := by
  funext a b
  change ComplexScalar.star (rankSevenCoefficients A (conjugate A) mu b a) =
    rankSevenCoefficients A (conjugate A) mu a b
  unfold rankSevenCoefficients
  rw [ComplexExterior.starSumOver]
  apply sumOverCongr
  intro i
  simp only [conjugate, ComplexScalar.star_mul, ComplexScalar.star_ofReal, ComplexScalar.star_star]
  grind

theorem pairedDensityHermitian {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    dagger (pairedDensity A mu) = pairedDensity A mu :=
  pairedStateHermitian A _

theorem pairedState_mul {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu nu : Fin 7 → R) (orth : OrthonormalFrame A) :
    pairedState A (fun i => mu i * nu i) =
      matMul (qubitIndices n) (pairedState A mu) (pairedState A nu) := by
  let source := List.finRange 7
  let sites := qubitIndices n
  let D := diagonal mu
  let D' := diagonal nu
  let I : Fin 7 → Fin 7 → ComplexScalar R := diagonal (fun _ => 1)
  let G := dagger A
  let E := diagonal (fun i => mu i * nu i)
  have nd : source.Nodup := List.nodup_finRange 7
  have complete (i : Fin 7) : i ∈ source := List.mem_finRange i
  have gram : matMul sites G A = I := by
    funext i j
    change sumOver sites (fun a => ComplexScalar.star (A a i) * A a j) =
      (if i=j then ofReal 1 else 0)
    exact orth i j
  have diagId (X : Fin 7 → Basis n → ComplexScalar R) : matMul source I X = X := by
    funext i j
    change matMul source (diagonal (fun _ => 1)) X i j = X i j
    rw [diagonalAction source nd _ _ i j (complete i)]
    exact Semiring.one_mul _
  have diagMul : matMul source D D' = E := by
    funext i j
    rw [diagonalAction source nd mu D' i j (complete i)]
    by_cases e : i=j
    · subst j
      simp only [D', E, diagonal, ite_true]
      apply ComplexScalar.ext <;> simp <;> grind
    · simp only [D', E, diagonal, ite_eq_right e, Semiring.mul_zero]
  unfold pairedState
  simp only [← rankSevenCoefficients_eq]
  change matMul source (matMul source A E) G =
    matMul sites (matMul source (matMul source A D) G) (matMul source (matMul source A D') G)
  symm
  calc
    _ = matMul source A (matMul source D
          (matMul source (matMul sites G A) (matMul source D' G))) := by
      simp only [matMulAssoc]
    _ = matMul source A (matMul source D (matMul source D' G)) := by rw [gram, diagId]
    _ = _ := by rw [← matMulAssoc source source D D' G, diagMul, matMulAssoc]

theorem pairedDensity_eq_square {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    pairedDensity A mu =
      matMul (qubitIndices n) (pairedState A mu) (pairedState A mu) := by
  unfold pairedDensity
  simp only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]
  exact pairedState_mul A mu mu orth

/-- A one-copy Pauli trace of a paired state uses only the seven
Schmidt coordinates and the compressed Pauli word. -/
theorem pauliTraceEqSource {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (p : Word n) :
    trace (qubitIndices n) (matMul (qubitIndices n) (wordEntry imaginaryUnit p) (pairedState A mu)) =
      trace (List.finRange 7) (matMul (List.finRange 7) (diagonal mu) (FrameExteriorSector.framedWord A p)) := by
  let sites := qubitIndices n
  let source := List.finRange 7
  let P := wordEntry (imaginaryUnit (R := R)) p
  let G := dagger A
  let D := diagonal mu
  unfold pairedState
  rw [← rankSevenCoefficients_eq]
  change trace sites (matMul sites P (matMul source (matMul source A D) G)) =
    trace source (matMul source D (matMul sites G (matMul sites P A)))
  rw [← matMulAssoc sites source P (matMul source A D) G]
  rw [traceMatMulSwap sites source, traceMatMulSwap source source D]
  simp only [matMulAssoc]

/-- The Pauli pair coefficient in the sector defects is the trace of the
two seven-column Pauli matrices separated by the same Schmidt diagonal. -/
theorem pauliPairTraceEqSource {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (p q : Word n) :
    let sites := qubitIndices n
    let source := List.finRange 7
    let N := pairedState A mu
    let D := diagonal mu
    trace sites (matMul sites (matMul sites (matMul sites (wordEntry imaginaryUnit p) N)
      (wordEntry imaginaryUnit q)) N) =
      trace source (matMul source (matMul source (matMul source D (FrameExteriorSector.framedWord A q))
        D) (FrameExteriorSector.framedWord A p)) := by
  dsimp only
  let sites := qubitIndices n
  let source := List.finRange 7
  let P := wordEntry (imaginaryUnit (R := R)) p
  let Q := wordEntry (imaginaryUnit (R := R)) q
  let G := dagger A
  let D := diagonal mu
  let X := matMul source (matMul source A D) G
  let L := matMul sites G (matMul sites P A)
  let M := matMul sites G (matMul sites Q A)
  unfold pairedState
  rw [← rankSevenCoefficients_eq]
  change trace sites (matMul sites (matMul sites (matMul sites P X) Q) X) =
    trace source (matMul source (matMul source (matMul source D M) D) L)
  have cyclic : trace sites (matMul sites (matMul sites (matMul sites P X) Q) X) =
      trace source (matMul source (matMul sites G (matMul sites P (matMul source A D)))
        (matMul source M D)) := by
    have form : matMul sites (matMul sites (matMul sites P X) Q) X =
        matMul source (matMul sites P (matMul source A (matMul source D (matMul source M D)))) G := by
      unfold X M
      simp only [matMulAssoc]
    rw [form, traceMatMulSwap sites source]
    simp only [matMulAssoc]
  rw [cyclic]
  have grouped : matMul source (matMul sites G (matMul sites P (matMul source A D))) (matMul source M D) =
      matMul source L (matMul source (matMul source D M) D) := by
    unfold L
    simp only [matMulAssoc]
  rw [grouped, traceMatMulSwap source source]

theorem densityPauliTraceReal {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (p : Word n) :
    let z := trace (qubitIndices n) (matMul (qubitIndices n) (wordEntry imaginaryUnit p) (pairedDensity A mu))
    ComplexScalar.star z = z := by
  let xs := qubitIndices n
  let P := wordEntry (imaginaryUnit (R := R)) p
  let K := pairedDensity A mu
  have herm : dagger P = P := by
    funext a b
    exact ComplexPauliMoment.wordHermitian p b a
  have traceDagger (X : Basis n → Basis n → ComplexScalar R) :
      ComplexScalar.star (trace xs X) = trace xs (dagger X) := by
    unfold trace
    rw [ComplexExterior.starSumOver]
    rfl
  change ComplexScalar.star (trace xs (matMul xs P K)) = trace xs (matMul xs P K)
  rw [traceDagger, daggerProduct, pairedDensityHermitian, herm, traceMatMulSwap]

private theorem realSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).re = (f a).re + sumOver xs (fun z => (f z).re)
    rw [ComplexScalar.re_add, ih]

theorem wedgeOverlapTraceEq {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) :
    wedgeOverlapTrace half A mu =
      (trace wedges (matMul wedges (diagonal (fun w => (amplitude mu w)^2))
        (exteriorSector (normalizedFrame half A)))).re := by
  unfold wedgeOverlapTrace trace
  rw [realSum]
  apply sumOverCongr
  intro w
  rw [diagonalAction _ ExteriorCuts.wedgesNodup _ _ w w (ExteriorCuts.memWedges w)]
  simp only [ComplexScalar.re_mul, ComplexScalar.re_ofReal, ComplexScalar.im_ofReal]
  grind

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem wedgeOverlapTracePhysical (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    wedgeOverlapTrace half A mu = 4 * normOverlap (amplitude mu) (physicalEntries half unit k A) := by
  unfold wedgeOverlapTrace normOverlap Compression.diagonalLoss
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro w
  rw [FrameExteriorSector.normalizedFrameSector_eq_four_effectEntry half unit k A]
  simp only [effectEntry, ComplexScalar.re_mul, ComplexScalar.re_ofReal, ComplexScalar.im_ofReal]
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem dimensionSquareInverse (half : R) (unit : 2*half=1) (n : Nat) :
    ((2:R)^n)^2 * half^(n+n) = 1 := by
  rw [Semiring.pow_add]
  have dim := SectorDefectAccounting.dimensionInverse half unit n
  grind

theorem physicalOverlapIdentity (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    (physicalSectorTerms half invTwentyFour k A mu).overlap =
      PhysicalChartRestriction.weight half (k+3) * normOverlap (amplitude mu) (physicalEntries half unit k A) := by
  change half^(k+3) * wedgeOverlapTrace half A mu = _
  rw [wedgeOverlapTracePhysical half unit]
  unfold PhysicalChartRestriction.weight
  grind

theorem physicalAlternatingIdentity (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    (physicalSectorTerms half invTwentyFour k A mu).alternating =
      (PhysicalChartRestriction.weight half (k+3))^2 * normAlt (amplitude mu) (physicalEntries half unit k A) := by
  change half^((k+3)+(k+3)) * wedgeSectorTrace half A mu = _
  unfold wedgeSectorTrace normAlt
  rw [FrameExteriorSector.physicalWedgeTrace_eq_spectral half unit, Semiring.pow_add]
  unfold PhysicalChartRestriction.weight
  grind

theorem pairedRawTraceSplit (half : R) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    24 * purity half (pairedState A mu) =
      rawSectorTrace half A mu .symmetric + 2 * rawSectorTrace half A mu .mixedEven +
        rawSectorTrace half A mu .antisymmetric := by
  have split := FourCopySectors.normalizedPairedSectorTrace (List.finRange 7) (by decide)
    (fun _ => by simp) half A A (diagonal mu)
  dsimp only at split
  have re := congrArg ComplexScalar.re split
  have traceEq := purityRectangularTrace (List.finRange 7) half A (conjugate A)
    (diagonal mu) (diagonalSymmetric mu) (diagonalReal mu)
  rw [rankSevenCoefficients_eq, conjugateInvolution] at traceEq
  change purity half (pairedState A mu) = _ at traceEq
  rw [traceEq]
  simp only [ComplexScalar.re_add, ComplexScalar.re_mul] at re
  change 24 * (pairedFrameTrace _ _ (normalizedFrame half A) (normalizedFrame half A)).re - 0 * _ =
    rawSectorTrace half A mu .symmetric +
      (2 * rawSectorTrace half A mu .mixedEven - 0 * _) + rawSectorTrace half A mu .antisymmetric at re
  grind

theorem rawAlternatingTransport (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    rawSectorTrace half A mu .antisymmetric = 24 * wedgeSectorTrace half A mu := by
  unfold rawSectorTrace wedgeSectorTrace
  rw [AlternatingTrace.physicalAlternatingTrace half unit,
    FrameExteriorSector.physicalWedgeTrace_eq_spectral half unit]
  grind

/-- The symmetric correction in the assembled physical sector formula is
an exact sum of squares of anticommuting Pauli pair coefficients. -/
theorem physicalSymmetricDefectEqSquares (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    SectorDefectAccounting.symmetricDefect (half^(k+3)) (physicalSectorTerms half invTwentyFour k A mu) =
      2*(half^(k+3))^5 * SymmetricDefect.antiSquares (SymmetricDefect.coeff (pairedState A mu)) := by
  have cert := SymmetricDefect.physicalSymmetricCertificate half invTwentyFour unit invUnit A mu
  change (half^(k+3))^3 * (sumOver (words (k+3)) (fun p =>
    (SymmetricDefect.physicalCoeff (matMul (qubitIndices (k+3)) (pairedState A mu) (pairedState A mu)) p)^4)) -
      half^((k+3)+(k+3))*invTwentyFour*(rawSectorTrace half A mu .symmetric - rawSectorTrace half A mu .antisymmetric) =
        _ at cert
  rw [← pairedDensity_eq_square A mu orth, rawAlternatingTransport half unit] at cert
  change (half^(k+3))^3 * pauliDensityFourth A mu -
      half^((k+3)+(k+3))*invTwentyFour*(rawSectorTrace half A mu .symmetric - 24*wedgeSectorTrace half A mu) =
        _ at cert
  rw [show SymmetricDefect.orbitMatrix A mu = pairedState A mu from rfl] at cert
  change (half^(k+3))^3 * pauliDensityFourth A mu -
      half^((k+3)+(k+3))*invTwentyFour*rawSectorTrace half A mu .symmetric +
      half^((k+3)+(k+3))*wedgeSectorTrace half A mu = _
  grind

theorem physicalSymmetricDefectNonnegative (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    0 ≤ SectorDefectAccounting.symmetricDefect (half^(k+3)) (physicalSectorTerms half invTwentyFour k A mu) := by
  rw [physicalSymmetricDefectEqSquares half invTwentyFour unit invUnit k A mu orth]
  exact SymmetricDefect.symmetricCertificateNonnegative half unit (pairedState A mu)

theorem pairedPurityEqSectorTotal (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    purity half (pairedState A mu) =
      SectorDefectAccounting.sectorTotal ((2:R)^(k+3)) (physicalSectorTerms half invTwentyFour k A mu) := by
  have split := pairedRawTraceSplit half k A mu
  rw [rawAlternatingTransport half unit] at split
  let sym := rawSectorTrace half A mu .symmetric
  let mix := rawSectorTrace half A mu .mixedEven
  let alt := wedgeSectorTrace half A mu
  have traceEq : purity half (pairedState A mu) = invTwentyFour * sym + 2*invTwentyFour * mix + alt := by
    have multiplied := congrArg (fun x => invTwentyFour * x) split
    change invTwentyFour * (24 * purity half (pairedState A mu)) =
      invTwentyFour * (sym + 2*mix + 24*alt) at multiplied
    grind
  have dim := dimensionSquareInverse half unit (k+3)
  rw [traceEq]
  change _ = ((2:R)^(k+3))^2 *
    (half^((k+3)+(k+3)) * invTwentyFour * sym +
      2 * (half^((k+3)+(k+3)) * invTwentyFour * mix) + half^((k+3)+(k+3)) * alt)
  grind

def frameDefects (half invTwentyFour : R) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) : R :=
  let source := List.finRange 7
  SectorDefectAccounting.totalDefect ((2:R)^(k+3)) (half^(k+3))
    ((sumOver source (fun i => (mu i)^4))^2) (sumOver source (fun i => (mu i)^8))
    (physicalSectorTerms half invTwentyFour k A mu)

/-- Exact physical purity difference from the closed-form computational
value, in the form consumed by the rank-seven inequalities. -/
theorem pairedPurityDefectDifference (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let t := physicalEntries half unit k A
    let a := amplitude mu
    purity half (pairedState A mu) - SectorDefectAccounting.computationalValue (List.finRange 7) mu a =
      168 * SectorDefectAccounting.exteriorGain a t -
        (frameDefects half invTwentyFour k A mu + 96 * SectorDefectAccounting.compressionLoss a t) := by
  dsimp only
  rw [pairedPurityEqSectorTotal half invTwentyFour unit invUnit]
  have diff := SectorDefectAccounting.physicalDefectAccounting half unit k A mu
    (physicalSectorTerms half invTwentyFour k A mu) rfl
    (physicalOverlapIdentity half invTwentyFour unit k A mu)
    (physicalAlternatingIdentity half invTwentyFour unit k A mu)
  dsimp only at diff
  unfold frameDefects
  grind

def PairedDefectBound (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) : Prop :=
  let t := physicalEntries half unit k A
  let a := amplitude mu
  168 * SectorDefectAccounting.exteriorGain a t ≤
    frameDefects half invTwentyFour k A mu + 96 * SectorDefectAccounting.compressionLoss a t

/-- The physical comparison is equivalent to the single gain-versus-defect
inequality, for the exact paired purity functional. -/
theorem pairedPurityBoundIffDefectBound (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    purity half (pairedState A mu) ≤
        SectorDefectAccounting.computationalValue (List.finRange 7) mu (amplitude mu) ↔
      PairedDefectBound half invTwentyFour unit k A mu := by
  have diff := pairedPurityDefectDifference half invTwentyFour unit invUnit k A mu
  dsimp only at diff
  unfold PairedDefectBound
  grind

/-- The two physical scalar comparisons suffice on a rectangular cut. -/
theorem orbitalPurityLeClosedForm (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (m n : Nat)
    (U : Basis (m+3) → Fin 7 → ComplexScalar R) (V : Basis (n+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (nonnegative : ∀ i, 0 ≤ mu i)
    (left : PairedDefectBound half invTwentyFour unit m U mu)
    (right : PairedDefectBound half invTwentyFour unit n (conjugate V) mu) :
    purity half (rankSevenCoefficients U V mu) ≤
      SectorDefectAccounting.computationalValue (List.finRange 7) mu (amplitude mu) := by
  apply rankSevenPurityLeOfPaired half U V mu nonnegative
  · exact (pairedPurityBoundIffDefectBound half invTwentyFour unit invUnit m U mu).mpr left
  · have h := (pairedPurityBoundIffDefectBound half invTwentyFour unit invUnit n (conjugate V) mu).mpr right
    unfold pairedState at h
    rw [PhysicalPairedReduction.conjugateInvolution] at h
    exact h

theorem pairedPurityComputationalDifference (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let t := physicalEntries half unit k A
    let a := amplitude mu
    purity half (pairedState A mu) - purity half (computationalCoefficients k k mu) =
      168 * SectorDefectAccounting.exteriorGain a t -
        (frameDefects half invTwentyFour k A mu + 96 * SectorDefectAccounting.compressionLoss a t) := by
  dsimp only
  rw [ComputationalPurity.computationalPurity_eq_value half unit]
  exact pairedPurityDefectDifference half invTwentyFour unit invUnit k A mu

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem computationalFrameReal (k : Nat) :
    conjugate (computationalFrame (R:=R) k) = computationalFrame k := by
  funext a i
  unfold conjugate computationalFrame
  split
  · exact ComplexScalar.star_ofReal (1:R)
  · exact ComplexScalar.star_ofReal (0:R)

/-- The combined physical defect is exactly zero on the genuine
computational frame, by the independently verified value and compression. -/
theorem computationalFrameDefectsZero (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (k : Nat) (mu : Fin 7 → R) :
    frameDefects half invTwentyFour k (computationalFrame k) mu = 0 := by
  have diff := pairedPurityComputationalDifference half invTwentyFour unit invUnit k (computationalFrame k) mu
  dsimp only at diff
  have gainZero : SectorDefectAccounting.exteriorGain (amplitude mu) (SectorDefectAccounting.referenceEntries R) = 0 := by
    rw [SectorDefectAccounting.gainDifference]
    grind
  have compEq : pairedState (computationalFrame (R:=R) k) mu = computationalCoefficients k k mu := by
    unfold pairedState computationalCoefficients
    rw [computationalFrameReal]
  rw [compEq, ComputationalExterior.computationalEntries_eq_reference half unit,
    gainZero, SectorDefectAccounting.referenceLossZero] at diff
  grind

/-- Exact physical assembly. The remaining comparison inputs are the two
scalar gain-versus-defect inequalities in the orthonormal Schmidt frames. -/
theorem rankSevenComputationalComparisonOfDefects (half invTwentyFour : R) (unit : 2*half=1)
    (invUnit : 24*invTwentyFour=1) (m n : Nat)
    (U : Basis (m+3) → Fin 7 → ComplexScalar R) (V : Basis (n+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (nonnegative : ∀ i, 0 ≤ mu i)
    (left : PairedDefectBound half invTwentyFour unit m U mu)
    (right : PairedDefectBound half invTwentyFour unit n (conjugate V) mu) :
    purity half (rankSevenCoefficients U V mu) ≤ purity half (computationalCoefficients m n mu) := by
  rw [ComputationalPurity.computationalPurity_eq_value half unit]
  exact orbitalPurityLeClosedForm half invTwentyFour unit invUnit m n U V mu nonnegative left right

end Order
end RankSeven.PhysicalDefectAssembly

#print axioms RankSeven.PhysicalDefectAssembly.densityPauliTraceReal
#print axioms RankSeven.PhysicalDefectAssembly.pairedDensity_eq_square
#print axioms RankSeven.PhysicalDefectAssembly.pauliTraceEqSource
#print axioms RankSeven.PhysicalDefectAssembly.pauliPairTraceEqSource
#print axioms RankSeven.PhysicalDefectAssembly.physicalOverlapIdentity
#print axioms RankSeven.PhysicalDefectAssembly.physicalAlternatingIdentity
#print axioms RankSeven.PhysicalDefectAssembly.physicalSymmetricDefectEqSquares
#print axioms RankSeven.PhysicalDefectAssembly.physicalSymmetricDefectNonnegative
#print axioms RankSeven.PhysicalDefectAssembly.pairedRawTraceSplit
#print axioms RankSeven.PhysicalDefectAssembly.pairedPurityDefectDifference
#print axioms RankSeven.PhysicalDefectAssembly.pairedPurityBoundIffDefectBound
#print axioms RankSeven.PhysicalDefectAssembly.orbitalPurityLeClosedForm
#print axioms RankSeven.PhysicalDefectAssembly.pairedPurityComputationalDifference
#print axioms RankSeven.PhysicalDefectAssembly.computationalFrameDefectsZero
#print axioms RankSeven.PhysicalDefectAssembly.rankSevenComputationalComparisonOfDefects
