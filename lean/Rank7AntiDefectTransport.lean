import Rank7PhysicalDefectAssembly
import Rank7PhysicalAntiQuartic
import Rank7PhysicalEdgeSwitching
import Rank7AntiPairIncidence
import Rank7AntiPlaneIncidence

namespace RankSeven.AntiDefectTransport

open Lean.Grind Pauli
open ComplexScalar (imaginaryUnit ofReal)
open PhysicalPairedReduction (dagger diagonal realEmbeddingPow diagonalAction fourWeights frameTwirl)
open RectangularPairedReduction (coefficients normalizedFrame rankSevenCoefficients_eq)
open PhysicalDefectAssembly (pairedState pairedDensity pairedState_mul pauliDensityFourth wedgeOverlapTrace physicalSectorTerms)
open PhysicalCompressionEffect (OrthonormalFrame)
open ExteriorCuts (wedges amplitude)
open FourCopySectors (Sector rawBlock)
open PhysicalAntiQuartic (wordFrame matrixSum quadTrace fourDelta)

variable {R C : Type} [CommRing R] [CommRing C]
local instance (n : Nat) : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

theorem wordFrameFactor {n : Nat} (i : C) (X : Basis n → Basis n → C) :
    let xs := fourIndices (qubitIndices n)
    wordFrame i X = matMul xs (unnormalizedTwirl i) (tensorFour X) := by
  dsimp only
  funext u v
  unfold wordFrame matrixSum unnormalizedTwirl
  simp only [fourMatMul]
  unfold matMul
  rw [sumOverSwap]
  apply sumOverCongr
  intro w
  rw [sumOverMulRight]

private theorem embedSum {α : Type} (xs : List α) (f : α → R) :
    ofReal (sumOver xs f) = sumOver xs (fun a => ofReal (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ofReal (f a + sumOver xs f) = ofReal (f a) + sumOver xs (fun b => ofReal (f b))
    rw [←ih]
    apply ComplexScalar.ext <;> simp <;> grind

theorem pairedTraceEqSpectrum {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (h : Fin 7 → R) (orth : OrthonormalFrame A) :
    trace (qubitIndices n) (pairedState A h) = ofReal (sumOver (List.finRange 7) h) := by
  let source := List.finRange 7
  let sites := qubitIndices n
  let I : Fin 7 → Fin 7 → ComplexScalar R := diagonal (fun _ => 1)
  have gram : matMul sites (dagger A) A = I := by
    funext i j
    change sumOver sites (fun u => ComplexScalar.star (A u i) * A u j) = if i=j then ofReal 1 else 0
    exact orth i j
  unfold pairedState
  rw [←rankSevenCoefficients_eq]
  change trace sites (matMul source (matMul source A (diagonal h)) (dagger A)) = _
  rw [traceMatMulSwap sites source, ←matMulAssoc sites source (dagger A) A,gram,embedSum]
  unfold trace
  apply sumOverCongr
  intro i
  rw [diagonalAction source (List.nodup_finRange 7) (fun _ => 1) (diagonal h) i i (List.mem_finRange i)]
  change (1:ComplexScalar R)*diagonal h i i = ofReal (h i)
  simp [diagonal, Semiring.one_mul]

theorem ambientAlternatingTraceEqSource {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (h : Fin 7 → R) :
    let xs := fourIndices (qubitIndices n)
    let src := fourIndices (List.finRange 7)
    trace xs (rawBlock .antisymmetric (wordFrame imaginaryUnit (pairedState A h))) =
      trace src (matMul src (rawBlock .antisymmetric (frameTwirl A)) (tensorFour (diagonal h))) := by
  dsimp only
  let sites := qubitIndices n
  let source := List.finRange 7
  let xs := fourIndices sites
  let src := fourIndices source
  let J := unnormalizedTwirl (imaginaryUnit (R:=R)) (n:=n)
  let L := tensorFour A
  let G := tensorFour (dagger A)
  let H := tensorFour (diagonal h)
  let JL := matMul xs J L
  have frame : frameTwirl A = matMul xs G JL := by
    unfold frameTwirl G JL L J xs sites dagger
    rw [fourTranspose, matMulAssoc]
  have factor : tensorFour (pairedState A h) = matMul src L (matMul src H G) := by
    unfold pairedState
    rw [←rankSevenCoefficients_eq]
    change tensorFour (matMul source (matMul source A (diagonal h)) (dagger A)) = _
    rw [fourMatMul,fourMatMul,matMulAssoc]
  have fixed := FourCopySectors.fullPermuted sites (HyperplaneIncidence.normalsNodup n) qubitIndicesComplete
  change trace xs (rawBlock .antisymmetric (wordFrame imaginaryUnit (pairedState A h))) =
    trace src (matMul src (rawBlock .antisymmetric (frameTwirl A)) H)
  rw [wordFrameFactor,factor]
  change trace xs (rawBlock .antisymmetric (matMul xs J (matMul src L (matMul src H G)))) = _
  rw [←matMulAssoc xs src J L,←matMulAssoc src src JL H G]
  rw [FourCopySectors.blockLeft,FourCopySectors.blockLeft,traceMatMulSwap xs src,
    ←matMulAssoc xs src G (rawBlock .antisymmetric JL)]
  rw [←FourCopySectors.blockRight xs fixed .antisymmetric G JL (FourCopySectors.tensorEquivariant _), ←frame]

private theorem realSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).re = (f a).re + sumOver xs (fun b => (f b).re)
    rw [ComplexScalar.re_add,ih]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem ambientAlternatingOverlap (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let xs := fourIndices (qubitIndices (k+3))
    (trace xs (rawBlock .antisymmetric (wordFrame imaginaryUnit (pairedDensity A mu)))).re =
      24*((2:R)^(k+3))^2 * (physicalSectorTerms half invTwentyFour k A mu).overlap := by
  dsimp only
  unfold pairedDensity
  rw [ambientAlternatingTraceEqSource]
  have lin := AlternatingTrace.alternatingOverlapToWedges (fun i => (mu i)^2)
    (frameTwirl A) (FourCopySectors.frameStructure A).1
  change trace (fourIndices (List.finRange 7))
    (matMul (fourIndices (List.finRange 7)) (rawBlock .antisymmetric (frameTwirl A))
      (tensorFour (diagonal (fun i => (mu i)^2)))) = _ at lin
  rw [lin]
  have weight (w : ExteriorCuts.Wedge7) :
      fourWeights (fun i => (mu i)^2) (FrameExteriorSector.sourceTuple w) = (amplitude mu w)^2 := by
    unfold fourWeights FrameExteriorSector.sourceTuple amplitude ExteriorCuts.product4
    grind only
  simp only [weight,ComplexScalar.re_mul,realSum,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal]
  let d := (2:R)^(k+3)
  let di := half^(k+3)
  have inv := SectorDefectAccounting.dimensionInverse half unit (k+3)
  have normAt (w : ExteriorCuts.Wedge7) : d*(FrameExteriorSector.exteriorSector (normalizedFrame half A) w w).re =
      (FrameExteriorSector.exteriorSector (frameTwirl A) w w).re := by
    unfold normalizedFrame RectangularPairedReduction.scaleMatrix
    rw [FrameExteriorSector.exteriorSector_scale]
    simp only [ComplexScalar.re_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal]
    change d*(di*(FrameExteriorSector.exteriorSector (frameTwirl A) w w).re - 0*_) = _
    grind
  change 24*sumOver wedges (fun w => (amplitude mu w)^2 *
    (FrameExteriorSector.exteriorSector (frameTwirl A) w w).re - 0*_)-0*_ =
    24*d^2*(di*wedgeOverlapTrace half A mu)
  have each (w : ExteriorCuts.Wedge7) :
      (amplitude mu w)^2*(FrameExteriorSector.exteriorSector (frameTwirl A) w w).re - 0*
        (FrameExteriorSector.exteriorSector (frameTwirl A) w w).im =
      d*((amplitude mu w)^2*(FrameExteriorSector.exteriorSector (normalizedFrame half A) w w).re) := by
    rw [←normAt w]
    grind
  rw [sumOverCongr wedges each]
  unfold wedgeOverlapTrace
  rw [←sumOverMulLeft]
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem pairedDensityPowerTraces {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let xs := qubitIndices n
    let N := pairedDensity A mu
    trace xs (matMul xs N N) = ofReal (sumOver (List.finRange 7) (fun i => (mu i)^4)) ∧
      quadTrace xs N N N N = ofReal (sumOver (List.finRange 7) (fun i => (mu i)^8)) := by
  let xs := qubitIndices n
  let N := pairedDensity A mu
  let P (e : Nat) := pairedState A (fun i => (mu i)^e)
  have mul (e : Nat) : matMul xs (P e) (P e) = P (e+e) := by
    unfold P xs
    rw [←pairedState_mul A _ _ orth]
    congr 1
    funext i
    rw [Semiring.pow_add]
  change trace xs (matMul xs (P 2) (P 2)) = _ ∧ quadTrace xs (P 2) (P 2) (P 2) (P 2) = _
  constructor
  · rw [mul]
    exact pairedTraceEqSpectrum A _ orth
  · unfold quadTrace
    rw [matMulAssoc xs xs (matMul xs (P 2) (P 2)) (P 2) (P 2), mul, mul]
    exact pairedTraceEqSpectrum A _ orth

theorem densityTraceWordOfReal {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (p : Word n) :
    let z := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) p
    z = ofReal z.re := by
  let z := trace (qubitIndices n)
    (matMul (qubitIndices n) (wordEntry imaginaryUnit p) (pairedDensity A mu))
  dsimp only
  have flip : SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) p = z :=
    traceMatMulSwap _ _ _ _
  rw [flip]
  have star := PhysicalDefectAssembly.densityPauliTraceReal A mu p
  change ComplexScalar.star z = z at star
  have imaginaryEq := congrArg ComplexScalar.im star
  rw [ComplexScalar.im_star] at imaginaryEq
  change -z.im=z.im at imaginaryEq
  have imZero : z.im=0 := by grind
  exact ComplexScalar.ext rfl imZero

theorem physicalDensityWordFourth {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    (sumOver (words n) (fun p => (SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) p)^4)).re =
      pauliDensityFourth A mu := by
  rw [realSum]
  unfold pauliDensityFourth
  apply sumOverCongr
  intro p
  have real := densityTraceWordOfReal A mu p
  dsimp only at real
  have fourth := congrArg (fun z : ComplexScalar R => z^4) real
  rw [←realEmbeddingPow] at fourth
  rw [fourth,ComplexScalar.re_ofReal]
  rw [SymmetricDefect.traceWord,traceMatMulSwap]

theorem physicalUnorderedAnticommutingMass {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    (PhysicalAntiQuartic.unorderedAntiMass c).re =
      PhysicalAntiQuartic.unorderedAntiMass (fun p => (c p).re) := by
  dsimp only
  unfold PhysicalAntiQuartic.unorderedAntiMass
  rw [realSum]
  apply sumOverCongr
  intro pair
  split
  · have a := densityTraceWordOfReal A mu pair.1
    have b := densityTraceWordOfReal A mu pair.2
    dsimp only at a b
    have left := congrArg (fun z : ComplexScalar R =>
      (z^2*(SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) pair.2)^2).re) a
    have right := congrArg (fun z : ComplexScalar R =>
      ((ofReal ((SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) pair.1).re))^2*z^2).re) b
    change _ = _ at left right
    rw [left,right]
    rw [←realEmbeddingPow,←realEmbeddingPow,ComplexScalar.re_mul,
      ComplexScalar.re_ofReal,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,ComplexScalar.im_ofReal]
    grind
  · rfl

theorem fourDeltaEqPhysical (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    (fourDelta imaginaryUnit (pairedDensity A mu)).re =
      4*SectorDefectAccounting.anticommutingDefect ((2:R)^(k+3))
        ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2)
        (sumOver (List.finRange 7) (fun i => (mu i)^8))
        (physicalSectorTerms half invTwentyFour k A mu) := by
  obtain ⟨t4,t8⟩ := pairedDensityPowerTraces A mu orth
  have alt := ambientAlternatingOverlap half invTwentyFour unit k A mu
  dsimp only at t4 t8 alt
  let d := (2:R)^(k+3)
  have embed : (2:ComplexScalar R)^(k+3) = ofReal d := (realEmbeddingPow (2:R) (k+3)).symm
  unfold fourDelta
  dsimp only
  rw [t4,t8,←realEmbeddingPow,embed]
  simp only [ComplexScalar.re_sub,ComplexScalar.re_add,ComplexScalar.re_mul,
    ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,ComplexScalar.im_mul]
  rw [alt,physicalDensityWordFourth]
  unfold SectorDefectAccounting.anticommutingDefect
  simp only [show (12:ComplexScalar R).re=12 from rfl, show (12:ComplexScalar R).im=0 from rfl,
    show (8:ComplexScalar R).re=8 from rfl, show (8:ComplexScalar R).im=0 from rfl,
    show (4:ComplexScalar R).re=4 from rfl, show (4:ComplexScalar R).im=0 from rfl]
  rw [show (physicalSectorTerms half invTwentyFour k A mu).pauliFourth=pauliDensityFourth A mu from rfl]
  grind only

/-- Physical anticommuting correction on the rank-seven Schmidt orbit,
expressed in actual Pauli coefficients and their ordered quartic. -/
theorem physicalAnticommutingOrderedExpansion (half invTwentyFour : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let di := half^(k+3)
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    4*SectorDefectAccounting.anticommutingDefect ((2:R)^(k+3))
        ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2)
        (sumOver (List.finRange 7) (fun i => (mu i)^8))
        (physicalSectorTerms half invTwentyFour k A mu) =
      24*di*(PhysicalAntiQuartic.antiMass c).re + 8*di^2*(PhysicalAntiQuartic.orderedQuartic imaginaryUnit c).re := by
  dsimp only
  let di := half^(k+3)
  let d := (2:R)^(k+3)
  have inv := SectorDefectAccounting.dimensionInverse half unit (k+3)
  have embed : (2:ComplexScalar R)^(k+3) = ofReal d := (realEmbeddingPow (2:R) (k+3)).symm
  have complexInv : (2:ComplexScalar R)^(k+3)*ofReal di=1 := by
    rw [embed]
    apply ComplexScalar.ext <;> simp <;> grind
  have raw := PhysicalAntiQuartic.orderedPhysicalDefect imaginaryUnit ComplexScalar.imaginaryUnit_sq
    (ofReal di) complexInv (pairedDensity A mu)
  have real := congrArg ComplexScalar.re raw
  have one : (24:ComplexScalar R)*ofReal di=ofReal (24*di) := by
    change ofReal (24:R)*ofReal di=_
    apply ComplexScalar.ext <;> simp <;> grind
  have two : (8:ComplexScalar R)*(ofReal di)^2=ofReal (8*di^2) := by
    rw [←realEmbeddingPow]
    change ofReal (8:R)*ofReal (di^2)=_
    apply ComplexScalar.ext <;> simp <;> grind
  simp only [one,two,ComplexScalar.re_add,ComplexScalar.re_mul,ComplexScalar.re_ofReal,
    ComplexScalar.im_ofReal] at real
  change _ = _ at real
  rw [fourDeltaEqPhysical half invTwentyFour unit k A mu orth] at real
  grind

/-- The actual rank-seven anticommuting defect, grouped into unordered
anticommuting pairs and the four-distinct-word plane terms. -/
theorem physicalAnticommutingGroupedExpansion (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) :
    let d := (2:R)^(k+3)
    let di := half^(k+3)
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    let planes := (fourIndices (words (k+3))).filter (ExteriorIsometry.increasing PhysicalAntiQuartic.wordKey)
    SectorDefectAccounting.anticommutingDefect d
        ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2)
        (sumOver (List.finRange 7) (fun i => (mu i)^8))
        (physicalSectorTerms half inv24 k A mu) =
      4*(3*d-4)*di^2*(PhysicalAntiQuartic.unorderedAntiMass c).re +
        64*di^2*(sumOver planes (PhysicalAntiQuartic.planeTerm imaginaryUnit c)).re := by
  dsimp only
  let n := k+3
  let di := half^n
  let d := (2:R)^n
  have embed : (2:ComplexScalar R)^n = ofReal d := (realEmbeddingPow (2:R) n).symm
  have inv := SectorDefectAccounting.dimensionInverse half unit n
  have complexInv : (2:ComplexScalar R)^n*ofReal di=1 := by
    rw [embed]
    apply ComplexScalar.ext <;> simp <;> grind
  have complexInv24 : (24:ComplexScalar R)*ofReal inv24=1 := by
    change ofReal (24:R)*ofReal inv24=_
    apply ComplexScalar.ext <;> simp <;> grind
  have raw := PhysicalAntiQuartic.physicalAntiQuarticExpansion imaginaryUnit ComplexScalar.imaginaryUnit_sq
    (ofReal di) complexInv (ofReal inv24) complexInv24 (pairedDensity A mu)
  have grouped := congrArg ComplexScalar.re raw
  have scalePair : (4:ComplexScalar R)*(3*(2:ComplexScalar R)^n-4)*(ofReal di)^2 =
      ofReal (4*(3*d-4)*di^2) := by
    rw [embed,←realEmbeddingPow]
    change ofReal (4:R)*(ofReal (3:R)*ofReal d-ofReal (4:R))*ofReal (di^2)=_
    apply ComplexScalar.ext <;> simp <;> grind
  have scalePlane : (64:ComplexScalar R)*(ofReal di)^2=ofReal (64*di^2) := by
    rw [←realEmbeddingPow]
    change ofReal (64:R)*ofReal (di^2)=_
    apply ComplexScalar.ext <;> simp <;> grind
  simp only [scalePair,scalePlane,ComplexScalar.re_add,ComplexScalar.re_mul,
    ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,
    show (4:ComplexScalar R).re=4 from rfl, show (4:ComplexScalar R).im=0 from rfl] at grouped
  change _ = _ at grouped
  rw [fourDeltaEqPhysical half inv24 unit k A mu orth] at grouped
  grind

/-- The sum of the checked physical edge blocks pays the complete
anticommuting pair debit once both incidence identities are supplied. -/
theorem anticommutingBoundFromIncidence (half : R) (unit : 2*half=1) {n : Nat}
    (directions : List (Word (n+1))) (r : Word (n+1) → Word (n+1))
    (companion : ∀ s ∈ directions, SymmetricDefect.anti s (r s)=true)
    (weights : Word (n+1) → Word (n+1) → R) (mass planes : R)
    (massEq : mass = sumOver directions (fun s =>
      sumOver (PauliEdgeBlocks.perpendicularWords s (r s)) (fun u => (weights s u)^2)))
    (planeEq : 4*planes = sumOver directions (fun s =>
      let xs := PauliEdgeBlocks.perpendicularWords s (r s)
      sumOver xs (fun u => sumOver xs
        (fun v => weights s u * PhysicalEdgeSwitching.physicalEdgeMatrix half s (r s) u v * weights s v)))) :
    let d := (2:R)^(n+1)
    let di := half^(n+1)
    4*di*mass ≤ 4*(3*d-4)*di^2*mass+64*di^2*planes := by
  dsimp only
  let d := (2:R)^(n+1)
  let di := half^(n+1)
  let a := (2:R)^n
  let e (s : Word (n+1)) := sumOver (PauliEdgeBlocks.perpendicularWords s (r s)) (fun u => (weights s u)^2)
  let q (s : Word (n+1)) :=
    let xs := PauliEdgeBlocks.perpendicularWords s (r s)
    sumOver xs (fun u => sumOver xs
      (fun v => weights s u*PhysicalEdgeSwitching.physicalEdgeMatrix half s (r s) u v*weights s v))
  have each (s : Word (n+1)) (hs : s ∈ directions) : 0 ≤ (a-1)*e s+q s :=
    PhysicalEdgeSwitching.physicalEdgeNonnegative half unit s (r s) (companion s hs) (weights s)
  have total := Compression.sumOverNonnegative directions (fun s => (a-1)*e s+q s) each
  have payment := OrderedRing.mul_nonneg (squareNonnegative di) total
  rw [sumOverAdd,←sumOverMulLeft] at payment
  change mass = sumOver directions e at massEq
  change 4*planes = sumOver directions q at planeEq
  rw [←massEq,←planeEq] at payment
  have scale : d=2*a := by unfold d a; rw [Semiring.pow_succ]; grind only
  have invert := SectorDefectAccounting.dimensionInverse half unit (n+1)
  change d*di=1 at invert
  have dSquared : d*di^2=di := by
    rw [Semiring.pow_succ,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul,←Semiring.mul_assoc,
      invert,Semiring.one_mul]
  change 4*di*mass ≤ 4*(3*d-4)*di^2*mass+64*di^2*planes
  have split : 4*(3*d-4)*di^2*mass+64*di^2*planes-4*di*mass =
      16*(di^2*((a-1)*mass+4*planes)) := by
    have calcD := congrArg (fun x => x*mass) dSquared
    grind only
  grind

theorem physicalAnticommutingChargeFromPlaneIncidence (half inv24 : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A)
    (planeIncidence :
      let n := k+3
      let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
      let planes := (fourIndices (words n)).filter (ExteriorIsometry.increasing PhysicalAntiQuartic.wordKey)
      let z s := AntiPairIncidence.edgeWeight (fun p => (c p).re) s (AntiPairIncidence.companion s)
      4*(sumOver planes (PhysicalAntiQuartic.planeTerm imaginaryUnit c)).re =
        sumOver (AntiPairIncidence.nonzeroWords n) (fun s =>
          let r := AntiPairIncidence.companion s
          let xs := PauliEdgeBlocks.perpendicularWords s r
          sumOver xs (fun u => sumOver xs
            (fun v => z s u * PhysicalEdgeSwitching.physicalEdgeMatrix half s r u v * z s v)))) :
    let n := k+3
    let s := physicalSectorTerms half inv24 k A mu
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    let p4 := sumOver (List.finRange 7) (fun i => (mu i)^4)
    let p8 := sumOver (List.finRange 7) (fun i => (mu i)^8)
    4*half^n*(PhysicalAntiQuartic.unorderedAntiMass c).re ≤
      SectorDefectAccounting.anticommutingDefect ((2:R)^n) (p4^2) p8 s := by
  dsimp only
  rw [physicalAnticommutingGroupedExpansion half inv24 unit unit24 k A mu orth]
  have mass := physicalUnorderedAnticommutingMass A mu
  dsimp only at mass
  rw [mass]
  let n := k+3
  let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
  let f (p : Word n) := (c p).re
  let w s := AntiPairIncidence.edgeWeight f s (AntiPairIncidence.companion s)
  exact anticommutingBoundFromIncidence half unit (n:=k+2) (AntiPairIncidence.nonzeroWords n)
    AntiPairIncidence.companion AntiPairIncidence.companionAnti w _
    _ (AntiPairIncidence.unorderedAntiMass_eq_edgeSquares half unit f) planeIncidence

/-- The physical anticommuting defect pays the entire anticommuting charge,
with both finite incidence counts instantiated on actual Pauli words. -/
theorem physicalAnticommutingCharge (half inv24 : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let n := k+3
    let s := physicalSectorTerms half inv24 k A mu
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    let p4 := sumOver (List.finRange 7) (fun i => (mu i)^4)
    let p8 := sumOver (List.finRange 7) (fun i => (mu i)^8)
    4*half^n*(PhysicalAntiQuartic.unorderedAntiMass c).re ≤
      SectorDefectAccounting.anticommutingDefect ((2:R)^n) (p4^2) p8 s := by
  apply physicalAnticommutingChargeFromPlaneIncidence half inv24 unit unit24 k A mu orth
  let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
  have real : (fun p => ofReal ((c p).re)) = c := by
    funext p
    exact (densityTraceWordOfReal A mu p).symm
  have inc := AntiPlaneIncidence.physicalPlaneEdgeSum half inv24 unit unit24 (fun p => (c p).re)
  rw [real] at inc
  exact inc

theorem physicalAnticommutingDefectNonnegative (half inv24 : R) (unit : 2*half=1)
    (unit24 : 24*inv24=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    0 ≤ SectorDefectAccounting.anticommutingDefect ((2:R)^(k+3))
      ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2) (sumOver (List.finRange 7) (fun i => (mu i)^8))
      (physicalSectorTerms half inv24 k A mu) := by
  have charge := physicalAnticommutingCharge half inv24 unit unit24 k A mu orth
  dsimp only at charge
  have exact := physicalUnorderedAnticommutingMass A mu
  dsimp only at exact
  rw [exact] at charge
  have mass : 0 ≤ PhysicalAntiQuartic.unorderedAntiMass
      (fun p => (SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu) p).re) := by
    unfold PhysicalAntiQuartic.unorderedAntiMass
    apply Compression.sumOverNonnegative
    intro pair _
    split
    · exact OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)
    · grind
  have half0 : 0 ≤ half := by grind
  have pow0 (n : Nat) : 0 ≤ half^n := by
    induction n with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih half0
  have paid := OrderedRing.mul_nonneg (pow0 (k+3)) mass
  grind

end Order
end RankSeven.AntiDefectTransport

#print axioms RankSeven.AntiDefectTransport.ambientAlternatingTraceEqSource
#print axioms RankSeven.AntiDefectTransport.ambientAlternatingOverlap
#print axioms RankSeven.AntiDefectTransport.physicalAnticommutingOrderedExpansion
#print axioms RankSeven.AntiDefectTransport.physicalAnticommutingGroupedExpansion
#print axioms RankSeven.AntiDefectTransport.anticommutingBoundFromIncidence
#print axioms RankSeven.AntiDefectTransport.physicalAnticommutingChargeFromPlaneIncidence
#print axioms RankSeven.AntiDefectTransport.physicalAnticommutingCharge
#print axioms RankSeven.AntiDefectTransport.physicalAnticommutingDefectNonnegative
