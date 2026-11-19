import Rank7ComplexExteriorBridge
import Rank7MissingHole

namespace RankSeven.ComplexExterior

open Lean.Grind Pauli ExteriorOccupation ExteriorOperators ExteriorPauliBase
open ComplexScalar (star ofReal normSq)

variable {R : Type} [CommRing R]
attribute [local instance] Ring.intCast

private theorem starSub (a b : ComplexScalar R) : star (a-b) = star a-star b := by
  apply ComplexScalar.ext <;> simp <;> grind

private theorem ofRealMul (a b : R) : ofReal (a*b) = ofReal a * ofReal b := by
  apply ComplexScalar.ext <;> simp <;> grind

private theorem ofRealSum {α : Type} (xs : List α) (f : α → R) :
    ofReal (sumOver xs f) = sumOver xs (fun i => ofReal (f i)) := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    change ofReal (f i + sumOver rest f) = ofReal (f i) + sumOver rest (fun i => ofReal (f i))
    rw [← ih]
    apply ComplexScalar.ext <;> simp <;> grind

def holeMass (x : Point → ComplexScalar R) : R :=
  sumOver points (fun i => normSq (x i))

theorem holePairing_eq_real_mass (x : Point → ComplexScalar R) :
    ExteriorOperators.pairing x (fun i => star (x i)) = ofReal (holeMass x) := by
  unfold ExteriorOperators.pairing holeMass
  rw [ofRealSum]
  apply sumOverCongr
  intro i
  rw [CommSemiring.mul_comm, ComplexScalar.star_mul_self]

theorem starScaledResidual (x : Point → ComplexScalar R) (half : R) (u : Form (ComplexScalar R)) :
    starForm (scaledHoleResidual x (fun i => star (x i)) (ofReal half) u) =
      scaledHoleResidual (fun i => star (x i)) x (ofReal half) (starForm u) := by
  let dual := fun i => star (x i)
  have mass : star (ExteriorOperators.pairing x dual) = ExteriorOperators.pairing dual x := by
    have massReal : ExteriorOperators.pairing x dual = ofReal (holeMass x) := holePairing_eq_real_mass x
    rw [holePairingSymmetric x dual, massReal, ComplexScalar.star_ofReal]
  have proj (m : Mask) : star (projectMaskWaves (ofReal half) u m) =
      projectMaskWaves (ofReal half) (starForm u) m :=
    congrFun (starProjectMaskWavesReal half u) m
  have occ (m : Mask) :
      star (occupation x dual (projectMaskWaves (ofReal half) u) m) =
        occupation dual x (projectMaskWaves (ofReal half) (starForm u)) m := by
    have h := congrFun (starOccupation x dual (projectMaskWaves (ofReal half) u)) m
    rw [starProjectMaskWavesReal] at h
    simpa only [starForm, dual, ComplexScalar.star_star] using h
  have starTwo : star (2 : ComplexScalar R) = 2 := ComplexScalar.star_ofReal (2 : R)
  funext m
  change star (ExteriorOperators.pairing x dual * u m -
      2 * (ExteriorOperators.pairing x dual * projectMaskWaves (ofReal half) u m -
        occupation x dual (projectMaskWaves (ofReal half) u) m)) = _
  rw [starSub, ComplexScalar.star_mul, ComplexScalar.star_mul, starSub, ComplexScalar.star_mul,
    starTwo, mass, proj m, occ m]
  rfl

section Order

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem holeMassPositive (x : Point → ComplexScalar R) (nonzero : ∃ i, x i ≠ 0) :
    0 < holeMass x := by
  obtain ⟨i, hi⟩ := nonzero
  exact sumPositiveAt points _ (fun j => ComplexScalar.normSq_nonnegative (x j)) i (by simp [points])
    (ComplexScalar.normSq_positive (x i) hi)

def squaredNorm (u : Form (ComplexScalar R)) : R := (formPairing (starForm u) u).re

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reRealMul (a : R) (b : ComplexScalar R) : (ofReal a * b).re = a * b.re := by
  simp <;> grind

/-- The one-half compression bound on the annihilated subspace over
    complex coordinates. An arbitrary nonzero hole is sufficient. -/
theorem eightPointComplexCompression (x : Point → ComplexScalar R) (half : R) (f : Form (ComplexScalar R))
    (unitHalf : 2 * half = 1) (nonzero : ∃ i, x i ≠ 0)
    (kernel : annihilate (fun i => star (x i)) f = fun _ => 0) :
    2 * squaredNorm (projectMaskWaves (ofReal half) f) ≤ squaredNorm f := by
  let dual := fun i => star (x i)
  have halfComplex : 2 * ofReal half = (1 : ComplexScalar R) := by
    change ofReal (2 : R) * ofReal half = ofReal 1
    rw [← ofRealMul, unitHalf]
  have kernelLeft : annihilate x (starForm f) = fun _ => 0 := by
    have h := starAnnihilate dual f
    change annihilate dual f = (fun _ => (0 : ComplexScalar R)) at kernel
    rw [kernel] at h
    have starZero : star (0 : ComplexScalar R) = 0 := ComplexScalar.star_ofReal (0 : R)
    have starZeroForm : starForm (fun _ => (0 : ComplexScalar R)) = fun _ => 0 := funext (fun _ => starZero)
    rw [starZeroForm] at h
    simpa only [dual, ComplexScalar.star_star] using h.symm
  have cert := eightPointCompressionCertificateOfMass x dual (ofReal half) (starForm f) f
    halfComplex kernelLeft kernel
  have nneg := formPairingStarSelf_nonnegative (scaledHoleResidual x dual (ofReal half) f)
  rw [starScaledResidual, cert, holePairing_eq_real_mass] at nneg
  have massSquare : (ofReal (holeMass x))^2 = ofReal ((holeMass x)^2) := by
    simp only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul, ← ofRealMul]
  rw [massSquare, reRealMul, ComplexScalar.re_sub] at nneg
  have projStar := starProjectMaskWavesReal half f
  rw [← projStar] at nneg
  change 0 ≤ (holeMass x)^2 *
    (squaredNorm f - ((ofReal (2 : R)) * formPairing (starForm (projectMaskWaves (ofReal half) f))
      (projectMaskWaves (ofReal half) f)).re) at nneg
  rw [reRealMul] at nneg
  change 0 ≤ (holeMass x)^2 * (squaredNorm f - 2 * squaredNorm (projectMaskWaves (ofReal half) f)) at nneg
  have pos := holeMassPositive x nonzero
  have scale := OrderedRing.mul_pos pos pos
  by_cases le : 2 * squaredNorm (projectMaskWaves (ofReal half) f) ≤ squaredNorm f
  · exact le
  · have opposite : 0 < 2 * squaredNorm (projectMaskWaves (ofReal half) f) - squaredNorm f := by grind
    have contra := OrderedRing.mul_pos scale opposite
    grind

/-- Arbitrary linear combinations of four-fold wedges of the listed
    columns use the same hole. -/
def wedgeLinearCombination (terms : List (ComplexScalar R × List (Point → ComplexScalar R))) :
    Form (ComplexScalar R) :=
  fun m => sumOver terms (fun term => term.1 * exteriorProduct term.2 m)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem annihilateCombination
    (dual : Point → ComplexScalar R)
    (terms : List (ComplexScalar R × List (Point → ComplexScalar R)))
    (orthogonal : ∀ term ∈ terms, ∀ v ∈ term.2, ExteriorOperators.pairing dual v = 0) :
    annihilate dual (wedgeLinearCombination terms) = fun _ => 0 := by
  funext m
  unfold annihilate combine site wedgeLinearCombination
  simp only [sumOverMulLeft]
  rw [sumOverSwap points terms]
  have one (t : ComplexScalar R × List (Point → ComplexScalar R)) (present : t ∈ terms) :
      sumOver points (fun i => dual i * (Int.cast (lowerCoeff i m) *
        (t.1 * exteriorProduct t.2 (toggle i m)))) = 0 := by
    have each (i : Point) :
        dual i * (Int.cast (lowerCoeff i m) * (t.1 * exteriorProduct t.2 (toggle i m))) =
          t.1 * (dual i * (Int.cast (lowerCoeff i m) * exteriorProduct t.2 (toggle i m))) := by grind
    rw [sumOverCongr _ each, ← sumOverMulLeft]
    change t.1 * annihilate dual (exteriorProduct t.2) m = 0
    rw [annihilate_exteriorProduct dual t.2 (orthogonal t present)]
    grind
  change (terms.map (fun t => sumOver points (fun i => dual i * (Int.cast (lowerCoeff i m) *
    (t.1 * exteriorProduct t.2 (toggle i m)))))).sum = 0
  rw [List.map_congr_left one]
  have zeros (xs : List (ComplexScalar R × List (Point → ComplexScalar R))) :
      (xs.map (fun _ => (0 : ComplexScalar R))).sum = 0 := by
    induction xs with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      grind
  exact zeros terms

/-- Eight-point complex compression for every four-wedge vector formed
    from at most seven columns, including their linear combinations. -/
theorem eightPointComplexCompressionOfRows (half : R) (unitHalf : 2 * half = 1)
    (rows : List (Point → ComplexScalar R)) (rankBound : rows.length ≤ 7)
    (terms : List (ComplexScalar R × List (Point → ComplexScalar R)))
    (insideSpan : ∀ term ∈ terms, term.2.length = 4 ∧ ∀ v ∈ term.2, v ∈ rows) :
    2 * squaredNorm (projectMaskWaves (ofReal half) (wedgeLinearCombination terms)) ≤
      squaredNorm (wedgeLinearCombination terms) := by
  have one : (1 : ComplexScalar R) ≠ 0 := by
    intro same
    have re := congrArg ComplexScalar.re same
    have positive : (0 : R) < 1 := OrderedRing.zero_lt_one
    simp only [ComplexScalar.re_one, ComplexScalar.re_zero] at re
    grind
  obtain ⟨dual, ⟨i, nonzero⟩, annihilates⟩ :=
    sevenRowsHaveHole one ComplexScalar.mul_ne_zero rows rankBound
  let x := fun i => star (dual i)
  have xNonzero : x i ≠ 0 := by
    intro same
    have h := congrArg star same
    have starZero : star (0 : ComplexScalar R) = 0 := ComplexScalar.star_ofReal (0 : R)
    exact nonzero (by simpa only [x, ComplexScalar.star_star, starZero] using h)
  have dualEq : (fun i => star (x i)) = dual := by funext j; exact ComplexScalar.star_star (dual j)
  apply eightPointComplexCompression x half _ unitHalf ⟨i, xNonzero⟩
  rw [dualEq]
  exact annihilateCombination dual terms (fun term present v member =>
    annihilates v ((insideSpan term present).2 v member))

end Order
end RankSeven.ComplexExterior

#print axioms RankSeven.ComplexExterior.eightPointComplexCompression
#print axioms RankSeven.ComplexExterior.eightPointComplexCompressionOfRows
