import Rank7PhysicalChartRestriction
import Rank7PhysicalExteriorSupport
import Rank7ExteriorDeterminantBridge

namespace RankSeven.PhysicalExteriorCompression

open Lean.Grind Pauli PhysicalWedges PhysicalChartRestriction HyperplaneInduction
open ExteriorPauliBase (Wedge wedgeIndices qubitBits physicalExteriorSum)
open ExteriorDeterminantBridge (baseRows baseDefect)
open GenericExteriorKernel (position supportedPair exteriorKernel)
open HyperplaneIncidence (HyperplaneCode)

variable {R : Type} [CommRing R]
attribute [local instance] Ring.intCast

theorem coefficientEq {n : Nat} (q : R) (u v : Coordinate n) :
    PhysicalExteriorSupport.coefficient q u.val v.val = defect q (u,v) := by
  unfold PhysicalExteriorSupport.coefficient defect
  by_cases same : u=v
  · subst v
    simp
  · have distinct : u.val ≠ v.val := fun h => same (Subtype.ext h)
    simp [same, distinct]

private theorem insideIff {n : Nat} (H : HyperplaneCode n) (w : Coordinate n) :
    PhysicalExteriorSupport.inside H w.val = true ↔ inside H w := by
  simp only [PhysicalExteriorSupport.inside, PhysicalExteriorSupport.sites,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true_iff]
  constructor
  · intro h j
    have four : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
    rcases four with rfl | rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

def wedgeRows {n : Nat} (w : Coordinate n) (j : Fin 4) : Basis n := position w.val j

/-- The charts and matrix coefficients used by the induction are the
    actual ordered binary hyperplanes and normalized physical entries. -/
noncomputable def charts (half : R) (halfUnit : 2*half = 1) :
    Charts (fun k => Coordinate (k+3)) R where
  coords k := coords (k+3)
  nodup k := coordsNodup (k+3)
  rows _ := wedgeRows
  K k := defect (weight half (k+3))
  q k := weight half (k+3)
  site _ := OrderedHyperplaneChart.site
  embed _ := embed
  present _ _ i _ := memCoords (embed _ i)
  coordinate _ H i j := embedPosition H i j
  caseOf _ ij := PhysicalExteriorSupport.pairCase ij.1.val ij.2.val ij.1.property ij.2.property
  parentEntry k ij := by
    rw [← coefficientEq, PhysicalExteriorSupport.parentEntry]
  childEntry k H hH ij _ := by
    classical
    obtain ⟨u,v⟩ := ij
    have proper := properOfMem H hH
    rw [PhysicalExteriorSupport.localEntry_formula _ _ _ _ _ H proper]
    simp only [Bool.and_eq_true_iff, insideIff, coefficientEq]
    rw [← weightDouble half halfUnit (k+3)]
    exact actualChildEntry (weight half (k+3)) H proper u v

/-- The base implementation and the arbitrary-dimensional determinant
    kernel use the same four-copy Pauli minors and normalization. -/
theorem baseKernel (i half : R) (u v : Wedge) :
    exteriorKernel i half (baseCoordinate u).val (baseCoordinate v).val =
      half^6 * physicalExteriorSum i u v := by
  unfold exteriorKernel
  rw [ExteriorPauliBase.physicalExteriorSum_eq_pauli_minors]
  congr 1

theorem baseDefectEntry (half : R) (halfUnit : 2*half = 1) (u v : Wedge) :
    defect (weight half 3) (baseCoordinate u,baseCoordinate v) = baseDefect half (u,v) := by
  have h1 : (1 : R)^4 = 1 := by grind
  have kernel := GenericExteriorKernel.sorted_kernel_entry (1 : R) half h1 halfUnit
    (baseCoordinate u).val (baseCoordinate v).val (baseCoordinate u).property (baseCoordinate v).property
  rw [baseKernel, ExteriorDeterminantBridge.normalized_physical_eq_gram _ _ h1 halfUnit] at kernel
  change half * Int.cast (ExteriorPauliBase.planeGram u v) =
    (if supportedPair (baseCoordinate u).val (baseCoordinate v).val then weight half 3 else 0) at kernel
  unfold defect baseDefect
  simp only [weightThree half halfUnit] at kernel ⊢
  rw [← kernel]
  by_cases same : u=v
  · subst v
    simp
  · have distinct : baseCoordinate u ≠ baseCoordinate v := fun e => same (baseCoordinateInjective e)
    simp only [ite_eq_right distinct, ite_eq_right same]

private theorem sumProduct {α β : Type} (xs : List α) (ys : List β) (f : α × β → R) :
    sumOver (productIndices xs ys) f = sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  unfold productIndices
  rw [sumOverFlatMap]
  apply sumOverCongr
  intro x
  simp [sumOver, List.map_map, Function.comp_def]

theorem reindexBase (half : R) (halfUnit : 2*half = 1)
    (A : Basis 3 → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    quadratic (coords 3) (defect (weight half 3)) (exteriorLift wedgeRows A v) =
      quadratic wedgeIndices (baseDefect half) (exteriorLift baseRows (fun i => A (qubitBits i)) v) := by
  have liftAt (w : Wedge) :
      exteriorLift wedgeRows A v (baseCoordinate w) =
      exteriorLift baseRows (fun i => A (qubitBits i)) v w := by
    simp only [exteriorLift, minor4, wedgeRows, baseRows, baseCoordinateAt]
  simp only [quadratic, sumProduct, baseSums, realWeight, liftAt, baseDefectEntry half halfUnit]

private theorem ofRealMul (a b : R) :
    ComplexScalar.ofReal a * ComplexScalar.ofReal b = ComplexScalar.ofReal (a*b) := by
  apply ComplexScalar.ext <;> simp <;> grind

private theorem ofRealPow (a : R) (n : Nat) :
    (ComplexScalar.ofReal a)^n = ComplexScalar.ofReal (a^n) := by
  induction n with
  | zero =>
    simp only [Semiring.pow_zero]
    rfl
  | succ n ih => rw [Semiring.pow_succ, Semiring.pow_succ, ih, ofRealMul]

/-- The entries of the actual complex Pauli kernel are real, with the
    exact affine-plane normalization used by the induction. -/
theorem normalizedComplexEntry (half : R) (halfUnit : 2*half = 1) {n : Nat}
    (u v : Coordinate n) :
    exteriorKernel ComplexScalar.imaginaryUnit (ComplexScalar.ofReal half) u.val v.val =
      ComplexScalar.ofReal (if supportedPair u.val v.val then weight half n else 0) := by
  have halfComplex : 2 * ComplexScalar.ofReal half = (1 : ComplexScalar R) := by
    change ComplexScalar.ofReal (2:R) * ComplexScalar.ofReal half = ComplexScalar.ofReal 1
    rw [ofRealMul, halfUnit]
  rw [GenericExteriorKernel.sorted_kernel_entry _ _ ComplexScalar.imaginaryUnit_fourth
    halfComplex u.val v.val u.property v.property]
  split
  · unfold weight
    change ComplexScalar.ofReal (4 : R) * (ComplexScalar.ofReal half) ^ n =
      ComplexScalar.ofReal (4 * half ^ n)
    rw [ofRealPow, ofRealMul]
  · rfl

def complexDefect {n : Nat} (half : R) (uv : Coordinate n × Coordinate n) : R :=
  ((if uv.1 = uv.2 then ComplexScalar.ofReal (weight half n) else 0) -
    exteriorKernel ComplexScalar.imaginaryUnit (ComplexScalar.ofReal half) uv.1.val uv.2.val).re

theorem complexDefect_eq (half : R) (halfUnit : 2*half = 1) {n : Nat}
    (uv : Coordinate n × Coordinate n) :
    complexDefect half uv = defect (weight half n) uv := by
  unfold complexDefect defect
  rw [normalizedComplexEntry half halfUnit]
  by_cases eq : uv.1 = uv.2 <;> simp only [eq, ite_true, ite_false, ComplexScalar.re_sub,
    ComplexScalar.re_ofReal, ComplexScalar.re_zero]

def physicalKernel {n : Nat} (half : R) (uv : Coordinate n × Coordinate n) : R :=
  (exteriorKernel ComplexScalar.imaginaryUnit (ComplexScalar.ofReal half) uv.1.val uv.2.val).re

theorem physicalKernel_eq (half : R) (halfUnit : 2*half = 1) {n : Nat}
    (uv : Coordinate n × Coordinate n) :
    physicalKernel half uv = if supportedPair uv.1.val uv.2.val then weight half n else 0 := by
  unfold physicalKernel
  rw [normalizedComplexEntry half halfUnit, ComplexScalar.re_ofReal]

/-- Exact reciprocal of the four-wedge scale in dimension 2^(k+3). -/
def inverseWeight (R : Type) [CommRing R] (k : Nat) : R := (2 : R)^(k+1)

theorem inverseWeight_mul_weight (half : R) (halfUnit : 2*half = 1) (k : Nat) :
    inverseWeight R k * weight half (k+3) = 1 := by
  induction k with
  | zero =>
    rw [weightThree half halfUnit]
    unfold inverseWeight
    simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using halfUnit
  | succ k ih =>
    change (2 : R)^((k+1)+1) * weight half ((k+3)+1) = 1
    rw [Semiring.pow_succ]
    calc
      _ = (2 : R)^(k+1) * (2 * weight half ((k+3)+1)) := by grind
      _ = _ := by
        rw [← weightDouble half halfUnit (k+3)]
        exact ih

theorem defectQuadratic (half : R) (halfUnit : 2*half = 1) {n : Nat}
    (z : Coordinate n → ComplexScalar R) :
    quadratic (coords n) (defect (weight half n)) z =
      weight half n * sumOver (coords n) (fun u => ComplexScalar.normSq (z u)) -
        quadratic (coords n) (physicalKernel half) z := by
  let q := weight half n
  let I (uv : Coordinate n × Coordinate n) := if uv.1 = uv.2 then q else 0
  have diagonal : quadratic (coords n) I z = q * sumOver (coords n) (fun u => ComplexScalar.normSq (z u)) := by
    unfold quadratic
    rw [sumProduct, sumOverMulLeft]
    apply sumOverCongr
    intro u
    have term (v : Coordinate n) :
        realWeight z (u,v) * I (u,v) = if u=v then q * ComplexScalar.normSq (z v) else 0 := by
      unfold I
      by_cases same : u=v
      · subst v
        simp only [realWeight, ComplexScalar.normSq]
        grind
      · simp only [ite_eq_right same]
        grind
    rw [sumOverCongr _ term]
    exact ExteriorPauliBase.sumOnIndex _ u _ (coordsNodup n) (memCoords u)
  have difference :
      quadratic (coords n) (defect q) z =
        quadratic (coords n) I z - quadratic (coords n) (physicalKernel half) z := by
    unfold quadratic
    rw [← Compression.sumOverSub]
    apply sumOverCongr
    intro uv
    rw [physicalKernel_eq half halfUnit]
    unfold defect I
    grind
  rw [difference, diagonal]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Physical exterior compression on every binary ambient dimension.
    This is the rank-seven four-wedge upper bound with arbitrary complex
    seven-column maps and arbitrary source exterior coefficients. -/
theorem rankSevenPhysicalExteriorCompression (half : R) (halfUnit : 2*half = 1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    0 ≤ quadratic (coords (k+3)) (defect (weight half (k+3))) (exteriorLift wedgeRows A v) := by
  exact allDimensions (charts half halfUnit)
    (fun A v => by
      change 0 ≤ quadratic (coords 3) (defect (weight half 3)) (exteriorLift wedgeRows A v)
      rw [reindexBase half halfUnit]
      exact ExteriorDeterminantBridge.base_quadratic_nonnegative half halfUnit _ v)
    k A v

/-- The same bound with the physical complex Pauli minor sum in the
    statement. There are no geometric or compression premises. -/
theorem rankSevenPauliMinorCompression (half : R) (halfUnit : 2*half = 1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    0 ≤ quadratic (coords (k+3)) (complexDefect half) (exteriorLift wedgeRows A v) := by
  have eq : (complexDefect half : Coordinate (k+3) × Coordinate (k+3) → R) =
      defect (weight half (k+3)) := funext (complexDefect_eq half halfUnit)
  rw [eq]
  exact rankSevenPhysicalExteriorCompression half halfUnit k A v

theorem rankSevenPauliKernelUpper (half : R) (halfUnit : 2*half = 1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    let z := exteriorLift wedgeRows A v
    quadratic (coords (k+3)) (physicalKernel half) z ≤
      weight half (k+3) * sumOver (coords (k+3)) (fun w => ComplexScalar.normSq (z w)) := by
  have h := rankSevenPhysicalExteriorCompression half halfUnit k A v
  rw [defectQuadratic half halfUnit] at h
  grind

end Order
end RankSeven.PhysicalExteriorCompression

#print axioms RankSeven.PhysicalExteriorCompression.rankSevenPhysicalExteriorCompression
#print axioms RankSeven.PhysicalExteriorCompression.rankSevenPauliMinorCompression
#print axioms RankSeven.PhysicalExteriorCompression.rankSevenPauliKernelUpper
