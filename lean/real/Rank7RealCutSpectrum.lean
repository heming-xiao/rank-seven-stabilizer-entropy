import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.List.Nodup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Rank7CutTrace

namespace RankSeven.RealCutSpectrum

open CutTrace
open scoped BigOperators

private def toComplex (z : ComplexScalar ℝ) : ℂ := ⟨z.re, z.im⟩
private def fromComplex (z : ℂ) : ComplexScalar ℝ := ⟨z.re, z.im⟩

private theorem fromTo (z : ComplexScalar ℝ) : fromComplex (toComplex z) = z := by cases z; rfl
private theorem toFrom (z : ℂ) : toComplex (fromComplex z) = z := by cases z; rfl

private theorem toComplexInjective : Function.Injective toComplex := by
  intro a b h
  simpa only [fromTo] using congrArg fromComplex h

private theorem toComplexAdd (a b : ComplexScalar ℝ) : toComplex (a + b) = toComplex a + toComplex b := rfl
private theorem toComplexMul (a b : ComplexScalar ℝ) : toComplex (a * b) = toComplex a * toComplex b := rfl

private theorem toComplexSum {α : Type} (xs : List α) (f : α → ComplexScalar ℝ) :
    toComplex (Pauli.sumOver xs f) = (xs.map (fun a => toComplex (f a))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [Pauli.sumOver, List.map_cons, List.sum_cons] at ih ⊢
    rw [toComplexAdd, ih]

private def view {α : Type} (xs : List α) (A : α → α → ComplexScalar ℝ) :
    Matrix (Fin xs.length) (Fin xs.length) ℂ :=
  fun i j => toComplex (A (xs.get i) (xs.get j))

private theorem viewMul {α : Type} (xs : List α) (A B : α → α → ComplexScalar ℝ) :
    view xs (Pauli.matMul xs A B) = view xs A * view xs B := by
  ext i j
  simp only [view, Pauli.matMul, Matrix.mul_apply, toComplexSum, toComplexMul]
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

private theorem viewDagger {α : Type} (xs : List α) (A : α → α → ComplexScalar ℝ) :
    view xs (PhysicalPairedReduction.dagger A) = star (view xs A) := by
  ext i j
  rfl

private theorem viewDiagonal {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (d : α → ℝ) :
    view xs (PhysicalPairedReduction.diagonal d) =
      Matrix.diagonal (fun i : Fin xs.length => (d (xs.get i) : ℂ)) := by
  ext i j
  by_cases eq : i = j
  · subst j
    simp [view, PhysicalPairedReduction.diagonal]
    rfl
  · have distinct : xs.get i ≠ xs.get j := fun h => eq (nd.injective_get h)
    change toComplex (if xs.get i = xs.get j then ComplexScalar.ofReal (d (xs.get i)) else 0) = _
    rw [ite_eq_right distinct, Matrix.diagonal_apply_ne _ eq]
    rfl

private theorem ofViewEq {α : Type} (xs : List α) {A B : α → α → ComplexScalar ℝ}
    (h : view xs A = view xs B) : AgreeOn xs A B := by
  intro i hi j hj
  obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hi
  obtain ⟨b, rfl⟩ := List.mem_iff_get.mp hj
  exact toComplexInjective (congrFun (congrFun h a) b)

/-- The selected complex Hermitian principal matrix has an actual unitary
spectral witness in the project's finite-list representation. -/
theorem spectralWitness {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (entries : Compression.HermitianEntries α ℝ) : Nonempty (SpectralWitness xs (matrix entries)) := by
  classical
  let T := matrix entries
  let M := view xs T
  have hm : M.IsHermitian := by
    change star M = M
    rw [← viewDagger xs T, matrixHermitian entries]
  let eigen := hm.eigenvectorUnitary
  let U : Matrix (Fin xs.length) (Fin xs.length) ℂ := eigen
  let position (i : α) (hi : i ∈ xs) : Fin xs.length := Classical.choose (List.mem_iff_get.mp hi)
  have atGet (i : Fin xs.length) (hi : xs.get i ∈ xs) : position (xs.get i) hi = i :=
    nd.injective_get (Classical.choose_spec (List.mem_iff_get.mp hi))
  let d (i : α) : ℝ := if hi : i ∈ xs then hm.eigenvalues (position i hi) else 0
  let V (i j : α) : ComplexScalar ℝ :=
    if hi : i ∈ xs then
      if hj : j ∈ xs then fromComplex (U (position i hi) (position j hj)) else 0
    else 0
  have value (i : Fin xs.length) : d (xs.get i) = hm.eigenvalues i := by
    simp only [d, dite_eq_left (List.mem_iff_get.mpr ⟨i, rfl⟩), atGet]
  have eigenView : view xs V = U := by
    ext i j
    simp only [view, V, dite_eq_left (List.mem_iff_get.mpr ⟨i, rfl⟩),
      dite_eq_left (List.mem_iff_get.mpr ⟨j, rfl⟩), atGet, toFrom]
  have identity : view xs (PhysicalPairedReduction.diagonal (fun _ => (1 : ℝ))) = 1 := by
    rw [viewDiagonal xs nd]
    simp
  refine ⟨⟨d, V, ofViewEq xs ?_, ofViewEq xs ?_⟩⟩
  · rw [viewMul, viewDagger, eigenView, identity]
    exact Unitary.coe_star_mul_self eigen
  · rw [viewMul, viewMul, viewDagger, eigenView, viewDiagonal xs nd]
    simp only [value]
    simpa only [M, U, eigen, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hm.spectral_theorem

/-- The physical cut price follows from the verified spectral theorem on
the actual matrix. No diagonalization witness is required from callers. -/
theorem cutCostLower {α : Type} [DecidableEq α] (entries : Compression.HermitianEntries α ℝ)
    (xs : List α) (nd : xs.Nodup) (cut : α → Bool) (effect : entries.IsCoordinateEffect xs)
    (k : Nat) (r : ℝ) (r0 : 0 ≤ r) (r1 : r < 1)
    (count : (Pauli.trace (xs.filter cut) (matrix entries)).re = (k : ℝ) + r) :
    r * (1-r) ≤ ExteriorCuts.cutCost xs cut
      (Compression.rowSlack xs (fun i => entries.realPart i i) entries.mass) entries.mass := by
  obtain ⟨S⟩ := spectralWitness (xs.filter cut) (nd.filter _) entries
  exact cutCostLowerFromSpectrum entries xs nd cut effect S k r r0 r1 count

/-- Apply the spectral rounding bound to the normalized four-wedge
compression of an actual orthonormal rank-seven frame. -/
theorem physicalCutLower (half : ℝ) (unit : 2*half=1) (n : Nat)
    (A : Pauli.Basis (n+3) → Fin 7 → ComplexScalar ℝ)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (cut : ExteriorCuts.Wedge7 → Bool) (k : Nat) (r : ℝ) (r0 : 0 ≤ r) (r1 : r < 1)
    (count : (Pauli.trace (ExteriorCuts.wedges.filter cut)
      (matrix (PhysicalCompressionEffect.physicalEntries half unit n A))).re = (k : ℝ) + r) :
    let entries := PhysicalCompressionEffect.physicalEntries half unit n A
    r * (1-r) ≤ ExteriorCuts.cutCost ExteriorCuts.wedges cut
      (Compression.rowSlack ExteriorCuts.wedges (fun i => entries.realPart i i) entries.mass) entries.mass :=
  cutCostLower _ _ ExteriorCuts.wedgesNodup cut
    (PhysicalCompressionEffect.rankSevenPhysicalEffect half unit n A orth) k r r0 r1 count

/-- Every actual cut has a fractional trace decomposition with a certified
quadratic cut price. -/
theorem physicalCutRounding (half : ℝ) (unit : 2*half=1) (n : Nat)
    (A : Pauli.Basis (n+3) → Fin 7 → ComplexScalar ℝ)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (cut : ExteriorCuts.Wedge7 → Bool) :
    let entries := PhysicalCompressionEffect.physicalEntries half unit n A
    ∃ (k : Nat) (r : ℝ), 0 ≤ r ∧ r < 1 ∧
      (Pauli.trace (ExteriorCuts.wedges.filter cut) (matrix entries)).re = (k : ℝ) + r ∧
      r * (1-r) ≤ ExteriorCuts.cutCost ExteriorCuts.wedges cut
        (Compression.rowSlack ExteriorCuts.wedges (fun i => entries.realPart i i) entries.mass) entries.mass := by
  let entries := PhysicalCompressionEffect.physicalEntries half unit n A
  let ys := ExteriorCuts.wedges.filter cut
  have nodup : ys.Nodup := ExteriorCuts.wedgesNodup.filter _
  have effect := PhysicalCompressionEffect.rankSevenPhysicalEffect half unit n A orth
  obtain ⟨S⟩ := spectralWitness ys nodup entries
  have inUnit (x : ℝ) (mem : x ∈ ys.map S.values) : 0 ≤ x ∧ x ≤ 1 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    exact eigenvalueBounds entries ys nodup (restrictionEffect entries _ cut effect) S i hi
  obtain ⟨k, r, hr, sum, _⟩ := RankSeven.traceRoundingCarry (ys.map S.values) inUnit
  have count : (Pauli.trace ys (matrix entries)).re = (k : ℝ) + r :=
    (traceSpectrum ys nodup (matrix entries) S).trans sum
  exact ⟨k, r, hr.1, hr.2, count, physicalCutLower half unit n A orth cut k r hr.1 hr.2 count⟩

theorem entropyOrder (prior optimum : ℝ) (positive : 0 < prior) (maximal : prior ≤ optimum) :
    -Real.log optimum ≤ -Real.log prior := by
  exact neg_le_neg (Real.strictMonoOn_log.monotoneOn positive (positive.trans_le maximal) maximal)

end RankSeven.RealCutSpectrum

#print axioms RankSeven.RealCutSpectrum.spectralWitness
#print axioms RankSeven.RealCutSpectrum.cutCostLower
#print axioms RankSeven.RealCutSpectrum.physicalCutLower
#print axioms RankSeven.RealCutSpectrum.physicalCutRounding
#print axioms RankSeven.RealCutSpectrum.entropyOrder

