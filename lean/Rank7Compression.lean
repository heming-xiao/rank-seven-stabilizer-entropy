import Rank7PauliTensor

namespace RankSeven.Compression

open Lean.Grind
open Pauli (sumOver sumOverCongr sumOverAdd sumOverMulLeft sumOverMulRight sumOverSwap)

variable {R α : Type} [CommRing R]

theorem sumOverSub (indices : List α) (f g : α → R) :
    sumOver indices (fun i => f i - g i) = sumOver indices f - sumOver indices g := by
  induction indices with
  | nil => simp [sumOver] <;> grind
  | cons i rest ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    grind

def diagonalLoss (indices : List α) (amplitude diagonal : α → R) : R :=
  sumOver indices fun i => amplitude i ^ 2 * diagonal i

def quadraticTrace (indices : List α) (amplitude : α → R) (mass : α → α → R) : R :=
  sumOver indices fun i => sumOver indices fun j => amplitude i * amplitude j * mass i j

def rowSlack (indices : List α) (diagonal : α → R) (mass : α → α → R) (i : α) : R :=
  diagonal i - sumOver indices (mass i)

def squaredGapCost (indices : List α) (amplitude : α → R) (mass : α → α → R) : R :=
  sumOver indices fun i => sumOver indices fun j => (amplitude i - amplitude j)^2 * mass i j

private theorem diagonalExpansion (indices : List α) (amplitude diagonal : α → R)
    (mass : α → α → R) :
    diagonalLoss indices amplitude (rowSlack indices diagonal mass) =
    diagonalLoss indices amplitude diagonal -
      sumOver indices (fun i => sumOver indices (fun j => amplitude i ^ 2 * mass i j)) := by
  unfold diagonalLoss rowSlack
  rw [← sumOverSub]
  apply sumOverCongr
  intro i
  rw [← sumOverMulLeft]
  grind

private theorem gapExpansion (indices : List α) (amplitude : α → R) (mass : α → α → R)
    (symmetric : ∀ i j, mass i j = mass j i) :
    squaredGapCost indices amplitude mass =
      2 * (sumOver indices (fun i => sumOver indices (fun j => amplitude i^2 * mass i j))
        - quadraticTrace indices amplitude mass) := by
  let weights i j := amplitude i ^ 2 * mass i j
  let mixed i j := amplitude i * amplitude j * mass i j
  have term (i j : α) :
      (amplitude i-amplitude j)^2 * mass i j =
        weights i j + weights j i - 2 * mixed i j := by
    dsimp [weights, mixed]
    rw [← symmetric i j]
    grind
  have groupMixed :
      (sumOver indices (fun i => sumOver indices (fun j => 2 * mixed i j))) =
        2 * sumOver indices (fun i => sumOver indices (mixed i)) := by
    simp only [sumOverMulLeft]
  unfold squaredGapCost quadraticTrace
  simp only [term, sumOverSub, sumOverAdd]
  rw [groupMixed]
  rw [sumOverSwap indices indices (fun i j => weights j i)]
  change
    (sumOver indices (fun i => sumOver indices (weights i))) +
      (sumOver indices (fun i => sumOver indices (weights i))) -
      2 * (sumOver indices (fun i => sumOver indices (mixed i))) = _
  clear term symmetric groupMixed
  grind

/-- Exact loss for diagonal amplitudes and a Hermitian compression.
    The doubled form uses ordered pairs of coordinates in the gap term. -/
theorem lossIdentity (indices : List α) (amplitude diagonal : α → R) (mass : α → α → R)
    (symmetric : ∀ i j, mass i j = mass j i) :
    2 * (diagonalLoss indices amplitude diagonal - quadraticTrace indices amplitude mass) =
      2 * diagonalLoss indices amplitude (rowSlack indices diagonal mass) +
        squaredGapCost indices amplitude mass := by
  rw [diagonalExpansion, gapExpansion indices amplitude mass symmetric]
  grind

/-- The two coordinates of a complex Hermitian matrix, with the real
    part symmetric and the imaginary part skew-symmetric. -/
structure HermitianEntries (α R : Type) [Neg R] where
  realPart : α → α → R
  imagPart : α → α → R
  realSymmetric : ∀ i j, realPart i j = realPart j i
  imagSkew : ∀ i j, imagPart i j = -imagPart j i

def HermitianEntries.mass (entries : HermitianEntries α R) (i j : α) : R :=
  entries.realPart i j ^ 2 + entries.imagPart i j ^ 2

theorem HermitianEntries.massSymmetric (entries : HermitianEntries α R) (i j : α) :
    entries.mass i j = entries.mass j i := by
  unfold mass
  rw [entries.realSymmetric i j, entries.imagSkew i j]
  grind

/-- Real trace of (T A T A) for diagonal (A), written out before
    applying Hermitian symmetry. -/
def HermitianEntries.realQuadraticTrace (entries : HermitianEntries α R)
    (indices : List α) (amplitude : α → R) : R :=
  sumOver indices fun i => sumOver indices fun j =>
    amplitude j * amplitude i *
      (entries.realPart i j * entries.realPart j i - entries.imagPart i j * entries.imagPart j i)

theorem HermitianEntries.realQuadraticTrace_eq (entries : HermitianEntries α R)
    (indices : List α) (amplitude : α → R) :
    entries.realQuadraticTrace indices amplitude = quadraticTrace indices amplitude entries.mass := by
  unfold realQuadraticTrace quadraticTrace
  apply sumOverCongr
  intro i
  apply sumOverCongr
  intro j
  unfold mass
  rw [← entries.realSymmetric i j, entries.imagSkew i j]
  grind

theorem HermitianEntries.realLossIdentity (entries : HermitianEntries α R)
    (indices : List α) (amplitude : α → R) :
    let diagonal i := entries.realPart i i
    2 * (diagonalLoss indices amplitude diagonal - entries.realQuadraticTrace indices amplitude) =
      2 * diagonalLoss indices amplitude (rowSlack indices diagonal entries.mass) +
        squaredGapCost indices amplitude entries.mass := by
  rw [entries.realQuadraticTrace_eq]
  exact lossIdentity _ _ _ _ entries.massSymmetric

section Order

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem sumOverNonnegative (indices : List α) (f : α → R)
    (nonnegative : ∀ i ∈ indices, 0 ≤ f i) : 0 ≤ sumOver indices f := by
  induction indices with
  | nil => simp [sumOver] <;> grind
  | cons i rest ih =>
    have head := nonnegative i (List.mem_cons_self)
    have tail := ih (fun j member => nonnegative j (List.mem_cons_of_mem i member))
    change 0 ≤ f i + sumOver rest f
    grind

theorem HermitianEntries.massNonnegative (entries : HermitianEntries α R) (i j : α) :
    0 ≤ entries.mass i j := by
  unfold mass
  have realNonneg := squareNonnegative (entries.realPart i j)
  have imagNonneg := squareNonnegative (entries.imagPart i j)
  grind

theorem HermitianEntries.realLossNonnegative (entries : HermitianEntries α R)
    (indices : List α) (amplitude : α → R)
    (contraction : ∀ i ∈ indices,
      0 ≤ rowSlack indices (fun j => entries.realPart j j) entries.mass i) :
    0 ≤ diagonalLoss indices amplitude (fun i => entries.realPart i i) -
      entries.realQuadraticTrace indices amplitude := by
  have identity := entries.realLossIdentity indices amplitude
  have first : 0 ≤ diagonalLoss indices amplitude (rowSlack indices
      (fun i => entries.realPart i i) entries.mass) := by
    apply sumOverNonnegative
    intro i member
    exact OrderedRing.mul_nonneg (squareNonnegative (amplitude i)) (contraction i member)
  have second : 0 ≤ squaredGapCost indices amplitude entries.mass := by
    apply sumOverNonnegative
    intro i _
    apply sumOverNonnegative
    intro j _
    exact OrderedRing.mul_nonneg (squareNonnegative (amplitude i - amplitude j))
      (entries.massNonnegative i j)
  grind

end Order

end RankSeven.Compression

#print axioms RankSeven.Compression.lossIdentity
#print axioms RankSeven.Compression.HermitianEntries.realLossIdentity
#print axioms RankSeven.Compression.HermitianEntries.realLossNonnegative
