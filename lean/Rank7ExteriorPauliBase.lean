import Rank7ExteriorOccupation
import Rank7PauliTwirlEntries

/-! Physical antisymmetric four-copy Pauli entries on the eight-point
cube, using the increasing wedge basis and the determinant permutation sum. -/
namespace RankSeven.ExteriorPauliBase

open RankSeven.Pauli RankSeven.ExteriorOccupation Lean.Grind

abbrev Wedge := Fin 70
abbrev Permutation := Four (Fin 4)

def fourMasks : List Nat :=
  (List.range 256).filter (fun m => (active m).length == 4)

def maskOf (w : Wedge) : Nat := fourMasks[w.val]?.getD 0

def tupleOf (w : Wedge) : Four Point :=
  let xs := active (maskOf w)
  ((xs[0]?.getD 0, xs[1]?.getD 0), (xs[2]?.getD 0, xs[3]?.getD 0))

def qubitBits (z : Point) : Basis 3 :=
  (z.val.testBit 2, z.val.testBit 1, z.val.testBit 0, ())

def pointBits (u : Four Point) : Four (Basis 3) :=
  ((qubitBits u.1.1, qubitBits u.1.2), (qubitBits u.2.1, qubitBits u.2.2))

def distinct (p : Permutation) : Bool :=
  p.1.1 != p.1.2 && p.1.1 != p.2.1 && p.1.1 != p.2.2 &&
    p.1.2 != p.2.1 && p.1.2 != p.2.2 && p.2.1 != p.2.2

def permutations : List Permutation := (fourIndices (List.finRange 4)).filter distinct

def oddPermutation (p : Permutation) : Bool :=
  let inversions := [(p.1.1 > p.1.2 : Bool), (p.1.1 > p.2.1 : Bool),
    (p.1.1 > p.2.2 : Bool), (p.1.2 > p.2.1 : Bool),
    (p.1.2 > p.2.2 : Bool), (p.2.1 > p.2.2 : Bool)]
  inversions.count true % 2 == 1

def atPosition (u : Four Point) (j : Fin 4) : Point :=
  match j.val with
  | 0 => u.1.1
  | 1 => u.1.2
  | 2 => u.2.1
  | _ => u.2.2

def permuted (u : Four Point) (p : Permutation) : Four Point :=
  ((atPosition u p.1.1, atPosition u p.1.2), (atPosition u p.2.1, atPosition u p.2.2))

theorem complete_basis_counts :
    fourMasks.length = 70 ∧ fourMasks.Nodup ∧
    permutations.length = 24 ∧ permutations.Nodup := by decide

/-- Each Pauli-word contribution in this expression is the determinant
of the 4-by-4 submatrix between the two coordinate wedges. -/
def physicalExteriorSum {C : Type} [CommRing C] (i : C) (u v : Wedge) : C :=
  sumOver permutations fun p =>
    let e := unnormalizedTwirl i (pointBits (tupleOf u)) (pointBits (permuted (tupleOf v) p))
    if oddPermutation p then -e else e

def allowedEntry (u v : Wedge) (p : Permutation) : Bool :=
  allowedTwirlEntry 3 (pointBits (tupleOf u)) (pointBits (permuted (tupleOf v) p))

def signedAllowed (u v : Wedge) (p : Permutation) : Int :=
  if allowedEntry u v p then (if oddPermutation p then -8 else 8) else 0

def planeGram (u v : Wedge) : Int :=
  sumOver directions fun n => planeWave n (maskOf u) * planeWave n (maskOf v)

private def evenBit (u : Four Bool) : Bool :=
  !(Bool.xor (Bool.xor u.1.1 u.1.2) (Bool.xor u.2.1 u.2.2))

private def evenBits : (n : Nat) → Four (Basis n) → Bool
  | 0, _ => true
  | n+1, u => evenBit (firstBits u) && evenBits n (remainingBits u)

private theorem allowedBit_even :
    ∀ u v : Four Bool, allowedBit u v = true → evenBit u = true ∧ evenBit v = true := by
  rintro ⟨⟨a,b⟩,c,d⟩ ⟨⟨e,f⟩,g,h⟩
  revert a b c d e f g h
  decide

private theorem allowed_even {n : Nat} (u v : Four (Basis n)) (h : allowedTwirlEntry n u v = true) :
    evenBits n u = true ∧ evenBits n v = true := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨u₀, v₀⟩ := allowedBit_even _ _ head
    obtain ⟨u₁, v₁⟩ := ih _ _ tail
    simp [evenBits, u₀, v₀, u₁, v₁]

private def affine (w : Wedge) : Bool := evenBits 3 (pointBits (tupleOf w))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
private theorem affine_permuted : ∀ (v : Wedge) (p : Permutation),
    distinct p = true → evenBits 3 (pointBits (permuted (tupleOf v) p)) = affine v := by
  rintro v ⟨⟨a,b⟩,c,d⟩
  revert v a b c d
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
private theorem nonplane_wave : ∀ (v : Wedge) (n : Direction),
    affine v = false → planeWave n (maskOf v) = 0 := by decide

private theorem zero_sum {α : Type} (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) : sumOver xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + sumOver xs f = 0
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]
    rfl

private theorem nonplane_count (u v : Wedge) (h : affine u = false ∨ affine v = false) :
    sumOver permutations (signedAllowed u v) = 32 * planeGram u v := by
  have hGram : planeGram u v = 0 := by
    apply zero_sum
    intro n _
    rcases h with hu | hv
    · rw [nonplane_wave _ _ hu, Int.zero_mul]
    · rw [nonplane_wave _ _ hv, Int.mul_zero]
  rw [hGram, Int.mul_zero]
  apply zero_sum
  intro p hp
  have hd := (List.mem_filter.mp hp).2
  cases he : allowedEntry u v p with
  | false => simp [signedAllowed, he]
  | true =>
    obtain ⟨hu, hv⟩ := allowed_even _ _ he
    rw [affine_permuted v p hd] at hv
    change affine u = true at hu
    rcases h with h | h <;> simp_all


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem parallel_plane_count : ∀ u v : Wedge, affine u = true → affine v = true →
    sumOver permutations (signedAllowed u v) = 32 * planeGram u v := by
  decide

theorem signed_translation_count (u v : Wedge) :
    sumOver permutations (signedAllowed u v) = 32 * planeGram u v := by
  cases hu : affine u <;> cases hv : affine v
  · exact nonplane_count _ _ (Or.inl hu)
  · exact nonplane_count _ _ (Or.inl hu)
  · exact nonplane_count _ _ (Or.inr hv)
  · exact parallel_plane_count _ _ hu hv

local instance {C : Type} [CommRing C] : IntCast C := Ring.intCast

private theorem cast_sumOver {C α : Type} [CommRing C] (xs : List α) (f : α → Int) :
    Int.cast (R := C) (sumOver xs f) = sumOver xs (fun x => Int.cast (f x)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons x xs ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    rw [Ring.intCast_add, ih]

theorem raw_physical_plane_gram {C : Type} [CommRing C] (i : C) (hi : i^4 = 1)
    (u v : Wedge) :
    physicalExteriorSum i u v =
      32 * sumOver directions (fun n => Int.cast (planeWave n (maskOf u)) *
        Int.cast (planeWave n (maskOf v))) := by
  have each (p : Permutation) :
      (let e := unnormalizedTwirl i (pointBits (tupleOf u)) (pointBits (permuted (tupleOf v) p))
       if oddPermutation p then -e else e) = Int.cast (R := C) (signedAllowed u v p) := by
    rw [unnormalizedTwirlEntry i hi]
    change (if oddPermutation p then -(if allowedEntry u v p then (2:C)^3 else 0)
              else (if allowedEntry u v p then (2:C)^3 else 0)) = _
    unfold signedAllowed
    cases allowedEntry u v p <;> cases oddPermutation p <;>
      simp <;> grind [Ring.intCast_ofNat, Ring.intCast_neg]
  unfold physicalExteriorSum
  rw [sumOverCongr permutations each, ← cast_sumOver, signed_translation_count,
    Ring.intCast_mul, Ring.intCast_ofNat, planeGram, cast_sumOver]
  congr 1
  apply sumOverCongr
  intro n
  exact Ring.intCast_mul _ _

/-- The three-qubit projector uses the Pauli average 2⁻⁶. The result is
    exactly the half-normalized matrix of the two-coset plane waves. -/
theorem normalized_physical_plane_gram {C : Type} [CommRing C] (i half : C)
    (hi : i^4 = 1) (unitHalf : 2 * half = 1) (u v : Wedge) :
    half^6 * physicalExteriorSum i u v =
      half * sumOver directions (fun n => Int.cast (planeWave n (maskOf u)) *
        Int.cast (planeWave n (maskOf v))) := by
  rw [raw_physical_plane_gram i hi]
  have scale : half^6 * (32 : C) = half := by
    calc
      _ = (2 * half)^5 * half := by grind
      _ = _ := by rw [unitHalf]; grind
  rw [← Semiring.mul_assoc, scale]

/-- Leibniz determinant of a single physical Pauli restricted to the
chosen four input and four output sites. -/
def pauliMinor {C : Type} [CommRing C] (i : C) (w : Word 3) (u v : Wedge) : C :=
  sumOver permutations fun p =>
    let e := tensorFour (wordEntry i w) (pointBits (tupleOf u))
      (pointBits (permuted (tupleOf v) p))
    if oddPermutation p then -e else e

private theorem signed_sum {C α : Type} [CommRing C] (b : Bool) (xs : List α) (f : α → C) :
    (if b then -sumOver xs f else sumOver xs f) =
      sumOver xs (fun x => if b then -(f x) else f x) := by
  induction xs with
  | nil => cases b <;> simp [sumOver] <;> grind
  | cons x xs ih =>
    cases b <;> simp [sumOver] at * <;> grind

theorem physicalExteriorSum_eq_pauli_minors {C : Type} [CommRing C] (i : C) (u v : Wedge) :
    physicalExteriorSum i u v = sumOver (words 3) (fun w => pauliMinor i w u v) := by
  unfold physicalExteriorSum unnormalizedTwirl pauliMinor
  simp only [signed_sum]
  rw [sumOverSwap permutations (words 3)]

/-- The physical normalization divides by 64. The plane-wave coefficients
here are 0 or 1; dividing their Gram matrix by two normalizes each wave. -/
theorem twice_normalized_pauli_minor_sum {C : Type} [CommRing C] (i norm : C)
    (hi : i^4 = 1) (hnorm : 64 * norm = 1) (u v : Wedge) :
    2 * (norm * sumOver (words 3) (fun w => pauliMinor i w u v)) =
      sumOver directions (fun n => Int.cast (planeWave n (maskOf u)) *
        Int.cast (planeWave n (maskOf v))) := by
  rw [← physicalExteriorSum_eq_pauli_minors, raw_physical_plane_gram i hi]
  grind

end RankSeven.ExteriorPauliBase

#print axioms RankSeven.ExteriorPauliBase.normalized_physical_plane_gram
