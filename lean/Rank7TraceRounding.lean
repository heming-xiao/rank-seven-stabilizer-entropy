import Init.Grind

namespace RankSeven

open Lean.Grind

attribute [local instance] Semiring.natCast

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem traceNatCastStep {k l : Nat} (hlt : k < l) :
    (Nat.cast k : R) + 1 ≤ (Nat.cast l : R) := by
  have hk : k + 1 ≤ l := Nat.succ_le_of_lt hlt
  have split : k + 1 + (l - (k + 1)) = l := Nat.add_sub_of_le hk
  have nonnegative : (0 : R) ≤ (Nat.cast (l - (k + 1)) : R) :=
    OrderedRing.natCast_nonneg
  conv => rhs; rw [← split, Semiring.natCast_add, Semiring.natCast_succ]
  grind

/-- An integer part and remainder in [0,1) are uniquely determined by their sum. -/
theorem traceRoundingRemainderUnique (s r u : R) (k l : Nat)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hk : s = (Nat.cast k : R) + r) (hl : s = (Nat.cast l : R) + u) :
    k = l ∧ r = u := by
  have notLess : ∀ {i j : Nat} {a b : R},
      s = (Nat.cast i : R) + a → s = (Nat.cast j : R) + b → a < 1 → 0 ≤ b → ¬ i < j := by
    intro i j a b hi hj ha hb hlt
    have next : (Nat.cast i : R) + 1 ≤ (Nat.cast j : R) := traceNatCastStep hlt
    grind
  have hkl : ¬ k < l := notLess hk hl hr1 hu0
  have hlk : ¬ l < k := notLess hl hk hu1 hr0
  have same : k = l := Nat.le_antisymm (Nat.le_of_not_gt hlk) (Nat.le_of_not_gt hkl)
  exact ⟨same, by rw [same] at hk; grind⟩

/-- Adding one eigenvalue merges it with the current remainder, carrying
one unit when their sum reaches one. Both branches increase the square budget. -/
theorem traceRoundingCarry (xs : List R)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    ∃ (k : Nat) (r : R),
      (0 ≤ r ∧ r < 1) ∧ xs.sum = (Nat.cast k : R) + r ∧
      (xs.map (fun x => x * x)).sum ≤ (Nat.cast k : R) + r * r := by
  induction xs with
  | nil =>
    refine ⟨0, 0, ?_⟩
    simp only [List.sum_nil, List.map_nil, Semiring.natCast_zero]
    have hone : (0 : R) < 1 := OrderedRing.zero_lt_one
    grind
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    obtain ⟨k, r, ⟨hr0, hr1⟩, hsum, hsq⟩ :=
      ih (fun z hz => hxs z (List.mem_cons_of_mem x hz))
    by_cases below : x + r < 1
    · refine ⟨k, x + r, ?_⟩
      simp only [List.sum_cons, List.map_cons]
      have hprod := OrderedRing.mul_nonneg hx.1 hr0
      grind
    · refine ⟨k + 1, x + r - 1, ?_⟩
      simp only [List.sum_cons, List.map_cons, Semiring.natCast_succ]
      have hxGap : 0 ≤ 1 - x := by grind
      have hrGap : 0 ≤ 1 - r := by grind
      have hprod := OrderedRing.mul_nonneg hxGap hrGap
      grind

/-- Upper bound on the sum of squares for a prescribed integer part and
remainder of the trace. The carry proof supplies that decomposition. -/
theorem traceRoundingSumSquares (xs : List R)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) (k : Nat) (r : R)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hsum : xs.sum = (Nat.cast k : R) + r) :
    (xs.map (fun x => x * x)).sum ≤ (Nat.cast k : R) + r * r := by
  obtain ⟨l, u, ⟨hu0, hu1⟩, hsum', hsq⟩ := traceRoundingCarry xs hxs
  obtain ⟨sameK, sameR⟩ :=
    traceRoundingRemainderUnique xs.sum r u k l hr0 hr1 hu0 hu1 hsum hsum'
  simpa only [← sameK, ← sameR] using hsq

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem traceVarianceSum (xs : List R) :
    (xs.map (fun x => x * (1 - x))).sum =
      xs.sum - (xs.map (fun x => x * x)).sum := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil]; grind
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    grind

/-- Fractional trace rounding, used for the scalar deficit of a compression:
the sum of x(1−x) is at least r(1−r) for the unique trace remainder r. -/
theorem traceRoundingVariance (xs : List R)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) (k : Nat) (r : R)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hsum : xs.sum = (Nat.cast k : R) + r) :
    r * (1 - r) ≤ (xs.map (fun x => x * (1 - x))).sum := by
  have hsq := traceRoundingSumSquares xs hxs k r hr0 hr1 hsum
  rw [traceVarianceSum, hsum]
  grind

/-- The integer produced by the carry recursion is the floor of the trace,
as witnessed by the two bounding inequalities and the unique remainder. -/
theorem traceRoundingFloor (xs : List R)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    ∃ k : Nat, (Nat.cast k : R) ≤ xs.sum ∧ xs.sum < (Nat.cast k : R) + 1 ∧
      (∀ l : Nat, (Nat.cast l : R) ≤ xs.sum → xs.sum < (Nat.cast l : R) + 1 → l = k) := by
  obtain ⟨k, r, ⟨hr0, hr1⟩, hsum, _⟩ := traceRoundingCarry xs hxs
  refine ⟨k, by grind, by grind, ?_⟩
  intro l hlo hhi
  let u := xs.sum - (Nat.cast l : R)
  have hu0 : 0 ≤ u := by dsimp [u]; grind
  have hu1 : u < 1 := by dsimp [u]; grind
  have hsum' : xs.sum = (Nat.cast l : R) + u := by dsimp [u]; grind
  exact (traceRoundingRemainderUnique xs.sum r u k l hr0 hr1 hu0 hu1 hsum hsum').1.symm

end RankSeven
