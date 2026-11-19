import Rank7ExteriorOperators

namespace RankSeven

open Lean.Grind

/-- Complex scalars as two coordinates, with multiplication given by i² = -1. -/
structure ComplexScalar (R : Type) where
  re : R
  im : R

namespace ComplexScalar

variable {R : Type} [CommRing R]

attribute [local instance] Semiring.natCast Ring.intCast

omit [CommRing R] in
theorem ext {z w : ComplexScalar R} (real : z.re = w.re) (imag : z.im = w.im) : z = w := by
  cases z
  cases w
  congr

/-- Include a real scalar as a complex scalar. -/
def ofReal (a : R) : ComplexScalar R := ⟨a, 0⟩

private def add (z w : ComplexScalar R) : ComplexScalar R :=
  ⟨z.re + w.re, z.im + w.im⟩

private def neg (z : ComplexScalar R) : ComplexScalar R := ⟨-z.re, -z.im⟩

private def sub (z w : ComplexScalar R) : ComplexScalar R :=
  ⟨z.re - w.re, z.im - w.im⟩

private def mul (z w : ComplexScalar R) : ComplexScalar R :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

private def power (z : ComplexScalar R) : Nat → ComplexScalar R
  | 0 => ofReal 1
  | n + 1 => mul (power z n) z

instance : CommRing (ComplexScalar R) where
  add := add
  mul := mul
  neg := neg
  sub := sub
  natCast := ⟨fun n => ofReal (Nat.cast n)⟩
  ofNat n := ⟨ofReal (OfNat.ofNat n)⟩
  intCast := ⟨fun n => ofReal (Int.cast n)⟩
  nsmul := ⟨fun n z => mul (ofReal (Nat.cast n)) z⟩
  zsmul := ⟨fun n z => mul (ofReal (Int.cast n)) z⟩
  npow := ⟨power⟩
  add_zero z := by
    change add z (ofReal 0) = z
    apply ext <;> simp only [add, ofReal] <;> grind
  add_comm z w := by
    change add z w = add w z
    apply ext <;> simp only [add] <;> grind
  add_assoc z w u := by
    change add (add z w) u = add z (add w u)
    apply ext <;> simp only [add] <;> grind
  mul_comm z w := by
    change mul z w = mul w z
    apply ext <;> simp only [mul] <;> grind
  mul_assoc z w u := by
    change mul (mul z w) u = mul z (mul w u)
    apply ext <;> simp only [mul] <;> grind
  mul_one z := by
    change mul z (ofReal 1) = z
    apply ext <;> simp only [mul, ofReal] <;> grind
  one_mul z := by
    change mul (ofReal 1) z = z
    apply ext <;> simp only [mul, ofReal] <;> grind
  left_distrib z w u := by
    change mul z (add w u) = add (mul z w) (mul z u)
    apply ext <;> simp only [mul, add] <;> grind
  right_distrib z w u := by
    change mul (add z w) u = add (mul z u) (mul w u)
    apply ext <;> simp only [mul, add] <;> grind
  zero_mul z := by
    change mul (ofReal 0) z = ofReal 0
    apply ext <;> simp only [mul, ofReal] <;> grind
  mul_zero z := by
    change mul z (ofReal 0) = ofReal 0
    apply ext <;> simp only [mul, ofReal] <;> grind
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    apply ext
    · exact Semiring.ofNat_succ n
    · change (0 : R) = 0 + 0
      grind
  ofNat_eq_natCast n := by
    apply ext
    · exact Semiring.ofNat_eq_natCast n
    · rfl
  nsmul_eq_natCast_mul _ _ := rfl
  neg_add_cancel z := by
    change add (neg z) z = ofReal 0
    apply ext <;> simp only [add, neg, ofReal] <;> grind
  sub_eq_add_neg z w := by
    change sub z w = add z (neg w)
    apply ext <;> simp only [sub, add, neg] <;> grind
  neg_zsmul i z := by
    change mul (ofReal (Int.cast (-i))) z = neg (mul (ofReal (Int.cast i)) z)
    rw [Ring.intCast_neg]
    apply ext <;> simp only [mul, neg, ofReal] <;> grind
  zsmul_natCast_eq_nsmul n z := by
    change mul (ofReal (Int.cast (Int.ofNat n))) z = mul (ofReal (Nat.cast n)) z
    have castEq : (Int.cast (Int.ofNat n) : R) = (Nat.cast n : R) :=
      (Ring.intCast_ofNat n).trans (Semiring.ofNat_eq_natCast n)
    rw [castEq]
  intCast_ofNat n := by
    apply ext
    · exact Ring.intCast_ofNat n
    · rfl
  intCast_neg i := by
    apply ext
    · exact Ring.intCast_neg i
    · change (0 : R) = -0
      grind

@[simp] theorem re_zero : (0 : ComplexScalar R).re = 0 := rfl
@[simp] theorem im_zero : (0 : ComplexScalar R).im = 0 := rfl
@[simp] theorem re_one : (1 : ComplexScalar R).re = 1 := rfl
@[simp] theorem im_one : (1 : ComplexScalar R).im = 0 := rfl

@[simp] theorem re_ofReal (a : R) : (ofReal a).re = a := rfl
@[simp] theorem im_ofReal (a : R) : (ofReal a).im = 0 := rfl

@[simp] theorem re_add (z w : ComplexScalar R) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : ComplexScalar R) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_neg (z : ComplexScalar R) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : ComplexScalar R) : (-z).im = -z.im := rfl
@[simp] theorem re_sub (z w : ComplexScalar R) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : ComplexScalar R) : (z - w).im = z.im - w.im := rfl

@[simp] theorem re_mul (z w : ComplexScalar R) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl

@[simp] theorem im_mul (z w : ComplexScalar R) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- Complex conjugation. -/
def star (z : ComplexScalar R) : ComplexScalar R := ⟨z.re, -z.im⟩

@[simp] theorem re_star (z : ComplexScalar R) : (star z).re = z.re := rfl
@[simp] theorem im_star (z : ComplexScalar R) : (star z).im = -z.im := rfl

@[simp] theorem star_star (z : ComplexScalar R) : star (star z) = z := by
  apply ext <;> simp <;> grind

@[simp] theorem star_add (z w : ComplexScalar R) : star (z + w) = star z + star w := by
  apply ext <;> simp <;> grind

@[simp] theorem star_mul (z w : ComplexScalar R) : star (z * w) = star z * star w := by
  apply ext <;> simp <;> grind

@[simp] theorem star_ofReal (a : R) : star (ofReal a) = ofReal a := by
  apply ext <;> simp <;> grind

/-- The conjugation interface for exterior creation and annihilation. -/
def scalarConjugation : ExteriorOperators.ScalarConjugation (ComplexScalar R) where
  star := star
  involutive := star_star
  fixesInteger i := star_ofReal (Int.cast i)
  mapAdd := star_add
  mapMul := star_mul

/-- The distinguished square root of minus one. -/
def imaginaryUnit : ComplexScalar R := ⟨0, 1⟩

@[simp] theorem re_imaginaryUnit : (imaginaryUnit (R := R)).re = 0 := rfl
@[simp] theorem im_imaginaryUnit : (imaginaryUnit (R := R)).im = 1 := rfl

theorem imaginaryUnit_sq : (imaginaryUnit (R := R)) ^ 2 = -1 := by
  rw [Semiring.pow_succ, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]
  apply ext <;> simp <;> grind

theorem imaginaryUnit_fourth : (imaginaryUnit (R := R)) ^ 4 = 1 := by
  have square := imaginaryUnit_sq (R := R)
  grind

/-- The squared length of a complex scalar in real coordinates. -/
def normSq (z : ComplexScalar R) : R := z.re ^ 2 + z.im ^ 2

@[simp] theorem normSq_zero : normSq (0 : ComplexScalar R) = 0 := by
  unfold normSq
  simp only [re_zero, im_zero]
  grind

@[simp] theorem normSq_one : normSq (1 : ComplexScalar R) = 1 := by
  unfold normSq
  simp only [re_one, im_one]
  grind

theorem normSq_ofReal (a : R) : normSq (ofReal a) = a ^ 2 := by
  unfold normSq
  simp only [re_ofReal, im_ofReal]
  grind

theorem normSq_star (z : ComplexScalar R) : normSq (star z) = normSq z := by
  unfold normSq
  simp only [re_star, im_star]
  grind

theorem normSq_mul (z w : ComplexScalar R) : normSq (z * w) = normSq z * normSq w := by
  unfold normSq
  simp only [re_mul, im_mul]
  grind

theorem star_mul_self (z : ComplexScalar R) : star z * z = ofReal (normSq z) := by
  apply ext <;> simp [normSq] <;> grind

@[simp] theorem re_star_mul_self (z : ComplexScalar R) :
    (star z * z).re = normSq z := by
  rw [star_mul_self, re_ofReal]

@[simp] theorem im_star_mul_self (z : ComplexScalar R) :
    (star z * z).im = 0 := by
  rw [star_mul_self, im_ofReal]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem squarePosOfNeZero (a : R) (nonzero : a ≠ 0) : 0 < a ^ 2 := by
  by_cases positive : 0 < a
  · have product := OrderedRing.mul_pos positive positive
    grind
  · have opposite : 0 < -a := by grind
    have product := OrderedRing.mul_pos opposite opposite
    grind

theorem normSq_nonnegative (z : ComplexScalar R) : 0 ≤ normSq z := by
  unfold normSq
  have realNonnegative := squareNonnegative z.re
  have imagNonnegative := squareNonnegative z.im
  grind

theorem normSq_positive (z : ComplexScalar R) (nonzero : z ≠ 0) : 0 < normSq z := by
  unfold normSq
  by_cases realZero : z.re = 0
  · have imagNonzero : z.im ≠ 0 := by
      intro imagZero
      exact nonzero (ext (realZero.trans re_zero.symm) (imagZero.trans im_zero.symm))
    have imagPositive := squarePosOfNeZero z.im imagNonzero
    grind
  · have realPositive := squarePosOfNeZero z.re realZero
    have imagNonnegative := squareNonnegative z.im
    grind

theorem normSq_eq_zero_iff (z : ComplexScalar R) : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro value
    by_cases zero : z = 0
    · exact zero
    · have positive := normSq_positive z zero
      grind
  · intro zero
    rw [zero, normSq_zero]

theorem mul_ne_zero (z w : ComplexScalar R) (nonzeroZ : z ≠ 0) (nonzeroW : w ≠ 0) :
    z * w ≠ 0 := by
  intro zero
  have realPositive := OrderedRing.mul_pos (normSq_positive z nonzeroZ) (normSq_positive w nonzeroW)
  have value := normSq_mul z w
  rw [zero, normSq_zero] at value
  grind

theorem mul_eq_zero (z w : ComplexScalar R) : z * w = 0 ↔ z = 0 ∨ w = 0 := by
  constructor
  · intro zero
    by_cases zeroZ : z = 0
    · exact Or.inl zeroZ
    · by_cases zeroW : w = 0
      · exact Or.inr zeroW
      · exact False.elim (mul_ne_zero z w zeroZ zeroW zero)
  · rintro (zeroZ | zeroW)
    · rw [zeroZ, Semiring.zero_mul]
    · rw [zeroW, Semiring.mul_zero]

end ComplexScalar
end RankSeven
