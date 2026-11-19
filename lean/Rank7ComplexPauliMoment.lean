import Rank7ComplexExteriorBridge
import Rank7PauliFrames

namespace RankSeven.ComplexPauliMoment

open Lean.Grind Pauli
open ComplexScalar (star ofReal imaginaryUnit normSq)
open ComplexExterior (starSumOver)

variable {R α β γ : Type} [CommRing R]

def conjugate (A : α → β → ComplexScalar R) : α → β → ComplexScalar R := fun a b => star (A a b)

theorem conjugateMatMul (indices : List β) (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    conjugate (matMul indices A B) = matMul indices (conjugate A) (conjugate B) := by
  funext a c
  simp only [conjugate, matMul, starSumOver, ComplexScalar.star_mul]

theorem conjugateSchmidt (indices : List α) (U M V : α → α → ComplexScalar R)
    (realM : conjugate M = M) :
    conjugate (schmidtCoefficients indices U M V) =
      schmidtCoefficients indices (conjugate U) M (conjugate V) := by
  unfold schmidtCoefficients
  rw [conjugateMatMul, conjugateMatMul, realM]
  rfl

theorem axisHermitian (p : Axis) (a b : Bool) :
    star (entry (imaginaryUnit (R := R)) p a b) = entry imaginaryUnit p b a := by
  cases p <;> cases a <;> cases b <;> apply ComplexScalar.ext <;> simp [entry] <;> grind

theorem wordHermitian {n : Nat} (p : Word n) (a b : Basis n) :
    star (wordEntry (imaginaryUnit (R := R)) p a b) = wordEntry imaginaryUnit p b a := by
  induction p with
  | empty =>
    change star (ofReal (1:R)) = ofReal 1
    exact ComplexScalar.star_ofReal _
  | cons axis w ih =>
    rcases a with ⟨a, as⟩
    rcases b with ⟨b, bs⟩
    change star (entry imaginaryUnit axis a b * wordEntry imaginaryUnit w as bs) = _
    rw [ComplexScalar.star_mul, axisHermitian, ih]
    rfl

private theorem sumPairs {α β : Type} (xs : List α) (ys : List β) (f : α × β → ComplexScalar R) :
    sumOver (productIndices xs ys) f =
      sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  unfold productIndices
  rw [sumOverFlatMap]
  apply sumOverCongr
  intro x
  simp [sumOver, List.map_map, Function.comp_def]

/-- The tensor product of two Hermitian operators has a real expectation
    with the actual conjugate of the coefficient matrix. -/
theorem productExpectationHermitian (left : List α) (right : List β)
    (T : α → β → ComplexScalar R) (P : α → α → ComplexScalar R) (Q : β → β → ComplexScalar R)
    (pHermitian : ∀ a c, star (P a c) = P c a)
    (qHermitian : ∀ b d, star (Q b d) = Q d b) :
    star (productExpectation left right T (conjugate T) P Q) =
      productExpectation left right T (conjugate T) P Q := by
  let coords := productIndices left right
  let f (a b : α × β) := star (T a.1 a.2) * P a.1 b.1 * T b.1 b.2 * Q a.2 b.2
  have form : productExpectation left right T (conjugate T) P Q =
      sumOver coords (fun a => sumOver coords (f a)) := by
    unfold coords productExpectation
    simp only [sumPairs, f, conjugate]
  rw [form, starSumOver]
  calc
    _ = sumOver coords (fun a => sumOver coords (fun b => f b a)) := by
      apply sumOverCongr
      intro a
      rw [starSumOver]
      apply sumOverCongr
      intro b
      unfold f
      rw [ComplexScalar.star_mul, ComplexScalar.star_mul, ComplexScalar.star_mul,
        ComplexScalar.star_star, pHermitian, qHermitian]
      grind
    _ = _ := sumOverSwap coords coords (fun a b => f b a)

section Order

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The fourth power used by the tensor calculation equals the fourth
    power of the modulus for every physical product-Pauli expectation. -/
theorem pauliExpectationFourth {m n : Nat} (T : Basis m → Basis n → ComplexScalar R)
    (p : Word m) (q : Word n) :
    let z := productExpectation (qubitIndices m) (qubitIndices n) T (conjugate T)
      (wordEntry imaginaryUnit p) (wordEntry imaginaryUnit q)
    z^4 = ofReal ((normSq z)^2) := by
  dsimp only
  let z := productExpectation (qubitIndices m) (qubitIndices n) T (conjugate T)
    (wordEntry imaginaryUnit p) (wordEntry imaginaryUnit q)
  have self : star z = z :=
    productExpectationHermitian _ _ _ _ _ (wordHermitian p) (wordHermitian q)
  have img := congrArg ComplexScalar.im self
  rw [ComplexScalar.im_star] at img
  have imagZero : z.im = 0 := by grind
  have realZ : z = ofReal z.re := ComplexScalar.ext rfl imagZero
  change z^4 = ofReal ((normSq z)^2)
  rw [realZ, ComplexScalar.normSq_ofReal]
  apply ComplexScalar.ext <;>
    simp only [Semiring.pow_succ, Semiring.pow_zero, ComplexScalar.re_mul,
      ComplexScalar.im_mul, ComplexScalar.re_one, ComplexScalar.im_one,
      ComplexScalar.re_ofReal, ComplexScalar.im_ofReal] <;> grind

end Order
end RankSeven.ComplexPauliMoment

#print axioms RankSeven.ComplexPauliMoment.productExpectationHermitian
#print axioms RankSeven.ComplexPauliMoment.pauliExpectationFourth
