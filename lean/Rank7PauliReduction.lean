import Init.Grind

namespace RankSeven

open Lean.Grind

namespace Pauli

inductive Axis where
  | identity | x | y | z
  deriving DecidableEq

/-- Computational basis of an (n)-qubit side. -/
def Basis : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Basis n

inductive Word : Nat → Type where
  | empty : Word 0
  | cons : Axis → Word n → Word (n + 1)

variable {C : Type} [CommRing C]

/-- Single-qubit Pauli entries, with `i` instantiated by the imaginary unit. -/
def entry (i : C) : Axis → Bool → Bool → C
  | .identity, false, false | .identity, true, true => 1
  | .x, false, true | .x, true, false => 1
  | .y, false, true => -i
  | .y, true, false => i
  | .z, false, false => 1
  | .z, true, true => -1
  | _, _, _ => 0

def axisSign : Axis → C
  | .y => -1
  | _ => 1

theorem entryTranspose (i : C) (axis : Axis) (u v : Bool) :
    entry i axis v u = axisSign axis * entry i axis u v := by
  cases axis <;> cases u <;> cases v <;> simp [entry, axisSign] <;> grind

def wordEntry (i : C) : {n : Nat} → Word n → Basis n → Basis n → C
  | _, .empty, _, _ => 1
  | _, .cons axis rest, (u, us), (v, vs) =>
    entry i axis u v * wordEntry i rest us vs

def wordSign : {n : Nat} → Word n → C
  | _, .empty => 1
  | _, .cons axis rest => axisSign axis * wordSign rest

theorem wordSignSquare {n : Nat} (w : Word n) : (wordSign w : C) ^ 2 = 1 := by
  induction w with
  | empty => simp [wordSign] <;> grind
  | cons axis rest ih =>
    have signSquare : (axisSign axis : C) ^ 2 = 1 := by
      cases axis <;> simp [axisSign] <;> grind
    simp only [wordSign]
    grind

theorem wordEntryTranspose {n : Nat} (i : C) (w : Word n) (u v : Basis n) :
    wordEntry i w v u = wordSign w * wordEntry i w u v := by
  induction w with
  | empty => simp [wordEntry, wordSign] <;> grind
  | cons axis rest ih =>
    rcases u with ⟨u, us⟩
    rcases v with ⟨v, vs⟩
    simp only [wordEntry, wordSign, entryTranspose i axis u v, ih us vs]
    grind

abbrev FourBasis (n : Nat) := Basis n × Basis n × Basis n × Basis n

def fourthEntry {n : Nat} (i : C) (w : Word n) (u v : FourBasis n) : C :=
  wordEntry i w u.1 v.1 * wordEntry i w u.2.1 v.2.1
    * wordEntry i w u.2.2.1 v.2.2.1 * wordEntry i w u.2.2.2 v.2.2.2

theorem fourthEntryTranspose {n : Nat} (i : C) (w : Word n) (u v : FourBasis n) :
    fourthEntry i w v u = fourthEntry i w u v := by
  have signSquare : (wordSign w : C) ^ 2 = 1 := wordSignSquare w
  have signFourth : (wordSign w : C) ^ 4 = 1 := by grind
  unfold fourthEntry
  rw [wordEntryTranspose i w u.1 v.1, wordEntryTranspose i w u.2.1 v.2.1,
    wordEntryTranspose i w u.2.2.1 v.2.2.1, wordEntryTranspose i w u.2.2.2 v.2.2.2]
  grind

def words : (n : Nat) → List (Word n)
  | 0 => [.empty]
  | n + 1 => (words n).flatMap fun rest =>
    [.cons .identity rest, .cons .x rest, .cons .y rest, .cons .z rest]

def twirlEntry {n : Nat} (i normalization : C) (u v : FourBasis n) : C :=
  normalization * (((words n).map fun w => fourthEntry i w u v).sum)

/-- The coefficient-matrix purity reduction uses (J^{\mathsf T}=J).
    Each word contributes a symmetric fourth tensor power, including odd-Y words. -/
theorem twirlTranspose {n : Nat} (i normalization : C) (u v : FourBasis n) :
    twirlEntry i normalization v u = twirlEntry i normalization u v := by
  unfold twirlEntry
  congr 2
  exact List.map_congr_left (fun w _ => fourthEntryTranspose i w u v)

/-- A tensor product with a leading zero qubit leaves the normalized fourth
    moment unchanged. The factors are the I, X, Y and Z expectations on |0⟩. -/
theorem zeroAncillaFourthMoment (i half moment : C) (normalization : half + half = 1) :
    half * ((entry i .identity false false)^4 * moment
      + (entry i .x false false)^4 * moment + (entry i .y false false)^4 * moment
      + (entry i .z false false)^4 * moment) = moment := by
  simp [entry]
  grind

section CoefficientMatrix

variable {α β : Type}

def sumOver {ι : Type} (indices : List ι) (term : ι → C) : C :=
  (indices.map term).sum

theorem sumOverCongr {ι : Type} (indices : List ι) {f g : ι → C}
    (h : ∀ a, f a = g a) : sumOver indices f = sumOver indices g := by
  unfold sumOver
  rw [List.map_congr_left (fun a _ => h a)]

theorem sumOverAdd {ι : Type} (indices : List ι) (f g : ι → C) :
    sumOver indices (fun a => f a + g a) = sumOver indices f + sumOver indices g := by
  induction indices with
  | nil => simp [sumOver] <;> grind
  | cons a rest ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    grind

theorem sumOverMulRight {ι : Type} (indices : List ι) (f : ι → C) (z : C) :
    sumOver indices f * z = sumOver indices (fun a => f a * z) := by
  induction indices with
  | nil => simp [sumOver] <;> grind
  | cons a rest ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    grind

theorem sumOverSwap (left : List α) (right : List β) (f : α → β → C) :
    sumOver left (fun a => sumOver right (f a)) =
      sumOver right (fun b => sumOver left (fun a => f a b)) := by
  induction left with
  | nil =>
    have zeros (indices : List β) : sumOver indices (fun _ => (0 : C)) = 0 := by
      induction indices with
      | nil => rfl
      | cons b rest ih =>
        simp only [sumOver, List.map_cons, List.sum_cons] at *
        grind
    exact (zeros right).symm
  | cons a rest ih =>
    change sumOver right (f a) + sumOver rest (fun a => sumOver right (f a)) =
      sumOver right (fun b => f a b + sumOver rest (fun a => f a b))
    rw [sumOverAdd, ih]

/-- The expectation of a product operator in a bipartite state whose
    coefficients are `T`. Use `barT` for the entrywise conjugate of `T`. -/
def productExpectation (left : List α) (right : List β) (T barT : α → β → C)
    (P : α → α → C) (Q : β → β → C) : C :=
  sumOver left fun a => sumOver right fun b => sumOver left fun c => sumOver right fun d =>
    barT a b * P a c * T c d * Q b d

/-- Trace of (T^\dagger P T Q^{\mathsf T}), with the indicated
    parenthesization of the four matrix factors. -/
def coefficientTrace (left : List α) (right : List β) (T barT : α → β → C)
    (P : α → α → C) (Q : β → β → C) : C :=
  sumOver right fun b => sumOver right fun d =>
    (sumOver left fun c => (sumOver left fun a => barT a b * P a c) * T c d) * Q b d

theorem productExpectationEqTrace (left : List α) (right : List β) (T barT : α → β → C)
    (P : α → α → C) (Q : β → β → C) :
    productExpectation left right T barT P Q = coefficientTrace left right T barT P Q := by
  let f a b c d := barT a b * P a c * T c d * Q b d
  calc
    _ = sumOver right (fun b => sumOver left (fun a => sumOver left (fun c =>
          sumOver right (fun d => f a b c d)))) :=
      sumOverSwap left right _
    _ = sumOver right (fun b => sumOver left (fun a => sumOver right (fun d =>
          sumOver left (fun c => f a b c d)))) := by
      apply sumOverCongr right
      intro b
      exact sumOverCongr left (fun a => sumOverSwap left right _)
    _ = sumOver right (fun b => sumOver right (fun d => sumOver left (fun a =>
          sumOver left (fun c => f a b c d)))) :=
      sumOverCongr right (fun b => sumOverSwap left right _)
    _ = sumOver right (fun b => sumOver right (fun d => sumOver left (fun c =>
          sumOver left (fun a => f a b c d)))) := by
      apply sumOverCongr right
      intro b
      exact sumOverCongr right (fun d => sumOverSwap left left _)
    _ = _ := by
      unfold coefficientTrace
      apply sumOverCongr right
      intro b
      apply sumOverCongr right
      intro d
      rw [sumOverMulRight]
      apply sumOverCongr left
      intro c
      rw [sumOverMulRight, sumOverMulRight]

end CoefficientMatrix

end Pauli

section PairedComparison

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def leftNorm : List (R × R) → R
  | [] => 0
  | (a, _) :: rest => a ^ 2 + leftNorm rest

def rightNorm : List (R × R) → R
  | [] => 0
  | (_, b) :: rest => b ^ 2 + rightNorm rest

def pairing : List (R × R) → R
  | [] => 0
  | (a, b) :: rest => a * b + pairing rest

theorem squareNonnegative (a : R) : 0 ≤ a ^ 2 := by
  by_cases sign : 0 ≤ a
  · have h := OrderedRing.mul_nonneg sign sign
    grind
  · have opposite : 0 ≤ -a := by grind
    have h := OrderedRing.mul_nonneg opposite opposite
    grind

private theorem gramIncrement (a b : R) (rest : List (R × R)) :
    0 ≤ a ^ 2 * rightNorm rest + b ^ 2 * leftNorm rest - 2 * a * b * pairing rest := by
  induction rest with
  | nil => simp [rightNorm, leftNorm, pairing] <;> grind
  | cons pair rest ih =>
    rcases pair with ⟨x, y⟩
    have square := squareNonnegative (a * y - b * x)
    simp only [leftNorm, rightNorm, pairing]
    grind

theorem pairingCauchySchwarz (pairs : List (R × R)) :
    pairing pairs ^ 2 ≤ leftNorm pairs * rightNorm pairs := by
  induction pairs with
  | nil => simp [pairing, leftNorm, rightNorm] <;> grind
  | cons pair rest ih =>
    rcases pair with ⟨a, b⟩
    have increment := gramIncrement a b rest
    simp only [leftNorm, rightNorm, pairing]
    grind

private theorem leftNormNonnegative (pairs : List (R × R)) : 0 ≤ leftNorm pairs := by
  induction pairs with
  | nil => simp [leftNorm]
  | cons pair rest ih =>
    rcases pair with ⟨a, b⟩
    have square := squareNonnegative a
    simp only [leftNorm]
    grind

/-- After expanding the Hermitian Hilbert–Schmidt inner product into real
    coordinates, the two paired bounds imply the same bound on the cross term. -/
theorem crossPurityLe (pairs : List (R × R)) (bound : R)
    (leftBound : leftNorm pairs ≤ bound) (rightBound : rightNorm pairs ≤ bound) :
    pairing pairs ≤ bound := by
  have nonnegative := leftNormNonnegative pairs
  have boundNonnegative : 0 ≤ bound := by grind
  have hright : 0 ≤ leftNorm pairs * (bound - rightNorm pairs) :=
    OrderedRing.mul_nonneg nonnegative (by grind)
  have hleft : 0 ≤ bound * (bound - leftNorm pairs) :=
    OrderedRing.mul_nonneg boundNonnegative (by grind)
  have cs := pairingCauchySchwarz pairs
  by_cases cross : pairing pairs ≤ bound
  · exact cross
  · have difference : 0 < pairing pairs - bound := by grind
    have sum : 0 < pairing pairs + bound := by grind
    have contradiction := OrderedRing.mul_pos difference sum
    grind

end PairedComparison

end RankSeven

#print axioms RankSeven.Pauli.twirlTranspose
#print axioms RankSeven.Pauli.zeroAncillaFourthMoment
#print axioms RankSeven.Pauli.productExpectationEqTrace
#print axioms RankSeven.crossPurityLe
