import Rank7PauliTensor

namespace RankSeven.Pauli

open Lean.Grind

variable {C : Type} [CommRing C]

def firstBits {n : Nat} (u : Four (Basis (n+1))) : Four Bool :=
  ((u.1.1.1, u.1.2.1), (u.2.1.1, u.2.2.1))

def remainingBits {n : Nat} (u : Four (Basis (n+1))) : Four (Basis n) :=
  ((u.1.1.2, u.1.2.2), (u.2.1.2, u.2.2.2))

/-- Each of the four copies must have the same bit flip, and their input
    bits must have even parity. -/
def allowedBit (u v : Four Bool) : Bool :=
  let flip := Bool.xor u.1.1 v.1.1
  (flip == Bool.xor u.1.2 v.1.2) && (flip == Bool.xor u.2.1 v.2.1) &&
    (flip == Bool.xor u.2.2 v.2.2) &&
    !(Bool.xor (Bool.xor u.1.1 u.1.2) (Bool.xor u.2.1 u.2.2))

def allowedTwirlEntry : (n : Nat) → Four (Basis n) → Four (Basis n) → Bool
  | 0, _, _ => true
  | n+1, u, v => allowedBit (firstBits u) (firstBits v) &&
      allowedTwirlEntry n (remainingBits u) (remainingBits v)

set_option maxHeartbeats 1600000 in
theorem sumSingleQubitAxes (i : C) (unitFourth : i ^ 4 = 1) (u v : Four Bool) :
    tensorFour (entry i .identity) u v + tensorFour (entry i .x) u v +
      tensorFour (entry i .y) u v + tensorFour (entry i .z) u v =
      if allowedBit u v then 2 else 0 := by
  rcases u with ⟨⟨u₀, u₁⟩, ⟨u₂, u₃⟩⟩
  rcases v with ⟨⟨v₀, v₁⟩, ⟨v₂, v₃⟩⟩
  cases u₀ <;> cases u₁ <;> cases u₂ <;> cases u₃ <;>
    cases v₀ <;> cases v₁ <;> cases v₂ <;> cases v₃ <;>
    simp [allowedBit, tensorFour, tensor, entry] <;> grind

private theorem fourWordCons {n : Nat} (i : C) (a : Axis) (w : Word n)
    (u v : Four (Basis (n+1))) :
    tensorFour (wordEntry i (.cons a w)) u v =
      tensorFour (entry i a) (firstBits u) (firstBits v) *
        tensorFour (wordEntry i w) (remainingBits u) (remainingBits v) := by
  simp only [tensorFour, tensor, firstBits, remainingBits]
  change
    ((entry i a u.1.1.1 v.1.1.1 * wordEntry i w u.1.1.2 v.1.1.2) *
      (entry i a u.1.2.1 v.1.2.1 * wordEntry i w u.1.2.2 v.1.2.2)) *
    ((entry i a u.2.1.1 v.2.1.1 * wordEntry i w u.2.1.2 v.2.1.2) *
      (entry i a u.2.2.1 v.2.2.1 * wordEntry i w u.2.2.2 v.2.2.2)) = _
  grind

private theorem twirlEntryStep {n : Nat} (i : C) (unitFourth : i ^ 4 = 1)
    (u v : Four (Basis (n+1))) :
    unnormalizedTwirl i u v =
      (if allowedBit (firstBits u) (firstBits v) then 2 else 0) *
        unnormalizedTwirl i (remainingBits u) (remainingBits v) := by
  unfold unnormalizedTwirl
  rw [words, sumOverFlatMap, sumOverMulLeft]
  apply sumOverCongr
  intro w
  let axisEntry a := tensorFour (entry i a) (firstBits u) (firstBits v)
  let tail := tensorFour (wordEntry i w) (remainingBits u) (remainingBits v)
  simp only [sumOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fourWordCons]
  change axisEntry .identity * tail +
      (axisEntry .x * tail + (axisEntry .y * tail + (axisEntry .z * tail + 0))) =
    (if allowedBit (firstBits u) (firstBits v) then 2 else 0) * tail
  have head := sumSingleQubitAxes i unitFourth (firstBits u) (firstBits v)
  calc
    _ = (axisEntry .identity + axisEntry .x + axisEntry .y + axisEntry .z) * tail := by grind
    _ = _ := by rw [head]

/-- Exact computational entries of the fourth-copy Pauli sum in every
    qubit dimension. This gives its common-translation and parity support. -/
theorem unnormalizedTwirlEntry {n : Nat} (i : C) (unitFourth : i ^ 4 = 1)
    (u v : Four (Basis n)) :
    unnormalizedTwirl i u v = if allowedTwirlEntry n u v then (2 : C)^n else 0 := by
  induction n with
  | zero =>
    simp [unnormalizedTwirl, words, tensorFour, tensor, wordEntry, sumOver, allowedTwirlEntry]
    grind
  | succ n ih =>
    rw [twirlEntryStep i unitFourth, ih]
    rw [allowedTwirlEntry, Semiring.pow_succ]
    cases allowedBit (firstBits u) (firstBits v) <;>
      cases allowedTwirlEntry n (remainingBits u) (remainingBits v) <;>
      simp <;> grind

/-- The conventional one-side projector has entries 2⁻ⁿ on its support. -/
theorem normalizedTwirlEntry {n : Nat} (i half : C) (unitFourth : i ^ 4 = 1)
    (unitHalf : 2*half = 1) (u v : Four (Basis n)) :
    half ^ (n+n) * unnormalizedTwirl i u v =
      if allowedTwirlEntry n u v then half ^ n else 0 := by
  have scale (k : Nat) : half ^ (k+k) * (2 : C)^k = half ^ k := by
    induction k with
    | zero => grind
    | succ k ih =>
      have exponents : k+1+(k+1) = (k+k)+1+1 := by omega
      rw [exponents, Semiring.pow_succ, Semiring.pow_succ,
        Semiring.pow_succ (2 : C) k, Semiring.pow_succ half k]
      calc
        _ = (half^(k+k) * (2 : C)^k) * (2*half) * half := by grind
        _ = _ := by rw [ih, unitHalf]; grind
  rw [unnormalizedTwirlEntry i unitFourth]
  cases allowedTwirlEntry n u v <;> simp <;> first | exact scale n | grind

def xorBasis : (n : Nat) → Basis n → Basis n → Basis n
  | 0, _, _ => ()
  | n+1, a, b => (Bool.xor a.1 b.1, xorBasis n a.2 b.2)

def affinePlaneFrame {n : Nat} (origin a b : Basis n) : Four (Basis n) :=
  ((origin, xorBasis n origin a),
    (xorBasis n origin b, xorBasis n (xorBasis n origin a) b))

private theorem parallelBits (x y a b : Bool) :
    allowedBit ((x, Bool.xor x a), (Bool.xor x b, Bool.xor (Bool.xor x a) b))
      ((y, Bool.xor y a), (Bool.xor y b, Bool.xor (Bool.xor y a) b)) = true := by
  cases x <;> cases y <;> cases a <;> cases b <;> decide

/-- In the shared-generator orientation, every pair of parallel affine
    plane frames lies on the support of the physical Pauli projector. -/
theorem parallelPlaneAllowed {n : Nat} (x y a b : Basis n) :
    allowedTwirlEntry n (affinePlaneFrame x a b) (affinePlaneFrame y a b) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (allowedBit ((x.1, Bool.xor x.1 a.1), (Bool.xor x.1 b.1, Bool.xor (Bool.xor x.1 a.1) b.1))
      ((y.1, Bool.xor y.1 a.1), (Bool.xor y.1 b.1, Bool.xor (Bool.xor y.1 a.1) b.1)) &&
      allowedTwirlEntry n (affinePlaneFrame x.2 a.2 b.2) (affinePlaneFrame y.2 a.2 b.2)) = true
    rw [parallelBits, ih]
    rfl

theorem normalizedTwirlParallelPlanes {n : Nat} (i half : C) (unitFourth : i ^ 4 = 1)
    (unitHalf : 2*half = 1) (x y a b : Basis n) :
    half ^ (n+n) * unnormalizedTwirl i (affinePlaneFrame x a b) (affinePlaneFrame y a b) =
      half ^ n := by
  rw [normalizedTwirlEntry i half unitFourth unitHalf, parallelPlaneAllowed]
  rfl

end RankSeven.Pauli

#print axioms RankSeven.Pauli.sumSingleQubitAxes
#print axioms RankSeven.Pauli.unnormalizedTwirlEntry
#print axioms RankSeven.Pauli.normalizedTwirlParallelPlanes
