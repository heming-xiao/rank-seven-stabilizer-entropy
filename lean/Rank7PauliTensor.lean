import Rank7PauliReduction

namespace RankSeven.Pauli

open Lean.Grind

variable {C α β γ δ : Type} [CommRing C]

def productIndices (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

def tensor (A : α → β → C) (B : γ → δ → C) (i : α × γ) (j : β × δ) : C :=
  A i.1 j.1 * B i.2 j.2

private theorem sumOverAppend (xs ys : List α) (f : α → C) :
    sumOver (xs ++ ys) f = sumOver xs f + sumOver ys f := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons x rest ih =>
    simp only [sumOver, List.cons_append, List.map_cons, List.sum_cons] at *
    grind

private theorem sumOverProductIndices (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f = sumOver xs (fun x => sumOver ys (fun y => f (x, y))) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    unfold productIndices
    rw [List.flatMap_cons, sumOverAppend]
    change sumOver (ys.map (fun y => (x, y))) f + sumOver (productIndices rest ys) f =
      sumOver ys (fun y => f (x, y)) + sumOver rest (fun x => sumOver ys (fun y => f (x, y)))
    rw [ih]
    simp [sumOver, List.map_map, Function.comp_def]

theorem sumOverMulLeft (xs : List α) (f : α → C) (z : C) :
    z * sumOver xs f = sumOver xs (fun a => z * f a) := by
  rw [CommSemiring.mul_comm z, sumOverMulRight]
  apply sumOverCongr
  intro a
  exact CommSemiring.mul_comm _ _

theorem factorProductSum (xs : List α) (ys : List β) (f : α → C) (g : β → C) :
    sumOver (productIndices xs ys) (fun p => f p.1 * g p.2) =
      sumOver xs f * sumOver ys g := by
  rw [sumOverProductIndices, sumOverMulRight]
  apply sumOverCongr
  intro x
  exact (sumOverMulLeft ys g (f x)).symm

theorem tensorExpectation
    (left₁ : List α) (right₁ : List β) (left₂ : List γ) (right₂ : List δ)
    (T₁ barT₁ : α → β → C) (T₂ barT₂ : γ → δ → C)
    (P₁ : α → α → C) (Q₁ : β → β → C) (P₂ : γ → γ → C) (Q₂ : δ → δ → C) :
    productExpectation (productIndices left₁ left₂) (productIndices right₁ right₂)
      (tensor T₁ T₂) (tensor barT₁ barT₂) (tensor P₁ P₂) (tensor Q₁ Q₂) =
      productExpectation left₁ right₁ T₁ barT₁ P₁ Q₁ *
      productExpectation left₂ right₂ T₂ barT₂ P₂ Q₂ := by
  let f a b c d := barT₁ a b * P₁ a c * T₁ c d * Q₁ b d
  let g a b c d := barT₂ a b * P₂ a c * T₂ c d * Q₂ b d
  let fD a b c := sumOver right₁ (f a b c)
  let gD a b c := sumOver right₂ (g a b c)
  let fC a b := sumOver left₁ (fD a b)
  let gC a b := sumOver left₂ (gD a b)
  let fB a := sumOver right₁ (fC a)
  let gB a := sumOver right₂ (gC a)
  have eliminateD (a : α × γ) (b : β × δ) (c : α × γ) :
      sumOver (productIndices right₁ right₂) (fun d => f a.1 b.1 c.1 d.1 * g a.2 b.2 c.2 d.2) =
        fD a.1 b.1 c.1 * gD a.2 b.2 c.2 :=
    factorProductSum right₁ right₂ (f a.1 b.1 c.1) (g a.2 b.2 c.2)
  have eliminateC (a : α × γ) (b : β × δ) :
      sumOver (productIndices left₁ left₂) (fun c =>
        sumOver (productIndices right₁ right₂) (fun d => f a.1 b.1 c.1 d.1 * g a.2 b.2 c.2 d.2)) =
        fC a.1 b.1 * gC a.2 b.2 :=
    (sumOverCongr _ (eliminateD a b)).trans (factorProductSum left₁ left₂ (fD a.1 b.1) (gD a.2 b.2))
  have eliminateB (a : α × γ) :
      sumOver (productIndices right₁ right₂) (fun b => sumOver (productIndices left₁ left₂) (fun c =>
        sumOver (productIndices right₁ right₂) (fun d => f a.1 b.1 c.1 d.1 * g a.2 b.2 c.2 d.2))) =
        fB a.1 * gB a.2 :=
    (sumOverCongr _ (eliminateC a)).trans (factorProductSum right₁ right₂ (fC a.1) (gC a.2))
  unfold productExpectation
  calc
    _ = sumOver (productIndices left₁ left₂) (fun a =>
          sumOver (productIndices right₁ right₂) (fun b =>
            sumOver (productIndices left₁ left₂) (fun c =>
              sumOver (productIndices right₁ right₂) (fun d =>
                f a.1 b.1 c.1 d.1 * g a.2 b.2 c.2 d.2)))) := by
      apply sumOverCongr
      intro a
      apply sumOverCongr
      intro b
      apply sumOverCongr
      intro c
      apply sumOverCongr
      intro d
      dsimp [tensor, f, g]
      grind
    _ = _ := (sumOverCongr _ eliminateB).trans (factorProductSum left₁ left₂ fB gB)

abbrev Four (α : Type) := (α × α) × (α × α)

def fourIndices (xs : List α) : List (Four α) :=
  productIndices (productIndices xs xs) (productIndices xs xs)

def tensorFour (A : α → β → C) : Four α → Four β → C :=
  tensor (tensor A A) (tensor A A)

theorem fourthExpectation (left : List α) (right : List β) (T barT : α → β → C)
    (P : α → α → C) (Q : β → β → C) :
    (productExpectation left right T barT P Q) ^ 4 =
      productExpectation (fourIndices left) (fourIndices right)
        (tensorFour T) (tensorFour barT) (tensorFour P) (tensorFour Q) := by
  simp only [tensorFour, fourIndices, tensorExpectation]
  grind

section OperatorSum

variable {ι κ : Type}

theorem sumExpectationsLeft (left : List α) (right : List β) (keys : List ι) (T barT : α → β → C)
    (P : ι → α → α → C) (Q : β → β → C) :
    sumOver keys (fun key => productExpectation left right T barT (P key) Q) =
      productExpectation left right T barT (fun a b => sumOver keys (fun key => P key a b)) Q := by
  unfold productExpectation
  rw [sumOverSwap keys left]
  apply sumOverCongr
  intro a
  rw [sumOverSwap keys right]
  apply sumOverCongr
  intro b
  rw [sumOverSwap keys left]
  apply sumOverCongr
  intro c
  rw [sumOverSwap keys right]
  apply sumOverCongr
  intro d
  change (sumOver keys (fun key => barT a b * P key a c * T c d * Q b d)) =
    barT a b * (sumOver keys (fun key => P key a c)) * T c d * Q b d
  rw [sumOverMulLeft, sumOverMulRight, sumOverMulRight]

theorem sumExpectationsRight (left : List α) (right : List β) (keys : List κ) (T barT : α → β → C)
    (P : α → α → C) (Q : κ → β → β → C) :
    sumOver keys (fun key => productExpectation left right T barT P (Q key)) =
      productExpectation left right T barT P (fun a b => sumOver keys (fun key => Q key a b)) := by
  unfold productExpectation
  rw [sumOverSwap keys left]
  apply sumOverCongr
  intro a
  rw [sumOverSwap keys right]
  apply sumOverCongr
  intro b
  rw [sumOverSwap keys left]
  apply sumOverCongr
  intro c
  rw [sumOverSwap keys right]
  apply sumOverCongr
  intro d
  rw [sumOverMulLeft]

/-- The two local fourth-copy operator sums give the full, unnormalized
    bipartite fourth moment. Take the lists of operators to be all sign-free
    Pauli words on the two sides. -/
theorem fourthOperatorSumEqTrace
    (left : List α) (right : List β) (leftKeys : List ι) (rightKeys : List κ)
    (T barT : α → β → C) (P : ι → α → α → C) (Q : κ → β → β → C) :
    sumOver leftKeys (fun p => sumOver rightKeys (fun q =>
      (productExpectation left right T barT (P p) (Q q)) ^ 4)) =
      coefficientTrace (fourIndices left) (fourIndices right) (tensorFour T) (tensorFour barT)
        (fun a b => sumOver leftKeys (fun p => tensorFour (P p) a b))
        (fun a b => sumOver rightKeys (fun q => tensorFour (Q q) a b)) := by
  simp only [fourthExpectation]
  calc
    _ = sumOver leftKeys (fun p =>
          productExpectation (fourIndices left) (fourIndices right) (tensorFour T) (tensorFour barT)
            (tensorFour (P p)) (fun a b => sumOver rightKeys (fun q => tensorFour (Q q) a b))) :=
      sumOverCongr leftKeys (fun p => sumExpectationsRight _ _ _ _ _ _ _)
    _ = _ := by rw [sumExpectationsLeft, productExpectationEqTrace]

end OperatorSum

def qubitIndices : (n : Nat) → List (Basis n)
  | 0 => [()]
  | n + 1 => productIndices [false, true] (qubitIndices n)

theorem qubitIndicesLength (n : Nat) : (qubitIndices n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (productIndices [false, true] (qubitIndices n)).length = 2 ^ (n + 1)
    simp [productIndices]
    rw [ih, Nat.pow_succ]
    omega

theorem qubitIndicesComplete {n : Nat} (a : Basis n) : a ∈ qubitIndices n := by
  induction n with
  | zero => cases a; exact List.mem_cons_self
  | succ n ih =>
    rcases a with ⟨bit, rest⟩
    apply List.mem_flatMap.mpr
    refine ⟨bit, ?_, List.mem_map.mpr ⟨rest, ih rest, rfl⟩⟩
    cases bit <;> simp

def unnormalizedTwirl {n : Nat} (i : C) (u v : Four (Basis n)) : C :=
  sumOver (words n) (fun word => tensorFour (wordEntry i word) u v)

theorem unnormalizedTwirlTranspose {n : Nat} (i : C) (u v : Four (Basis n)) :
    unnormalizedTwirl i v u = unnormalizedTwirl i u v := by
  unfold unnormalizedTwirl
  apply sumOverCongr
  intro word
  let reorder (x : Four (Basis n)) : FourBasis n := (x.1.1, x.1.2, x.2.1, x.2.2)
  have entries (a b : Four (Basis n)) :
      tensorFour (wordEntry i word) a b = fourthEntry i word (reorder a) (reorder b) := by
    simp only [tensorFour, tensor, fourthEntry, reorder]
    grind
  rw [entries, entries]
  exact fourthEntryTranspose i word (reorder u) (reorder v)

def pauliMoment {m n : Nat} (i : C) (T barT : Basis m → Basis n → C) : C :=
  sumOver (words m) fun p => sumOver (words n) fun q =>
    (productExpectation (qubitIndices m) (qubitIndices n) T barT (wordEntry i p) (wordEntry i q)) ^ 4

theorem pauliMomentEqTrace {m n : Nat} (i : C) (T barT : Basis m → Basis n → C) :
    pauliMoment i T barT =
      coefficientTrace (fourIndices (qubitIndices m)) (fourIndices (qubitIndices n))
        (tensorFour T) (tensorFour barT) (unnormalizedTwirl i) (unnormalizedTwirl i) :=
  fourthOperatorSumEqTrace _ _ _ _ T barT (wordEntry i) (wordEntry i)

/-- Leading-zero embedding of the left coefficient index. -/
def padLeft (T : α → β → C) (a : Bool × α) (b : β) : C :=
  if a.1 then 0 else T a.2 b

theorem expectationPadLeft (left : List α) (right : List β)
    (T barT : α → β → C) (W : Bool → Bool → C) (P : α → α → C) (Q : β → β → C) :
    productExpectation (productIndices [false, true] left) right
      (padLeft T) (padLeft barT) (tensor W P) Q =
      W false false * productExpectation left right T barT P Q := by
  let zeroQubit (a : Bool) (_ : Unit) : C := if a then 0 else 1
  let trivialOp : Unit → Unit → C := fun _ _ => 1
  have localFactor : productExpectation [false, true] [()] zeroQubit zeroQubit W trivialOp =
      W false false := by
    simp only [productExpectation, sumOver, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zeroQubit, trivialOp, Bool.false_eq_true, ↓reduceIte]
    grind
  have unitSum (f : Unit × β → C) :
      sumOver (productIndices [()] right) f = sumOver right (fun b => f ((), b)) := by
    rw [sumOverProductIndices]
    change sumOver right (fun b => f ((), b)) + 0 = _
    grind
  have padded (M : α → β → C) (a : Bool × α) (b : β) :
      tensor zeroQubit M a ((), b) = padLeft M a b := by
    simp only [tensor, zeroQubit, padLeft]
    split <;> grind
  have rightOp (b d : β) : tensor trivialOp Q ((), b) ((), d) = Q b d := by
    simp [tensor, trivialOp] <;> grind
  have combined := tensorExpectation [false, true] [()] left right zeroQubit zeroQubit T barT W trivialOp P Q
  rw [localFactor] at combined
  simpa only [productExpectation, unitSum, padded, rightOp] using combined

theorem sumOverFlatMap {ι κ : Type} (keys : List ι) (parts : ι → List κ) (f : κ → C) :
    sumOver (keys.flatMap parts) f = sumOver keys (fun key => sumOver (parts key) f) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    rw [List.flatMap_cons, sumOverAppend, ih]
    rfl

private theorem pauliHeadContribution {m n : Nat} (i : C)
    (T barT : Basis m → Basis n → C) (w : Word m) (q : Word n) :
    sumOver [Word.cons .identity w, Word.cons .x w, Word.cons .y w, Word.cons .z w]
      (fun p => (productExpectation (qubitIndices (m + 1)) (qubitIndices n)
        (padLeft T) (padLeft barT) (wordEntry i p) (wordEntry i q)) ^ 4) =
      2 * (productExpectation (qubitIndices m) (qubitIndices n) T barT
        (wordEntry i w) (wordEntry i q)) ^ 4 := by
  have oneAxis (a : Axis) :
      productExpectation (qubitIndices (m + 1)) (qubitIndices n)
        (padLeft T) (padLeft barT) (wordEntry i (.cons a w)) (wordEntry i q) =
      entry i a false false * productExpectation (qubitIndices m) (qubitIndices n) T barT
        (wordEntry i w) (wordEntry i q) :=
    expectationPadLeft _ _ _ _ _ _ _
  simp only [sumOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, oneAxis, entry]
  grind

theorem pauliMomentPadLeft {m n : Nat} (i : C) (T barT : Basis m → Basis n → C) :
    pauliMoment i (m := m + 1) (padLeft T) (padLeft barT) = 2 * pauliMoment i T barT := by
  unfold pauliMoment
  rw [words, sumOverFlatMap, sumOverMulLeft]
  apply sumOverCongr
  intro w
  rw [sumOverSwap, sumOverMulLeft]
  apply sumOverCongr
  intro q
  exact pauliHeadContribution i T barT w q

def normalizedPauliMoment {m n : Nat} (i half : C) (T barT : Basis m → Basis n → C) : C :=
  half ^ (m + n) * pauliMoment i T barT

/-- The normalized fourth moment is invariant under adding an actual
    leading zero qubit, for rectangular coefficient matrices of all sizes. -/
theorem normalizedPauliMomentPadLeft {m n : Nat} (i half : C) (unitHalf : half + half = 1)
    (T barT : Basis m → Basis n → C) :
    normalizedPauliMoment i half (m := m + 1) (padLeft T) (padLeft barT) =
      normalizedPauliMoment i half T barT := by
  unfold normalizedPauliMoment
  rw [pauliMomentPadLeft, Nat.succ_add, Semiring.pow_succ]
  grind

def padLeftMany {m n : Nat} (T : Basis m → Basis n → C) :
    (k : Nat) → Basis (m+k) → Basis n → C
  | 0 => T
  | k + 1 => padLeft (padLeftMany T k)

theorem normalizedPauliMomentPadLeftMany {m n : Nat} (i half : C) (unitHalf : half + half = 1)
    (T barT : Basis m → Basis n → C) (k : Nat) :
    normalizedPauliMoment i half (padLeftMany T k) (padLeftMany barT k) =
      normalizedPauliMoment i half T barT := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (normalizedPauliMomentPadLeft i half unitHalf (padLeftMany T k) (padLeftMany barT k)).trans ih

end RankSeven.Pauli

#print axioms RankSeven.Pauli.tensorExpectation
#print axioms RankSeven.Pauli.fourthOperatorSumEqTrace
#print axioms RankSeven.Pauli.pauliMomentEqTrace
#print axioms RankSeven.Pauli.unnormalizedTwirlTranspose
#print axioms RankSeven.Pauli.qubitIndicesComplete
#print axioms RankSeven.Pauli.normalizedPauliMomentPadLeftMany
