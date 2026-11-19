import Rank7PauliTensor

namespace RankSeven.Pauli

open Lean.Grind

variable {C α β γ δ : Type} [CommRing C]

def matMul (middle : List β) (A : α → β → C) (B : β → γ → C) (a : α) (c : γ) : C :=
  sumOver middle fun b => A a b * B b c

def transpose (A : α → β → C) (b : β) (a : α) : C := A a b

def trace (indices : List α) (A : α → α → C) : C := sumOver indices fun a => A a a

theorem matMulAssoc (middle₁ : List β) (middle₂ : List γ)
    (A : α → β → C) (B : β → γ → C) (D : γ → δ → C) :
    matMul middle₂ (matMul middle₁ A B) D = matMul middle₁ A (matMul middle₂ B D) := by
  funext a d
  unfold matMul
  simp only [sumOverMulRight, sumOverMulLeft]
  rw [sumOverSwap middle₂ middle₁]
  apply sumOverCongr
  intro b
  apply sumOverCongr
  intro c
  grind

omit [CommRing C] in
theorem transposeTranspose (A : α → β → C) : transpose (transpose A) = A := rfl

theorem transposeMatMul (middle : List β) (A : α → β → C) (B : β → γ → C) :
    transpose (matMul middle A B) = matMul middle (transpose B) (transpose A) := by
  funext c a
  unfold transpose matMul
  apply sumOverCongr
  intro b
  grind

theorem traceMatMulSwap (first : List α) (second : List β) (A : α → β → C) (B : β → α → C) :
    trace first (matMul second A B) = trace second (matMul first B A) := by
  unfold trace matMul
  rw [sumOverSwap first second]
  apply sumOverCongr
  intro b
  apply sumOverCongr
  intro a
  grind

theorem tensorMatMul {α' β' γ' : Type} (middle : List β) (middle' : List β')
    (A : α → β → C) (B : β → γ → C) (A' : α' → β' → C) (B' : β' → γ' → C) :
    tensor (matMul middle A B) (matMul middle' A' B') =
      matMul (productIndices middle middle') (tensor A A') (tensor B B') := by
  funext a c
  unfold tensor matMul
  rw [← factorProductSum middle middle']
  apply sumOverCongr
  intro b
  grind

theorem fourMatMul (middle : List β) (A : α → β → C) (B : β → γ → C) :
    tensorFour (matMul middle A B) =
      matMul (fourIndices middle) (tensorFour A) (tensorFour B) := by
  simp only [tensorFour, fourIndices, tensorMatMul]

theorem fourTranspose (A : α → β → C) :
    tensorFour (transpose A) = transpose (tensorFour A) := rfl

theorem coefficientTraceMatMul (left : List α) (right : List β) (T barT : α → β → C)
    (P : α → α → C) (Q : β → β → C) :
    coefficientTrace left right T barT P Q =
      trace right (matMul right (matMul left (matMul left (transpose barT) P) T) (transpose Q)) := rfl

def schmidtCoefficients (indices : List α) (U M V : α → α → C) : α → α → C :=
  matMul indices (matMul indices U M) (transpose V)

/-- When the middle matrix is symmetric and both fourth-copy operator sums
    are Pauli twirls, the two local frames enter the trace separately. -/
theorem frameTrace (indices : List α)
    (U barU H V barV J : α → α → C) (hs : transpose H = H) (js : transpose J = J) :
    coefficientTrace indices indices
      (schmidtCoefficients indices U H V) (schmidtCoefficients indices barU H barV) J J =
      trace indices (matMul indices
        (matMul indices (matMul indices H (matMul indices (matMul indices (transpose barU) J) U)) H)
        (matMul indices (matMul indices (transpose V) J) barV)) := by
  rw [coefficientTraceMatMul]
  simp only [schmidtCoefficients, transposeMatMul, transposeTranspose, hs, js, matMulAssoc]
  rw [traceMatMulSwap indices indices barV]
  simp only [matMulAssoc]

def pairedFrameTrace (indices : List α) (H A B : α → α → C) : C :=
  trace indices (matMul indices (matMul indices (matMul indices H A) H) B)

/-- The fourth Pauli moment on any balanced cut is the paired-frame trace
    with the unnormalized fourth-copy Pauli sums. `barU` and `barV` are the
    conjugate local-frame entries in the physical specialization. -/
theorem pauliMomentEqPairedFrameTrace {n : Nat} (i : C) (U barU M V barV : Basis n → Basis n → C)
    (middleSymmetric : transpose M = M) :
    let basis := qubitIndices n
    let fourBasis := fourIndices basis
    let J : Four (Basis n) → Four (Basis n) → C := unnormalizedTwirl i
    let A := matMul fourBasis (matMul fourBasis (transpose (tensorFour barU)) J) (tensorFour U)
    let B := matMul fourBasis (matMul fourBasis (transpose (tensorFour V)) J) (tensorFour barV)
    pauliMoment i (schmidtCoefficients basis U M V) (schmidtCoefficients basis barU M barV) =
      pairedFrameTrace fourBasis (tensorFour M) A B := by
  dsimp only
  rw [pauliMomentEqTrace]
  simp only [schmidtCoefficients, fourMatMul, fourTranspose]
  change coefficientTrace _ _ (schmidtCoefficients _ _ _ _) (schmidtCoefficients _ _ _ _) _ _ = _
  have hs : transpose (tensorFour M) = tensorFour M := by rw [← fourTranspose, middleSymmetric]
  have js : transpose (unnormalizedTwirl i (n := n)) = unnormalizedTwirl i := by
    funext a b
    exact unnormalizedTwirlTranspose i a b
  exact frameTrace _ _ _ _ _ _ _ hs js

/-- The balanced physical normalization (2^{-2n}) with the unnormalized
    local Pauli sums. Set `half` to the inverse of two. -/
theorem normalizedPauliMomentEqPairedFrameTrace {n : Nat} (i half : C)
    (U barU M V barV : Basis n → Basis n → C) (middleSymmetric : transpose M = M) :
    let basis := qubitIndices n
    let fourBasis := fourIndices basis
    let J : Four (Basis n) → Four (Basis n) → C := unnormalizedTwirl i
    let A := matMul fourBasis (matMul fourBasis (transpose (tensorFour barU)) J) (tensorFour U)
    let B := matMul fourBasis (matMul fourBasis (transpose (tensorFour V)) J) (tensorFour barV)
    normalizedPauliMoment i half (schmidtCoefficients basis U M V) (schmidtCoefficients basis barU M barV) =
      half ^ (n+n) * pairedFrameTrace fourBasis (tensorFour M) A B :=
  congrArg (fun x => half ^ (n+n) * x) (pauliMomentEqPairedFrameTrace i U barU M V barV middleSymmetric)

end RankSeven.Pauli

#print axioms RankSeven.Pauli.normalizedPauliMomentEqPairedFrameTrace
