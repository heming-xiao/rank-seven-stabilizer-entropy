import Rank7ExteriorPauliBase

namespace RankSeven.ExteriorPauliBase

open RankSeven.Pauli RankSeven.ExteriorOccupation Lean.Grind

variable {C : Type} [CommRing C]

attribute [local instance] Ring.intCast

def wedgeIndices : List Wedge := List.finRange 70

def wave (normal : Direction) (w : Wedge) : C := Int.cast (planeWave normal (maskOf w))

def expandWaves (coeff : Direction → C) (w : Wedge) : C :=
  sumOver directions fun n => coeff n * wave n w

def waveCoordinates (u : Wedge → C) (n : Direction) : C :=
  sumOver wedgeIndices fun w => wave n w * u w

def wedgePairing (u v : Wedge → C) : C :=
  sumOver wedgeIndices fun w => u w * v w

def projectWaves (half : C) (u : Wedge → C) : Wedge → C :=
  expandWaves fun n => half * waveCoordinates u n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem waveGramInt :
    ∀ n m : Direction,
      sumOver wedgeIndices (fun w => planeWave n (maskOf w) * planeWave m (maskOf w)) =
        if n = m then (2 : Int) else 0 := by
  decide

private theorem castSum {α : Type} (xs : List α) (f : α → Int) :
    (Int.cast (sumOver xs f) : C) = sumOver xs fun x => Int.cast (f x) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons a rest ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    rw [Ring.intCast_add, ih]

theorem waveGram (n m : Direction) :
    sumOver wedgeIndices (fun w => (wave n w : C) * wave m w) = if n = m then 2 else 0 := by
  unfold wave
  simp only [← Ring.intCast_mul]
  rw [← castSum, waveGramInt]
  split
  · exact Ring.intCast_ofNat 2
  · exact Ring.intCast_ofNat 0

theorem sumOnIndex {α : Type} [DecidableEq α] (xs : List α) (i : α) (f : α → C)
    (distinct : xs.Nodup) (present : i ∈ xs) :
    sumOver xs (fun j => if i = j then f j else 0) = f i := by
  have zeros (ys : List α) : sumOver ys (fun _ => (0 : C)) = 0 := by
    induction ys with
    | nil => rfl
    | cons a rest ih =>
      change 0 + sumOver rest (fun _ => (0 : C)) = 0
      rw [ih]
      grind
  induction xs with
  | nil => cases present
  | cons j rest ih =>
    rcases List.nodup_cons.mp distinct with ⟨fresh, tailDistinct⟩
    by_cases eq : i = j
    · subst j
      have tail :
          sumOver rest (fun j => if i = j then f j else 0) = 0 := by
        have entry : (rest.map (fun j => if i = j then f j else 0)) = rest.map (fun _ => (0 : C)) := by
          apply List.map_congr_left
          intro j member
          have ne : ¬ i = j := fun h => fresh (h ▸ member)
          rw [ite_eq_right ne]
        unfold sumOver
        rw [entry]
        exact zeros rest
      change (if i = i then f i else 0) + sumOver rest (fun j => if i = j then f j else 0) = f i
      rw [ite_eq_left rfl, tail]
      grind
    · have tailPresent : i ∈ rest := by
        rcases List.mem_cons.mp present with h | restMember
        · exact False.elim (eq h)
        · exact restMember
      change (if i = j then f j else 0) + sumOver rest (fun j => if i = j then f j else 0) = f i
      rw [ite_eq_right eq, ih tailDistinct tailPresent]
      grind

theorem waveCoordinates_expand (coeff : Direction → C) (n : Direction) :
    waveCoordinates (expandWaves coeff) n = 2 * coeff n := by
  unfold waveCoordinates expandWaves
  simp only [sumOverMulLeft]
  rw [sumOverSwap wedgeIndices directions]
  have reduction (m : Direction) :
      sumOver wedgeIndices (fun w => wave n w * (coeff m * wave m w)) =
        if n = m then 2 * coeff m else 0 := by
    have entry (w : Wedge) :
        wave n w * (coeff m * wave m w) = (wave n w * wave m w) * coeff m := by grind
    rw [sumOverCongr _ entry, ← sumOverMulRight, waveGram n m]
    split <;> grind
  rw [sumOverCongr _ reduction]
  have distinct : directions.Nodup := by decide
  have present : n ∈ directions := by simp [directions]
  exact sumOnIndex directions n (fun m => 2 * coeff m) distinct present

theorem expandWaves_adjoint (coeff : Direction → C) (v : Wedge → C) :
    wedgePairing (expandWaves coeff) v =
      sumOver directions (fun n => coeff n * waveCoordinates v n) := by
  unfold wedgePairing expandWaves waveCoordinates
  simp only [sumOverMulRight, sumOverMulLeft]
  rw [sumOverSwap wedgeIndices directions]
  apply sumOverCongr
  intro n
  apply sumOverCongr
  intro w
  grind

theorem expandWaves_pairing (a b : Direction → C) :
    wedgePairing (expandWaves a) (expandWaves b) =
      2 * sumOver directions (fun n => a n * b n) := by
  rw [expandWaves_adjoint, sumOverMulLeft]
  apply sumOverCongr
  intro n
  rw [waveCoordinates_expand]
  grind

theorem projectWaves_idempotent (half : C) (unitHalf : 2*half = 1) (u : Wedge → C) :
    projectWaves half (projectWaves half u) = projectWaves half u := by
  funext w
  unfold projectWaves
  have coeff (n : Direction) :
      waveCoordinates (expandWaves (fun m => half * waveCoordinates u m)) n =
        waveCoordinates u n := by
    rw [waveCoordinates_expand]
    grind
  simp only [coeff]

theorem projectWaves_selfAdjoint (half : C) (u v : Wedge → C) :
    wedgePairing (projectWaves half u) v = wedgePairing u (projectWaves half v) := by
  have symmetric (a b : Wedge → C) : wedgePairing a b = wedgePairing b a := by
    apply sumOverCongr
    intro w
    exact CommSemiring.mul_comm _ _
  rw [symmetric u (projectWaves half v)]
  simp only [projectWaves, expandWaves_adjoint]
  apply sumOverCongr
  intro n
  grind

/-- The actual eight-point exterior Pauli action is the orthogonal
    plane-wave projection, at the standard four-copy normalization. -/
theorem physicalExteriorAction (i half : C) (fourth : i^4 = 1) (unitHalf : 2*half = 1)
    (v : Wedge → C) (w : Wedge) :
    projectWaves half v w =
      sumOver wedgeIndices (fun z => (half^6 * physicalExteriorSum i w z) * v z) := by
  simp only [normalized_physical_plane_gram i half fourth unitHalf]
  unfold projectWaves expandWaves waveCoordinates
  simp only [sumOverMulLeft, sumOverMulRight]
  rw [sumOverSwap wedgeIndices directions]
  apply sumOverCongr
  intro n
  apply sumOverCongr
  intro z
  simp only [wave]
  grind

/-- Apply the ordinary signed removal coefficient to a superposition of
    plane waves and a superposition of hole labels. -/
def annihilateWaves (hole : Point → C) (coeff : Direction → C) (m : Nat) : C :=
  sumOver columns fun c =>
    hole c.1 * coeff c.2 * Int.cast (annihilationEntry c.1 c.2 m)

theorem annihilateWaves_eq_tensor (hole : Point → C) (coeff : Direction → C)
    {m : Nat} (present : m ∈ tripleMasks) :
    annihilateWaves hole coeff m = contraction (fun c => hole c.1 * coeff c.2) m := by
  have valid : m ∈ List.range 256 ∧ three m = true := List.mem_filter.mp present
  let index : Fin 256 := ⟨m, List.mem_range.mp valid.1⟩
  have has := findColumn_covers_triples index
  change (findColumn m).isSome = three m at has
  cases located : findColumn m with
  | none => rw [located, valid.2] at has; cases has
  | some winner =>
    have winnerMask := findColumn_spec located
    let f (c : Column) := signed c (hole c.1 * coeff c.2)
    have singleton (c : Column) :
        hole c.1 * coeff c.2 * Int.cast (annihilationEntry c.1 c.2 m) =
          if winner = c then f c else 0 := by
      have entry := coordinate_annihilation_entry c.1 c.2 index
      change annihilationEntry c.1 c.2 m =
        (if rowMask c = m then (if negative c then -1 else 1) else 0) at entry
      have maskIndicator : rowMask c = m ↔ winner = c := by
        constructor
        · intro matchMask
          have named : findColumn (rowMask c) = some c := findColumn_rowMask c.1 c.2
          rw [matchMask, located] at named
          exact Option.some.inj named
        · intro eq
          rw [← eq]
          exact winnerMask
      rw [entry]
      by_cases matchColumn : winner = c
      · rw [ite_eq_left (maskIndicator.mpr matchColumn), ite_eq_left matchColumn]
        unfold f signed
        cases negative c <;> simp <;> grind
      · rw [ite_eq_right (fun h => matchColumn (maskIndicator.mp h)), ite_eq_right matchColumn]
        grind
    unfold annihilateWaves contraction
    rw [located, sumOverCongr columns singleton]
    have winnerPresent : winner ∈ columns := by
      apply List.mem_flatMap.mpr
      exact ⟨winner.1, by simp [points], List.mem_map.mpr ⟨winner.2, by simp [directions], rfl⟩⟩
    exact sumOnIndex columns winner f (by decide) winnerPresent

theorem annihilateWavesPairing (hole dualHole : Point → C) (a b : Direction → C) :
    sumOver tripleMasks (fun m => annihilateWaves hole a m * annihilateWaves dualHole b m) =
      sumOver points (fun z => hole z * dualHole z) * sumOver directions (fun n => a n * b n) := by
  have actual :
      sumOver tripleMasks (fun m => annihilateWaves hole a m * annihilateWaves dualHole b m) =
        sumOver tripleMasks (fun m =>
          contraction (fun c => hole c.1 * a c.2) m * contraction (fun c => dualHole c.1 * b c.2) m) := by
    unfold sumOver
    congr 1
    apply List.map_congr_left
    intro m present
    rw [annihilateWaves_eq_tensor hole a present, annihilateWaves_eq_tensor dualHole b present]
  rw [actual]
  have h := uniform_occupation_pairing (1 : C) 1 hole dualHole a b
  simpa only [Semiring.one_mul] using h

/-- Exact half-occupation pairing on the range of the physical projector.
    The left coefficients can be the complex conjugates of a left vector. -/
theorem projectedHalfOccupation (hole dualHole : Point → C) (half : C) (u v : Wedge → C)
    (unitHole : sumOver points (fun z => hole z * dualHole z) = 1) :
    2 * sumOver tripleMasks (fun m =>
      annihilateWaves hole (fun n => half * waveCoordinates u n) m *
        annihilateWaves dualHole (fun n => half * waveCoordinates v n) m) =
      wedgePairing (projectWaves half u) (projectWaves half v) := by
  rw [annihilateWavesPairing, unitHole]
  simp only [projectWaves, expandWaves_pairing, Semiring.one_mul]

end RankSeven.ExteriorPauliBase

#print axioms RankSeven.ExteriorPauliBase.projectWaves_idempotent
#print axioms RankSeven.ExteriorPauliBase.projectWaves_selfAdjoint
#print axioms RankSeven.ExteriorPauliBase.physicalExteriorAction
#print axioms RankSeven.ExteriorPauliBase.projectedHalfOccupation
