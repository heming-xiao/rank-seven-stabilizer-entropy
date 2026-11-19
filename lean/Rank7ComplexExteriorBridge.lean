import Rank7ComplexScalar
import Rank7EightPointCompression

namespace RankSeven.ComplexExterior

open Lean.Grind
open Pauli (sumOver sumOverCongr)
open ExteriorOccupation (Point Direction)
open ExteriorOperators (Mask Form masks formPairing combine site waveForm annihilate create occupation)
open ExteriorPauliBase (projectMaskWaves restrictFour waveCoordinates wave)
open ComplexScalar (star normSq ofReal)

variable {R : Type} [CommRing R]

attribute [local instance] Ring.intCast

/-- Conjugate all amplitudes of an exterior form in the mask basis. -/
def starForm (f : Form (ComplexScalar R)) : Form (ComplexScalar R) :=
  fun m => star (f m)

@[simp] theorem starForm_involutive (f : Form (ComplexScalar R)) :
    starForm (starForm f) = f := by
  funext m
  exact ComplexScalar.star_star (f m)

private theorem starIntCast (i : Int) :
    star (Int.cast (R := ComplexScalar R) i) = Int.cast i :=
  (ComplexScalar.scalarConjugation (R := R)).fixesInteger i

theorem starSumOver {α : Type} (indices : List α) (f : α → ComplexScalar R) :
    star (sumOver indices f) = sumOver indices (fun i => star (f i)) := by
  induction indices with
  | nil =>
    change star (ofReal (0 : R)) = ofReal 0
    exact ComplexScalar.star_ofReal 0
  | cons i rest ih =>
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons, ComplexScalar.star_add, ih]

private theorem reSumOver {α : Type} (indices : List α) (f : α → ComplexScalar R) :
    (sumOver indices f).re = sumOver indices (fun i => (f i).re) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons, ComplexScalar.re_add, ih]

private theorem imSumOver {α : Type} (indices : List α) (f : α → ComplexScalar R) :
    (sumOver indices f).im = sumOver indices (fun i => (f i).im) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons, ComplexScalar.im_add, ih]

private theorem sumZero {α : Type} (indices : List α) :
    sumOver indices (fun _ => (0 : R)) = 0 := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    change (0 : R) + sumOver rest (fun _ => 0) = 0
    rw [ih, Semiring.add_zero]

/-- The real part of the Hermitian self-pairing is the sum of squared moduli. -/
theorem formPairingStarSelf_re (f : Form (ComplexScalar R)) :
    (formPairing (starForm f) f).re = sumOver masks (fun m => normSq (f m)) := by
  unfold formPairing
  rw [reSumOver]
  simp only [starForm, ComplexScalar.re_star_mul_self]

theorem formPairingStarSelf_im (f : Form (ComplexScalar R)) :
    (formPairing (starForm f) f).im = 0 := by
  unfold formPairing
  rw [imSumOver]
  simp only [starForm, ComplexScalar.im_star_mul_self]
  exact sumZero masks

theorem formPairingStarSelf (f : Form (ComplexScalar R)) :
    formPairing (starForm f) f = ofReal (sumOver masks (fun m => normSq (f m))) :=
  ComplexScalar.ext (formPairingStarSelf_re f) (formPairingStarSelf_im f)

private theorem starCombine (coef : Point → Mask → Int) (x : Point → ComplexScalar R)
    (f : Form (ComplexScalar R)) :
    starForm (combine coef x f) = combine coef (fun i => star (x i)) (starForm f) := by
  funext m
  unfold starForm combine site
  rw [starSumOver]
  apply sumOverCongr
  intro i
  rw [ComplexScalar.star_mul, ComplexScalar.star_mul, starIntCast]

/-- Conjugation commutes with annihilation when its covector is conjugated. -/
theorem starAnnihilate (x : Point → ComplexScalar R) (f : Form (ComplexScalar R)) :
    starForm (annihilate x f) = annihilate (fun i => star (x i)) (starForm f) :=
  starCombine _ x f

theorem starCreate (x : Point → ComplexScalar R) (f : Form (ComplexScalar R)) :
    starForm (create x f) = create (fun i => star (x i)) (starForm f) :=
  starCombine _ x f

/-- Conjugation of occupation conjugates both its creation and hole vectors. -/
theorem starOccupation (x dual : Point → ComplexScalar R) (f : Form (ComplexScalar R)) :
    starForm (occupation x dual f) =
      occupation (fun i => star (x i)) (fun i => star (dual i)) (starForm f) := by
  unfold occupation
  rw [starCreate, starAnnihilate]

theorem starWaveForm (coeff : Direction → ComplexScalar R) :
    starForm (waveForm coeff) = waveForm (fun n => star (coeff n)) := by
  funext m
  unfold starForm waveForm
  rw [starSumOver]
  apply sumOverCongr
  intro n
  rw [ComplexScalar.star_mul, starIntCast]

private theorem starRestrictedWaveCoordinates (f : Form (ComplexScalar R)) (n : Direction) :
    star (waveCoordinates (restrictFour f) n) =
      waveCoordinates (restrictFour (starForm f)) n := by
  unfold waveCoordinates
  rw [starSumOver]
  apply sumOverCongr
  intro w
  unfold wave restrictFour starForm
  rw [ComplexScalar.star_mul, starIntCast]

/-- Conjugation preserves the planar projector's coordinate formula, with
its weight conjugated as well. This algebraic identity uses any weight. -/
theorem starProjectMaskWaves (weight : ComplexScalar R) (f : Form (ComplexScalar R)) :
    starForm (projectMaskWaves weight f) = projectMaskWaves (star weight) (starForm f) := by
  unfold projectMaskWaves
  rw [starWaveForm]
  simp only [ComplexScalar.star_mul, starRestrictedWaveCoordinates]

theorem starProjectMaskWavesReal (weight : R) (f : Form (ComplexScalar R)) :
    starForm (projectMaskWaves (ofReal weight) f) =
      projectMaskWaves (ofReal weight) (starForm f) := by
  rw [starProjectMaskWaves, ComplexScalar.star_ofReal]

section Order

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem formPairingStarSelf_nonnegative (f : Form (ComplexScalar R)) :
    0 ≤ (formPairing (starForm f) f).re := by
  rw [formPairingStarSelf_re]
  exact Compression.sumOverNonnegative masks _ (fun m _ => ComplexScalar.normSq_nonnegative (f m))

theorem sumPositiveAt {α : Type} (indices : List α) (f : α → R)
    (nonnegative : ∀ i, 0 ≤ f i) (i : α) (member : i ∈ indices) (positive : 0 < f i) :
    0 < sumOver indices f := by
  induction indices with
  | nil => cases member
  | cons j rest ih =>
    change 0 < f j + sumOver rest f
    rcases List.mem_cons.mp member with same | memberTail
    · subst j
      have tail := Compression.sumOverNonnegative rest f (fun k _ => nonnegative k)
      grind
    · have tail := ih memberTail
      have head := nonnegative j
      grind

/-- A nonzero exterior form has strictly positive real squared norm. -/
theorem formPairingStarSelf_positive (f : Form (ComplexScalar R)) (m : Mask) (nonzero : f m ≠ 0) :
    0 < (formPairing (starForm f) f).re := by
  rw [formPairingStarSelf_re]
  exact sumPositiveAt masks _ (fun n => ComplexScalar.normSq_nonnegative (f n)) m
    (by simp [masks]) (ComplexScalar.normSq_positive (f m) nonzero)

end Order
end RankSeven.ComplexExterior
