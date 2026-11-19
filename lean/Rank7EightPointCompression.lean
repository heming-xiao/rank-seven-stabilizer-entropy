import Rank7PlaneProjector
import Rank7ExteriorOperators
import Rank7Compression

namespace RankSeven.ExteriorPauliBase

open Lean.Grind RankSeven.Pauli RankSeven.ExteriorOccupation RankSeven.ExteriorOperators

variable {C : Type} [CommRing C]
attribute [local instance] Ring.intCast

def maskIndex (w : Wedge) : Mask := Fin.ofNat 256 (maskOf w)

theorem maskIndexVal : ∀ w : Wedge, (maskIndex w).val = maskOf w := by decide

theorem wedgeMasksOrdered :
    wedgeIndices.map maskIndex = masks.filter (fun m => degree m == 4) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem waveOnlyDegreeFour :
    ∀ n : Direction, ∀ m : Mask, degree m ≠ 4 → planeWave n m.val = 0 := by decide

def restrictFour (f : Form C) (w : Wedge) : C := f (maskIndex w)

def projectMaskWaves (half : C) (u : Form C) : Form C :=
  waveForm fun n => half * waveCoordinates (restrictFour u) n

theorem restrict_waveForm (coeff : Direction → C) :
    restrictFour (waveForm coeff) = expandWaves coeff := by
  funext w
  unfold restrictFour waveForm expandWaves wave
  simp only [maskIndexVal]

theorem restrict_projectMaskWaves (half : C) (u : Form C) :
    restrictFour (projectMaskWaves half u) = projectWaves half (restrictFour u) :=
  restrict_waveForm _

private theorem sumOverFilterZero {α : Type} (xs : List α) (keep : α → Bool) (f : α → C)
    (supported : ∀ i, keep i = false → f i = 0) :
    sumOver xs f = sumOver (xs.filter keep) f := by
  induction xs with
  | nil => rfl
  | cons i tail ih =>
    cases hi : keep i
    · rw [List.filter_cons, hi]
      change f i + sumOver tail f = sumOver (tail.filter keep) f
      rw [supported i hi, ih]
      grind
    · rw [List.filter_cons, hi]
      change f i + sumOver tail f = f i + sumOver (tail.filter keep) f
      rw [ih]

theorem waveForm_pairing (coeff : Direction → C) (f : Form C) :
    formPairing (waveForm coeff) f =
      sumOver directions fun n => coeff n * waveCoordinates (restrictFour f) n := by
  have normalSum (n : Direction) :
      sumOver masks (fun m => Int.cast (planeWave n m.val) * f m) =
        waveCoordinates (restrictFour f) n := by
    let e (m : Mask) := Int.cast (planeWave n m.val) * f m
    have support (m : Mask) (outside : (degree m == 4) = false) : e m = 0 := by
      have hm : degree m ≠ 4 := by simpa using outside
      dsimp [e]
      rw [waveOnlyDegreeFour n m hm]
      grind
    rw [sumOverFilterZero masks (fun m : Mask => degree m == 4) e support, ← wedgeMasksOrdered]
    unfold sumOver waveCoordinates restrictFour wave
    simp only [List.map_map, Function.comp_def, e, maskIndexVal]
    rfl
  unfold formPairing waveForm
  simp only [sumOverMulRight]
  rw [sumOverSwap masks directions]
  apply sumOverCongr
  intro n
  rw [← normalSum n, sumOverMulLeft]
  apply sumOverCongr
  intro m
  grind

theorem projectMaskWaves_idempotent (half : C) (unitHalf : 2*half = 1) (u : Form C) :
    projectMaskWaves half (projectMaskWaves half u) = projectMaskWaves half u := by
  unfold projectMaskWaves
  rw [restrict_waveForm]
  have each (n : Direction) :
      waveCoordinates (expandWaves (fun m => half * waveCoordinates (restrictFour u) m)) n =
        waveCoordinates (restrictFour u) n := by
    rw [waveCoordinates_expand]
    grind
  simp only [each]

theorem projectMaskWaves_selfAdjoint (half : C) (u v : Form C) :
    formPairing (projectMaskWaves half u) v = formPairing u (projectMaskWaves half v) := by
  rw [formPairing_symm u (projectMaskWaves half v)]
  simp only [projectMaskWaves, waveForm_pairing]
  apply sumOverCongr
  intro n
  grind

theorem waveForm_normPair (a b : Direction → C) :
    formPairing (waveForm a) (waveForm b) =
      2 * sumOver directions (fun n => a n * b n) := by
  rw [waveForm_pairing, restrict_waveForm, sumOverMulLeft]
  apply sumOverCongr
  intro n
  rw [waveCoordinates_expand]
  grind

/-- Matrix of the projected eight-point exterior Pauli action on its
    actual four-particle sector. -/
theorem physicalMaskAction (i half : C) (fourth : i^4 = 1) (unitHalf : 2*half = 1)
    (u : Form C) (w : Wedge) :
    restrictFour (projectMaskWaves half u) w =
      sumOver wedgeIndices (fun z => (half^6 * physicalExteriorSum i w z) * restrictFour u z) := by
  rw [restrict_projectMaskWaves]
  exact physicalExteriorAction i half fourth unitHalf _ w

private theorem tripleValues :
    (masks.filter (fun m => degree m == 3)).map Fin.val = tripleMasks := by decide

theorem actualAnnihilationOnWaves (x dual : Point → C) (a b : Direction → C) :
    2 * formPairing (annihilate x (waveForm a)) (annihilate dual (waveForm b)) =
      ExteriorOperators.pairing x dual * formPairing (waveForm a) (waveForm b) := by
  have grade := annihilate_grade (k := 3) x (waveForm_grade_four a)
  let term (m : Mask) := annihilate x (waveForm a) m * annihilate dual (waveForm b) m
  have support (m : Mask) (outside : (degree m == 3) = false) : term m = 0 := by
    have d : degree m ≠ 3 := by simpa using outside
    dsimp [term]
    rw [grade m d]
    grind
  unfold formPairing
  change 2 * sumOver masks term = _
  rw [sumOverFilterZero masks (fun m => degree m == 3) term support]
  have lower (m : Mask) : term m = annihilateWaves x a m.val * annihilateWaves dual b m.val := by
    unfold term annihilateWaves
    rw [annihilate_waveForm, annihilate_waveForm]
  rw [sumOverCongr _ lower]
  have filtered :
      sumOver (masks.filter (fun m => degree m == 3))
          (fun m => annihilateWaves x a m.val * annihilateWaves dual b m.val) =
        sumOver tripleMasks (fun m => annihilateWaves x a m * annihilateWaves dual b m) := by
    rw [← tripleValues]
    simp [sumOver, List.map_map, Function.comp_def]
  rw [filtered]
  change _ = ExteriorOperators.pairing x dual * formPairing (waveForm a) (waveForm b)
  rw [waveForm_normPair, annihilateWavesPairing]
  unfold ExteriorOperators.pairing
  grind

theorem maskedOccupationPairingWithMass (x dual : Point → C) (half : C) (u v : Form C) :
    2 * formPairing (projectMaskWaves half u)
      (occupation x dual (projectMaskWaves half v)) =
      ExteriorOperators.pairing x dual * formPairing (projectMaskWaves half u) (projectMaskWaves half v) := by
  have transpose :
      formPairing (projectMaskWaves half u) (occupation x dual (projectMaskWaves half v)) =
        formPairing (annihilate x (projectMaskWaves half u))
          (annihilate dual (projectMaskWaves half v)) := by
    unfold occupation
    rw [formPairing_symm (projectMaskWaves half u), ← annihilate_adjoint, formPairing_symm]
  rw [transpose]
  exact actualAnnihilationOnWaves x dual _ _

theorem maskedOccupationPairing (x dual : Point → C) (half : C) (u v : Form C)
    (unitHole : ExteriorOperators.pairing x dual = 1) :
    2 * formPairing (projectMaskWaves half u)
      (occupation x dual (projectMaskWaves half v)) =
      formPairing (projectMaskWaves half u) (projectMaskWaves half v) := by
  rw [maskedOccupationPairingWithMass, unitHole, Semiring.one_mul]

private theorem formPairingTest (m : Mask) (u : Form C) :
    formPairing (fun z => if m = z then 1 else 0) u = u m := by
  unfold formPairing
  have term (z : Mask) :
      (if m = z then (1 : C) else 0) * u z = if m = z then u z else 0 := by
    split <;> grind
  rw [sumOverCongr _ term]
  exact sumOnIndex masks m u (List.nodup_finRange _) (by simp [masks])

/-- The normalized physical eight-point projector has exactly half occupation
    on its range for every unit hole, including arbitrary dual coefficients. -/
theorem eightPointOccupationSandwich (x dual : Point → C) (half : C) (u : Form C)
    (unitHalf : 2*half = 1) (unitHole : ExteriorOperators.pairing x dual = 1) (m : Mask) :
    2 * projectMaskWaves half (occupation x dual (projectMaskWaves half u)) m =
      projectMaskWaves half u m := by
  have asForms (v : Form C) :
      2 * formPairing v (projectMaskWaves half (occupation x dual (projectMaskWaves half u))) =
        formPairing v (projectMaskWaves half u) := by
    rw [← projectMaskWaves_selfAdjoint half v (occupation x dual (projectMaskWaves half u))]
    rw [maskedOccupationPairing x dual half v u unitHole, projectMaskWaves_selfAdjoint half,
      projectMaskWaves_idempotent half unitHalf]
  have h := asForms (fun z => if m = z then 1 else 0)
  simpa only [formPairingTest] using h

private theorem pairingSubRight (g u v : Form C) :
    formPairing g (fun m => u m - v m) = formPairing g u - formPairing g v := by
  unfold formPairing
  rw [← Compression.sumOverSub]
  apply sumOverCongr
  intro m
  grind

private theorem pairingSubLeft (g u v : Form C) :
    formPairing (fun m => g m - u m) v = formPairing g v - formPairing u v := by
  rw [formPairing_symm (fun m => g m - u m), pairingSubRight,
    formPairing_symm v g, formPairing_symm v u]

private theorem pairingScaleRight (g u : Form C) (c : C) :
    formPairing g (fun m => c * u m) = c * formPairing g u := by
  unfold formPairing
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro m
  grind

private theorem pairingScaleLeft (g u : Form C) (c : C) :
    formPairing (fun m => c * g m) u = c * formPairing g u := by
  rw [formPairing_symm (fun m => c*g m), pairingScaleRight, formPairing_symm u g]

private theorem pairingZero (g : Form C) : formPairing g (fun _ => 0) = 0 := by
  simpa only [Semiring.zero_mul] using pairingScaleRight g g (0 : C)

def holeResidual (x dual : Point → C) (half : C) (f : Form C) : Form C :=
  fun m => f m - 2 * (projectMaskWaves half f m - occupation x dual (projectMaskWaves half f) m)

theorem holePairingSymmetric (x dual : Point → C) :
    ExteriorOperators.pairing dual x = ExteriorOperators.pairing x dual := by
  unfold ExteriorOperators.pairing
  apply sumOverCongr
  intro i
  exact CommSemiring.mul_comm _ _

theorem occupationScaledSquare (x dual : Point → C) (half : C) (f : Form C) (hhalf : 2*half = 1) :
    occupation x dual (occupation x dual f) =
      fun m => ExteriorOperators.pairing x dual * occupation x dual f m := by
  let mass := ExteriorOperators.pairing x dual
  let lowered := annihilate dual f
  have car : annihilate dual (create x lowered) = fun m => mass * lowered m := by
    funext m
    have h := annihilate_create_car dual x lowered m
    have double : annihilate dual lowered = fun _ => 0 :=
      annihilate_square_zero half hhalf dual f
    have zeroCreated : create x (fun _ => (0 : C)) = fun _ => 0 :=
      combine_zero raiseCoeff x
    rw [double, zeroCreated, holePairingSymmetric x dual] at h
    grind
  change create x (annihilate dual (create x lowered)) =
    (fun m => mass * create x lowered m)
  rw [car]
  funext m
  unfold create combine site
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro i
  grind

def scaledHoleResidual (x dual : Point → C) (half : C) (f : Form C) : Form C :=
  let mass := ExteriorOperators.pairing x dual
  fun m => mass * f m -
    2 * (mass * projectMaskWaves half f m - occupation x dual (projectMaskWaves half f) m)

/-- Exact norm-defect certificate for an unnormalized hole. Its only
    scaling is the squared hole mass, so no square root is needed. -/
theorem eightPointCompressionCertificateOfMass (x dual : Point → C) (half : C) (g f : Form C)
    (unitHalf : 2*half = 1)
    (leftKernel : annihilate x g = fun _ => 0) (rightKernel : annihilate dual f = fun _ => 0) :
    formPairing (scaledHoleResidual dual x half g) (scaledHoleResidual x dual half f) =
      ExteriorOperators.pairing x dual ^ 2 *
        (formPairing g f - 2 * formPairing (projectMaskWaves half g) (projectMaskWaves half f)) := by
  let mass := ExteriorOperators.pairing x dual
  let p := projectMaskWaves half g
  let q := projectMaskWaves half f
  let np := occupation dual x p
  let nq := occupation x dual q
  have annihilatedLeft : occupation dual x g = fun _ => 0 := by
    unfold occupation
    rw [leftKernel]
    exact combine_zero raiseCoeff dual
  have annihilatedRight : occupation x dual f = fun _ => 0 := by
    unfold occupation
    rw [rightKernel]
    exact combine_zero raiseCoeff x
  have zeroL : formPairing g nq = 0 := by
    change formPairing g (occupation x dual q) = 0
    rw [occupation_dual_adjoint, annihilatedLeft, formPairing_symm, pairingZero]
  have zeroR : formPairing np f = 0 := by
    change formPairing (occupation dual x p) f = 0
    rw [← occupation_dual_adjoint, annihilatedRight, pairingZero]
  have pairG : formPairing g q = formPairing p q := by
    change _ = formPairing (projectMaskWaves half g) (projectMaskWaves half f)
    rw [projectMaskWaves_selfAdjoint half, projectMaskWaves_idempotent half unitHalf]
  have pairF : formPairing p f = formPairing p q := by
    rw [← pairG]
    exact projectMaskWaves_selfAdjoint half g f
  have adjoint : formPairing np q = formPairing p nq :=
    (occupation_dual_adjoint x dual p q).symm
  have normN : formPairing np nq = mass * formPairing p nq := by
    change formPairing (occupation dual x p) (occupation x dual q) = _
    rw [← occupation_dual_adjoint, occupationScaledSquare x dual half q unitHalf, pairingScaleRight]
  have halfN : 2 * formPairing p nq = mass * formPairing p q :=
    maskedOccupationPairingWithMass x dual half g f
  have scaledHalf := congrArg (fun v => mass * v) halfN
  unfold scaledHoleResidual
  rw [holePairingSymmetric x dual]
  change formPairing (fun m => mass*g m - 2*(mass*p m - np m))
      (fun m => mass*f m - 2*(mass*q m - nq m)) =
    mass ^ 2 * (formPairing g f - 2 * formPairing p q)
  simp only [pairingSubLeft, pairingSubRight, pairingScaleLeft, pairingScaleRight]
  grind

/-- The same certificate in the original unit-hole normalization. -/
theorem eightPointCompressionCertificate (x dual : Point → C) (half : C) (g f : Form C)
    (unitHalf : 2*half = 1) (unitHole : ExteriorOperators.pairing x dual = 1)
    (leftKernel : annihilate x g = fun _ => 0) (rightKernel : annihilate dual f = fun _ => 0) :
    formPairing (holeResidual dual x half g) (holeResidual x dual half f) =
      formPairing g f - 2 * formPairing (projectMaskWaves half g) (projectMaskWaves half f) := by
  have h := eightPointCompressionCertificateOfMass x dual half g f unitHalf leftKernel rightKernel
  unfold scaledHoleResidual at h
  rw [holePairingSymmetric x dual, unitHole] at h
  unfold holeResidual
  simp only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] at h
  exact h

section Real

variable [LE C] [LT C] [Std.IsLinearOrder C] [Std.LawfulOrderLT C] [OrderedRing C]

/-- The physical eight-point compression is bounded by one half on
    the real four-forms annihilated by the specified unit hole. -/
theorem eightPointRealCompression (x : Point → C) (half : C) (f : Form C)
    (unitHalf : 2*half = 1) (unitHole : ExteriorOperators.pairing x x = 1)
    (kernel : annihilate x f = fun _ => 0) :
    2 * formPairing (projectMaskWaves half f) (projectMaskWaves half f) ≤ formPairing f f := by
  have cert := eightPointCompressionCertificate x x half f f unitHalf unitHole kernel kernel
  have nonnegative : 0 ≤ formPairing (holeResidual x x half f) (holeResidual x x half f) := by
    apply Compression.sumOverNonnegative
    intro m _
    have nonneg := squareNonnegative (holeResidual x x half f m)
    grind
  grind

end Real

end RankSeven.ExteriorPauliBase

#print axioms RankSeven.ExteriorPauliBase.projectMaskWaves_idempotent
#print axioms RankSeven.ExteriorPauliBase.projectMaskWaves_selfAdjoint
#print axioms RankSeven.ExteriorPauliBase.physicalMaskAction
#print axioms RankSeven.ExteriorPauliBase.eightPointOccupationSandwich
#print axioms RankSeven.ExteriorPauliBase.eightPointCompressionCertificateOfMass
#print axioms RankSeven.ExteriorPauliBase.eightPointCompressionCertificate
#print axioms RankSeven.ExteriorPauliBase.eightPointRealCompression
