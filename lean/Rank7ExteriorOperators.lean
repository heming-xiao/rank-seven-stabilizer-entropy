import Rank7ExteriorOccupation

/-! Coordinate fermionic creation and annihilation on the exterior algebra of
the eight-point affine cube. All grades use the same 256 coordinate masks;
grade-restricted forms have zero coefficients outside their specified grade. -/
namespace RankSeven.ExteriorOperators

open RankSeven.Pauli RankSeven.ExteriorOccupation Lean.Grind

abbrev Mask := Fin 256
abbrev Form (C : Type) := Mask → C

def toggle (i : Point) (m : Mask) : Mask := Fin.ofNat 256 (m.val ^^^ (2^i.val))
def occupied (i : Point) (m : Mask) : Bool := m.val.testBit i.val
def degree (m : Mask) : Nat := (active m.val).length
def signBelow (i : Point) (m : Mask) : Int :=
  let below := m.val % (2^i.val)
  let half := below ^^^ (below >>> 4)
  let pair := half ^^^ (half >>> 2)
  if (pair ^^^ (pair >>> 1)).testBit 0 then -1 else 1

set_option maxRecDepth 100000 in
theorem signBelow_is_wedge_sign : ∀ (i : Point) (m : Mask), signBelow i m =
    (if ((active m.val).filter (fun t => t < i)).length % 2 == 1 then -1 else 1) := by decide

/-- Coefficients indexed by the output wedge. The input is obtained by
toggling the particle label. -/
def lowerCoeff (i : Point) (m : Mask) : Int := if occupied i m then 0 else signBelow i m
def raiseCoeff (i : Point) (m : Mask) : Int := if occupied i m then signBelow i m else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem toggle_data : ∀ (i : Point) (m : Mask),
    toggle i (toggle i m) = m ∧ lowerCoeff i (toggle i m) = raiseCoeff i m ∧
    raiseCoeff i (toggle i m) = lowerCoeff i m ∧
    (lowerCoeff i m ≠ 0 → degree (toggle i m) = degree m + 1) ∧
    (raiseCoeff i m ≠ 0 → degree m = degree (toggle i m) + 1) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem toggle_commutes : ∀ (i j : Point) (m : Mask),
    toggle i (toggle j m) = toggle j (toggle i m) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The two paths have opposite sorting signs unless they undo the very
same operation. Checking signs is independent of subsequent amplitudes. -/
theorem coordinate_coefficients : ∀ (i j : Point) (m : Mask),
    (lowerCoeff i m * raiseCoeff j (toggle i m) +
      raiseCoeff j m * lowerCoeff i (toggle j m) = (if i = j then 1 else 0)) ∧
    (lowerCoeff i m * lowerCoeff j (toggle i m) +
      lowerCoeff j m * lowerCoeff i (toggle j m) = 0) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lower_planeWave : ∀ (i : Point) (n : Direction) (m : Mask),
    lowerCoeff i m * planeWave n (toggle i m).val = annihilationEntry i n m.val := by decide

local instance {C : Type} [CommRing C] : IntCast C := Ring.intCast

def site {C : Type} [CommRing C] (coef : Point → Mask → Int) (i : Point)
    (f : Form C) (m : Mask) : C := Int.cast (coef i m) * f (toggle i m)

def combine {C : Type} [CommRing C] (coef : Point → Mask → Int)
    (u : Point → C) (f : Form C) (m : Mask) : C :=
  sumOver points fun i => u i * site coef i f m

abbrev annihilate {C : Type} [CommRing C] := @combine C _ lowerCoeff
abbrev create {C : Type} [CommRing C] := @combine C _ raiseCoeff

def pairing {C : Type} [CommRing C] (u v : Point → C) : C :=
  sumOver points fun i => u i * v i

theorem site_car {C : Type} [CommRing C] (i j : Point) (f : Form C) (m : Mask) :
    site lowerCoeff i (site raiseCoeff j f) m + site raiseCoeff j (site lowerCoeff i f) m =
      if i = j then f m else 0 := by
  have hc := congrArg (Int.cast (R := C)) (coordinate_coefficients i j m).1
  rw [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul] at hc
  unfold site
  rw [toggle_commutes i j m]
  by_cases h : i = j
  · subst j
    simp only [ite_true, (toggle_data i m).1] at *
    grind
  · simp only [h, ite_false] at *
    grind

theorem site_lower_lower {C : Type} [CommRing C] (i j : Point) (f : Form C) (m : Mask) :
    site lowerCoeff i (site lowerCoeff j f) m + site lowerCoeff j (site lowerCoeff i f) m = 0 := by
  have hc := congrArg (Int.cast (R := C)) (coordinate_coefficients i j m).2
  rw [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul, Ring.intCast_ofNat] at hc
  unfold site
  rw [toggle_commutes i j m]
  grind

private theorem expand_composite {C : Type} [CommRing C]
    (co ci : Point → Mask → Int) (u v : Point → C) (f : Form C) (m : Mask) :
    combine co u (combine ci v f) m =
      sumOver points (fun i => sumOver points (fun j =>
        (u i * v j) * site co i (site ci j f) m)) := by
  unfold combine site
  apply sumOverCongr
  intro i
  rw [← Semiring.mul_assoc, sumOverMulLeft]
  apply sumOverCongr
  intro j
  grind

private theorem sum_anticommutator {C : Type} [CommRing C]
    (co ci : Point → Mask → Int) (u v : Point → C) (f : Form C) (m : Mask) :
    combine co u (combine ci v f) m + combine ci v (combine co u f) m =
      sumOver points (fun i => sumOver points (fun j =>
        (u i * v j) * (site co i (site ci j f) m + site ci j (site co i f) m))) := by
  rw [expand_composite, expand_composite,
    sumOverSwap points points (fun i j => (v i * u j) * site ci i (site co j f) m),
    ← sumOverAdd]
  apply sumOverCongr
  intro i
  rw [← sumOverAdd]
  apply sumOverCongr
  intro j
  grind

private theorem sum_delta {C : Type} [CommRing C] (i : Point) (w : Point → C) :
    sumOver points (fun j => if i = j then w j else 0) = w i := by
  have locate (i : Point) :
      ((points.filter (fun j => i == j)) = [i]) := by revert i; decide
  have filtered (xs : List Point) :
      sumOver xs (fun j => if i = j then w j else 0) =
        sumOver (xs.filter (fun j => i == j)) w := by
    induction xs with
    | nil => rfl
    | cons j xs ih =>
      by_cases eq : i = j <;> simp [sumOver, eq] at *
      all_goals grind
  rw [filtered, locate]
  simp [sumOver]
  grind

/-- Canonical anticommutation for arbitrary coefficient vectors. In the
complex application u contains the conjugated coefficients of the hole. -/
theorem annihilate_create_car {C : Type} [CommRing C] (u v : Point → C) (f : Form C) (m : Mask) :
    annihilate u (create v f) m + create v (annihilate u f) m = pairing u v * f m := by
  rw [sum_anticommutator]
  unfold pairing
  rw [sumOverMulRight]
  apply sumOverCongr
  intro i
  calc
    _ = sumOver points (fun j => if i = j then (u i * v j) * f m else 0) := by
      apply sumOverCongr
      intro j
      rw [site_car]
      split <;> grind
    _ = (u i * v i) * f m := sum_delta i (fun j => (u i * v j) * f m)

theorem annihilate_anticommutes {C : Type} [CommRing C] (u v : Point → C) (f : Form C) (m : Mask) :
    annihilate u (annihilate v f) m + annihilate v (annihilate u f) m = 0 := by
  rw [sum_anticommutator]
  simp only [site_lower_lower]
  have innerZero (x : Point) : sumOver points (fun j => (u x * v j) * 0) = 0 := by
    simp [points, sumOver, List.finRange, Semiring.mul_zero] <;> grind
  simp only [innerZero]
  simp [points, sumOver, List.finRange] <;> grind

private theorem zeroSum {C α : Type} [CommRing C] (xs : List α) (f : α → C)
    (h : ∀ x, f x = 0) : sumOver xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change f x + sumOver xs f = 0; rw [h, ih]; grind

theorem combine_zero {C : Type} [CommRing C] (co : Point → Mask → Int) (u : Point → C) :
    combine co u (fun _ => (0 : C)) = fun _ => 0 := by
  funext m
  apply zeroSum
  intro i
  unfold site
  grind

theorem annihilate_square_zero {C : Type} [CommRing C] (half : C) (hhalf : 2*half = 1)
    (u : Point → C) (f : Form C) : annihilate u (annihilate u f) = fun _ => 0 := by
  funext m
  have h := annihilate_anticommutes u u f m
  have hscale := congrArg (fun t => half*t) h
  grind

private theorem create_zero {C : Type} [CommRing C] (v : Point → C) :
    create v (fun _ => (0:C)) = fun _ => 0 := combine_zero raiseCoeff v

/-- Creation uses the column x; contraction uses the dual covector xDual.
For a complex Hilbert space take xDual to be the coordinatewise conjugate of x. -/
def occupation {C : Type} [CommRing C] (x xDual : Point → C) (f : Form C) : Form C :=
  create x (annihilate xDual f)

theorem occupation_idempotent {C : Type} [CommRing C] (half : C) (hhalf : 2*half=1)
    (x xDual : Point → C) (unit : pairing xDual x = 1) (f : Form C) :
    occupation x xDual (occupation x xDual f) = occupation x xDual f := by
  have h : annihilate xDual (create x (annihilate xDual f)) = annihilate xDual f := by
    funext m
    have hc := annihilate_create_car xDual x (annihilate xDual f) m
    rw [annihilate_square_zero half hhalf, create_zero, unit] at hc
    grind
  unfold occupation
  rw [h]

def homogeneous {C : Type} [CommRing C] (k : Nat) (f : Form C) : Prop :=
  ∀ m, degree m ≠ k → f m = 0

theorem annihilate_grade {C : Type} [CommRing C] {k : Nat} {f : Form C}
    (u : Point → C) (hf : homogeneous (k+1) f) : homogeneous k (annihilate u f) := by
  intro m hm
  apply zeroSum
  intro i
  unfold site
  by_cases h : lowerCoeff i m = 0
  · rw [h, Ring.intCast_ofNat]; grind
  · have hd := (toggle_data i m).2.2.2.1 h
    rw [hf _ (by omega)]
    grind

theorem create_grade {C : Type} [CommRing C] {k : Nat} {f : Form C}
    (v : Point → C) (hf : homogeneous k f) : homogeneous (k+1) (create v f) := by
  intro m hm
  apply zeroSum
  intro i
  unfold site
  by_cases h : raiseCoeff i m = 0
  · rw [h, Ring.intCast_ofNat]; grind
  · have hd := (toggle_data i m).2.2.2.2 h
    rw [hf _ (by omega)]
    grind

def vacuum {C : Type} [CommRing C] (m : Mask) : C := if m.val = 0 then 1 else 0

set_option maxRecDepth 100000 in
private theorem no_vacuum_input : ∀ (i : Point) (m : Mask),
    (toggle i m).val = 0 → lowerCoeff i m = 0 := by decide

theorem annihilate_vacuum {C : Type} [CommRing C] (u : Point → C) :
    annihilate u vacuum = fun _ => 0 := by
  funext m
  apply zeroSum
  intro i
  unfold site vacuum
  split
  next h => rw [no_vacuum_input _ _ h, Ring.intCast_ofNat]; grind
  next => grind

def exteriorProduct {C : Type} [CommRing C] (vs : List (Point → C)) : Form C :=
  vs.foldr create vacuum

theorem exteriorProduct_grade {C : Type} [CommRing C] (vs : List (Point → C)) :
    homogeneous vs.length (exteriorProduct vs) := by
  induction vs with
  | nil =>
    intro m hm
    by_cases h : m.val = 0
    · have e : m = 0 := Fin.ext h
      subst m
      exact False.elim (hm (show degree (0 : Mask) = 0 from rfl))
    · simp [exteriorProduct, vacuum, h]
  | cons v vs ih => exact create_grade v ih

theorem annihilate_exteriorProduct {C : Type} [CommRing C] (u : Point → C)
    (vs : List (Point → C)) (orthogonal : ∀ v ∈ vs, pairing u v = 0) :
    annihilate u (exteriorProduct vs) = fun _ => 0 := by
  induction vs with
  | nil => exact annihilate_vacuum u
  | cons v vs ih =>
    have hv := orthogonal v (by simp)
    have ht := ih (by intro w hw; exact orthogonal w (by simp [hw]))
    funext m
    change annihilate u (create v (exteriorProduct vs)) m = 0
    have h := annihilate_create_car u v (exteriorProduct vs) m
    rw [hv, ht, create_zero] at h
    grind

theorem four_wedge_in_hole_complement {C : Type} [CommRing C] (x xDual : Point → C)
    (a b c d : Point → C)
    (ha : pairing xDual a = 0) (hb : pairing xDual b = 0)
    (hc : pairing xDual c = 0) (hd : pairing xDual d = 0) :
    occupation x xDual (exteriorProduct [a,b,c,d]) = fun _ => 0 := by
  unfold occupation
  rw [annihilate_exteriorProduct _ _ (by intro w hw; simp at hw; rcases hw with h|h|h|h <;> subst w <;> assumption)]
  exact combine_zero _ _

def masks : List Mask := List.finRange 256

def formPairing {C : Type} [CommRing C] (g f : Form C) : C := sumOver masks fun m => g m * f m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem toggle_perm : ∀ (i : Point), (masks.map (toggle i)).Perm masks := by decide

private theorem sumPerm {C α : Type} [CommRing C] {xs ys : List α} (p : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver, List.map_cons, List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver, List.map_cons, List.sum_cons]; grind
  | trans _ _ a b => exact a.trans b

private theorem reindex_toggle {C : Type} [CommRing C] (i : Point) (f : Mask → C) :
    sumOver masks (fun m => f (toggle i m)) = sumOver masks f := by
  simpa [sumOver, List.map_map, Function.comp_def] using sumPerm (toggle_perm i) f

theorem site_adjoint {C : Type} [CommRing C] (i : Point) (g f : Form C) :
    formPairing g (site lowerCoeff i f) = formPairing (site raiseCoeff i g) f := by
  unfold formPairing
  rw [← reindex_toggle i (fun m => g m * site lowerCoeff i f m)]
  apply sumOverCongr
  intro m
  unfold site
  rw [(toggle_data i m).2.1, (toggle_data i m).1]
  grind

private theorem pair_combine {C : Type} [CommRing C] (co : Point → Mask → Int)
    (u : Point → C) (g f : Form C) :
    formPairing g (combine co u f) = sumOver points fun i => u i * formPairing g (site co i f) := by
  unfold formPairing combine
  simp only [sumOverMulLeft]
  rw [sumOverSwap masks points]
  apply sumOverCongr
  intro i
  apply sumOverCongr
  intro m
  grind

theorem formPairing_symm {C : Type} [CommRing C] (g f : Form C) :
    formPairing g f = formPairing f g :=
  sumOverCongr masks (fun _ => CommSemiring.mul_comm _ _)

theorem annihilate_adjoint {C : Type} [CommRing C] (u : Point → C) (g f : Form C) :
    formPairing g (annihilate u f) = formPairing (create u g) f := by
  rw [formPairing_symm (create u g), pair_combine, pair_combine]
  apply sumOverCongr
  intro i
  rw [site_adjoint, formPairing_symm (site raiseCoeff i g)]

theorem occupation_dual_adjoint {C : Type} [CommRing C] (x xDual : Point → C) (g f : Form C) :
    formPairing g (occupation x xDual f) = formPairing (occupation xDual x g) f := by
  unfold occupation
  rw [formPairing_symm g, ← annihilate_adjoint, formPairing_symm (annihilate xDual f), annihilate_adjoint]

/-- For complex amplitudes, conjugation exchanges the two coefficient vectors,
so the contragredient identity becomes Hermitian self-adjointness. -/
structure ScalarConjugation (C : Type) [CommRing C] where
  star : C → C
  involutive : ∀ t, star (star t) = t
  fixesInteger : ∀ (n : Int), star (Int.cast n) = Int.cast n
  mapAdd : ∀ a b, star (a+b) = star a + star b
  mapMul : ∀ a b, star (a*b) = star a * star b

private theorem star_sum {C α : Type} [CommRing C] (s : ScalarConjugation C)
    (xs : List α) (f : α → C) :
    s.star (sumOver xs f) = sumOver xs fun x => s.star (f x) := by
  induction xs with
  | nil =>
    change s.star 0 = 0
    have h := s.fixesInteger 0
    have zero : Int.cast (R := C) (0 : Int) = 0 := Ring.intCast_ofNat 0
    rw [zero] at h
    exact h
  | cons x xs ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at *
    rw [s.mapAdd, ih]

private theorem star_combine {C : Type} [CommRing C] (s : ScalarConjugation C)
    (co : Point → Mask → Int) (x : Point → C) (f : Form C) :
    (fun m => s.star (combine co x f m)) = combine co (fun i => s.star (x i)) (fun m => s.star (f m)) := by
  funext m
  unfold combine site
  rw [star_sum]
  apply sumOverCongr
  intro i
  rw [s.mapMul, s.mapMul, s.fixesInteger]

theorem occupation_hermitian {C : Type} [CommRing C] (s : ScalarConjugation C)
    (x : Point → C) (g f : Form C) :
    formPairing (fun m => s.star (g m)) (occupation x (fun i => s.star (x i)) f) =
      formPairing (fun m => s.star (occupation x (fun i => s.star (x i)) g m)) f := by
  rw [occupation_dual_adjoint]
  unfold occupation create annihilate
  rw [star_combine, star_combine]
  simp only [s.involutive]

def waveForm {C : Type} [CommRing C] (v : Direction → C) (m : Mask) : C :=
  sumOver directions fun n => v n * Int.cast (planeWave n m.val)

set_option maxRecDepth 100000 in
private theorem wave_support : ∀ (m : Mask) (n : Direction),
    degree m ≠ 4 → planeWave n m.val = 0 := by decide

theorem waveForm_grade_four {C : Type} [CommRing C] (v : Direction → C) :
    homogeneous 4 (waveForm v) := by
  intro m hm
  apply zeroSum
  intro n
  rw [wave_support _ _ hm, Ring.intCast_ofNat]
  grind

/-- The same contraction used on arbitrary forms specializes exactly to
the already verified plane-wave contractions, including their signs. -/
theorem annihilate_waveForm {C : Type} [CommRing C] (u : Point → C) (v : Direction → C) (m : Mask) :
    annihilate u (waveForm v) m =
      sumOver columns (fun c => u c.1 * v c.2 * Int.cast (annihilationEntry c.1 c.2 m.val)) := by
  unfold annihilate combine site waveForm columns
  rw [sumOverFlatMap]
  apply sumOverCongr
  intro i
  rw [← Semiring.mul_assoc, sumOverMulLeft]
  change sumOver directions _ = sumOver (directions.map (fun n => (i,n))) _
  unfold sumOver
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro n _
  have h := congrArg (Int.cast (R := C)) (lower_planeWave i n m)
  rw [Ring.intCast_mul] at h
  grind

end RankSeven.ExteriorOperators
