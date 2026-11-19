import Init.Grind

namespace RankSeven.Interval

open Lean.Grind

attribute [local instance] Ring.intCast Semiring.natCast

variable {R : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem castLe {a b : Int} (h : a ≤ b) : (Int.cast a : R) ≤ Int.cast b := by
  -- A nonnegative integer difference is a natural number.
  have nonnegative : 0 ≤ b - a := by omega
  have natural : (↑(b - a).toNat : Int) = b - a := Int.toNat_of_nonneg nonnegative
  have naturalNonnegative (n : Nat) : (0 : R) ≤ Nat.cast n := by
    induction n with
    | zero => grind
    | succ n ih =>
      rw [Semiring.natCast_succ]
      have one : (0 : R) < 1 := OrderedRing.zero_lt_one
      grind
  have castEq := congrArg (Int.cast (R := R)) natural
  rw [Ring.intCast_natCast, Ring.intCast_sub] at castEq
  have step := naturalNonnegative (b - a).toNat
  grind

private theorem scalePositive (s : Int) (hs : 0 < s) : (0 : R) < Int.cast s := by
  have h := castLe (R := R) (by omega : 1 ≤ s)
  have one : (0 : R) < 1 := OrderedRing.zero_lt_one
  grind

private theorem castLt {a b : Int} (h : a < b) : (Int.cast a : R) < Int.cast b := by
  have gap := scalePositive (R := R) (b - a) (by omega)
  rw [Ring.intCast_sub] at gap
  grind

private theorem cancelScale {s x y : R} (hs : 0 < s) (h : s * x ≤ s * y) : x ≤ y := by
  by_cases order : x ≤ y
  · exact order
  · have greater : y < x := by grind
    have contradict := OrderedRing.mul_lt_mul_of_pos_left greater hs
    grind

private theorem mulMono {a b c : R} (h : a ≤ b) (sign : 0 ≤ c) : a * c ≤ b * c := by
  have diff : 0 ≤ b - a := by grind
  have result := OrderedRing.mul_nonneg diff sign
  grind

private theorem mulAnti {a b c : R} (h : a ≤ b) (sign : c ≤ 0) : b * c ≤ a * c := by
  have opposite : 0 ≤ -c := by grind
  have result := mulMono h opposite
  grind

/-- C++ truncates division toward zero. Its remainder test changes this to
    Euclidean division, which rounds down when the denominator is positive. -/
def cppFloor (n d : Int) : Int :=
  n.tdiv d - if n.tmod d < 0 then 1 else 0

theorem cppFloorEq (n d : Int) (hd : 0 < d) : cppFloor n d = n / d := by
  have sign : d.sign = 1 := Int.sign_eq_one_of_pos hd
  unfold cppFloor
  rw [Int.ediv_eq_tdiv, sign]
  by_cases divides : d ∣ n
  · have rem : n.tmod d = 0 := Int.tmod_eq_zero_of_dvd divides
    simp [divides, rem]
  · by_cases hn : 0 ≤ n
    · have rem : 0 ≤ n.tmod d := Int.tmod_nonneg _ hn
      simp [hn, Int.not_lt.mpr rem]
    · have nonnegRem := Int.tmod_nonneg d (show 0 ≤ -n by omega)
      rw [Int.neg_tmod] at nonnegRem
      have remNotZero : n.tmod d ≠ 0 := fun h => divides (Int.dvd_of_tmod_eq_zero h)
      have negative : n.tmod d < 0 := by omega
      simp [hn, divides, negative]

def floor (n d : Int) : Int := n / d

def ceil (n d : Int) : Int := -floor (-n) d

theorem floorLower (n d : Int) (hd : 0 < d) : floor n d * d ≤ n :=
  Int.ediv_mul_le n (by omega)

theorem ceilUpper (n d : Int) (hd : 0 < d) : n ≤ ceil n d * d := by
  have h := floorLower (-n) d hd
  unfold ceil
  grind

/-- A square-root certificate can be exported from the C++ contractor.
    Lean checks the integer inequalities directly and discards its floating-point seed. -/
def isFloorSqrt (n r : Int) : Bool :=
  decide (0 ≤ r ∧ r * r ≤ n ∧ n < (r + 1) * (r + 1))

theorem floorSqrtSound {n r : Int} (accepted : isFloorSqrt n r = true)
    {root : R} (nonneg : 0 ≤ root) (square : root * root = Int.cast n) :
    Int.cast r ≤ root ∧ root < Int.cast (r + 1) := by
  have h : 0 ≤ r ∧ r * r ≤ n ∧ n < (r + 1) * (r + 1) :=
    _root_.of_decide_eq_true accepted
  have rNonneg := castLe (R := R) h.1
  rw [Ring.intCast_ofNat] at rNonneg
  have rUpper := scalePositive (R := R) (r + 1) (by omega)
  have lower := castLe (R := R) h.2.1
  have upper := castLt (R := R) h.2.2
  simp only [Ring.intCast_mul] at lower upper
  constructor
  · by_cases comparison : Int.cast r ≤ root
    · exact comparison
    · have diff : 0 < Int.cast r - root := by grind
      have sum : 0 < Int.cast r + root := by grind
      have conflict := OrderedRing.mul_pos diff sum
      grind
  · by_cases comparison : root < Int.cast (r + 1)
    · exact comparison
    · have diff : 0 ≤ root - Int.cast (r + 1) := by grind
      have sum : 0 ≤ root + Int.cast (r + 1) := by grind
      have conflict := OrderedRing.mul_nonneg diff sum
      grind


/-- The integer computed by the C++ seed-and-correction loop. -/
def integerSqrt (n : Int) : Int := Int.ofNat n.toNat.sqrt

theorem integerSqrtCertified (n : Int) (nonnegative : 0≤n) : isFloorSqrt n (integerSqrt n)=true := by
  apply _root_.decide_eq_true
  let m := n.toNat
  have source : (↑m:Int)=n := Int.toNat_of_nonneg nonnegative
  have lower := Int.ofNat_le.mpr (Nat.sqrt_le m)
  have upper := Int.ofNat_lt.mpr (Nat.lt_succ_sqrt m)
  simp only [Int.natCast_mul,Int.natCast_succ] at lower upper
  rw [source] at lower upper
  exact ⟨Int.natCast_nonneg _,lower,upper⟩

structure Grid where
  scale : Int
  positive : 0 < scale

def cppGrid : Grid := ⟨2 ^ 27, by decide⟩

structure Bounds where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

namespace Bounds

def Contains (grid : Grid) (a : Bounds) (x : R) : Prop :=
  Int.cast a.lo ≤ Int.cast grid.scale * x ∧ Int.cast grid.scale * x ≤ Int.cast a.hi

def point (x : Int) : Bounds := ⟨x, x⟩

def rational (grid : Grid) (n d : Int) : Bounds :=
  ⟨floor (n * grid.scale) d, ceil (n * grid.scale) d⟩

def add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

def sub (a b : Bounds) : Bounds := ⟨a.lo - b.hi, a.hi - b.lo⟩

def smallest (a b : Bounds) : Bounds := ⟨min a.lo b.lo, min a.hi b.hi⟩

def largest (a b : Bounds) : Bounds := ⟨max a.lo b.lo, max a.hi b.hi⟩

def positivePart (a : Bounds) : Bounds := ⟨max 0 a.lo, max 0 a.hi⟩

def absolute (a : Bounds) : Bounds := ⟨max 0 (max a.lo (-a.hi)), max a.hi (-a.lo)⟩

theorem cppAbsoluteEq (a : Bounds) (ordered : a.lo ≤ a.hi) :
    a.absolute =
      let l := max (-a.lo) a.lo
      let h := max (-a.hi) a.hi
      ⟨if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min l h, max l h⟩ := by
  unfold absolute
  congr 1 <;> omega

def square (grid : Grid) (a : Bounds) : Bounds :=
  let magnitude := a.absolute
  ⟨floor (magnitude.lo * magnitude.lo) grid.scale, ceil (magnitude.hi * magnitude.hi) grid.scale⟩

def mul (grid : Grid) (a b : Bounds) : Bounds :=
  let p := a.lo * b.lo
  let q := a.lo * b.hi
  let r := a.hi * b.lo
  let s := a.hi * b.hi
  ⟨floor (min (min p q) (min r s)) grid.scale,
   ceil (max (max p q) (max r s)) grid.scale⟩

def div (grid : Grid) (a b : Bounds) : Bounds :=
  let lowerDen := if a.lo < 0 then b.lo else b.hi
  let upperDen := if a.hi < 0 then b.hi else b.lo
  ⟨floor (a.lo * grid.scale) lowerDen, ceil (a.hi * grid.scale) upperDen⟩

theorem rationalSound {grid : Grid} {n d : Int} {x : R} (hd : 0 < d)
    (hx : Int.cast d * x = Int.cast n) : (rational grid n d).Contains grid x := by
  have positive := scalePositive (R := R) d hd
  have lower := castLe (R := R) (floorLower (n * grid.scale) d hd)
  have upper := castLe (R := R) (ceilUpper (n * grid.scale) d hd)
  simp only [Ring.intCast_mul] at lower upper
  unfold Contains rational
  exact ⟨cancelScale positive (by grind), cancelScale positive (by grind)⟩

theorem addSound {grid : Grid} {a b : Bounds} {x y : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y) : (a.add b).Contains grid (x + y) := by
  simp only [Contains, add] at *
  grind

theorem subSound {grid : Grid} {a b : Bounds} {x y : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y) : (a.sub b).Contains grid (x - y) := by
  simp only [Contains, sub] at *
  grind

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem maxCastUpper (u v : Int) (y : R)
    (hu : Int.cast u ≤ y) (hv : Int.cast v ≤ y) : Int.cast (max u v) ≤ y := by
  rw [Int.max_def]
  split <;> assumption

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem minCastLower (u v : Int) (y : R)
    (hu : y ≤ Int.cast u) (hv : y ≤ Int.cast v) : y ≤ Int.cast (min u v) := by
  rw [Int.min_def]
  split <;> assumption

theorem smallestSound {grid : Grid} {a b : Bounds} {x y z : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y)
    (selected : (x ≤ y ∧ z = x) ∨ (y ≤ x ∧ z = y)) :
    (a.smallest b).Contains grid z := by
  have s := scalePositive (R := R) grid.scale grid.positive
  have sNonneg : (0 : R) ≤ Int.cast grid.scale := by grind
  obtain ⟨order, rfl⟩ | ⟨order, rfl⟩ := selected
  · have step := mulMono order sNonneg
    refine ⟨?_, minCastLower _ _ _ hx.2 (by grind [hy.2])⟩
    have lower := castLe (R := R) (Int.min_le_left a.lo b.lo)
    change Int.cast (min a.lo b.lo) ≤ _
    grind [hx.1]
  · have step := mulMono order sNonneg
    refine ⟨?_, minCastLower _ _ _ (by grind [hx.2]) hy.2⟩
    have lower := castLe (R := R) (Int.min_le_right a.lo b.lo)
    change Int.cast (min a.lo b.lo) ≤ _
    grind [hy.1]

theorem largestSound {grid : Grid} {a b : Bounds} {x y z : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y)
    (selected : (y ≤ x ∧ z = x) ∨ (x ≤ y ∧ z = y)) :
    (a.largest b).Contains grid z := by
  have s := scalePositive (R := R) grid.scale grid.positive
  have sNonneg : (0 : R) ≤ Int.cast grid.scale := by grind
  obtain ⟨order, rfl⟩ | ⟨order, rfl⟩ := selected
  · have step := mulMono order sNonneg
    refine ⟨maxCastUpper _ _ _ hx.1 (by grind [hy.1]), ?_⟩
    have upper := castLe (R := R) (Int.le_max_left a.hi b.hi)
    change _ ≤ Int.cast (max a.hi b.hi)
    grind [hx.2]
  · have step := mulMono order sNonneg
    refine ⟨maxCastUpper _ _ _ (by grind [hx.1]) hy.1, ?_⟩
    have upper := castLe (R := R) (Int.le_max_right a.hi b.hi)
    change _ ≤ Int.cast (max a.hi b.hi)
    grind [hy.2]

theorem positivePartSound {grid : Grid} {a : Bounds} {x z : R}
    (hx : a.Contains grid x) (selected : (x ≤ 0 ∧ z = 0) ∨ (0 ≤ x ∧ z = x)) :
    a.positivePart.Contains grid z := by
  have zero : (point 0).Contains grid (0 : R) := by
    simp only [Contains, point]
    grind
  exact largestSound zero hx selected

private theorem absoluteSound {grid : Grid} {a : Bounds} {x y : R} (hx : a.Contains grid x)
    (nonnegative : 0 ≤ y) (magnitude : y = x ∨ y = -x) : a.absolute.Contains grid y := by
  have s := scalePositive (R := R) grid.scale grid.positive
  have syNonneg := OrderedRing.mul_nonneg (show (0 : R) ≤ Int.cast grid.scale by grind) nonnegative
  have lo := hx.1
  have hi := hx.2
  have loUpper : (Int.cast a.lo : R) ≤ Int.cast grid.scale * y := by
    rcases magnitude with rfl | rfl <;> grind
  have hiUpper : (Int.cast (-a.hi) : R) ≤ Int.cast grid.scale * y := by
    rcases magnitude with rfl | rfl <;> grind
  refine ⟨maxCastUpper _ _ _ (by grind) (maxCastUpper _ _ _ loUpper hiUpper), ?_⟩
  change _ ≤ Int.cast (max a.hi (-a.lo))
  rcases magnitude with rfl | rfl
  · have upper := castLe (R := R) (Int.le_max_left a.hi (-a.lo))
    grind
  · have upper := castLe (R := R) (Int.le_max_right a.hi (-a.lo))
    grind

theorem squareSound {grid : Grid} {a : Bounds} {x : R} (hx : a.Contains grid x) :
    (a.square grid).Contains grid (x * x) := by
  obtain ⟨y, nonnegative, magnitude⟩ : ∃ y : R, 0 ≤ y ∧ (y = x ∨ y = -x) := by
    by_cases sign : 0 ≤ x
    · exact ⟨x, sign, Or.inl rfl⟩
    · exact ⟨-x, by grind, Or.inr rfl⟩
  let m := a.absolute
  have hs := absoluteSound hx nonnegative magnitude
  have aLower := castLe (R := R) (Int.le_max_left 0 (max a.lo (-a.hi)))
  have lowerNonneg : (0 : R) ≤ Int.cast m.lo := by
    change 0 ≤ Int.cast (max 0 (max a.lo (-a.hi)))
    grind
  have yNonneg : 0 ≤ (Int.cast grid.scale : R) * y := by grind [hs.1]
  have upperNonneg : (0 : R) ≤ Int.cast m.hi := by grind [hs.2]
  have loFirst := mulMono hs.1 lowerNonneg
  have loSecond := mulMono hs.1 yNonneg
  have hiFirst := mulMono hs.2 upperNonneg
  have hiSecond := mulMono hs.2 yNonneg
  have sameSquare : y * y = x * x := by rcases magnitude with rfl | rfl <;> grind
  have scale := scalePositive (R := R) grid.scale grid.positive
  have lower := castLe (R := R) (floorLower (m.lo * m.lo) grid.scale grid.positive)
  have upper := castLe (R := R) (ceilUpper (m.hi * m.hi) grid.scale grid.positive)
  simp only [Ring.intCast_mul] at lower upper
  change Int.cast (floor (m.lo * m.lo) grid.scale) ≤ Int.cast grid.scale * (x * x) ∧
    Int.cast grid.scale * (x * x) ≤ Int.cast (ceil (m.hi * m.hi) grid.scale)
  rw [← sameSquare]
  exact ⟨cancelScale scale (by grind), cancelScale scale (by grind)⟩

private theorem linearBetween {lo hi x z lb ub : R} (hx₁ : lo ≤ x) (hx₂ : x ≤ hi)
    (endLo : lb ≤ lo * z ∧ lo * z ≤ ub) (endHi : lb ≤ hi * z ∧ hi * z ≤ ub) :
    lb ≤ x * z ∧ x * z ≤ ub := by
  by_cases sign : 0 ≤ z
  · have lower := mulMono hx₁ sign
    have upper := mulMono hx₂ sign
    grind
  · have nonpositive : z ≤ 0 := by grind
    have lower := mulAnti hx₂ nonpositive
    have upper := mulAnti hx₁ nonpositive
    grind

theorem mulSound {grid : Grid} {a b : Bounds} {x y : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y) : (mul grid a b).Contains grid (x * y) := by
  let lo := min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
  let hi := max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
  have lows : lo ≤ a.lo * b.lo ∧ lo ≤ a.lo * b.hi ∧ lo ≤ a.hi * b.lo ∧ lo ≤ a.hi * b.hi := by
    have h := Int.le_min.mp (Int.le_refl lo)
    exact ⟨(Int.le_min.mp h.1).1, (Int.le_min.mp h.1).2,
      (Int.le_min.mp h.2).1, (Int.le_min.mp h.2).2⟩
  have highs : a.lo * b.lo ≤ hi ∧ a.lo * b.hi ≤ hi ∧ a.hi * b.lo ≤ hi ∧ a.hi * b.hi ≤ hi := by
    have h := Int.max_le.mp (Int.le_refl hi)
    exact ⟨(Int.max_le.mp h.1).1, (Int.max_le.mp h.1).2,
      (Int.max_le.mp h.2).1, (Int.max_le.mp h.2).2⟩
  have corner {u v : Int} (l : lo ≤ u * v) (h : u * v ≤ hi) :
      (Int.cast lo : R) ≤ Int.cast u * Int.cast v ∧ Int.cast u * Int.cast v ≤ (Int.cast hi : R) := by
    simpa only [Ring.intCast_mul] using And.intro (castLe (R := R) l) (castLe (R := R) h)
  have left := linearBetween hx.1 hx.2 (corner lows.1 highs.1) (corner lows.2.2.1 highs.2.2.1)
  have right := linearBetween hx.1 hx.2 (corner lows.2.1 highs.2.1) (corner lows.2.2.2 highs.2.2.2)
  have product := linearBetween hy.1 hy.2 (by simpa only [CommSemiring.mul_comm] using left)
    (by simpa only [CommSemiring.mul_comm] using right)
  have lower := castLe (R := R) (floorLower lo grid.scale grid.positive)
  have upper := castLe (R := R) (ceilUpper hi grid.scale grid.positive)
  have scale := scalePositive (R := R) grid.scale grid.positive
  change Int.cast (floor lo grid.scale) ≤ Int.cast grid.scale * (x * y)
    ∧ Int.cast grid.scale * (x * y) ≤ Int.cast (ceil hi grid.scale)
  constructor
  · apply cancelScale scale
    simp only [Ring.intCast_mul] at lower
    have productLower := product.1
    grind
  · apply cancelScale scale
    simp only [Ring.intCast_mul] at upper
    have productUpper := product.2
    grind

/-- Enclosure for the C++ quotient when all denominator values are positive.
    The equation `y * quotient = x` also lets the theorem apply over ℝ. -/
theorem divSound {grid : Grid} {a b : Bounds} {x y quotient : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y) (positiveDen : 0 < b.lo)
    (value : y * quotient = x) : (div grid a b).Contains grid quotient := by
  let S : R := Int.cast grid.scale
  let X := S * x
  let Y := S * y
  have hlo : (Int.cast a.lo : R) ≤ X := hx.1
  have hhi : X ≤ (Int.cast a.hi : R) := hx.2
  have denLo : (Int.cast b.lo : R) ≤ Y := hy.1
  have denHi : Y ≤ (Int.cast b.hi : R) := hy.2
  have loPos := scalePositive (R := R) b.lo positiveDen
  have yPos : 0 < Y := by grind
  have scalePos := scalePositive (R := R) grid.scale grid.positive
  have scaleNonneg : 0 ≤ S := by grind
  have hiPos : 0 < b.hi := by
    have order : b.lo ≤ b.hi := by
      by_cases order : b.lo ≤ b.hi
      · exact order
      · have clash := castLt (R := R) (show b.hi < b.lo by omega)
        grind
    omega
  let loDen := if a.lo < 0 then b.lo else b.hi
  let hiDen := if a.hi < 0 then b.hi else b.lo
  have loDenPos : 0 < loDen := by
    unfold loDen
    split <;> assumption
  have hiDenPos : 0 < hiDen := by
    unfold hiDen
    split <;> assumption
  have loRatio : Int.cast a.lo * Y ≤ X * Int.cast loDen := by
    have reduced : Int.cast a.lo * Y ≤ Int.cast a.lo * (Int.cast loDen : R) := by
      by_cases sign : a.lo < 0
      · have h := castLe (R := R) (by omega : a.lo ≤ 0)
        rw [Ring.intCast_ofNat] at h
        have step := mulAnti denLo h
        simp only [loDen, ite_eq_left sign]
        grind
      · have h := castLe (R := R) (by omega : 0 ≤ a.lo)
        rw [Ring.intCast_ofNat] at h
        have step := mulMono denHi h
        simp only [loDen, ite_eq_right sign]
        grind
    have positive := scalePositive (R := R) loDen loDenPos
    have step := mulMono hlo (show (0 : R) ≤ Int.cast loDen by grind)
    grind
  have hiRatio : X * Int.cast hiDen ≤ Int.cast a.hi * Y := by
    have increased : Int.cast a.hi * (Int.cast hiDen : R) ≤ Int.cast a.hi * Y := by
      by_cases sign : a.hi < 0
      · have h := castLe (R := R) (by omega : a.hi ≤ 0)
        rw [Ring.intCast_ofNat] at h
        have step := mulAnti denHi h
        simp only [hiDen, ite_eq_left sign]
        grind
      · have h := castLe (R := R) (by omega : 0 ≤ a.hi)
        rw [Ring.intCast_ofNat] at h
        have step := mulMono denLo h
        simp only [hiDen, ite_eq_right sign]
        grind
    have positive := scalePositive (R := R) hiDen hiDenPos
    have step := mulMono hhi (show (0 : R) ≤ Int.cast hiDen by grind)
    grind
  change Int.cast (floor (a.lo * grid.scale) loDen) ≤ S * quotient
    ∧ S * quotient ≤ Int.cast (ceil (a.hi * grid.scale) hiDen)
  have quotientScaled : Y * quotient = X := by
    dsimp [Y, X]
    rw [Semiring.mul_assoc, value]
  constructor
  · have rounded := castLe (R := R) (floorLower (a.lo * grid.scale) loDen loDenPos)
    simp only [Ring.intCast_mul] at rounded
    have lhs := mulMono rounded (show 0 ≤ Y by grind)
    have rhs := mulMono loRatio scaleNonneg
    apply cancelScale yPos
    apply cancelScale (scalePositive loDen loDenPos)
    calc
      _ = Int.cast (floor (a.lo * grid.scale) loDen) * Int.cast loDen * Y := by grind
      _ ≤ Int.cast a.lo * S * Y := lhs
      _ = Int.cast a.lo * Y * S := by grind
      _ ≤ X * Int.cast loDen * S := rhs
      _ = Int.cast loDen * (Y * (S * quotient)) := by
        rw [← quotientScaled]
        grind
  · have rounded := castLe (R := R) (ceilUpper (a.hi * grid.scale) hiDen hiDenPos)
    simp only [Ring.intCast_mul] at rounded
    have lhs := mulMono hiRatio scaleNonneg
    have rhs := mulMono rounded (show 0 ≤ Y by grind)
    apply cancelScale yPos
    apply cancelScale (scalePositive hiDen hiDenPos)
    calc
      _ = X * Int.cast hiDen * S := by
        rw [← quotientScaled]
        grind
      _ ≤ Int.cast a.hi * Y * S := lhs
      _ = Int.cast a.hi * S * Y := by grind
      _ ≤ Int.cast (ceil (a.hi * grid.scale) hiDen) * Int.cast hiDen * Y := rhs
      _ = Int.cast hiDen * (Y * Int.cast (ceil (a.hi * grid.scale) hiDen)) := by grind


/-- Outward integer square-root rounding with scale retained.
The one-unit upper allowance matches the C++ verifier even for a square. -/
def root (grid : Grid) (a : Bounds) : Bounds :=
  ⟨integerSqrt (a.lo*grid.scale), integerSqrt (a.hi*grid.scale)+1⟩

theorem rootSound {grid : Grid} {a : Bounds} {x r : R}
    (hx : a.Contains grid x) (nonnegative : 0≤a.lo) (r0 : 0≤r) (square : r*r=x) :
    (a.root grid).Contains grid r := by
  let S : R := Int.cast grid.scale
  let L := integerSqrt (a.lo*grid.scale)
  let U := integerSqrt (a.hi*grid.scale)
  have hiNonnegative : 0≤a.hi := by
    by_cases order : 0≤a.hi
    · exact order
    · have conflict := castLt (R:=R) (show a.hi<a.lo by omega)
      grind only [hx.1,hx.2]
  have loCertified : 0≤L ∧ L*L≤a.lo*grid.scale ∧ a.lo*grid.scale<(L+1)*(L+1) :=
    _root_.of_decide_eq_true (integerSqrtCertified _ (Int.mul_nonneg nonnegative (by have p := grid.positive; omega)))
  have hiCertified : 0≤U ∧ U*U≤a.hi*grid.scale ∧ a.hi*grid.scale<(U+1)*(U+1) :=
    _root_.of_decide_eq_true (integerSqrtCertified _ (Int.mul_nonneg hiNonnegative (by have p := grid.positive; omega)))
  have scale : 0<S := scalePositive (R:=R) grid.scale grid.positive
  have rS := OrderedRing.mul_nonneg (Std.le_of_lt scale) r0
  have low := castLe (R:=R) loCertified.2.1
  have high := castLt (R:=R) hiCertified.2.2
  simp only [Ring.intCast_mul] at low high
  have lowerScaled := OrderedRing.mul_le_mul_of_nonneg_right hx.1 (Std.le_of_lt scale)
  have upperScaled := OrderedRing.mul_le_mul_of_nonneg_right hx.2 (Std.le_of_lt scale)
  have scaledSquare : (S*r)*(S*r)=S*x*S := by
    rw [←square]
    grind only
  have leftRange : (Int.cast L:R)*Int.cast L≤(S*r)*(S*r) := by
    rw [scaledSquare]
    exact Std.le_trans low lowerScaled
  have rightRange : (S*r)*(S*r)<(Int.cast (U+1):R)*Int.cast (U+1) := by
    rw [scaledSquare]
    exact Std.lt_of_le_of_lt upperScaled high
  have diff (a b : R) : (a-b)*(a+b)=a*a-b*b := by grind only
  have loPos := castLe (R:=R) loCertified.1
  rw [Ring.intCast_zero] at loPos
  have hiPos := castLe (R:=R) (show 0≤U+1 by have p := hiCertified.1; omega)
  rw [Ring.intCast_zero] at hiPos
  change (Int.cast L:R)≤S*r ∧ S*r≤Int.cast (U+1)
  constructor
  · by_cases ok : (Int.cast L:R)≤S*r
    · exact ok
    · have d := OrderedRing.mul_pos (show 0<(Int.cast L:R)-S*r by grind only)
        (show 0<(Int.cast L:R)+S*r by grind only)
      rw [diff] at d
      grind only
  · by_cases ok : S*r≤(Int.cast (U+1):R)
    · exact ok
    · have d := OrderedRing.mul_nonneg (show 0≤S*r-(Int.cast (U+1):R) by grind only)
        (show 0≤S*r+(Int.cast (U+1):R) by grind only)
      rw [diff] at d
      grind only

theorem nonpositive {grid : Grid} {a : Bounds} {x : R} (hx : a.Contains grid x)
    (h : a.hi ≤ 0) : x ≤ 0 := by
  have upper := castLe (R := R) h
  have contained := hx.2
  apply cancelScale (scalePositive grid.scale grid.positive)
  grind

/-- Soundness of the upper tail contractor's nonpositive discount prune. -/
theorem discountPrune {grid : Grid} {cBox dBox : Bounds} {c d : R}
    (hc : cBox.Contains grid c) (hd : dBox.Contains grid d)
    {cLower dUpper : R}
    (lower : Int.cast grid.scale * cLower = Int.cast cBox.lo)
    (upper : Int.cast grid.scale * dUpper = Int.cast dBox.hi)
    (ordered : 0 ≤ c) (inUnit : dUpper ≤ 1)
    (test : ((point dBox.hi).sub (mul grid
      ((point grid.scale).sub (point dBox.hi)) (point cBox.lo))).hi ≤ 0) :
    d - (1 - d) * c ≤ 0 := by
  have scale := scalePositive (R := R) grid.scale grid.positive
  have cMonotone : cLower ≤ c := cancelScale scale (by grind [hc.1])
  have dMonotone : d ≤ dUpper := cancelScale scale (by grind [hd.2])
  have dh : (point dBox.hi).Contains grid dUpper := by simp [Contains, point, upper]
  have cl : (point cBox.lo).Contains grid cLower := by simp [Contains, point, lower]
  have one : (point grid.scale).Contains grid (1 : R) := by
    simp [Contains, point, Semiring.mul_one]
  have complement := subSound one dh
  have discount := subSound dh (mulSound complement cl)
  have endpoint := nonpositive discount test
  have dGap := OrderedRing.mul_nonneg (show 0 ≤ dUpper - d by grind) ordered
  have cGap := OrderedRing.mul_nonneg (show 0 ≤ 1 - dUpper by grind)
    (show 0 ≤ c - cLower by grind)
  grind

end Bounds

/-- The exact integer mixing predicate used by the C++ corner branch. -/
def blend (s₁ t₁ s₂ t₂ : Int) : Bool :=
  if max s₁ t₁ ≤ 0 ∨ max s₂ t₂ ≤ 0 then false
  else if (0 < s₁ ∧ 0 < s₂) ∨ (0 < t₁ ∧ 0 < t₂) then true
  else if 0 < s₁ then decide ((-s₂) * (s₁ - t₁) < s₁ * (t₂ - s₂))
  else decide ((-s₁) * (s₂ - t₂) < s₂ * (t₁ - s₁))

/-- Positive weighted sums at the registered lower endpoints also give
    positive sums for the enclosed comparisons. Weights are unnormalized. -/
theorem blendSound {s₁ t₁ s₂ t₂ : Int} (accepted : blend s₁ t₁ s₂ t₂ = true) :
    ∃ w v : Int, 0 ≤ w ∧ 0 ≤ v ∧
      0 < w * s₁ + v * t₁ ∧ 0 < w * s₂ + v * t₂ := by
  unfold blend at accepted
  split at accepted
  · contradiction
  · rename_i nonempty
    have first : 0 < s₁ ∨ 0 < t₁ := by omega
    have second : 0 < s₂ ∨ 0 < t₂ := by omega
    split at accepted
    · rename_i sameSide
      rcases sameSide with ⟨hs₁, hs₂⟩ | ⟨ht₁, ht₂⟩
      · exact ⟨1, 0, by grind⟩
      · exact ⟨0, 1, by grind⟩
    · rename_i noSameSide
      split at accepted
      · rename_i s₁Pos
        have t₁Nonpos : t₁ ≤ 0 := by omega
        have s₂Nonpos : s₂ ≤ 0 := by omega
        have t₂Pos : 0 < t₂ := by omega
        have cross := _root_.of_decide_eq_true accepted
        exact ⟨t₂ - t₁, s₁ - s₂, by grind⟩
      · rename_i s₁Nonpos
        have t₁Pos : 0 < t₁ := by omega
        have t₂Nonpos : t₂ ≤ 0 := by omega
        have s₂Pos : 0 < s₂ := by omega
        have cross := _root_.of_decide_eq_true accepted
        exact ⟨t₁ - t₂, s₂ - s₁, by grind⟩

theorem blendEnclosed {grid : Grid} {s₁ t₁ s₂ t₂ : Int} {a b c d : R}
    (accepted : blend s₁ t₁ s₂ t₂ = true)
    (ha : Int.cast s₁ ≤ Int.cast grid.scale * a) (hb : Int.cast t₁ ≤ Int.cast grid.scale * b)
    (hc : Int.cast s₂ ≤ Int.cast grid.scale * c) (hd : Int.cast t₂ ≤ Int.cast grid.scale * d) :
    ∃ w v : R, 0 ≤ w ∧ 0 ≤ v ∧ 0 < w * a + v * b ∧ 0 < w * c + v * d := by
  obtain ⟨w, v, nonnegW, nonnegV, first, second⟩ := blendSound accepted
  have wNonneg := castLe (R := R) nonnegW
  have vNonneg := castLe (R := R) nonnegV
  have firstPositive := scalePositive (R := R) _ first
  have secondPositive := scalePositive (R := R) _ second
  have wNonneg' : 0 ≤ (Int.cast w : R) := by grind
  have vNonneg' : 0 ≤ (Int.cast v : R) := by grind
  simp only [Ring.intCast_add, Ring.intCast_mul] at firstPositive secondPositive
  have haW := mulMono ha wNonneg'
  have hbV := mulMono hb vNonneg'
  have hcW := mulMono hc wNonneg'
  have hdV := mulMono hd vNonneg'
  have scale := scalePositive (R := R) grid.scale grid.positive
  have recover (p : R) (positive : 0 < Int.cast grid.scale * p) : 0 < p := by
    by_cases sign : 0 < p
    · exact sign
    · have contradiction := OrderedRing.mul_nonneg (show 0 ≤ (Int.cast grid.scale : R) by grind)
        (show 0 ≤ -p by grind)
      grind
  exact ⟨Int.cast w, Int.cast v, wNonneg', vNonneg',
    recover _ (by grind), recover _ (by grind)⟩

def lerp (t a b : R) : R := (1 - t) * a + t * b

theorem lerpPositive {t a b : R} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < lerp t a b := by
  have leftWeight : 0 ≤ 1 - t := by grind
  unfold lerp
  by_cases tPositive : 0 < t
  · have left := OrderedRing.mul_nonneg leftWeight (show 0 ≤ a by grind)
    have right := OrderedRing.mul_pos tPositive hb
    grind
  · have tZero : t = 0 := by grind
    rw [tZero]
    grind

structure Bilinear (R : Type) where
  constant : R
  first : R
  second : R
  interaction : R

def Bilinear.eval (f : Bilinear R) (c d : R) : R :=
  f.constant + f.first * c + f.second * d + f.interaction * c * d

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem Bilinear.interpolate (f : Bilinear R) (c₀ c₁ d₀ d₁ s t : R) :
    f.eval (lerp s c₀ c₁) (lerp t d₀ d₁) =
      lerp t (lerp s (f.eval c₀ d₀) (f.eval c₁ d₀)) (lerp s (f.eval c₀ d₁) (f.eval c₁ d₁)) := by
  unfold eval lerp
  grind

/-- A bilinear margin that is positive at all four ordered tail corners
    stays positive at every convex combination of the two axes. -/
theorem Bilinear.positiveOnRectangle (f : Bilinear R) (c₀ c₁ d₀ d₁ s t : R)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h₀₀ : 0 < f.eval c₀ d₀) (h₁₀ : 0 < f.eval c₁ d₀)
    (h₀₁ : 0 < f.eval c₀ d₁) (h₁₁ : 0 < f.eval c₁ d₁) :
    0 < f.eval (lerp s c₀ c₁) (lerp t d₀ d₁) := by
  rw [f.interpolate]
  exact lerpPositive ht₀ ht₁ (lerpPositive hs₀ hs₁ h₀₀ h₁₀) (lerpPositive hs₀ hs₁ h₀₁ h₁₁)

end RankSeven.Interval

#print axioms RankSeven.Interval.cppFloorEq
#print axioms RankSeven.Interval.floorSqrtSound
#print axioms RankSeven.Interval.Bounds.rationalSound
#print axioms RankSeven.Interval.Bounds.cppAbsoluteEq
#print axioms RankSeven.Interval.Bounds.squareSound
#print axioms RankSeven.Interval.Bounds.smallestSound
#print axioms RankSeven.Interval.Bounds.largestSound
#print axioms RankSeven.Interval.Bounds.positivePartSound
#print axioms RankSeven.Interval.Bounds.mulSound
#print axioms RankSeven.Interval.Bounds.divSound
#print axioms RankSeven.Interval.Bounds.discountPrune
#print axioms RankSeven.Interval.blendSound
#print axioms RankSeven.Interval.blendEnclosed
#print axioms RankSeven.Interval.Bilinear.positiveOnRectangle

#print axioms RankSeven.Interval.integerSqrtCertified
#print axioms RankSeven.Interval.Bounds.rootSound
