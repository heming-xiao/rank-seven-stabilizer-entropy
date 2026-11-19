import Rank7PauliTensor

/-! A finite coordinate proof of the crossed exterior compression bound. All
scalar arguments work over any linearly ordered commutative ring. -/

namespace RankSeven.ExteriorCuts

set_option linter.unusedSectionVars false

open Lean.Grind RankSeven.Pauli

variable {R ι : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R] [DecidableRel (α := R) (· ≤ ·)]

def pos (x : R) : R := if 0 ≤ x then x else 0

private theorem posNonneg (x : R) : 0 ≤ pos x := by unfold pos; split <;> grind
private theorem posMono {x y : R} (h : x ≤ y) : pos x ≤ pos y := by
  unfold pos; split <;> split <;> grind

/-- Squared width lost at an outside coordinate of amplitude y. -/
def error (l u y : R) : R := pos ((pos (u-l))^2 - (pos (u-y))^2)

/-- Length of the nominal interval above y, including inactive intervals. -/
def clipped (l u y : R) : R := pos (pos (u-y) - pos (l-y))

private theorem clippedNonneg (l u y : R) : 0 ≤ clipped l u y := posNonneg _

private theorem clippedUpper (l u y : R) : clipped l u y ≤ pos (u-y) := by
  unfold clipped
  have := posNonneg (l-y)
  have := posNonneg (u-y)
  unfold pos at *; split <;> grind

/-- Disjoint spectral intervals spend at most one amplitude difference.
The intermediate `lHigh` is precisely the separation of the two intervals. -/
theorem lengthBudget (lLow uLow lHigh uHigh x y : R)
    (apart : uLow ≤ lHigh) (lowInside : uLow ≤ x) (highInside : uHigh ≤ x) :
    clipped lLow uLow y + clipped lHigh uHigh y ≤ pos (x-y) := by
  have h₁ := clippedUpper lLow uLow y
  have h₂ : pos (uLow-y) ≤ pos (lHigh-y) := posMono (by grind)
  have h₃ : pos (uHigh-y) ≤ pos (x-y) := posMono (by grind)
  have h₄ : pos (uLow-y) ≤ pos (x-y) := posMono (by grind)
  unfold clipped at h₁ ⊢
  generalize pos (uLow-y) = k at *
  generalize pos (lLow-y) = d at *
  generalize pos (uHigh-y) = m at *
  generalize pos (lHigh-y) = e at *
  generalize pos (x-y) = t at *
  unfold pos at *; split <;> grind

private theorem posOfNonpos (x : R) (h : x ≤ 0) : pos x = 0 := by
  unfold pos; split <;> grind

private theorem posOfNonneg (x : R) (h : 0 ≤ x) : pos x = x := by
  unfold pos; split <;> grind

omit [DecidableRel (α := R) (· ≤ ·)] in
private theorem sqMono {v w : R} (hv : 0 ≤ v) (h : v ≤ w) : v^2 ≤ w^2 := by
  have a : 0 ≤ w-v := by grind
  have b : 0 ≤ w+v := by grind
  have := OrderedRing.mul_nonneg a b
  grind

private theorem sqNonneg (v : R) : 0 ≤ v^2 := by
  by_cases h : 0 ≤ v
  · have := OrderedRing.mul_nonneg h h
    grind
  · have hn : 0 ≤ -v := by grind
    have := OrderedRing.mul_nonneg hn hn
    grind

private theorem posSqLe (v : R) : (pos v)^2 ≤ v^2 := by
  have := sqNonneg v
  unfold pos; split <;> grind

private theorem twoSquares (a b t : R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a+b ≤ t) : a^2 + b^2 ≤ t^2 := by
  have hp := OrderedRing.mul_nonneg ha hb
  have hs := sqMono (v := a+b) (by grind) h
  grind

theorem clippedSquaresBudget (lLow uLow lHigh uHigh x y : R)
    (apart : uLow ≤ lHigh) (lo : uLow ≤ x) (hi : uHigh ≤ x) :
    (clipped lLow uLow y)^2 + (clipped lHigh uHigh y)^2 ≤ (x-y)^2 := by
  have h := twoSquares _ _ _ (clippedNonneg lLow uLow y) (clippedNonneg lHigh uHigh y)
    (lengthBudget lLow uLow lHigh uHigh x y apart lo hi)
  have := posSqLe (x-y)
  grind

private theorem oneSquare (l u x y : R) (hu : u ≤ x) :
    (clipped l u y)^2 ≤ (x-y)^2 := by
  have h₁ := clippedUpper l u y
  have h₂ : pos (u-y) ≤ pos (x-y) := posMono (by grind)
  have := sqMono (clippedNonneg l u y) (show clipped l u y ≤ pos (x-y) by grind)
  have := posSqLe (x-y)
  grind

private theorem clippedBelow (l u y : R) (h : y ≤ l) :
    clipped l u y = pos (u-l) := by
  unfold clipped pos; repeat' split <;> grind

private theorem clippedAbove (l u y : R) (h : l ≤ y) :
    clipped l u y = pos (u-y) := by
  unfold clipped pos; repeat' split <;> grind

/-- Identifies the coordinate error with the unbought part of the width. -/
theorem widthDecomposition (l u y : R) :
    (pos (u-l))^2 = (clipped l u y)^2 + error l u y := by
  by_cases h : y ≤ l
  · rw [clippedBelow l u y h]
    have h' : pos (u-l) ≤ pos (u-y) := posMono (by grind)
    have := sqMono (posNonneg _) h'
    unfold error
    rw [posOfNonpos ((pos (u-l))^2 - (pos (u-y))^2) (by grind)]
    grind
  · have h' : l ≤ y := by grind
    rw [clippedAbove l u y h']
    have h'' : pos (u-y) ≤ pos (u-l) := posMono (by grind)
    have := sqMono (posNonneg _) h''
    unfold error
    rw [posOfNonneg ((pos (u-l))^2 - (pos (u-y))^2) (by grind)]
    grind

/-- The error is supported on outside coordinates lying above l. -/
theorem errorOfBelow (l u y : R) (h : y ≤ l) : error l u y = 0 := by
  have t := widthDecomposition l u y
  rw [clippedBelow l u y h] at t
  grind

/-- Nested memberships: outside both, inside the lower cut only, or inside both. -/
inductive Level where | outside | lower | both

def Level.low : Level → Bool | .outside => false | _ => true
def Level.high : Level → Bool | .both => true | _ => false

def insideBounds (k : Level) (uLow uHigh x : R) : Prop :=
  (k.low = true → uLow ≤ x) ∧ (k.high = true → uHigh ≤ x)

def indicator (b : Bool) : R := if b then 1 else 0

def crossing (i j : Bool) : R := indicator (i && !j)

/-- Diagonal claimed width for an index. The first supplied cut is the lower one. -/
def diagBill (wl wh : R) (i : Level) : R :=
  wl * indicator i.low + wh * indicator i.high

def edgeBill (wl wh : R) (i j : Level) : R :=
  wl * crossing i.low j.low + wh * crossing i.high j.high

def outsideTax (lo uLo hi uHi y : R) (j : Level) : R :=
  error lo uLo y * indicator (!j.low) + error hi uHi y * indicator (!j.high)

private theorem diagonalBudget (lo uLo hi uHi x : R) (i : Level)
    (hl : 0 ≤ lo) (hh : 0 ≤ hi) (apart : uLo ≤ hi)
    (ins : insideBounds i uLo uHi x) :
    diagBill ((pos (uLo-lo))^2) ((pos (uHi-hi))^2) i ≤ x^2 := by
  have both := clippedSquaresBudget lo uLo hi uHi x 0 apart
  have one := oneSquare lo uLo x 0
  rw [clippedBelow lo uLo 0 hl, clippedBelow hi uHi 0 hh] at both
  rw [clippedBelow lo uLo 0 hl] at one
  have := sqNonneg x
  cases i <;> simp [diagBill, indicator, Level.low, Level.high, insideBounds] at * <;> grind

private theorem directedEdgeBudget (lo uLo hi uHi x y : R) (i j : Level)
    (apart : uLo ≤ hi) (iBounds : insideBounds i uLo uHi x)
    (jBounds : insideBounds j uLo uHi y) :
    let wl := (pos (uLo-lo))^2
    let wh := (pos (uHi-hi))^2
    edgeBill wl wh i j + edgeBill wl wh j i ≤
      (x-y)^2 + (outsideTax lo uLo hi uHi x i + outsideTax lo uLo hi uHi y j) := by
  dsimp only
  have lr := widthDecomposition lo uLo x
  have lr' := widthDecomposition lo uLo y
  have hr := widthDecomposition hi uHi x
  have hr' := widthDecomposition hi uHi y
  have lx := posNonneg ((pos (uLo-lo))^2 - (pos (uLo-x))^2)
  have ly := posNonneg ((pos (uLo-lo))^2 - (pos (uLo-y))^2)
  have hx := posNonneg ((pos (uHi-hi))^2 - (pos (uHi-x))^2)
  have hy := posNonneg ((pos (uHi-hi))^2 - (pos (uHi-y))^2)
  change 0 ≤ error lo uLo x at lx
  change 0 ≤ error lo uLo y at ly
  change 0 ≤ error hi uHi x at hx
  change 0 ≤ error hi uHi y at hy
  have bl := clippedSquaresBudget lo uLo hi uHi x y apart
  have br := clippedSquaresBudget lo uLo hi uHi y x apart
  have al := oneSquare lo uLo x y
  have ar := oneSquare lo uLo y x
  have ah := oneSquare hi uHi x y
  have bh := oneSquare hi uHi y x
  have hsq := sqNonneg (x-y)
  have sym : (y-x)^2 = (x-y)^2 := by grind
  cases i <;> cases j <;>
    simp [edgeBill, crossing, indicator, outsideTax, Level.low, Level.high, insideBounds]
      at iBounds jBounds ⊢ <;> grind

private theorem taxNonnegative (lo uLo hi uHi x : R) (i : Level) :
    0 ≤ outsideTax lo uLo hi uHi x i := by
  have l : 0 ≤ error lo uLo x := posNonneg _
  have h : 0 ≤ error hi uHi x := posNonneg _
  cases i <;> simp [outsideTax, indicator, Level.low, Level.high] <;> grind

private theorem sumMono (xs : List ι) {f g : ι → R} (h : ∀ i, f i ≤ g i) :
    sumOver xs f ≤ sumOver xs g := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons i is ih =>
    change f i + sumOver is f ≤ g i + sumOver is g
    have := h i
    grind

private theorem scaleLe {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a*c ≤ b*c := by
  have h' : 0 ≤ b-a := by grind
  have := OrderedRing.mul_nonneg h' hc
  grind

def pairSum (xs : List ι) (F : ι → ι → R) : R :=
  sumOver xs (fun i => sumOver xs (F i))

private theorem pairMono (xs : List ι) {F G : ι → ι → R} (h : ∀ i j, F i j ≤ G i j) :
    pairSum xs F ≤ pairSum xs G := sumMono xs (fun i => sumMono xs (h i))

private theorem pairCongr (xs : List ι) {F G : ι → ι → R} (h : ∀ i j, F i j = G i j) :
    pairSum xs F = pairSum xs G := sumOverCongr xs (fun i => sumOverCongr xs (h i))

private theorem pairAdd (xs : List ι) (F G : ι → ι → R) :
    pairSum xs (fun i j => F i j + G i j) = pairSum xs F + pairSum xs G := by
  unfold pairSum
  simp only [← sumOverAdd]

private theorem swapPair (xs : List ι) (F : ι → ι → R) :
    pairSum xs (fun i j => F j i) = pairSum xs F :=
  sumOverSwap xs xs _

private theorem bothDirections (xs : List ι) (F e : ι → ι → R) (sym : ∀ i j, e i j = e j i) :
    pairSum xs (fun i j => (F i j + F j i)*e i j) =
      2 * pairSum xs (fun i j => F i j * e i j) := by
  let H i j := F i j * e i j
  calc
    _ = pairSum xs (fun i j => H i j + H j i) := by
      apply pairCongr
      intro i j
      dsimp [H]
      rw [← sym i j]
      grind
    _ = _ := by rw [pairAdd xs H (fun i j => H j i), swapPair xs H]; dsimp [H]; grind

/-- Defect of a coordinate block, counted with oriented cross entries only. -/
def cutCost (xs : List ι) (cut : ι → Bool) (slack : ι → R) (off : ι → ι → R) : R :=
  sumOver xs (fun i => indicator (cut i) * slack i) +
    pairSum xs (fun i j => crossing (cut i) (cut j) * off i j)

private theorem sumLinear (xs : List ι) (wl wh : R) (F G : ι → R) :
    sumOver xs (fun i => wl*F i + wh*G i) = wl*sumOver xs F + wh*sumOver xs G := by
  rw [sumOverAdd xs (fun i => wl*F i) (fun i => wh*G i), ← sumOverMulLeft, ← sumOverMulLeft]

private theorem pairLinear (xs : List ι) (wl wh : R) (F G : ι → ι → R) :
    pairSum xs (fun i j => wl*F i j + wh*G i j) =
      wl*pairSum xs F + wh*pairSum xs G := by
  unfold pairSum
  simp only [sumLinear]

private theorem nominalBill (xs : List ι) (tier : ι → Level) (s : ι → R) (e : ι → ι → R)
    (wl wh : R) :
    wl * cutCost xs (fun i => (tier i).low) s e +
      wh * cutCost xs (fun i => (tier i).high) s e =
    sumOver xs (fun i => diagBill wl wh (tier i) * s i) +
      pairSum xs (fun i j => edgeBill wl wh (tier i) (tier j) * e i j) := by
  let low i := (tier i).low
  let high i := (tier i).high
  have d : sumOver xs (fun i => diagBill wl wh (tier i) * s i) =
      wl * sumOver xs (fun i => indicator (low i)*s i) +
      wh * sumOver xs (fun i => indicator (high i)*s i) := by
    rw [← sumLinear]
    apply sumOverCongr; intro i; dsimp [diagBill, low, high]; grind
  have p : pairSum xs (fun i j => edgeBill wl wh (tier i) (tier j) * e i j) =
      wl * pairSum xs (fun i j => crossing (low i) (low j)*e i j) +
      wh * pairSum xs (fun i j => crossing (high i) (high j)*e i j) := by
    rw [← pairLinear]
    apply pairCongr; intro i j; dsimp [edgeBill, low, high]; grind
  rw [d,p]
  dsimp [cutCost,low,high]; grind

/-- The crossed two-cut coordinate inequality, with both sides doubled.
Here e is the off-diagonal squared-entry matrix (zero diagonal in the physical
application), slack is diag(T-T²), and cap is a bound on the off-diagonal row mass. -/
theorem crossedCutsTwice (xs : List ι) (tier : ι → Level)
    (a slack cap : ι → R) (e : ι → ι → R) (lo uLo hi uHi : R)
    (loNonneg : 0 ≤ lo) (hiNonneg : 0 ≤ hi) (apart : uLo ≤ hi)
    (inside : ∀ i, insideBounds (tier i) uLo uHi (a i))
    (slackNonneg : ∀ i, 0 ≤ slack i) (edgeNonneg : ∀ i j, 0 ≤ e i j)
    (sym : ∀ i j, e i j = e j i)
    (rowBound : ∀ i, sumOver xs (e i) ≤ cap i) :
    2 * ((pos (uLo-lo))^2 * cutCost xs (fun i => (tier i).low) slack e +
         (pos (uHi-hi))^2 * cutCost xs (fun i => (tier i).high) slack e) ≤
      2 * sumOver xs (fun i => (a i)^2 * slack i) +
      pairSum xs (fun i j => (a i - a j)^2 * e i j) +
      2 * sumOver xs (fun i => outsideTax lo uLo hi uHi (a i) (tier i) * cap i) := by
  let wl := (pos (uLo-lo))^2
  let wh := (pos (uHi-hi))^2
  let bill i j := edgeBill wl wh (tier i) (tier j)
  let tax i := outsideTax lo uLo hi uHi (a i) (tier i)
  let gap i j := (a i-a j)^2
  have diag := sumMono xs (fun i => scaleLe
    (diagonalBudget lo uLo hi uHi (a i) (tier i) loNonneg hiNonneg apart (inside i))
    (slackNonneg i))
  have taxPos (i : ι) : 0 ≤ tax i := taxNonnegative lo uLo hi uHi (a i) (tier i)
  have taxSum : pairSum xs (fun i j => tax i * e i j) ≤
      sumOver xs (fun i => tax i * cap i) := by
    unfold pairSum
    apply sumMono
    intro i
    rw [← sumOverMulLeft]
    have h := scaleLe (rowBound i) (taxPos i)
    grind
  have edges : 2 * pairSum xs (fun i j => bill i j * e i j) ≤
      pairSum xs (fun i j => gap i j * e i j) +
      2 * pairSum xs (fun i j => tax i * e i j) := by
    rw [← bothDirections xs bill e sym, ← bothDirections xs (fun i _ => tax i) e sym, ← pairAdd]
    apply pairMono
    intro i j
    have hb := directedEdgeBudget lo uLo hi uHi (a i) (a j) (tier i) (tier j)
      apart (inside i) (inside j)
    change bill i j + bill j i ≤ gap i j + (tax i + tax j) at hb
    have := scaleLe hb (edgeNonneg i j)
    grind
  rw [nominalBill]
  change 2 * (sumOver xs (fun i => diagBill wl wh (tier i) * slack i) +
      pairSum xs (fun i j => bill i j * e i j)) ≤
    2 * sumOver xs (fun i => (a i)^2 * slack i) +
      pairSum xs (fun i j => gap i j * e i j) + 2 * sumOver xs (fun i => tax i * cap i)
  change sumOver xs (fun i => diagBill wl wh (tier i) * slack i) ≤ _ at diag
  grind

def offDiagonal [DecidableEq ι] (e : ι → ι → R) (i j : ι) : R :=
  if i = j then 0 else e i j

private theorem offCutCost [DecidableEq ι] (xs : List ι) (cut : ι → Bool)
    (s : ι → R) (e : ι → ι → R) :
    cutCost xs cut s (offDiagonal e) = cutCost xs cut s e := by
  have hc : pairSum xs (fun i j => crossing (cut i) (cut j) * offDiagonal e i j) =
      pairSum xs (fun i j => crossing (cut i) (cut j) * e i j) := by
    apply pairCongr; intro i j
    by_cases h : i = j
    · subst j; cases cut i <;> simp [crossing,indicator,offDiagonal] <;> grind
    · simp [offDiagonal,h]
  unfold cutCost; rw [hc]

private theorem offGap [DecidableEq ι] (xs : List ι) (a : ι → R) (e : ι → ι → R) :
    pairSum xs (fun i j => (a i-a j)^2 * offDiagonal e i j) =
    pairSum xs (fun i j => (a i-a j)^2 * e i j) := by
  apply pairCongr; intro i j
  by_cases h : i = j
  · subst j; grind
  · simp [offDiagonal,h]

/-- Equation (1) in ordinary normalization. The only matrix hypotheses are
nonnegative diagonal slack, symmetric nonnegative squared entries e, and the
off-diagonal row estimate. The row cap is w(i)(1-w(i)) in the physical case.
Diagonal entries of e are allowed, since gaps and cut crossings both annul them. -/
theorem crossedCuts [DecidableEq ι] (xs : List ι) (tier : ι → Level)
    (a slack w : ι → R) (e : ι → ι → R) (lo uLo hi uHi half : R)
    (halfEq : 2*half = 1)
    (loNonneg : 0 ≤ lo) (hiNonneg : 0 ≤ hi) (apart : uLo ≤ hi)
    (inside : ∀ i, insideBounds (tier i) uLo uHi (a i))
    (slackNonneg : ∀ i, 0 ≤ slack i) (edgeNonneg : ∀ i j, 0 ≤ e i j)
    (sym : ∀ i j, e i j = e j i)
    (rowBound : ∀ i, sumOver xs (offDiagonal e i) ≤ w i*(1-w i)) :
    (pos (uLo-lo))^2 * cutCost xs (fun i => (tier i).low) slack e +
    (pos (uHi-hi))^2 * cutCost xs (fun i => (tier i).high) slack e -
    sumOver xs (fun i => outsideTax lo uLo hi uHi (a i) (tier i) * (w i*(1-w i))) ≤
      sumOver xs (fun i => (a i)^2 * slack i) +
      half * pairSum xs (fun i j => (a i - a j)^2 * e i j) := by
  have ep (i j) : 0 ≤ offDiagonal e i j := by
    by_cases h : i=j <;> simp [offDiagonal,h] <;> first | exact edgeNonneg i j | grind
  have es (i j) : offDiagonal e i j = offDiagonal e j i := by
    by_cases h : i=j
    · subst j; rfl
    · have hn : ¬ j=i := fun t => h t.symm
      simp [offDiagonal,h,hn,sym i j]
  have h := crossedCutsTwice xs tier a slack (fun i => w i*(1-w i)) (offDiagonal e)
    lo uLo hi uHi loNonneg hiNonneg apart inside slackNonneg ep es rowBound
  rw [offCutCost,offCutCost,offGap] at h
  have hg : 2 * (half * pairSum xs (fun i j => (a i-a j)^2 * e i j)) =
      pairSum xs (fun i j => (a i-a j)^2 * e i j) := by
    calc
      _ = (2*half) * pairSum xs (fun i j => (a i-a j)^2 * e i j) := by grind
      _ = _ := by rw [halfEq]; grind
  grind

/-- No variance penalty is incurred at coordinates that respect every outside threshold. -/
theorem outsideTaxOfSeparated (lo uLo hi uHi y : R) (i : Level)
    (lowOutside : i.low = false → y ≤ lo)
    (highOutside : i.high = false → y ≤ hi) :
    outsideTax lo uLo hi uHi y i = 0 := by
  have l := errorOfBelow lo uLo y
  have h := errorOfBelow hi uHi y
  cases i <;> simp [outsideTax,indicator,Level.low,Level.high] at * <;> grind


/-- Four strictly increasing labels in the physical seven-coordinate support. -/
structure Wedge7 where
  i : Fin 7
  j : Fin 7
  k : Fin 7
  m : Fin 7
  ij : i < j
  jk : j < k
  km : k < m
  deriving DecidableEq

def Wedge7.level (w : Wedge7) : Level :=
  if w.i = 0 ∧ w.j = 1 then .both
  else if w.i = 0 ∧ w.j ≤ 2 then .lower
  else .outside

/-- These are exactly 023m and 123m (m=4,5,6). -/
def Wedge7.highBad (w : Wedge7) : Prop := w.i ≤ 1 ∧ w.j = 2 ∧ w.k = 3

/-- These are exactly 123m (m=4,5,6). -/
def Wedge7.lowBad (w : Wedge7) : Prop := w.i = 1 ∧ w.j = 2 ∧ w.k = 3

instance (w : Wedge7) : Decidable w.highBad := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (w : Wedge7) : Decidable w.lowBad := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Use the individual Schmidt amplitudes, so square roots need no field extension. -/
def product4 (s : Fin 7 → R) (i j k m : Fin 7) : R := s i * s j * s k * s m

def amplitude (s : Fin 7 → R) (w : Wedge7) : R := product4 s w.i w.j w.k w.m

private theorem mulMonotone {a b c d : R} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hab : a ≤ b) (hcd : c ≤ d) : a*c ≤ b*d := by
  have h₁ := scaleLe hcd ha
  have h₂ := scaleLe hab hd
  grind

private theorem productNonneg (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i) (i j k m : Fin 7) :
    0 ≤ product4 s i j k m := OrderedRing.mul_nonneg
      (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (hs i) (hs j)) (hs k)) (hs m)

private theorem productOrder (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (i j k m I J K M : Fin 7)
    (hi : i ≤ I) (hj : j ≤ J) (hk : k ≤ K) (hm : m ≤ M) :
    product4 s I J K M ≤ product4 s i j k m := by
  exact mulMonotone (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (hs I) (hs J)) (hs K))
    (hs m) (mulMonotone (OrderedRing.mul_nonneg (hs I) (hs J)) (hs k)
      (mulMonotone (hs I) (hs j) (ord _ _ hi) (ord _ _ hj)) (ord _ _ hk)) (ord _ _ hm)

def sharedLower (s : Fin 7 → R) : R :=
  let a := product4 s 0 3 4 5
  let b := product4 s 1 2 4 5
  if a ≤ b then b else a

private theorem sharedLowerBounds (s : Fin 7 → R) :
    product4 s 0 3 4 5 ≤ sharedLower s ∧ product4 s 1 2 4 5 ≤ sharedLower s := by
  by_cases h : product4 s 0 3 4 5 ≤ product4 s 1 2 4 5 <;> simp [sharedLower,h] <;> grind

private theorem lowInsideLabels (w : Wedge7) (hin : w.level.low = true) :
    w.i = 0 ∧ w.j ≤ 2 := by
  have := w.ij
  unfold Wedge7.level at hin
  split at hin
  · omega
  · split at hin <;> simp_all [Level.low]

private theorem highInsideLabels (w : Wedge7) (hin : w.level.high = true) :
    w.i = 0 ∧ w.j = 1 := by
  unfold Wedge7.level at hin
  split at hin
  · assumption
  · split at hin <;> simp_all [Level.high]

private theorem lowAndHighInside (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (w : Wedge7) :
    insideBounds w.level (product4 s 0 2 5 6) (product4 s 0 1 5 6) (amplitude s w) := by
  have hkm := w.km
  constructor
  · intro h
    have h' := lowInsideLabels w h
    apply productOrder s hs ord <;> omega
  · intro h
    have h' := highInsideLabels w h
    apply productOrder s hs ord <;> omega

private theorem highRegular (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (w : Wedge7)
    (outside : w.level.high = false) (good : ¬ w.highBad) :
    amplitude s w ≤ product4 s 0 2 4 5 := by
  have ij := w.ij; have jk := w.jk; have km := w.km
  have nh : ¬(w.i = 0 ∧ w.j = 1) := by
    intro h
    simp [Wedge7.level,h,Level.high] at outside
  unfold Wedge7.highBad at good
  apply productOrder s hs ord <;> omega

private theorem lowRegular (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (w : Wedge7)
    (outside : w.level.low = false) (good : ¬ w.lowBad) :
    amplitude s w ≤ sharedLower s := by
  have ij := w.ij; have jk := w.jk; have km := w.km
  have nh : ¬(w.i = 0 ∧ w.j ≤ 2) := by
    intro h
    unfold Wedge7.level at outside
    split at outside
    · contradiction
    · simp [Level.low] at outside
  unfold Wedge7.lowBad at good
  have ⟨hl,hr⟩ := sharedLowerBounds s
  by_cases hi : w.i = 0
  · have h : amplitude s w ≤ product4 s 0 3 4 5 := by
      apply productOrder s hs ord <;> omega
    grind
  · have h : amplitude s w ≤ product4 s 1 2 4 5 := by
      apply productOrder s hs ord <;> omega
    grind

private theorem supportedError (b : Bool) (bad : Prop) [Decidable bad] (e : R)
    (hin : bad → b=false) (good : b=false → ¬bad → e=0) :
    e * indicator (!b) = (if bad then e else 0) := by
  cases b <;> by_cases hb : bad <;> simp_all [indicator] <;> grind

/-- The exact two error sets, after sorting the physical four-fold products. -/
theorem rankSevenOutsideTax (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (w : Wedge7) :
    outsideTax (sharedLower s) (product4 s 0 2 5 6)
      (product4 s 0 2 4 5) (product4 s 0 1 5 6) (amplitude s w) w.level =
    (if w.lowBad then error (sharedLower s) (product4 s 0 2 5 6) (amplitude s w) else 0) +
    (if w.highBad then error (product4 s 0 2 4 5) (product4 s 0 1 5 6) (amplitude s w) else 0) := by
  unfold outsideTax
  congr 1
  · apply supportedError
    · intro h
      have t := h.1
      have ne : ¬w.i=0 := by omega
      simp [Wedge7.level,ne,Level.low]
    · intro out good
      exact errorOfBelow _ _ _ (lowRegular s hs ord w out good)
  · apply supportedError
    · intro h
      have t := h.2.1
      have ne : ¬w.j=1 := by omega
      unfold Wedge7.level
      split
      · omega
      · split <;> rfl
    · intro out good
      exact errorOfBelow _ _ _ (highRegular s hs ord w out good)


/-- All physical four-label coordinates, with no repeated labels or tuples. -/
def wedges : List Wedge7 := Id.run do
  let labels := List.ofFn fun i : Fin 7 => i
  return labels.flatMap fun i => labels.flatMap fun j =>
    labels.flatMap fun k => labels.flatMap fun m =>
      if h : i < j ∧ j < k ∧ k < m then [⟨i,j,k,m,h.1,h.2.1,h.2.2⟩] else []

theorem wedgesCount : wedges.length = 35 := by decide
theorem wedgesNodup : wedges.Nodup := by decide

theorem memWedges (w : Wedge7) : w ∈ wedges := by
  rcases w with ⟨i,j,k,m,ij,jk,km⟩
  let labels := List.ofFn fun v : Fin 7 => v
  have hm (v : Fin 7) : v ∈ labels := by simp [labels]; omega
  apply List.mem_flatMap.mpr; refine ⟨i,hm _,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨j,hm _,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨k,hm _,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨m,hm _,?_⟩
  simp [ij,jk,km]

theorem highBadCount : (wedges.filter (fun w => decide w.highBad)).length = 6 := by decide
theorem lowBadCount : (wedges.filter (fun w => decide w.lowBad)).length = 3 := by decide

/-- Actual 35-coordinate rank-seven inequality. The nominal highest cut is 01,
and the shared cut is 0 with either 1 or 2. The endpoint estimates and their
six/three error supports follow from the ordering of the seven Schmidt amplitudes. -/
theorem rankSevenCrossedCuts (s : Fin 7 → R) (hs : ∀ i, 0 ≤ s i)
    (ord : ∀ i j, i ≤ j → s j ≤ s i) (slack w : Wedge7 → R)
    (e : Wedge7 → Wedge7 → R) (half : R) (halfEq : 2*half = 1)
    (slackNonneg : ∀ i, 0 ≤ slack i) (edgeNonneg : ∀ i j, 0 ≤ e i j)
    (sym : ∀ i j, e i j = e j i)
    (rowBound : ∀ i, sumOver wedges (offDiagonal e i) ≤ w i*(1-w i)) :
    let lₛ := sharedLower s
    let uₛ := product4 s 0 2 5 6
    let l₁ := product4 s 0 2 4 5
    let u₁ := product4 s 0 1 5 6
    let a := amplitude s
    (pos (uₛ-lₛ))^2 * cutCost wedges (fun i => i.level.low) slack e +
    (pos (u₁-l₁))^2 * cutCost wedges (fun i => i.level.high) slack e -
      sumOver wedges (fun i =>
        ((if i.lowBad then error lₛ uₛ (a i) else 0) +
         (if i.highBad then error l₁ u₁ (a i) else 0)) * (w i*(1-w i))) ≤
      sumOver wedges (fun i => (a i)^2 * slack i) +
        half * pairSum wedges (fun i j => (a i-a j)^2 * e i j) := by
  have sl : 0 ≤ sharedLower s := by
    have := (sharedLowerBounds s).1
    have := productNonneg s hs 0 3 4 5
    grind
  have apart : product4 s 0 2 5 6 ≤ product4 s 0 2 4 5 := by
    apply productOrder s hs ord <;> decide
  have h := crossedCuts wedges Wedge7.level (amplitude s) slack w e
    (sharedLower s) (product4 s 0 2 5 6) (product4 s 0 2 4 5) (product4 s 0 1 5 6)
    half halfEq sl (productNonneg s hs 0 2 4 5) apart (lowAndHighInside s hs ord)
    slackNonneg edgeNonneg sym rowBound
  simpa only [rankSevenOutsideTax s hs ord] using h

end RankSeven.ExteriorCuts
