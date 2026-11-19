import Std
import Rank7PauliTensor

/-! The one-hole tensor in the eight-point affine space. A point is a
three-bit word. Its seven two-dimensional directions are the kernels
of the seven nonzero binary linear functionals. A wedge row uses an
eight-bit occupancy mask, with creation order the increasing point order.
-/
namespace RankSeven.ExteriorOccupation

abbrev Point := Fin 8
abbrev Direction := Fin 7
abbrev Column := Point × Direction

def points : List Point := List.finRange 8
def directions : List Direction := List.finRange 7
def columns : List Column := points.flatMap (fun z => directions.map (fun n => (z,n)))

/-- Parity of the three bits of the intersection of point and normal. -/
def side (n : Direction) (z : Point) : Bool :=
  let word := z.val &&& (n.val + 1)
  (word == 1) || (word == 2) || (word == 4) || (word == 7)

def inPlane (c : Column) (z : Point) : Bool := side c.2 z == side c.2 c.1

def planePoints (c : Column) : List Point := points.filter (inPlane c)

def rowMask (c : Column) : Nat :=
  ((planePoints c).filter (fun x => x != c.1)).foldl (fun b x => b.lor (2^x.val)) 0

/-- The contraction crosses precisely the occupied labels below the hole. -/
def negative (c : Column) : Bool :=
  ((planePoints c).filter (fun x => x < c.1)).length % 2 == 1

def active (m : Nat) : List Point := points.filter (fun x => m.testBit x.val)

def three (m : Nat) : Bool := m < 256 && (active m).length == 3

def findColumn (m : Nat) : Option Column := columns.find? (fun c => rowMask c == m)

/-- Occupancy mask of either affine plane with the given normal. -/
def cosetMask (n : Direction) (b : Bool) : Nat :=
  (points.filter (fun z => side n z == b)).foldl (fun m x => m.lor (2^x.val)) 0

/-- Coefficient of the exterior monomial indexed by m in the unnormalized
all-plus sum of the two parallel planes. -/
def planeWave (n : Direction) (m : Nat) : Int :=
  if m == cosetMask n false || m == cosetMask n true then 1 else 0

/-- Entry of ordinary coordinate annihilation: restore the removed mode,
look up the input four-wedge coefficient, and apply the sorting sign. -/
def annihilationEntry (z : Point) (n : Direction) (m : Nat) : Int :=
  if m.testBit z.val then 0
  else
    let amplitude := planeWave n (m.lor (2^z.val))
    let below := (active m).filter (fun t => t < z)
    if below.length % 2 == 1 then -amplitude else amplitude

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem coordinate_annihilation_entry :
    ∀ z : Point, ∀ n : Direction, ∀ m : Fin 256,
      annihilationEntry z n m.val =
        if rowMask (z,n) = m.val then (if negative (z,n) then -1 else 1) else 0 := by
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem affine_plane_entries :
    ∀ z : Point, ∀ n : Direction,
      (planePoints (z,n)).length = 4 ∧
      three (rowMask (z,n)) = true ∧
      ((active (rowMask (z,n))).foldl (fun x t => x ^^^ t.val) 0) = z.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem findColumn_rowMask :
    ∀ z : Point, ∀ n : Direction, findColumn (rowMask (z,n)) = some (z,n) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem findColumn_covers_triples :
    ∀ m : Fin 256, (findColumn m.val).isSome = three m.val := by
  decide

theorem findColumn_spec {m : Nat} {c : Column} (h : findColumn m = some c) :
    rowMask c = m := by
  have := List.find?_some h
  simpa using this

/-- The unscaled contraction and its transpose, extended by zero off triples. -/
def signed {C : Type} [Neg C] (c : Column) (x : C) : C :=
  if negative c then -x else x

def contraction {C : Type} [Zero C] [Neg C] (f : Column → C) (m : Nat) : C :=
  match findColumn m with
  | none => 0
  | some c => signed c (f c)

def contractionTranspose {C : Type} [Neg C] (g : Nat → C) (c : Column) : C :=
  signed c (g (rowMask c))

open Lean.Grind

theorem signed_signed {C : Type} [CommRing C] (c : Column) (x : C) :
    signed c (signed c x) = x := by
  unfold signed
  split <;> grind

theorem transpose_contraction {C : Type} [CommRing C] (f : Column → C) (c : Column) :
    contractionTranspose (contraction f) c = f c := by
  rcases c with ⟨z,n⟩
  simp only [contractionTranspose, contraction, findColumn_rowMask z n, signed_signed]

theorem contraction_transpose_on_triples {C : Type} [CommRing C]
    (g : Nat → C) (m : Fin 256) (hm : three m.val = true) :
    contraction (contractionTranspose g) m.val = g m.val := by
  have someRow := findColumn_covers_triples m
  rw [hm] at someRow
  cases he : findColumn m.val with
  | none => simp [he] at someRow
  | some c =>
    simp [contraction, he, contractionTranspose, signed_signed, findColumn_spec he]

open RankSeven.Pauli

/-- The actual exterior basis consists of distinct increasing triples. -/
def tripleMasks : List Nat := (List.range 256).filter three

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rowMasks_perm_triples : (columns.map rowMask).Perm tripleMasks := by
  decide

private theorem pairedSum_perm {C α : Type} [CommRing C] {xs ys : List α}
    (p : xs.Perm ys) (f : α → C) : sumOver xs f = sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver, List.map_cons, List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver, List.map_cons, List.sum_cons]; grind
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem contraction_on_column {C : Type} [CommRing C] (f : Column → C) (c : Column) :
    contraction f (rowMask c) = signed c (f c) := by
  rcases c with ⟨z,n⟩
  simp [contraction, findColumn_rowMask]

theorem signed_product {C : Type} [CommRing C] (c : Column) (x y : C) :
    signed c x * signed c y = x*y := by
  unfold signed
  split <;> grind

/-- A bilinear identity in the actual exterior basis. For a complex
Hermitian pairing the left input supplies the conjugated coefficients.
The signed tensor is real, so conjugation preserves its entries. -/
theorem contraction_pairing {C : Type} [CommRing C] (f g : Column → C) :
    sumOver tripleMasks (fun m => contraction f m * contraction g m) =
      sumOver columns (fun c => f c * g c) := by
  rw [← pairedSum_perm rowMasks_perm_triples]
  unfold sumOver
  simp only [List.map_map, Function.comp_def, contraction_on_column, signed_product]

/-- Explicit local uniform occupation for arbitrary hole superpositions and
arbitrary direction superpositions, including their coherent cross terms.
The common coefficient of the two cosets in a normalized direction vector
is 1/√2, so the product of the two scaling factors specializes to 1/2. -/
theorem uniform_occupation_pairing {C : Type} [CommRing C]
    (leftScale rightScale : C) (u v : Point → C) (a b : Direction → C) :
    sumOver tripleMasks (fun m =>
      (leftScale * contraction (fun c => u c.1 * a c.2) m) *
      (rightScale * contraction (fun c => v c.1 * b c.2) m)) =
    (leftScale * rightScale) *
      (sumOver points (fun z => u z * v z) * sumOver directions (fun n => a n * b n)) := by
  calc
    _ = sumOver tripleMasks (fun m => (leftScale*rightScale) *
      (contraction (fun c => u c.1 * a c.2) m *
       contraction (fun c => v c.1 * b c.2) m)) := by
      apply sumOverCongr
      intro m
      grind
    _ = (leftScale*rightScale) * sumOver columns (fun c =>
      (u c.1 * a c.2) * (v c.1 * b c.2)) := by
      rw [← sumOverMulLeft, contraction_pairing]
    _ = (leftScale*rightScale) * sumOver (productIndices points directions)
      (fun c => (u c.1 * v c.1) * (a c.2 * b c.2)) := by
      congr 1
      apply sumOverCongr
      intro c
      grind
    _ = _ := by
      rw [factorProductSum points directions (fun z => u z * v z) (fun n => a n * b n)]

/-- At normalization q=1/2, twice the coherent exterior pairing equals the
input pairing. The only scalar hypothesis is the normalization of two equal
coset amplitudes (or a mutually dual choice of amplitudes). -/
theorem twice_normalized_occupation {C : Type} [CommRing C]
    (leftScale rightScale : C) (h : 2 * (leftScale * rightScale) = 1)
    (u v : Point → C) (a b : Direction → C) :
    2 * sumOver tripleMasks (fun m =>
      (leftScale * contraction (fun c => u c.1 * a c.2) m) *
      (rightScale * contraction (fun c => v c.1 * b c.2) m)) =
      sumOver points (fun z => u z * v z) * sumOver directions (fun n => a n * b n) := by
  rw [uniform_occupation_pairing, ← Semiring.mul_assoc, h, Semiring.one_mul]


end RankSeven.ExteriorOccupation
