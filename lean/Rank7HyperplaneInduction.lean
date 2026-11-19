import Rank7HyperplaneResolution
import Rank7ComplexScalar
import Rank7PlaneProjector
import Rank7ExteriorCuts
import Rank7Compression

/-! Transfer of the real quadratic form of the rank-seven exterior defect through
binary hyperplane charts. Levels k=0,1,... denote ambient dimensions 2^(k+3). -/

namespace RankSeven.HyperplaneInduction

open Lean.Grind RankSeven.Pauli RankSeven.HyperplaneIncidence RankSeven.HyperplaneResolution
open ExteriorPauliBase (sumOnIndex)

def cubeDecEq : (n : Nat) → DecidableEq (Basis n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 =>
    letI : DecidableEq (Basis n) := cubeDecEq n
    inferInstanceAs (DecidableEq (Bool × Basis n))
local instance {n : Nat} : DecidableEq (Basis n) := cubeDecEq n

/-- All proper affine hyperplanes, with both offsets for every nonzero normal. -/
def hyperplanes (n : Nat) : List (HyperplaneCode n) :=
  let normals := (qubitIndices n).filter fun v => !isZero n v
  normals.map (fun v => (v,false)) ++ normals.map (fun v => (v,true))

theorem hyperplanesComplete {n : Nat} (H : HyperplaneCode n) (proper : H.1 ≠ zero n) :
    H ∈ hyperplanes n := by
  rcases H with ⟨v,b⟩
  have nz : isZero n v = false := by
    cases hz : isZero n v
    · rfl
    · exact False.elim (proper ((isZero_iff _ _).mp hz))
  have mem : v ∈ (qubitIndices n).filter (fun v => !isZero n v) :=
    List.mem_filter.mpr ⟨qubitIndicesComplete _,by simp [nz]⟩
  unfold hyperplanes
  cases b
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨v,mem,rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨v,mem,rfl⟩)

theorem hyperplanesNodup (n : Nat) : (hyperplanes n).Nodup := by
  unfold hyperplanes
  apply List.nodup_append.mpr
  have h := List.Pairwise.filter (fun v => !isZero n v) (normalsNodup n)
  refine ⟨List.Pairwise.map _ (fun _ _ ne e => ne (congrArg Prod.fst e)) h,
    List.Pairwise.map _ (fun _ _ ne e => ne (congrArg Prod.fst e)) h,?_⟩
  intro x hx y hy eq
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
  exact Bool.noConfusion (congrArg Prod.snd eq)

/-- Coordinates of the defect fall into three classes. Plane diagonals and
entries between different direction blocks are zero. The other classes carry
the actual supporting coordinates so that their counts are proved, not fields. -/
inductive EntryCase (n : Nat) where
  | silent
  | nonplane (p x y z : Basis n) (px : p≠x) (py : p≠y) (pz : p≠z)
      (xy : x≠y) (xz : x≠z) (yz : y≠z)
      (notPlane : isZero n (xorBasis n (xorBasis n p x)
        (xorBasis n (xorBasis n p y) (xorBasis n p z))) = false)
  | parallel (p a b d : Basis n) (ha : a≠zero n) (hb : b≠zero n) (hab : a≠b)
      (hd : d≠zero n) (hda : d≠a) (hdb : d≠b) (hdab : d≠xorBasis n a b)

def support {n : Nat} : EntryCase n → List (HyperplaneCode n)
  | .silent => []
  | .nonplane p x y z .. => fourPointHyperplanes p x y z
  | .parallel p a b d .. => jointSupport p a b d

private theorem properSupport {n : Nat} (c : EntryCase n) (H : HyperplaneCode n)
    (h : H ∈ support c) : H ∈ hyperplanes n := by
  apply hyperplanesComplete
  cases c with
  | silent => cases h
  | nonplane p x y z _ _ _ _ _ _ _ => exact ((memFourPointHyperplanes p x y z H).mp h).1
  | parallel p a b d _ _ _ _ _ _ _ => exact ((memJointSupport p a b d H).mp h).1

variable {R α β : Type} [CommRing R]
attribute [local instance] Semiring.natCast

def entry {n : Nat} (q : R) : EntryCase n → R
  | .silent => 0
  | .nonplane .. => q
  | .parallel .. => -q

/-- Deposit a finite entry list into an enclosing index set and aggregate
equal entries. This handles coordinate embeddings and hyperplane supports. -/
def deposit {α β : Type} [DecidableEq α] (ys : List β) (map : β → α) (v : β → R) (x : α) : R :=
  sumOver ys fun y => if map y=x then v y else 0

private theorem sumCongrMember (xs : List α) {f g : α → R} (h : ∀ x ∈ xs, f x = g x) :
    sumOver xs f = sumOver xs g := congrArg List.sum (List.map_congr_left h)

private theorem depositPairing [DecidableEq α] (xs : List α) (ys : List β) (map : β → α)
    (v : β → R) (f : α → R) (nd : xs.Nodup) (contained : ∀ y ∈ ys, map y ∈ xs) :
    sumOver xs (fun x => f x * deposit ys map v x) =
      sumOver ys (fun y => f (map y)*v y) := by
  unfold deposit
  simp only [sumOverMulLeft]
  rw [sumOverSwap xs ys]
  apply sumCongrMember
  intro y hy
  calc
    _ = sumOver xs (fun x => if map y=x then f x * v y else 0) := by
      apply sumOverCongr; intro x
      by_cases h : map y=x <;> simp [h] <;> grind
    _ = _ := sumOnIndex xs (map y) (fun x => f x*v y) nd (contained y hy)

/-- Actual child defect entry on a hyperplane, for each classified ambient pair. -/
def localEntry {n : Nat} (q : R) (c : EntryCase n) (H : HyperplaneCode n) : R :=
  deposit (support c) id (fun _ => entry (2*q) c) H

theorem entryResolution (k : Nat) (q : R) (c : EntryCase (k+4)) :
    sumOver (hyperplanes (k+4)) (localEntry q c) =
      (((2^(k+2):Nat):R)-2) * entry q c := by
  have h := depositPairing (hyperplanes (k+4)) (support c) id (fun _ => entry (2*q) c)
    (fun _ => (1:R)) (hyperplanesNodup _) (properSupport c)
  simp only [Semiring.one_mul] at h
  change sumOver _ (deposit _ _ _) = _
  rw [h]
  cases c with
  | silent => change (0:R)=_ * 0; grind
  | nonplane p x y z px py pz xy xz yz ng =>
    have g := nonplaneDefectDiagonal (k:=k+1) p x y z px py pz xy xz yz ng q
    have zeroSub (v : R) : v-0=v := by grind
    simpa only [entry,support,zeroSub] using g
  | parallel p a b d ha hb hab hd hda hdb hdab =>
    have g := parallelDefectOffDiagonal (k:=k+1) p a b d ha hb hab hd hda hdb hdab q
    have subZero (v : R) : 0-v= -v := by grind
    simpa only [entry,support,subZero] using g

/-- Pair evaluation of a real kernel on complex exterior coordinates. All
physical four-wedge projectors in the computational basis have real entries. -/
def realWeight (z : α → ComplexScalar R) (ij : α × α) : R :=
  (z ij.1).re * (z ij.2).re + (z ij.1).im * (z ij.2).im

def quadratic (xs : List α) (K : α × α → R) (z : α → ComplexScalar R) : R :=
  sumOver (productIndices xs xs) fun ij => realWeight z ij * K ij

def pairMap (e : β → α) (xy : β × β) : α × α := (e xy.1,e xy.2)

def embeddedKernel [DecidableEq α] (ys : List β) (e : β → α) (K : β × β → R) : α × α → R :=
  deposit (productIndices ys ys) (pairMap e) K

theorem pairMember {xs : List α} {x y : α} (hx : x∈xs) (hy : y∈xs) :
    (x,y) ∈ productIndices xs xs := List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩

theorem pairsNodup (xs : List α) (ys : List β) (hx : xs.Nodup) (hy : ys.Nodup) :
    (productIndices xs ys).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a xs ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp hx
    apply List.nodup_append.mpr
    refine ⟨List.Pairwise.map _ (fun _ _ ne e => ne (congrArg Prod.snd e)) hy,ih nd,?_⟩
    intro u hu v hv eq
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hu
    obtain ⟨c,hc,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hv
    have ac := congrArg Prod.fst eq
    change a=c at ac
    exact fresh (ac ▸ hc)

/-- Quadratic congruence for a coordinate chart. It is proved by swapping the
two finite sums, without assuming an operator-level restriction identity. -/
theorem coordinateCongruence [DecidableEq α] (xs : List α) (ys : List β) (e : β → α)
    (K : β × β → R) (z : α → ComplexScalar R) (nd : xs.Nodup)
    (contained : ∀ y ∈ ys, e y ∈ xs) :
    quadratic xs (embeddedKernel ys e K) z = quadratic ys K (fun y => z (e y)) := by
  apply depositPairing (productIndices xs xs) (productIndices ys ys) (pairMap e) K
    (realWeight z) (pairsNodup _ _ nd nd)
  intro xy hxy
  obtain ⟨u,hu,h⟩ := List.mem_flatMap.mp hxy
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact pairMember (contained u hu) (contained v hv)

/-- Entrywise (224) now acts on every complex vector, before any chart or
rank restriction. The coefficient multiplying the parent is m-2. -/
theorem quadraticResolution (k : Nat) (q : R) (xs : List α)
    (caseOf : α × α → EntryCase (k+4)) (z : α → ComplexScalar R) :
    sumOver (hyperplanes (k+4)) (fun H => quadratic xs (fun ij => localEntry q (caseOf ij) H) z) =
      (((2^(k+2):Nat):R)-2) * quadratic xs (fun ij => entry q (caseOf ij)) z := by
  unfold quadratic
  rw [sumOverSwap, sumOverMulLeft]
  apply sumOverCongr; intro ij
  rw [←sumOverMulLeft, entryResolution]
  grind

/-- Fourth exterior power on seven input coordinates, expanded as signed
4-by-4 minors. The source vector has the 35 exterior coefficients. -/
def sourceSite (w : ExteriorCuts.Wedge7) (j : Fin 4) : Fin 7 :=
  match j.val with | 0 => w.i | 1 => w.j | 2 => w.k | _ => w.m

def minor4 {C S : Type} [CommRing C] (A : S → Fin 7 → C) (row : Fin 4 → S)
    (w : ExteriorCuts.Wedge7) : C := sumOver ExteriorPauliBase.permutations fun perm =>
  let v := A (row 0) (sourceSite w perm.1.1) * A (row 1) (sourceSite w perm.1.2) *
           A (row 2) (sourceSite w perm.2.1) * A (row 3) (sourceSite w perm.2.2)
  if ExteriorPauliBase.oddPermutation perm then -v else v

def exteriorLift {C S : Type} [CommRing C] (rows : α → Fin 4 → S)
    (A : S → Fin 7 → C) (v : ExteriorCuts.Wedge7 → C) (i : α) : C :=
  sumOver ExteriorCuts.wedges fun w => minor4 A (rows i) w * v w

/-- An order-compatible embedding of four-index coordinates transports the
actual exterior power of the restricted map; no determinant identity is assumed. -/
theorem exteriorLiftRestriction {C S T : Type} [CommRing C] (rows : α → Fin 4 → S)
    (childRows : β → Fin 4 → T) (sites : T → S) (embed : β → α)
    (coordinate : ∀ i j, rows (embed i) j = sites (childRows i j))
    (A : S → Fin 7 → C) (v : ExteriorCuts.Wedge7 → C) (i : β) :
    exteriorLift rows A v (embed i) =
      exteriorLift childRows (fun t => A (sites t)) v i := by
  unfold exteriorLift
  apply sumOverCongr; intro w
  unfold minor4
  simp only [coordinate]

/-- The chart-compatibility data needed to run the rank-seven induction.
Each equation for a kernel is a single classified coordinate, not a sum rule,
PSD certificate or hypothetical induction step. The order condition selects
charts that preserve the order of the four rows defining the minors. -/
structure Charts (W : Nat → Type) [∀ k, DecidableEq (W k)] (R : Type) [CommRing R] where
  coords : (k : Nat) → List (W k)
  nodup : ∀ k, (coords k).Nodup
  rows : (k : Nat) → W k → Fin 4 → Basis (k+3)
  K : (k : Nat) → W k × W k → R
  q : Nat → R
  site : (k : Nat) → HyperplaneCode (k+4) → Basis (k+3) → Basis (k+4)
  embed : (k : Nat) → HyperplaneCode (k+4) → W k → W (k+1)
  present : ∀ k H i, i ∈ coords k → embed k H i ∈ coords (k+1)
  coordinate : ∀ k H i j, rows (k+1) (embed k H i) j = site k H (rows k i j)
  caseOf : (k : Nat) → W (k+1) × W (k+1) → EntryCase (k+4)
  parentEntry : ∀ k ij, K (k+1) ij = entry (q (k+1)) (caseOf k ij)
  childEntry : ∀ k H, H ∈ hyperplanes (k+4) → ∀ ij,
    ij ∈ productIndices (coords (k+1)) (coords (k+1)) →
    embeddedKernel (coords k) (embed k H) (K k) ij = localEntry (q (k+1)) (caseOf k ij) H

/-- Congruence plus the counted entrywise resolution gives the restricted-map
form of (224), with the same input vector v on every child. -/
theorem restrictedResolution {W : Nat → Type} [∀ k, DecidableEq (W k)]
    (charts : Charts W R) (k : Nat) (A : Basis (k+4) → Fin 7 → ComplexScalar R)
    (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    sumOver (hyperplanes (k+4)) (fun H => quadratic (charts.coords k) (charts.K k)
      (exteriorLift (charts.rows k) (fun t => A (charts.site k H t)) v)) =
    (((2^(k+2):Nat):R)-2) * quadratic (charts.coords (k+1)) (charts.K (k+1))
      (exteriorLift (charts.rows (k+1)) A v) := by
  let z := exteriorLift (charts.rows (k+1)) A v
  have sub (H) (present : H ∈ hyperplanes (k+4)) :
      quadratic (charts.coords k) (charts.K k)
        (exteriorLift (charts.rows k) (fun t => A (charts.site k H t)) v) =
      quadratic (charts.coords (k+1))
        (fun ij => localEntry (charts.q (k+1)) (charts.caseOf k ij) H) z := by
    have hl := exteriorLiftRestriction (charts.rows (k+1)) (charts.rows k)
      (charts.site k H) (charts.embed k H) (charts.coordinate k H) A v
    have hv : exteriorLift (charts.rows k) (fun t => A (charts.site k H t)) v =
        (fun x => z (charts.embed k H x)) := funext (fun x => (hl x).symm)
    rw [hv, ←coordinateCongruence (charts.coords (k+1)) (charts.coords k)
      (charts.embed k H) (charts.K k) z (charts.nodup _) (charts.present k H)]
    unfold quadratic
    apply sumCongrMember; intro ij hij
    rw [charts.childEntry k H present ij hij]
  rw [sumCongrMember _ sub,quadraticResolution]
  have eqK : charts.K (k+1) = (fun ij => entry (charts.q (k+1)) (charts.caseOf k ij)) :=
    funext (charts.parentEntry k)
  rw [eqK]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem castNonnegative (k : Nat) : 0 ≤ (k:R) := by
  induction k with
  | zero =>
    have h : ((0:Nat):R)=0 := by grind
    rw [h]; grind
  | succ k ih => rw [Semiring.natCast_succ]; grind

private theorem scalePositive (k : Nat) : (0:R) < ((2^(k+2):Nat):R)-2 := by
  have p : 4 ≤ 2^(k+2) := Nat.pow_le_pow_right (n:=2) (by decide) (show 2 ≤ k+2 by omega)
  have h : 2^(k+2) = (2^(k+2)-4)+4 := by omega
  have ht := congrArg (fun a : Nat => (a:R)) h
  rw [Semiring.natCast_add] at ht
  have h4 : ((4:Nat):R)=4 := by grind
  rw [h4] at ht
  have := castNonnegative (R:=R) (2^(k+2)-4)
  grind

/-- Induction from the eight-point inequality. No positivity at any larger
level is a hypothesis. The chart data concern only finite geometry and entries. -/
theorem allDimensions {W : Nat → Type} [∀ k, DecidableEq (W k)]
    (charts : Charts W R)
    (base : ∀ (A : Basis 3 → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R),
      0 ≤ quadratic (charts.coords 0) (charts.K 0) (exteriorLift (charts.rows 0) A v))
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (v : ExteriorCuts.Wedge7 → ComplexScalar R) :
    0 ≤ quadratic (charts.coords k) (charts.K k) (exteriorLift (charts.rows k) A v) := by
  induction k with
  | zero => exact base A v
  | succ k ih =>
    have s := Compression.sumOverNonnegative (hyperplanes (k+4))
      (fun H => quadratic (charts.coords k) (charts.K k)
        (exteriorLift (charts.rows k) (fun t => A (charts.site k H t)) v)) (fun H _ => ih _)
    rw [restrictedResolution] at s
    let val := quadratic (charts.coords (k+1)) (charts.K (k+1)) (exteriorLift (charts.rows (k+1)) A v)
    change 0 ≤ val
    change 0 ≤ (((2^(k+2):Nat):R)-2)*val at s
    have h := scalePositive (R:=R) k
    by_cases neg : val < 0
    · have hv : 0 < -val := by grind
      have := OrderedRing.mul_pos h hv
      grind
    · grind
end Order

end RankSeven.HyperplaneInduction
