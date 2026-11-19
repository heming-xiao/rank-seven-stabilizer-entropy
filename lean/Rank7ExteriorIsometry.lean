import Rank7HyperplaneInduction
import Rank7GenericExteriorKernel
import Rank7PhysicalWedges

/-! Finite fourth exterior Gram matrices, in the signed-minor convention used
by the dimension induction. All sums are over explicit lists. -/
namespace RankSeven.ExteriorIsometry

open Lean.Grind Pauli HyperplaneInduction ExteriorPauliBase ExteriorCuts
open GenericExteriorKernel (position)

variable {C R S : Type} [CommRing C] [CommRing R]

def columns (w : Wedge7) (p : Permutation) : Four (Fin 7) :=
  ((sourceSite w p.1.1,sourceSite w p.1.2),(sourceSite w p.2.1,sourceSite w p.2.2))

private def sg (C : Type) [CommRing C] (p : Permutation) : C :=
  if oddPermutation p then -1 else 1

theorem minorTensor (A : S → Fin 7 → C) (r : Four S) (w : Wedge7) :
    minor4 A (position r) w =
      sumOver permutations (fun p => sg C p * tensorFour A r (columns w p)) := by
  unfold minor4
  apply sumOverCongr
  intro p
  simp only [position, Fin.val_zero, columns, tensorFour,tensor,sg]
  change (if oddPermutation p then -(_ * _ * _ * _) else _ * _ * _ * _) = _
  cases oddPermutation p <;> simp <;> grind

/-- Paired column Gram on the underlying space; the two factors can be independent. -/
def columnGram (xs : List S) (A B : S → Fin 7 → C) (i j : Fin 7) : C :=
  sumOver xs fun x => A x i * B x j

private theorem factorFour (xs : List S) (A B : S → Fin 7 → C) (i j : Four (Fin 7)) :
    sumOver (fourIndices xs) (fun r => tensorFour A r i * tensorFour B r j) =
      tensorFour (columnGram xs A B) i j := by
  let pair (u v : Fin 7 × Fin 7) (r : S × S) :=
    (A r.1 u.1 * B r.1 v.1) * (A r.2 u.2 * B r.2 v.2)
  have f (u v) : sumOver (productIndices xs xs) (pair u v) =
      columnGram xs A B u.1 v.1 * columnGram xs A B u.2 v.2 :=
    factorProductSum xs xs (fun x => A x u.1 * B x v.1) (fun x => A x u.2 * B x v.2)
  calc
    _ = sumOver (fourIndices xs) (fun r => pair i.1 j.1 r.1 * pair i.2 j.2 r.2) := by
      apply sumOverCongr; intro r; dsimp [pair,tensorFour,tensor]; grind
    _ = _ := by
      unfold fourIndices
      rw [factorProductSum,f,f]; rfl

private theorem sumProduct {α β : Type} (xs : List α) (ys : List β) (f : α → C) (g : β → C) :
    sumOver xs f * sumOver ys g = sumOver xs (fun x => sumOver ys (fun y => f x * g y)) := by
  rw [sumOverMulRight]; exact sumOverCongr xs (fun x => sumOverMulLeft ys g (f x))

/-- The full ordered four-tensor Gram of the actual minors depends only on
the seven-by-seven one-particle Gram. No orthonormality is needed. -/
theorem orderedMinorGram (xs : List S) (A B : S → Fin 7 → C) (w v : Wedge7) :
    sumOver (fourIndices xs) (fun r => minor4 A (position r) w * minor4 B (position r) v) =
    sumOver permutations (fun p => sumOver permutations (fun q =>
      (sg C p * sg C q) * tensorFour (columnGram xs A B) (columns w p) (columns v q))) := by
  simp only [minorTensor,sumProduct]
  rw [sumOverSwap]
  apply sumOverCongr; intro p
  rw [sumOverSwap]
  apply sumOverCongr; intro q
  rw [← factorFour, sumOverMulLeft]
  apply sumOverCongr; intro r; grind

private def mask (r : Four (Fin 7)) : Nat :=
  2^r.1.1.val+2^r.1.2.val+2^r.2.1.val+2^r.2.2.val

private def maskW (w : Wedge7) : Nat :=
  2^w.i.val+2^w.j.val+2^w.k.val+2^w.m.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem columnMaskTable :
    wedges.all (fun w => permutations.all (fun p => mask (columns w p) == maskW w)) = true ∧
    (wedges.map maskW).Nodup := by decide

private theorem map_inj_on {α β : Type} (xs : List α) (f : α → β) (nodup : (xs.map f).Nodup)
    {a b : α} (ha : a∈xs) (hb : b∈xs) (eq : f a = f b) : a=b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx,hn⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · exact False.elim (hx (eq ▸ List.mem_map.mpr ⟨b,hb,rfl⟩))
    · exact False.elim (hx (List.mem_map.mpr ⟨a,List.mem_cons.mp ha |>.resolve_left (by
        intro h; subst a; exact hx (List.mem_map.mpr ⟨_,by assumption,rfl⟩)),eq⟩))
    · exact ih hn ha hb

private theorem sourceInj (w : Wedge7) (i j : Fin 4) (h : sourceSite w i = sourceSite w j) : i=j := by
  have indices : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  have h1 := w.ij; have h2 := w.jk; have h3 := w.km
  rcases indices i with rfl|rfl|rfl|rfl <;> rcases indices j with rfl|rfl|rfl|rfl <;>
    first | rfl | change (_ : Fin 7) = (_ : Fin 7) at h; simp [sourceSite] at h; omega

private theorem columnsInj (w v : Wedge7) (p q : Permutation)
    (hp : p∈permutations) (hq : q∈permutations) (h : columns w p = columns v q) :
    w=v ∧ p=q := by
  have hm (a : Wedge7) (s : Permutation) (hs : s∈permutations) :
      mask (columns a s) = maskW a :=
    beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp columnMaskTable.1 a (memWedges a)) s hs)
  have eq : maskW w = maskW v := (hm w p hp).symm.trans ((congrArg mask h).trans (hm v q hq))
  obtain rfl := map_inj_on _ _ columnMaskTable.2 (memWedges w) (memWedges v) eq
  exact ⟨rfl,Prod.ext (Prod.ext (sourceInj w _ _ (congrArg (fun u => u.1.1) h))
    (sourceInj w _ _ (congrArg (fun u => u.1.2) h))) (Prod.ext
    (sourceInj w _ _ (congrArg (fun u => u.2.1) h)) (sourceInj w _ _ (congrArg (fun u => u.2.2) h)))⟩

private def delta {α : Type} [DecidableEq α] (i j : α) : C := if i=j then 1 else 0

private theorem deltaFour (u v : Four (Fin 7)) :
    tensorFour (delta (C:=C)) u v = delta u v := by
  rcases u with ⟨⟨a,b⟩,c,d⟩; rcases v with ⟨⟨e,f⟩,g,h⟩
  simp [tensorFour,tensor,delta,Prod.mk.injEq]
  split <;> split <;> split <;> split <;> simp_all <;> grind

private theorem sumCongrMem {α : Type} (xs : List α) {f g : α → C}
    (h : ∀ x ∈ xs, f x = g x) : sumOver xs f = sumOver xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem sumConst24 (c : C) : sumOver permutations (fun _ => c) = 24*c := by
  letI : NatCast C := Semiring.natCast
  have gen {α : Type} (xs : List α) : sumOver xs (fun _ => c) = (xs.length:C)*c := by
    induction xs with
    | nil => simp [sumOver]; grind
    | cons a xs ih =>
      change c + sumOver xs (fun _ => c) = _
      rw [ih,List.length_cons,Semiring.natCast_succ]; grind
  have h := gen permutations
  rw [complete_basis_counts.2.2.1] at h
  exact h.trans (by grind)

/-- Four ordered tensor slots give the factor 4!, and the 35 minor columns
have pairwise zero cross terms for any pair of biorthonormal seven-column maps. -/
theorem orderedOrthonormal (xs : List S) (A B : S → Fin 7 → C)
    (orth : ∀ i j, columnGram xs A B i j = if i=j then 1 else 0) (w v : Wedge7) :
    sumOver (fourIndices xs) (fun r => minor4 A (position r) w * minor4 B (position r) v) =
      24*(if w=v then 1 else 0) := by
  rw [orderedMinorGram]
  have gram : columnGram xs A B = delta := funext (fun i => funext (orth i))
  simp only [gram,deltaFour]
  calc
    _ = sumOver permutations (fun _ => if w=v then (1:C) else 0) := by
      apply sumCongrMem; intro p hp
      calc
        _ = sumOver permutations (fun q => if p=q then (if w=v then (1:C) else 0) else 0) := by
          apply sumCongrMem; intro q hq
          by_cases e : columns w p = columns v q
          · obtain ⟨rfl,rfl⟩ := columnsInj _ _ _ _ hp hq e
            simp [delta,sg]; cases oddPermutation p <;> simp <;> grind
          · by_cases h : p=q
            · subst q; have ne : w≠v := by intro hw; subst v; exact e rfl
              simp [delta,e,ne] <;> grind
            · simp [delta,e,h] <;> grind
        _ = _ := sumOnIndex permutations p (fun _ => if w=v then (1:C) else 0)
          complete_basis_counts.2.2.2 hp
    _ = _ := sumConst24 _

section Complex
open ComplexScalar

private theorem starSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    star (sumOver xs f) = sumOver xs (fun x => star (f x)) := by
  induction xs with
  | nil => exact star_ofReal (0:R)
  | cons a xs ih =>
    change star (f a + sumOver xs f) = star (f a) + _
    rw [star_add,ih]; rfl

theorem starMinor (A : S → Fin 7 → ComplexScalar R) (r : Fin 4 → S) (w : Wedge7) :
    star (minor4 A r w) = minor4 (fun s i => star (A s i)) r w := by
  unfold minor4
  rw [starSum]
  apply sumOverCongr; intro p
  split
  · have neg (z : ComplexScalar R) : star (-z) = -star z := by
      apply ComplexScalar.ext <;> simp <;> grind
    rw [neg]; simp only [star_mul]
  · simp only [star_mul]

/-- Conjugated ordered Gram for the complex amplitudes appearing in the lift. -/
theorem orderedComplexGram (xs : List S) (A : S → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver xs (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (w v : Wedge7) :
    sumOver (fourIndices xs) (fun r => star (minor4 A (position r) w) * minor4 A (position r) v) =
      24*(if w=v then 1 else 0) := by
  simp only [starMinor]
  exact orderedOrthonormal xs _ A orth w v

/-- Contract the genuine exterior lift against any minor Gram. This includes
both canonical increasing coordinates and the redundant ordered tensor slots. -/
theorem exteriorPairing {α : Type} (rs : List α) (rows : α → Fin 4 → S)
    (A : S → Fin 7 → ComplexScalar R) (u v : Wedge7 → ComplexScalar R) :
    sumOver rs (fun r => star (exteriorLift rows A u r) * exteriorLift rows A v r) =
      sumOver wedges (fun i => sumOver wedges (fun j => (star (u i) * v j) *
        sumOver rs (fun r => star (minor4 A (rows r) i) * minor4 A (rows r) j))) := by
  simp only [exteriorLift,starSum,star_mul,sumProduct]
  rw [sumOverSwap]
  apply sumOverCongr; intro i
  rw [sumOverSwap]
  apply sumOverCongr; intro j
  rw [sumOverMulLeft]
  apply sumOverCongr; intro r; grind

theorem orderedExteriorPairing (xs : List S) (A : S → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver xs (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (u v : Wedge7 → ComplexScalar R) :
    sumOver (fourIndices xs) (fun r => star (exteriorLift position A u r) * exteriorLift position A v r) =
      24*sumOver wedges (fun w => star (u w) * v w) := by
  rw [exteriorPairing,sumOverMulLeft]
  apply sumCongrMem; intro i _
  simp only [orderedComplexGram xs A orth]
  calc
    _ = sumOver wedges (fun j => if i=j then 24*(star (u i)*v j) else 0) := by
      apply sumOverCongr; intro j
      by_cases e : i=j <;> simp [e] <;> grind
    _ = _ := sumOnIndex _ i (fun j => 24*(star (u i)*v j)) wedgesNodup (memWedges i)

end Complex

private theorem sumPerm {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private def fourList {α : Type} (u : Four α) := [u.1.1,u.1.2,u.2.1,u.2.2]

private def listProduct : List C → C
  | [] => 1
  | x :: xs => x * listProduct xs

private theorem prodPerm {xs ys : List C} (h : xs.Perm ys) : listProduct xs = listProduct ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [listProduct,ih]
  | swap => simp only [listProduct]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private def identity4 : Permutation := ((0,1),(2,3))

set_option maxRecDepth 10000 in
private theorem reorderTable : permutations.all (fun p =>
    decide ((fourList p).Perm (fourList identity4)) &&
    decide ((permutations.map (fun q => GenericExteriorKernel.reorder q p)).Perm permutations) &&
    permutations.all (fun q => oddPermutation (GenericExteriorKernel.reorder q p) ==
      (oddPermutation q ^^ oddPermutation p)) &&
    permutations.any (fun q => GenericExteriorKernel.reorder p q == identity4 &&
      GenericExteriorKernel.reorder q p == identity4)) = true := by decide

private theorem reorderFacts (p : Permutation) (hp : p∈permutations) :
    (fourList p).Perm (fourList identity4) ∧
    (permutations.map (fun q => GenericExteriorKernel.reorder q p)).Perm permutations ∧
    (∀ q∈permutations, oddPermutation (GenericExteriorKernel.reorder q p) =
      (oddPermutation q ^^ oddPermutation p)) ∧
    ∃ q∈permutations, GenericExteriorKernel.reorder p q = identity4 ∧
      GenericExteriorKernel.reorder q p = identity4 := by
  have h := List.all_eq_true.mp reorderTable p hp
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.any_eq_true,beq_iff_eq] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩

private theorem reorderComposition {α : Type} (u : Four α) (p q : Permutation) :
    GenericExteriorKernel.reorder (GenericExteriorKernel.reorder u p) q =
      GenericExteriorKernel.reorder u (GenericExteriorKernel.reorder p q) := by
  change ((position (GenericExteriorKernel.reorder u p) _,position (GenericExteriorKernel.reorder u p) _),
    (position (GenericExteriorKernel.reorder u p) _,position (GenericExteriorKernel.reorder u p) _)) = _
  simp only [GenericExteriorKernel.position_reorder]; rfl

private theorem columnsReorder (w : Wedge7) (q p : Permutation) :
    columns w (GenericExteriorKernel.reorder q p) = GenericExteriorKernel.reorder (columns w q) p := by
  have each (j : Fin 4) : position (columns w q) j = sourceSite w (position q j) := by
    have options : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by revert j; decide
    rcases options with rfl|rfl|rfl|rfl <;> rfl
  simp only [GenericExteriorKernel.reorder,columns] at each ⊢
  simp only [each]

private theorem tensorReorder (A : S → Fin 7 → C) (r : Four S) (s : Four (Fin 7))
    (p : Permutation) (hp : p∈permutations) :
    tensorFour A (GenericExteriorKernel.reorder r p) (GenericExteriorKernel.reorder s p) =
      tensorFour A r s := by
  have e := prodPerm ((reorderFacts p hp).1.map (fun j => A (position r j) (position s j)))
  simp only [fourList,identity4,List.map_cons,List.map_nil,listProduct,Semiring.mul_one] at e
  dsimp only [tensorFour,tensor,GenericExteriorKernel.reorder]
  change _ = (A (position r 0) (position s 0) * A (position r 1) (position s 1)) *
    (A (position r 2) (position s 2) * A (position r 3) (position s 3))
  simp only [Semiring.mul_assoc] at e ⊢
  exact e

theorem minorReorder (A : S → Fin 7 → C) (r : Four S) (w : Wedge7)
    (p : Permutation) (hp : p∈permutations) :
    minor4 A (position (GenericExteriorKernel.reorder r p)) w =
      sg C p * minor4 A (position r) w := by
  simp only [minorTensor]
  let f q := sg C q * tensorFour A (GenericExteriorKernel.reorder r p) (columns w q)
  have reindex := sumPerm (reorderFacts p hp).2.1 f
  change sumOver permutations f = _
  rw [← reindex,sumOverMulLeft]
  simp only [sumOver,List.map_map,Function.comp_def]
  apply congrArg List.sum; apply List.map_congr_left; intro q hq
  dsimp only [f]
  rw [columnsReorder,tensorReorder A r (columns w q) p hp]
  unfold sg
  rw [(reorderFacts p hp).2.2.1 q hq]
  cases oddPermutation p <;> cases oddPermutation q <;> simp <;> grind

def increasing {S : Type} (key : S → Nat) (r : Four S) : Bool :=
  decide (key r.1.1 < key r.1.2 ∧ key r.1.2 < key r.2.1 ∧ key r.2.1 < key r.2.2)

def apart {S : Type} (k : S → Nat) (r : Four S) : Prop :=
  k r.1.1 ≠ k r.1.2 ∧ k r.1.1 ≠ k r.2.1 ∧ k r.1.1 ≠ k r.2.2 ∧
  k r.1.2 ≠ k r.2.1 ∧ k r.1.2 ≠ k r.2.2 ∧ k r.2.1 ≠ k r.2.2

private theorem sortedExists (key : S → Nat) (r : Four S) (hw : apart key r) :
    ∃ p∈permutations, increasing key (GenericExteriorKernel.reorder r p) = true := by
  let a := key r.1.1
  let b := key r.1.2
  let c := key r.2.1
  let d := key r.2.2
  change a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d at hw
  by_cases h10 : b < a
  · by_cases h20 : c < b
    · by_cases h30 : d < c
      · exact ⟨((3,2),(1,0)),by decide,decide_eq_true (show d<c ∧ c<b ∧ b<a by omega)⟩
      · by_cases h31 : d < b
        · exact ⟨((2,3),(1,0)),by decide,decide_eq_true (show c<d ∧ d<b ∧ b<a by omega)⟩
        · by_cases h32 : d < a
          · exact ⟨((2,1),(3,0)),by decide,decide_eq_true (show c<b ∧ b<d ∧ d<a by omega)⟩
          · exact ⟨((2,1),(0,3)),by decide,decide_eq_true (show c<b ∧ b<a ∧ a<d by omega)⟩
    · by_cases h21 : c < a
      · by_cases h30 : d < b
        · exact ⟨((3,1),(2,0)),by decide,decide_eq_true (show d<b ∧ b<c ∧ c<a by omega)⟩
        · by_cases h31 : d < c
          · exact ⟨((1,3),(2,0)),by decide,decide_eq_true (show b<d ∧ d<c ∧ c<a by omega)⟩
          · by_cases h32 : d < a
            · exact ⟨((1,2),(3,0)),by decide,decide_eq_true (show b<c ∧ c<d ∧ d<a by omega)⟩
            · exact ⟨((1,2),(0,3)),by decide,decide_eq_true (show b<c ∧ c<a ∧ a<d by omega)⟩
      · by_cases h30 : d < b
        · exact ⟨((3,1),(0,2)),by decide,decide_eq_true (show d<b ∧ b<a ∧ a<c by omega)⟩
        · by_cases h31 : d < a
          · exact ⟨((1,3),(0,2)),by decide,decide_eq_true (show b<d ∧ d<a ∧ a<c by omega)⟩
          · by_cases h32 : d < c
            · exact ⟨((1,0),(3,2)),by decide,decide_eq_true (show b<a ∧ a<d ∧ d<c by omega)⟩
            · exact ⟨((1,0),(2,3)),by decide,decide_eq_true (show b<a ∧ a<c ∧ c<d by omega)⟩
  · by_cases h20 : c < a
    · by_cases h30 : d < c
      · exact ⟨((3,2),(0,1)),by decide,decide_eq_true (show d<c ∧ c<a ∧ a<b by omega)⟩
      · by_cases h31 : d < a
        · exact ⟨((2,3),(0,1)),by decide,decide_eq_true (show c<d ∧ d<a ∧ a<b by omega)⟩
        · by_cases h32 : d < b
          · exact ⟨((2,0),(3,1)),by decide,decide_eq_true (show c<a ∧ a<d ∧ d<b by omega)⟩
          · exact ⟨((2,0),(1,3)),by decide,decide_eq_true (show c<a ∧ a<b ∧ b<d by omega)⟩
    · by_cases h21 : c < b
      · by_cases h30 : d < a
        · exact ⟨((3,0),(2,1)),by decide,decide_eq_true (show d<a ∧ a<c ∧ c<b by omega)⟩
        · by_cases h31 : d < c
          · exact ⟨((0,3),(2,1)),by decide,decide_eq_true (show a<d ∧ d<c ∧ c<b by omega)⟩
          · by_cases h32 : d < b
            · exact ⟨((0,2),(3,1)),by decide,decide_eq_true (show a<c ∧ c<d ∧ d<b by omega)⟩
            · exact ⟨((0,2),(1,3)),by decide,decide_eq_true (show a<c ∧ c<b ∧ b<d by omega)⟩
      · by_cases h30 : d < a
        · exact ⟨((3,0),(1,2)),by decide,decide_eq_true (show d<a ∧ a<b ∧ b<c by omega)⟩
        · by_cases h31 : d < b
          · exact ⟨((0,3),(1,2)),by decide,decide_eq_true (show a<d ∧ d<b ∧ b<c by omega)⟩
          · by_cases h32 : d < c
            · exact ⟨((0,1),(3,2)),by decide,decide_eq_true (show a<b ∧ b<d ∧ d<c by omega)⟩
            · exact ⟨((0,1),(2,3)),by decide,decide_eq_true (show a<b ∧ b<c ∧ c<d by omega)⟩

private theorem sortedReorderUnique (key : S → Nat) (r : Four S) (p : Permutation)
    (sorted : increasing key r = true) (newSorted : increasing key (GenericExteriorKernel.reorder r p) = true) :
    p = identity4 := by
  have bound : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  have order (i j : Fin 4) : key (position r i) < key (position r j) ↔ i<j := by
    have h := _root_.of_decide_eq_true sorted
    change key r.1.1 < key r.1.2 ∧ key r.1.2 < key r.2.1 ∧ key r.2.1 < key r.2.2 at h
    rcases bound i with rfl|rfl|rfl|rfl <;> rcases bound j with rfl|rfl|rfl|rfl <;>
      simp [position] <;> omega
  have h := _root_.of_decide_eq_true newSorted
  change key (position r p.1.1) < key (position r p.1.2) ∧ _ at h
  have h₁ := (order _ _).mp h.1
  have h₂ := (order p.1.2 p.2.1).mp h.2.1
  have h₃ := (order p.2.1 p.2.2).mp h.2.2
  have onlyOrder : ∀ a b c d : Fin 4, a<b → b<c → c<d → ((a,b),(c,d))=identity4 := by decide
  exact onlyOrder _ _ _ _ h₁ h₂ h₃

private theorem divisionTable : permutations.all (fun p => permutations.all (fun q =>
    permutations.any (fun t => GenericExteriorKernel.reorder p t == q))) = true := by decide

private theorem sortedIff (key : S → Nat) (r : Four S) (p : Permutation) (hp : p∈permutations)
    (hs : increasing key (GenericExteriorKernel.reorder r p) = true)
    (q : Permutation) (hq : q∈permutations) :
    increasing key (GenericExteriorKernel.reorder r q) = true ↔ p=q := by
  constructor
  · intro hq'
    obtain ⟨t,_,ht⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp divisionTable p hp) q hq)
    obtain rfl := (beq_iff_eq.mp ht).symm
    rw [←reorderComposition] at hq'
    have e := sortedReorderUnique key _ t hs hq'
    subst t; rfl
  · rintro rfl; exact hs

private theorem allRowsPerm [DecidableEq S] (sites : List S) (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (p : Permutation) (hp : p∈permutations) :
    ((fourIndices sites).map (fun r => GenericExteriorKernel.reorder r p)).Perm (fourIndices sites) := by
  have completeRows (r : Four S) : r∈fourIndices sites :=
    pairMember (pairMember (complete _) (complete _)) (pairMember (complete _) (complete _))
  have pairUnique := pairsNodup sites sites unique unique
  have rowsUnique : (fourIndices sites).Nodup := pairsNodup _ _ pairUnique pairUnique
  obtain ⟨t,_,pt,tp⟩ := (reorderFacts p hp).2.2.2
  have inj (a b : Four S) (e : GenericExteriorKernel.reorder a p = GenericExteriorKernel.reorder b p) : a=b := by
    have h := congrArg (fun u => GenericExteriorKernel.reorder u t) e
    rw [reorderComposition,reorderComposition,pt] at h; exact h
  have mapped : ((fourIndices sites).map (fun r => GenericExteriorKernel.reorder r p)).Nodup :=
    List.Pairwise.map (fun r => GenericExteriorKernel.reorder r p)
    (fun a b (ne : a≠b) h => ne (inj a b h)) rowsUnique
  apply List.perm_iff_count.mpr
  intro r
  have member : r ∈ (fourIndices sites).map (fun r => GenericExteriorKernel.reorder r p) := by
    refine List.mem_map.mpr ⟨GenericExteriorKernel.reorder r t,completeRows _,?_⟩
    rw [reorderComposition,tp]; rfl
  rw [mapped.count, rowsUnique.count]
  simp [member,completeRows]

private theorem sumZero {α : Type} (xs : List α) : sumOver xs (fun _ => (0:C)) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumOver xs _ = 0; rw [ih]; grind

/-- Sum of a symmetric four-row integrand supported on distinct rows, using
the complete, nonrepeating sorted coordinate basis exactly once. -/
theorem orderedToSorted [DecidableEq S] (sites : List S) (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (key : S → Nat) (f : Four S → C)
    (symm : ∀ r p, p∈permutations → f (GenericExteriorKernel.reorder r p) = f r)
    (degenerate : ∀ r, ¬apart key r → f r = 0) :
    sumOver (fourIndices sites) f =
      24*sumOver ((fourIndices sites).filter (increasing key)) f := by
  let g (r : Four S) := if increasing key r then f r else 0
  have orbit (r : Four S) : sumOver permutations (fun p => g (GenericExteriorKernel.reorder r p)) = f r := by
    by_cases h : apart key r
    · obtain ⟨p,hp,hs⟩ := sortedExists key r h
      calc
        _ = sumOver permutations (fun q => if p=q then f r else 0) := by
          apply sumCongrMem; intro q hq
          simp only [g,sortedIff key r p hp hs q hq,symm r q hq]
        _ = _ := sumOnIndex permutations p (fun _ => f r) complete_basis_counts.2.2.2 hp
    · rw [degenerate r h]
      calc
        _ = sumOver permutations (fun _ => (0:C)) := by
          apply sumCongrMem; intro p hp; simp [g,symm r p hp,degenerate r h]
        _ = _ := sumZero _
  have filter (xs : List (Four S)) : sumOver xs g = sumOver (xs.filter (increasing key)) f := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      change g r + sumOver xs g = _
      rw [ih,List.filter_cons]
      cases h : increasing key r <;> simp [g,h,sumOver] <;> grind
  calc
    _ = sumOver (fourIndices sites) (fun r => sumOver permutations (fun p => g (GenericExteriorKernel.reorder r p))) :=
      sumOverCongr _ (fun r => (orbit r).symm)
    _ = sumOver permutations (fun _ => sumOver (fourIndices sites) g) := by
      rw [sumOverSwap]; apply sumCongrMem; intro p hp
      simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (allRowsPerm sites complete unique p hp) g
    _ = _ := by rw [sumConst24,filter]


private theorem oddStabilizer (key : S → Nat) (inj : ∀ a b, key a = key b → a=b)
    (r : Four S) (degenerate : ¬apart key r) :
    ∃ p∈permutations, oddPermutation p=true ∧ GenericExteriorKernel.reorder r p = r := by
  rcases r with ⟨⟨a,b⟩,c,d⟩
  by_cases e01 : a=b
  · subst b; exact ⟨((1,0),(2,3)),by decide,by decide,rfl⟩
  by_cases e02 : a=c
  · subst c; exact ⟨((2,1),(0,3)),by decide,by decide,rfl⟩
  by_cases e03 : a=d
  · subst d; exact ⟨((3,1),(2,0)),by decide,by decide,rfl⟩
  by_cases e12 : b=c
  · subst c; exact ⟨((0,2),(1,3)),by decide,by decide,rfl⟩
  by_cases e13 : b=d
  · subst d; exact ⟨((0,3),(2,1)),by decide,by decide,rfl⟩
  by_cases e23 : c=d
  · subst d; exact ⟨((0,1),(3,2)),by decide,by decide,rfl⟩
  exact False.elim (degenerate ⟨fun h => e01 (inj _ _ h),fun h => e02 (inj _ _ h),fun h => e03 (inj _ _ h),fun h => e12 (inj _ _ h),fun h => e13 (inj _ _ h),fun h => e23 (inj _ _ h)⟩)

theorem signedMinorSorted (sites : List S) [DecidableEq S] (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (key : S → Nat) (inj : ∀ a b, key a = key b → a=b)
    (noTwo : ∀ z : C, z = -z → z=0) (A B : S → Fin 7 → C) (w v : Wedge7) :
    sumOver (fourIndices sites) (fun r => minor4 A (position r) w * minor4 B (position r) v) =
    24*sumOver ((fourIndices sites).filter (increasing key))
      (fun r => minor4 A (position r) w * minor4 B (position r) v) := by
  apply orderedToSorted sites complete unique key
  · intro r p hp
    rw [minorReorder A r w p hp,minorReorder B r v p hp]
    unfold sg; cases oddPermutation p <;> simp <;> grind
  · intro r ht
    obtain ⟨p,hp,neg,fixed⟩ := oddStabilizer key inj r ht
    have eq := minorReorder A r w p hp
    rw [fixed] at eq
    simp only [sg,neg,ite_true] at eq
    have vanish : minor4 A (position r) w = 0 := noTwo _ (eq.trans (by grind))
    rw [vanish]; grind

section OrderedComplex
open ComplexScalar
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem complexNoTwo (z : ComplexScalar R) (e : z = -z) : z=0 := by
  have hr := congrArg ComplexScalar.re e
  have hi := congrArg ComplexScalar.im e
  change z.re = -z.re at hr
  change z.im = -z.im at hi
  apply ComplexScalar.ext
  · change z.re = 0; grind
  · change z.im = 0; grind

private theorem cancelComplex24 {x y : ComplexScalar R} (e : 24*x = 24*y) : x=y := by
  have r := congrArg ComplexScalar.re e
  have i := congrArg ComplexScalar.im e
  change (24:R)*x.re-0*x.im = 24*y.re-0*y.im at r
  change (24:R)*x.im+0*x.re = 24*y.im+0*y.re at i
  apply ComplexScalar.ext <;> grind

/-- Fourth-order Cauchy–Binet for biorthogonal columns on the canonically
increasing coordinate basis. -/
theorem sortedComplexGram [DecidableEq S] (sites : List S) (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (key : S → Nat) (inj : ∀ a b, key a = key b → a=b)
    (A : S → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver sites (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (w v : Wedge7) :
    sumOver ((fourIndices sites).filter (increasing key))
      (fun r => star (minor4 A (position r) w) * minor4 A (position r) v) = if w=v then 1 else 0 := by
  have eq := orderedComplexGram sites A orth w v
  simp only [starMinor] at eq ⊢
  rw [signedMinorSorted sites complete unique key inj complexNoTwo] at eq
  exact cancelComplex24 eq

/-- The fourfold exterior lift of an orthonormal seven-column map preserves
every complex inner product on the 35-dimensional source. -/
theorem exteriorIsometry [DecidableEq S] (sites : List S) (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (key : S → Nat) (inj : ∀ a b, key a = key b → a=b)
    (A : S → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver sites (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (u v : Wedge7 → ComplexScalar R) :
    sumOver ((fourIndices sites).filter (increasing key))
      (fun r => star (exteriorLift position A u r) * exteriorLift position A v r) =
      sumOver wedges (fun w => star (u w) * v w) := by
  rw [exteriorPairing]; apply sumOverCongr; intro i
  simp only [sortedComplexGram sites complete unique key inj A orth]
  calc
    _ = sumOver wedges (fun j => if i=j then star (u i)*v j else 0) := by
      apply sumOverCongr; intro j
      by_cases e : i=j <;> simp [e] <;> grind
    _ = _ := sumOnIndex _ i (fun j => star (u i)*v j) wedgesNodup (memWedges i)

private def sourceFour (w : Wedge7) : Four (Fin 7) := ((w.i,w.j),(w.k,w.m))

private theorem columnPositions (w : Wedge7) (p : Permutation) :
    columns w p = GenericExteriorKernel.reorder (sourceFour w) p := rfl

/-- No orthogonality hypotheses: fourth Cauchy–Binet identifies the
cross-Gram of the signed sorted minors with the minor of the cross-Gram. -/
theorem cauchyBinet [DecidableEq S] (sites : List S) (complete : ∀ s, s∈sites)
    (unique : sites.Nodup) (key : S → Nat) (inj : ∀ a b, key a = key b → a=b)
    (A B : S → Fin 7 → ComplexScalar R) (w v : Wedge7) :
    sumOver ((fourIndices sites).filter (increasing key))
      (fun r => star (minor4 A (position r) w) * minor4 B (position r) v) =
      minor4 (columnGram sites (fun s j => star (A s j)) B) (sourceSite w) v := by
  let L s j := star (A s j)
  let G := columnGram sites L B
  simp only [starMinor]
  apply cancelComplex24
  rw [← signedMinorSorted sites complete unique key inj complexNoTwo, orderedMinorGram]
  change _ = 24 * minor4 G (position (sourceFour w)) v
  rw [minorTensor, ←sumConst24]
  apply sumCongrMem; intro p hp
  let term q := (sg (ComplexScalar R) p * sg (ComplexScalar R) q) *
    tensorFour G (columns w p) (columns v q)
  have reindex := sumPerm (reorderFacts p hp).2.1 term
  change sumOver permutations term = _
  rw [←reindex]
  simp only [sumOver,List.map_map,Function.comp_def]
  apply congrArg List.sum; apply List.map_congr_left; intro q hq
  dsimp only [term]
  rw [columnsReorder,columnPositions w,tensorReorder G _ _ p hp]
  unfold sg
  rw [(reorderFacts p hp).2.2.1 q hq]
  cases oddPermutation p <;> cases oddPermutation q <;> simp <;> grind

private theorem physicalEnumeration (n : Nat) :
    ((PhysicalWedges.coords n).map Subtype.val).Perm
      ((fourIndices (qubitIndices n)).filter (increasing (PlaneOrientation.label n))) := by
  letI : DecidableEq (Basis n) := cubeDecEq n
  have left : ((PhysicalWedges.coords n).map Subtype.val).Nodup :=
    List.Pairwise.map Subtype.val (fun _ _ ne e => ne (Subtype.ext e)) (PhysicalWedges.coordsNodup _)
  have nd := HyperplaneIncidence.normalsNodup n
  have tw := pairsNodup (qubitIndices n) (qubitIndices n) nd nd
  have four : (fourIndices (qubitIndices n)).Nodup := pairsNodup _ _ tw tw
  have right : ((fourIndices (qubitIndices n)).filter (increasing (PlaneOrientation.label n))).Nodup :=
    four.filter (increasing (PlaneOrientation.label n))
  apply List.perm_iff_count.mpr
  intro r
  rw [left.count,right.count]
  have full : r ∈ fourIndices (qubitIndices n) :=
    pairMember (pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
      (pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
  by_cases hs : PlaneOrientation.Increasing r
  · let u : PhysicalWedges.Coordinate n := ⟨r,hs⟩
    have l : r ∈ (PhysicalWedges.coords n).map Subtype.val :=
      List.mem_map.mpr ⟨u,PhysicalWedges.memCoords u,rfl⟩
    have b : increasing (PlaneOrientation.label n) r = true := decide_eq_true hs
    have h := List.mem_filter.mpr ⟨full,b⟩
    simp only [ite_eq_left l,ite_eq_left h]
  · have l : r ∉ (PhysicalWedges.coords n).map Subtype.val := by
      rintro h; obtain ⟨u,_,rfl⟩ := List.mem_map.mp h; exact hs u.property
    have b : increasing (PlaneOrientation.label n) r = false := decide_eq_false hs
    simp [l,b]

/-- The full physical computational-basis coordinate list, with its actual
subtype row functions, satisfies the fourth exterior isometry in every dimension. -/
theorem physicalIsometry (n : Nat) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver (qubitIndices n) (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (u v : Wedge7 → ComplexScalar R) :
    sumOver (PhysicalWedges.coords n) (fun r =>
      star (exteriorLift (fun t : PhysicalWedges.Coordinate n => position t.val) A u r) *
        exteriorLift (fun t : PhysicalWedges.Coordinate n => position t.val) A v r) =
      sumOver wedges (fun w => star (u w) * v w) := by
  letI : DecidableEq (Basis n) := cubeDecEq n
  let f (r : Four (Basis n)) := star (exteriorLift position A u r) * exteriorLift position A v r
  have transport := sumPerm (physicalEnumeration n) f
  calc
    _ = sumOver ((fourIndices (qubitIndices n)).filter (increasing (PlaneOrientation.label n))) f := by
      simpa only [f,exteriorLift,sumOver,List.map_map,Function.comp_def] using transport
    _ = _ := exteriorIsometry (qubitIndices n) qubitIndicesComplete (HyperplaneIncidence.normalsNodup n)
      (PlaneOrientation.label n) (PlaneOrientation.labelInjective n) A orth u v

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun x => (f x).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a + sumOver xs f).re = _; rw [ComplexScalar.re_add,ih]; rfl

theorem physicalNormIsometry (n : Nat) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : ∀ i j, sumOver (qubitIndices n) (fun s => star (A s i) * A s j) = if i=j then 1 else 0)
    (v : Wedge7 → ComplexScalar R) :
    sumOver (PhysicalWedges.coords n) (fun r =>
      normSq (exteriorLift (fun t : PhysicalWedges.Coordinate n => position t.val) A v r)) =
    sumOver wedges (fun w => normSq (v w)) := by
  have h := congrArg ComplexScalar.re (physicalIsometry n A orth v v)
  simpa only [reSum,ComplexScalar.re_star_mul_self] using h

end OrderedComplex


end RankSeven.ExteriorIsometry
