import Rank7GenericExteriorKernel
import Rank7HyperplaneInduction

namespace RankSeven.PhysicalWedges

open Lean.Grind Pauli PlaneOrientation HyperplaneIncidence HyperplaneInduction
open GenericExteriorKernel (position)

abbrev Coordinate (n : Nat) := {u : Four (Basis n) // Increasing u}

local instance {n : Nat} : DecidableEq (Basis n) := cubeDecEq n

instance (n : Nat) : DecidableEq (Coordinate n) :=
  inferInstanceAs (DecidableEq {u : Four (Basis n) // Increasing u})

local instance {n : Nat} (u : Four (Basis n)) : Decidable (Increasing u) := by
  unfold Increasing
  infer_instance

private def increasingOnly {n : Nat} (u : Four (Basis n)) : Option (Coordinate n) :=
  if h : Increasing u then some ⟨u, h⟩ else none

def coords (n : Nat) : List (Coordinate n) :=
  (fourIndices (qubitIndices n)).filterMap increasingOnly

theorem memCoords {n : Nat} (w : Coordinate n) : w ∈ coords n := by
  apply List.mem_filterMap.mpr
  let h (a b : Basis n) :=
    pairMember (qubitIndicesComplete a) (qubitIndicesComplete b)
  refine ⟨w.val, pairMember (h w.val.1.1 w.val.1.2) (h w.val.2.1 w.val.2.2), ?_⟩
  unfold increasingOnly
  rw [dite_eq_left w.property]

theorem coordsNodup (n : Nat) : (coords n).Nodup := by
  unfold coords
  have two := pairsNodup (qubitIndices n) (qubitIndices n) (normalsNodup n) (normalsNodup n)
  have four : (fourIndices (qubitIndices n)).Nodup :=
    pairsNodup _ _ two two
  apply List.Pairwise.filterMap increasingOnly _ four
  intro a b distinct va hva vb hvb h
  subst vb
  unfold increasingOnly at hva hvb
  split at hva <;> split at hvb <;> try contradiction
  exact distinct (congrArg Subtype.val ((Option.some.inj hva).trans (Option.some.inj hvb).symm))

def mapFourSites {α β : Type} (f : α → β) (u : Four α) : Four β :=
  ((f u.1.1, f u.1.2), (f u.2.1, f u.2.2))

theorem mapFourPosition {α β : Type} (f : α → β) (u : Four α) (i : Fin 4) :
    position (mapFourSites f u) i = f (position u i) := by
  have possibilities : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases possibilities with rfl | rfl | rfl | rfl <;> rfl

theorem fourExt {α : Type} {u v : Four α} (pointwise : ∀ j, position u j = position v j) : u = v :=
  Prod.ext (Prod.ext (pointwise 0) (pointwise 1)) (Prod.ext (pointwise 2) (pointwise 3))

theorem coordinateExt {n : Nat} {u v : Coordinate n}
    (pointwise : ∀ j, position u.val j = position v.val j) : u = v :=
  Subtype.ext (fourExt pointwise)

def mapCoordinate {n m : Nat} (site : Basis n → Basis m)
    (increasingSite : ∀ a b, label n a < label n b → label m (site a) < label m (site b))
    (w : Coordinate n) : Coordinate m :=
  ⟨mapFourSites site w.val,
    ⟨increasingSite _ _ w.property.1, increasingSite _ _ w.property.2.1, increasingSite _ _ w.property.2.2⟩⟩

theorem mapCoordinatePosition {n m : Nat} (site : Basis n → Basis m)
    (increasingSite : ∀ a b, label n a < label n b → label m (site a) < label m (site b))
    (w : Coordinate n) (j : Fin 4) :
    position (mapCoordinate site increasingSite w).val j = site (position w.val j) :=
  mapFourPosition site w.val j

theorem mapCoordinateInjective {n m : Nat} (site : Basis n → Basis m)
    (increasingSite : ∀ a b, label n a < label n b → label m (site a) < label m (site b))
    (injectiveSite : ∀ {a b}, site a = site b → a = b) {u v : Coordinate n}
    (equal : mapCoordinate site increasingSite u = mapCoordinate site increasingSite v) : u = v := by
  apply coordinateExt
  intro j
  apply injectiveSite
  exact (mapCoordinatePosition site increasingSite u j).symm.trans
    ((congrArg (fun w : Coordinate m => position w.val j) equal).trans
      (mapCoordinatePosition site increasingSite v j))

theorem leftInverseCoordinate {n m : Nat} (site : Basis n → Basis m) (unsite : Basis m → Basis n)
    (increasingSite : ∀ a b,
      label n a < label n b ↔ label m (site a) < label m (site b))
    (w : Coordinate m) (back : ∀ j, site (unsite (position w.val j)) = position w.val j) :
    ∃ v : Coordinate n, mapCoordinate site (fun a b => (increasingSite a b).mp) v = w := by
  have sorted :
      Increasing (mapFourSites unsite w.val) := by
    have hop (i j : Fin 4)
        (increase : label m (position w.val i) < label m (position w.val j)) :
        label n (unsite (position w.val i)) < label n (unsite (position w.val j)) := by
      apply (increasingSite _ _).mpr
      rw [back i, back j]
      exact increase
    exact ⟨hop 0 1 w.property.1, hop 1 2 w.property.2.1, hop 2 3 w.property.2.2⟩
  refine ⟨⟨mapFourSites unsite w.val, sorted⟩, ?_⟩
  apply coordinateExt
  intro j
  rw [mapCoordinatePosition]
  change site (position (mapFourSites unsite w.val) j) = _
  rw [mapFourPosition, back]

section Kernels

variable {R α β : Type} [CommRing R] [DecidableEq α] [DecidableEq β]

/-- The embedded matrix keeps its exact entry on image coordinates. -/
theorem embeddedKernel_image (xs : List β) (embed : β → α)
    (injective : ∀ {x y}, embed x = embed y → x = y) (unique : xs.Nodup)
    (K : β × β → R) (i j : β) (hi : i ∈ xs) (hj : j ∈ xs) :
    embeddedKernel xs embed K (embed i, embed j) = K (i,j) := by
  unfold embeddedKernel deposit
  have term (uv : β × β) :
      (if pairMap embed uv = (embed i, embed j) then K uv else 0) =
        if (i,j) = uv then K uv else 0 := by
    by_cases matchPair : (i,j) = uv
    · subst uv
      simp [pairMap]
    · have apart : pairMap embed uv ≠ (embed i, embed j) := by
        intro same
        have left := injective (congrArg Prod.fst same)
        have right := injective (congrArg Prod.snd same)
        exact matchPair (Prod.ext left.symm right.symm)
      simp [apart, matchPair]
  rw [sumOverCongr _ term]
  exact ExteriorPauliBase.sumOnIndex _ (i,j) K (pairsNodup xs xs unique unique) (pairMember hi hj)

omit [DecidableEq β] in
theorem embeddedKernel_absent (xs : List β) (embed : β → α) (K : β × β → R) (ij : α × α)
    (absent : ∀ p : β × β, pairMap embed p ≠ ij) :
    embeddedKernel xs embed K ij = 0 := by
  unfold embeddedKernel deposit
  simp only [ite_eq_right (absent _)]
  have zeroSum (terms : List (β × β)) : sumOver terms (fun _ => (0 : R)) = 0 := by
    induction terms with
    | nil => rfl
    | cons a rest ih =>
      change 0 + sumOver rest (fun _ => (0 : R)) = 0
      rw [ih]
      grind
  exact zeroSum _

end Kernels

section Base

open ExteriorPauliBase (Wedge wedgeIndices pointBits qubitBits tupleOf atPosition)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem baseIncreasing : ∀ w : Wedge, Increasing (pointBits (tupleOf w)) := by
  decide

def baseCoordinate (w : Wedge) : Coordinate 3 :=
  ⟨pointBits (tupleOf w), baseIncreasing w⟩

theorem baseCoordinateAt (w : Wedge) (j : Fin 4) :
    position (baseCoordinate w).val j = qubitBits (atPosition (tupleOf w) j) := by
  have possibilities : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rcases possibilities with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem baseCoordinatePermutation : (wedgeIndices.map baseCoordinate).Perm (coords 3) := by
  decide

theorem baseCoordinateInjective {u v : Wedge} (equal : baseCoordinate u = baseCoordinate v) : u = v := by
  have injOn {α β : Type} (xs : List α) (f : α → β) (unique : (xs.map f).Nodup)
      {a b : α} (inA : a ∈ xs) (inB : b ∈ xs) (eq : f a = f b) : a = b := by
    induction xs with
    | nil => cases inA
    | cons c xs ih =>
      obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp inA with headA | memA <;>
        rcases List.mem_cons.mp inB with headB | memB
      · exact headA.trans headB.symm
      · subst a
        exact False.elim (fresh (List.mem_map.mpr ⟨b, memB, eq.symm⟩))
      · subst b
        exact False.elim (fresh (List.mem_map.mpr ⟨a, memA, eq⟩))
      · exact ih tail memA memB
  exact injOn _ baseCoordinate (baseCoordinatePermutation.symm.nodup (coordsNodup 3))
    (by simp [wedgeIndices]) (by simp [wedgeIndices]) equal

theorem baseSums {R : Type} [CommRing R] (f : Coordinate 3 → R) :
    sumOver (coords 3) f = sumOver wedgeIndices (fun w => f (baseCoordinate w)) := by
  have byPerm {α : Type} {xs ys : List α} (perm : xs.Perm ys) (g : α → R) :
      sumOver xs g = sumOver ys g := by
    induction perm with
    | nil => rfl
    | cons a perm ih =>
      simp only [sumOver, List.map_cons, List.sum_cons] at *
      rw [ih]
    | swap a b xs =>
      simp only [sumOver, List.map_cons, List.sum_cons]
      grind
    | trans perm₁ perm₂ ih₁ ih₂ => exact ih₁.trans ih₂
  rw [byPerm baseCoordinatePermutation.symm f]
  simp [sumOver, List.map_map, Function.comp_def]

end Base
end RankSeven.PhysicalWedges

#print axioms RankSeven.PhysicalWedges.coordsNodup
#print axioms RankSeven.PhysicalWedges.leftInverseCoordinate
#print axioms RankSeven.PhysicalWedges.embeddedKernel_image
#print axioms RankSeven.PhysicalWedges.baseCoordinatePermutation
