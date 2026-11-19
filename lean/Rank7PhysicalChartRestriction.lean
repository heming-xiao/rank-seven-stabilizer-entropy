import Rank7PhysicalWedges
import Rank7OrderedHyperplaneChart

namespace RankSeven.PhysicalChartRestriction

open Lean.Grind Pauli HyperplaneIncidence HyperplaneInduction
open GenericExteriorKernel (position supportedPair)
open OrderedHyperplaneChart (site unsite siteIn siteUnsite siteLtIff siteInjective siteSupportedPair siteFour)
open PhysicalWedges

def weight {R : Type} [CommRing R] (half : R) (n : Nat) : R := 4 * half^n

theorem weightThree {R : Type} [CommRing R] (half : R) (halfUnit : 2 * half = 1) :
    weight half 3 = half := by
  unfold weight
  calc
    _ = (2 * half)^2 * half := by grind
    _ = _ := by rw [halfUnit]; grind

theorem weightDouble {R : Type} [CommRing R] (half : R) (halfUnit : 2 * half = 1) (n : Nat) :
    weight half n = 2 * weight half (n+1) := by
  unfold weight
  rw [Semiring.pow_succ]
  calc
    _ = 4 * half^n * (2*half) := by rw [halfUnit, Semiring.mul_one]
    _ = _ := by grind

def defect {n : Nat} {R : Type} [CommRing R] (q : R) (uv : Coordinate n × Coordinate n) : R :=
  (if uv.1 = uv.2 then q else 0) -
    (if supportedPair uv.1.val uv.2.val then q else 0)

def embed {n : Nat} (H : HyperplaneCode (n+1)) : Coordinate n → Coordinate (n+1) :=
  mapCoordinate (site H) (fun a b => (siteLtIff H a b).mpr)

theorem embedPosition {n : Nat} (H : HyperplaneCode (n+1)) (w : Coordinate n) (j : Fin 4) :
    position (embed H w).val j = site H (position w.val j) :=
  mapCoordinatePosition _ _ w j

theorem embedInjective {n : Nat} (H : HyperplaneCode (n+1)) {u v : Coordinate n}
    (same : embed H u = embed H v) : u = v :=
  mapCoordinateInjective _ _ (siteInjective H) same

def inside {n : Nat} (H : HyperplaneCode n) (w : Coordinate n) : Prop :=
  ∀ j : Fin 4, contains H (position w.val j) = true

theorem embedInside {n : Nat} (H : HyperplaneCode (n+1)) (proper : H.1 ≠ zero (n+1)) (w : Coordinate n) :
    inside H (embed H w) := by
  intro j
  rw [embedPosition]
  exact siteIn H proper _

theorem insideHasPreimage {n : Nat} (H : HyperplaneCode (n+1))
    (proper : H.1 ≠ zero (n+1)) (w : Coordinate (n+1)) (h : inside H w) :
    ∃ v, embed H v = w :=
  leftInverseCoordinate (site H) (unsite H) (fun a b => (siteLtIff H a b).symm)
    w (fun j => siteUnsite H proper _ (h j))

theorem defectEmbedded {n : Nat} {R : Type} [CommRing R] (q : R)
    (H : HyperplaneCode (n+1)) (u v : Coordinate n) :
    defect q (embed H u, embed H v) = defect q (u,v) := by
  have hs : supportedPair (embed H u).val (embed H v).val = supportedPair u.val v.val :=
    siteSupportedPair H u.val v.val
  simp only [defect, hs]
  by_cases same : u=v
  · subst v
    simp
  · have different : embed H u ≠ embed H v := fun h => same (embedInjective H h)
    rw [ite_eq_right different, ite_eq_right same]

theorem properOfMem {n : Nat} (H : HyperplaneCode n) (mem : H ∈ hyperplanes n) :
    H.1 ≠ zero n := by
  unfold hyperplanes at mem
  rcases List.mem_append.mp mem with left | right
  · obtain ⟨a, valid, rfl⟩ := List.mem_map.mp left
    have hv := (List.mem_filter.mp valid).2
    intro zeroEq
    change a = zero n at zeroEq
    have hz := (isZero_iff n a).mpr zeroEq
    simp [hz] at hv
  · obtain ⟨a, valid, rfl⟩ := List.mem_map.mp right
    have hv := (List.mem_filter.mp valid).2
    intro zeroEq
    change a = zero n at zeroEq
    have hz := (isZero_iff n a).mpr zeroEq
    simp [hz] at hv

/-- The actual child defect is the restriction on precisely the wedges
    supported in a proper affine hyperplane, and is zero off its image. -/
theorem actualChildEntry {n : Nat} {R : Type} [CommRing R] (q : R)
    (H : HyperplaneCode (n+1)) (proper : H.1 ≠ zero (n+1))
    (u v : Coordinate (n+1)) [Decidable (inside H u ∧ inside H v)] :
    embeddedKernel (coords n) (embed H) (defect q) (u,v) =
      if inside H u ∧ inside H v then defect q (u,v) else 0 := by
  by_cases insideBoth : inside H u ∧ inside H v
  · rw [ite_eq_left insideBoth]
    obtain ⟨a, ha⟩ := insideHasPreimage H proper u insideBoth.1
    obtain ⟨b, hb⟩ := insideHasPreimage H proper v insideBoth.2
    rw [← ha, ← hb, embeddedKernel_image (coords n) (embed H) (embedInjective H) (coordsNodup n)
      _ a b (memCoords a) (memCoords b), defectEmbedded]
  · rw [ite_eq_right insideBoth]
    apply embeddedKernel_absent
    intro uv eq
    have first : embed H uv.1 = u := congrArg Prod.fst eq
    have second : embed H uv.2 = v := congrArg Prod.snd eq
    exact insideBoth ⟨first ▸ embedInside H proper uv.1, second ▸ embedInside H proper uv.2⟩

end RankSeven.PhysicalChartRestriction

#print axioms RankSeven.PhysicalChartRestriction.actualChildEntry
