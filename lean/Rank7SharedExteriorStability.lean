import Rank7SharedOddLeakage

namespace RankSeven.SharedExteriorStability

open Lean.Grind Pauli ComplexScalar
open HighestExteriorStability (Form value diagonal)

attribute [local instance] Semiring.natCast

def colorTest {α : Type} [DecidableEq α] (anchor : α) (occupied : List α) (color : α) : Bool :=
  decide (color≠anchor ∧ color∈occupied ∧ (anchor∈occupied ∨ 2≤occupied.count color))

/-- In a five-site wedge, at most four outside colors have an occupant
and a second occupant in the union of that color with the anchor color. -/
theorem atMostFourColors {α : Type} [DecidableEq α] (anchor : α)
    (occupied colors : List α) (five : occupied.length≤5) (distinct : colors.Nodup) :
    (colors.filter (colorTest anchor occupied)).length≤4 := by
  let selected := colors.filter (colorTest anchor occupied)
  have nd : selected.Nodup := List.filter_sublist.nodup distinct
  have test (b : α) (hb : b∈selected) :
      b≠anchor ∧ b∈occupied ∧ (anchor∈occupied ∨ 2≤occupied.count b) :=
    of_decide_eq_true (List.mem_filter.mp hb).2
  have reserve (x : α) (hx : x∈occupied) (keep : selected ⊆ occupied.erase x) :
      selected.length≤4 := by
    have h := nd.length_le_of_subset keep
    rw [List.length_erase_of_mem hx] at h
    omega
  by_cases inside : anchor∈occupied
  · exact reserve anchor inside (fun b hb => (List.mem_erase_of_ne (test b hb).1).mpr (test b hb).2.1)
  by_cases empty : selected=[]
  · change selected.length≤4
    rw [empty]
    exact Nat.zero_le 4
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil selected empty
  have twice : 2≤occupied.count x := (test x hx).2.2.resolve_left inside
  apply reserve x (test x hx).2.1
  intro b hb
  by_cases same : b=x
  · subst b
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  · exact (List.mem_erase_of_ne same).mpr (test b hb).2.1

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]


/-- The occupation multiplicity bounds the total nonnegative mass
tested by the color restrictions. -/
theorem colorMass {α β : Type} [DecidableEq α] (anchor : α) (colors : List α)
    (distinct : colors.Nodup) (states : List β) (occupants : β → List α)
    (five : ∀z,z∈states → (occupants z).length≤5)
    (weight : β → R) (positive : ∀z,z∈states → 0≤weight z) :
    sumOver colors (fun b => sumOver states (fun z => if colorTest anchor (occupants z) b then weight z else 0))≤
      4*sumOver states weight := by
  have count (xs : List α) (test : α → Bool) (w : R) :
      sumOver xs (fun b => if test b then w else 0)=(Nat.cast (xs.filter test).length : R)*w := by
    induction xs with
    | nil =>
      change 0=(Nat.cast 0:R)*w
      rw [Semiring.natCast_zero,Semiring.zero_mul]
    | cons b rest ih =>
      change (if test b then w else 0)+sumOver rest (fun b => if test b then w else 0)=_
      rw [ih]
      cases sel : test b
      · simp only [sel,Bool.false_eq_true,ite_false,List.filter_cons]
        grind only
      · simp only [sel,ite_true,List.filter_cons,List.length_cons,Semiring.natCast_succ]
        grind only
  rw [sumOverSwap,sumOverMulLeft]
  have point (z : β) (hz : z∈states) :
      0≤4*weight z-sumOver colors (fun b => if colorTest anchor (occupants z) b then weight z else 0) := by
    rw [count]
    let len := (colors.filter (colorTest anchor (occupants z))).length
    have bound : len≤4 := atMostFourColors anchor (occupants z) colors (five z hz) distinct
    have eq : len+(4-len)=4 := by omega
    have e := congrArg (fun a : Nat => (Nat.cast a : R)) eq
    rw [Semiring.natCast_add] at e
    have h : 0≤(Nat.cast (4-len) : R) := OrderedRing.natCast_nonneg
    have four : (Nat.cast 4 : R)=4 := by
      rw [Semiring.natCast_succ 3,Semiring.natCast_succ 2,Semiring.natCast_succ 1,
        Semiring.natCast_succ 0,Semiring.natCast_zero]
      grind only
    rw [four] at e
    have le : (Nat.cast len : R)≤4 := by grind only
    have q := OrderedRing.mul_le_mul_of_nonneg_right le (positive z hz)
    change 0≤4*weight z-(Nat.cast len : R)*weight z
    grind only
  have q := Compression.sumOverNonnegative _ _ point
  rw [Compression.sumOverSub] at q
  grind only

/-- The real quadratic comparison after summing the color-restricted
cross terms of the two one-outside components. -/
theorem quadraticPrice (q : Form R) (n0 n1 n2 n3 E : R)
    (singlePos : 0≤n1+n2) (tailPos : 0≤n3)
    (mass : n0+n1+n2+n3=1) (small : E≤2) (nonnegative : 0≤E)
    (singleMass : n1+n2≤E) (tailMass : 4*n3≤E^2)
    (positive : ∀a b c d,0≤value q a b c d)
    (upper : ∀a b c d,2*value q a b c d≤5*diagonal n0 n1 n2 n3 a b c d)
    (reference : q.q0≤2*n0)
    (colors : (q.q01+q.q02)^2≤16*(n1+n2)*(2*n0-q.q0)) :
    value q 1 1 1 1-2≤18*E := by
  let u := n1+n2
  let δ := 2*n0-q.q0
  let s := q.q01+q.q02
  let t := q.q03+q.q13+q.q23
  have anchor : 2*s≤δ+16*u := by
    have hδ : 0≤δ := by unfold δ; grind only
    have eq : (δ+16*u)^2-4*s^2=(δ-16*u)^2+4*(16*u*δ-s^2) := by grind only
    have c : s^2≤16*u*δ := colors
    have nonneg := squareNonnegative (δ-16*u)
    by_cases h : 2*s≤δ+16*u
    · exact h
    · have bad := OrderedRing.mul_pos (show 0<2*s-(δ+16*u) by grind only)
        (show 0<2*s+(δ+16*u) by grind only)
      grind only
  have middle := upper 0 1 1 0
  have last := upper 0 0 0 1
  have summed : 16*t^2≤25*n3 := by
    have plus := upper (4*t) (4*t) (4*t) 5
    have minus := positive (4*t) (4*t) (4*t) (-5)
    have diff : value q (4*t) (4*t) (4*t) 5-
        value q (4*t) (4*t) (4*t) (-5)=80*t^2 := by
      unfold value t
      grind only
    have d : diagonal n0 n1 n2 n3 (4*t) (4*t) (4*t) 5=16*t^2*(1-n3)+25*n3 := by
      unfold diagonal
      grind only
    rw [d] at plus
    have h := OrderedRing.mul_nonneg tailPos (squareNonnegative t)
    grind only
  have tailCross : 8*t≤5*E := by
    by_cases h : 8*t≤5*E
    · exact h
    · have bad := OrderedRing.mul_pos (show 0<8*t-5*E by grind only) (show 0<8*t+5*E by grind only)
      grind only
  have tailLinear := OrderedRing.mul_nonneg nonnegative (show 0≤2-E by grind only)
  simp only [value,diagonal] at middle last ⊢
  unfold s δ u at anchor
  unfold t at tailCross
  grind only

end RankSeven.SharedExteriorStability

#print axioms RankSeven.SharedExteriorStability.atMostFourColors
#print axioms RankSeven.SharedExteriorStability.colorMass
#print axioms RankSeven.SharedExteriorStability.quadraticPrice
