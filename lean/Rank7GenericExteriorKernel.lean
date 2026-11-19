import Rank7ExteriorPauliBase
import Rank7HyperplaneIncidence
import Rank7PlaneOrientation

/-! Signed four-wedge Pauli averages in arbitrary binary dimension.
The generator order is (origin, origin+a, origin+b, origin+a+b). -/
namespace RankSeven.GenericExteriorKernel

open RankSeven.Pauli RankSeven.HyperplaneIncidence RankSeven.ExteriorPauliBase Lean.Grind

def position {α : Type} (u : Four α) (j : Fin 4) : α :=
  match j.val with
  | 0 => u.1.1
  | 1 => u.1.2
  | 2 => u.2.1
  | _ => u.2.2

def reorder {α : Type} (u : Four α) (p : Permutation) : Four α :=
  ((position u p.1.1, position u p.1.2), (position u p.2.1, position u p.2.2))

private theorem four_cases : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide

def parity {n : Nat} (u : Four (Basis n)) : Basis n :=
  xorBasis n (xorBasis n u.1.1 u.1.2) (xorBasis n u.2.1 u.2.2)

def sameShift {n : Nat} (u v : Four (Basis n)) : Prop :=
  let t := xorBasis n u.1.1 v.1.1
  t = xorBasis n u.1.2 v.1.2 ∧ t = xorBasis n u.2.1 v.2.1 ∧ t = xorBasis n u.2.2 v.2.2

private theorem one_bit_support (a b c d e f g h : Bool) :
    allowedBit ((a,b),(c,d)) ((e,f),(g,h)) = true ↔
    ((a ^^ b) ^^ (c ^^ d)) = false ∧
    (a ^^ e) = (b ^^ f) ∧ (a ^^ e) = (c ^^ g) ∧ (a ^^ e) = (d ^^ h) := by
  revert a b c d e f g h; decide

theorem allowed_iff_parity_shift {n : Nat} (u v : Four (Basis n)) :
    allowedTwirlEntry n u v = true ↔ parity u = zero n ∧ sameShift u v := by
  induction n with
  | zero => simp [allowedTwirlEntry, parity, xorBasis, zero, sameShift]; rfl
  | succ n ih =>
    rw [allowedTwirlEntry, Bool.and_eq_true_iff, ih]
    change (allowedBit ((_,_),(_,_)) ((_,_),(_,_)) = true ∧ _) ↔ _
    rw [one_bit_support]
    simp only [parity, sameShift, remainingBits, xorBasis, zero]
    grind only

private theorem xor_self {n : Nat} (a : Basis n) : xorBasis n a a = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorBasis,zero,ih]; rfl

private theorem xor_zero {n : Nat} (a : Basis n) : xorBasis n a (zero n) = a := by
  induction n with
  | zero => cases a; rfl
  | succ n ih => simp [xorBasis,zero,ih]; rfl

private theorem xor_comm {n : Nat} (a b : Basis n) : xorBasis n a b = xorBasis n b a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xorBasis, Bool.xor_comm a.1 b.1, ih a.2 b.2]; rfl

private theorem xor_pair_shift {n : Nat} (s a b : Basis n) :
    xorBasis n (xorBasis n s a) (xorBasis n s b) = xorBasis n a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have bitLaw : ∀ x y z : Bool, ((x ^^ y) ^^ (x ^^ z)) = (y ^^ z) := by decide
    simp only [xorBasis, ih s.2 a.2 b.2, bitLaw]; rfl

private theorem xor_eq_zero {n : Nat} (a b : Basis n) : xorBasis n a b = zero n ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg (xorBasis n a) h
    simpa only [xorCancelLeft,xor_zero] using hc.symm
  · rintro rfl; exact xor_self _

/-- Here the common shift is an actual translation of the four labelled sites. -/
theorem allowed_iff_translation {n : Nat} (u v : Four (Basis n)) :
    allowedTwirlEntry n u v = true ↔ parity u = zero n ∧
      ∃ t : Basis n, ∀ k : Fin 4, position v k = xorBasis n t (position u k) := by
  rw [allowed_iff_parity_shift]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    let t := xorBasis n u.1.1 v.1.1
    have fix (a b : Basis n) (h : t = xorBasis n a b) : b = xorBasis n t a := by
      rw [h, xor_comm _ a, xorCancelLeft]
    refine ⟨t, fun k => ?_⟩
    rcases four_cases k with h|h|h|h <;> subst k
    · exact fix _ _ rfl
    · exact fix _ _ h₁
    · exact fix _ _ h₂
    · exact fix _ _ h₃
  · rintro ⟨t,h⟩
    have atK (k : Fin 4) : xorBasis n (position u k) (position v k) = t := by
      rw [h, xor_comm t, xorCancelLeft]
    exact ⟨(atK 0).trans (atK 1).symm, (atK 0).trans (atK 2).symm, (atK 0).trans (atK 3).symm⟩

def indexXor (a b : Fin 4) : Fin 4 := Fin.ofNat 4 (a.val ^^^ b.val)
def shiftPermutation (k : Fin 4) : Permutation :=
  ((k, indexXor 1 k), (indexXor 2 k, indexXor 3 k))

private def paramBit (x a b : Bool) (i : Fin 4) : Bool :=
  position ((x, x ^^ a), (x ^^ b, (x ^^ a) ^^ b)) i

def planePoint : (n : Nat) → Basis n → Basis n → Basis n → Fin 4 → Basis n
  | 0, _, _, _, _ => ()
  | n+1, x, a, b, i => (paramBit x.1 a.1 b.1 i, planePoint n x.2 a.2 b.2 i)

private theorem param_bit_difference : ∀ (x y a b : Bool) (p q : Fin 4),
    (paramBit x a b p ^^ paramBit y a b q) = paramBit (x ^^ y) a b (indexXor p q) := by decide

theorem planePoint_difference {n : Nat} (x y a b : Basis n) (p q : Fin 4) :
    xorBasis n (planePoint n x a b p) (planePoint n y a b q) =
      planePoint n (xorBasis n x y) a b (indexXor p q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorBasis,planePoint,param_bit_difference,ih x.2 y.2 a.2 b.2]; rfl

private theorem coordinates {n : Nat} (x a b : Basis n) :
    planePoint n x a b 0 = x ∧ planePoint n x a b 1 = xorBasis n x a ∧
    planePoint n x a b 2 = xorBasis n x b ∧
    planePoint n x a b 3 = xorBasis n (xorBasis n x a) b := by
  induction n with
  | zero => cases x; exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨h₀,h₁,h₂,h₃⟩ := ih x.2 a.2 b.2
    simp only [planePoint,paramBit,position,xorBasis,h₀,h₁,h₂,h₃]
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem position_planeFrame {n : Nat} (x a b : Basis n) (k : Fin 4) :
    position (affinePlaneFrame x a b) k = planePoint n x a b k := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := coordinates x a b
  rcases four_cases k with h|h|h|h <;> subst k
  · exact h₀.symm
  · exact h₁.symm
  · exact h₂.symm
  · exact h₃.symm

private theorem planePoint_injective {n : Nat} (x a b : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a ≠ b)
    (p q : Fin 4) (h : planePoint n x a b p = planePoint n x a b q) : p = q := by
  have hz : planePoint n (zero n) a b (indexXor p q) = zero n := by
    calc
      _ = planePoint n (xorBasis n x x) a b (indexXor p q) := by rw [xor_self]
      _ = xorBasis n (planePoint n x a b p) (planePoint n x a b q) := (planePoint_difference _ _ _ _ _ _).symm
      _ = zero n := by rw [h, xor_self]
  obtain ⟨h₀,h₁,h₂,h₃⟩ := coordinates (zero n) a b
  have za : xorBasis n (zero n) a = a := (xor_comm _ _).trans (xor_zero _)
  have zb : xorBasis n (zero n) b = b := (xor_comm _ _).trans (xor_zero _)
  rw [za] at h₁ h₃
  rw [zb] at h₂
  have ind : indexXor p q = 0 := by
    rcases four_cases (indexXor p q) with c|c|c|c
    · exact c
    · rw [c,h₁] at hz; contradiction
    · rw [c,h₂] at hz; contradiction
    · rw [c,h₃] at hz; exact False.elim (hab ((xor_eq_zero a b).mp hz))
  have cancel : ∀ (i j : Fin 4), indexXor i j = 0 → i=j := by decide
  exact cancel p q ind

private theorem indexConditions (p : Permutation) :
    ((indexXor 0 p.1.1 = indexXor 1 p.1.2) ∧
     (indexXor 0 p.1.1 = indexXor 2 p.2.1) ∧
     (indexXor 0 p.1.1 = indexXor 3 p.2.2)) ↔ p = shiftPermutation p.1.1 := by
  rcases p with ⟨⟨w,x⟩,y,z⟩; revert w x y z; decide

theorem parallel_permutation_iff {n : Nat} (x y a b : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a ≠ b) (p : Permutation) :
    allowedTwirlEntry n (affinePlaneFrame x a b) (reorder (affinePlaneFrame y a b) p) = true ↔
      p = shiftPermutation p.1.1 := by
  have hp := ((allowed_iff_parity_shift _ _).mp (parallelPlaneAllowed x x a b)).1
  rw [allowed_iff_parity_shift, and_iff_right hp, ← indexConditions]
  have inj (k l : Fin 4) : planePoint n (xorBasis n x y) a b k = planePoint n (xorBasis n x y) a b l ↔ k = l :=
    ⟨planePoint_injective _ _ _ ha hb hab _ _, fun e => e ▸ rfl⟩
  let dif (k l : Fin 4) := xorBasis n (position (affinePlaneFrame x a b) k) (position (affinePlaneFrame y a b) l)
  change (dif 0 p.1.1 = dif 1 p.1.2 ∧ dif 0 p.1.1 = dif 2 p.2.1 ∧ dif 0 p.1.1 = dif 3 p.2.2) ↔ _
  have delta (k l : Fin 4) : dif k l = planePoint n (xorBasis n x y) a b (indexXor k l) := by
    dsimp [dif]; rw [position_planeFrame,position_planeFrame,planePoint_difference]
  simp only [delta,inj]

def signed {C : Type} [CommRing C] (b : Bool) (x : C) : C := if b then -x else x

/-- The ordinary determinant of the four-by-four minor of a single Pauli
word. Its row and column tuples explicitly specify the chosen orientations. -/
def wordMinor {C : Type} [CommRing C] {n : Nat} (i : C) (w : Word n) (u v : Four (Basis n)) : C :=
  sumOver permutations fun p =>
    signed (oddPermutation p) (tensorFour (wordEntry i w) u (reorder v p))

def exteriorKernel {C : Type} [CommRing C] {n : Nat} (i half : C) (u v : Four (Basis n)) : C :=
  half^(n+n) * sumOver (words n) (fun w => wordMinor i w u v)

private theorem sumSigned {C α : Type} [CommRing C] (b : Bool) (xs : List α) (f : α → C) :
    sumOver xs (fun a => signed b (f a)) = signed b (sumOver xs f) := by
  induction xs with
  | nil => cases b <;> simp [sumOver,signed] <;> grind
  | cons x xs ih =>
    cases b <;> simp [sumOver,signed] at * <;> grind

theorem kernel_as_signed_translations {C : Type} [CommRing C] {n : Nat}
    (i half : C) (hi : i^4=1) (hhalf : 2*half=1) (u v : Four (Basis n)) :
    exteriorKernel i half u v = sumOver permutations (fun p =>
      if allowedTwirlEntry n u (reorder v p) then signed (oddPermutation p) (half^n) else 0) := by
  unfold exteriorKernel wordMinor
  rw [sumOverSwap (words n) permutations, sumOverMulLeft]
  apply sumOverCongr
  intro p
  rw [sumSigned]
  have normalize := normalizedTwirlEntry i half hi hhalf u (reorder v p)
  unfold unnormalizedTwirl at normalize
  cases h : allowedTwirlEntry n u (reorder v p) <;> cases oddPermutation p <;>
    simp [h,signed] at * <;> grind

def isShift (p : Permutation) : Bool := p == shiftPermutation p.1.1

theorem four_even_shifts :
    permutations.filter isShift = [shiftPermutation 0,shiftPermutation 1,shiftPermutation 2,shiftPermutation 3] ∧
    ∀ k : Fin 4, oddPermutation (shiftPermutation k) = false := by decide

private theorem sumIndicator {C α : Type} [CommRing C] (xs : List α) (b : α → Bool) (f : α → C) :
    sumOver xs (fun x => if b x then f x else 0) = sumOver (xs.filter b) f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : b x <;> simp [h,sumOver] at * <;> grind

private theorem sumOnShifts {C : Type} [CommRing C] (q : C) :
    sumOver permutations (fun p => if isShift p then signed (oddPermutation p) q else 0) = 4*q := by
  rw [sumIndicator, four_even_shifts.1]
  simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,four_even_shifts.2,signed]
  grind

/-- The normalized physical average for two plane wedges with the same
ordered pair of independent generators, in any ambient number of qubits. -/
theorem parallel_exterior_kernel {C : Type} [CommRing C] {n : Nat} (i half : C)
    (hi : i^4=1) (hhalf : 2*half=1) (x y a b : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a≠b) :
    exteriorKernel i half (affinePlaneFrame x a b) (affinePlaneFrame y a b) = 4*half^n := by
  rw [kernel_as_signed_translations _ _ hi hhalf, ← sumOnShifts]
  apply sumOverCongr
  intro p
  have h := parallel_permutation_iff x y a b ha hb hab p
  simp only [isShift, beq_iff_eq, h]

private theorem zero_sum {C α : Type} [CommRing C] (xs : List α) (f : α → C) (h : ∀ x ∈ xs, f x=0) :
    sumOver xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change f a + sumOver xs f = 0
    rw [h _ (by simp), ih (by intro x hx; exact h x (by simp [hx]))]
    grind

theorem nonplane_exterior_kernel {C : Type} [CommRing C] {n : Nat} (i half : C)
    (hi : i^4=1) (hhalf : 2*half=1) (u v : Four (Basis n)) (hu : parity u ≠ zero n) :
    exteriorKernel i half u v = 0 := by
  rw [kernel_as_signed_translations _ _ hi hhalf]
  apply zero_sum
  intro p _
  split
  next h => exact False.elim (hu ((allowed_iff_parity_shift _ _).mp h).1)
  next => rfl

theorem position_reorder {α : Type} (u : Four α) (p : Permutation) (k : Fin 4) :
    position (reorder u p) k = position u (position p k) := by
  rcases four_cases k with h|h|h|h <;> subst k <;> rfl

private theorem permutation_onto (p : Permutation) (hp : p ∈ permutations) :
    ∀ k : Fin 4, ∃ j : Fin 4, position p j = k := by
  have all : ∀ a b c d : Fin 4, distinct ((a,b),(c,d)) = true →
      ∀ k : Fin 4, ∃ j : Fin 4, position ((a,b),(c,d)) j = k := by decide
  exact all _ _ _ _ (List.mem_filter.mp hp).2

def directionMember {n : Nat} (u : Four (Basis n)) (d : Basis n) : Prop :=
  ∃ j k : Fin 4, xorBasis n (position u j) (position u k) = d

private theorem reorder_direction {n : Nat} (v : Four (Basis n)) (p : Permutation)
    (hp : p ∈ permutations) (d : Basis n) : directionMember (reorder v p) d ↔ directionMember v d := by
  constructor
  · rintro ⟨j,k,h⟩
    exact ⟨position p j, position p k, by simpa only [position_reorder] using h⟩
  · rintro ⟨j,k,h⟩
    obtain ⟨j',hj⟩ := permutation_onto p hp j
    obtain ⟨k',hk⟩ := permutation_onto p hp k
    exact ⟨j',k',by simpa only [position_reorder,hj,hk] using h⟩

theorem allowed_same_directions {n : Nat} (u v : Four (Basis n)) (p : Permutation)
    (hp : p ∈ permutations) (h : allowedTwirlEntry n u (reorder v p) = true) (d : Basis n) :
    directionMember u d ↔ directionMember v d := by
  obtain ⟨s, hs⟩ := ((allowed_iff_translation _ _).mp h).2
  rw [← reorder_direction v p hp d]
  unfold directionMember
  simp only [hs,xor_pair_shift]

/-- Vanishing for different directions, expressed entirely by differences
of the four input sites and valid for arbitrary orientations. -/
theorem nonparallel_exterior_kernel {C : Type} [CommRing C] {n : Nat} (i half : C)
    (hi : i^4=1) (hhalf : 2*half=1) (u v : Four (Basis n))
    (different : ¬ ∀ d, directionMember u d ↔ directionMember v d) :
    exteriorKernel i half u v = 0 := by
  rw [kernel_as_signed_translations _ _ hi hhalf]
  apply zero_sum
  intro p hp
  split
  next h => exact False.elim (different (allowed_same_directions u v p hp h))
  next => rfl

/-- Differences of points in one plane give precisely its binary
two-generator span, independently of the origin. -/
theorem frame_direction_members {n : Nat} (x a b d : Basis n) :
    directionMember (affinePlaneFrame x a b) d ↔
      d = zero n ∨ d = a ∨ d = b ∨ d = xorBasis n a b := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := coordinates (zero n) a b
  have za : xorBasis n (zero n) a = a := (xor_comm _ _).trans (xor_zero _)
  have zb : xorBasis n (zero n) b = b := (xor_comm _ _).trans (xor_zero _)
  rw [za] at h₁ h₃
  rw [zb] at h₂
  unfold directionMember
  simp only [position_planeFrame,planePoint_difference,xor_self]
  constructor
  · rintro ⟨j,k,h⟩
    rcases four_cases (indexXor j k) with e|e|e|e <;> rw [e] at h <;> grind
  · intro h
    rcases h with rfl|rfl|rfl|rfl
    · exact ⟨0,0,h₀⟩
    · exact ⟨0,1,h₁⟩
    · exact ⟨0,2,h₂⟩
    · exact ⟨0,3,h₃⟩

private def mapFour {α β : Type} (f : α → β) (u : Four α) : Four β :=
  ((f u.1.1, f u.1.2), (f u.2.1, f u.2.2))

private theorem map_position {α β : Type} (f : α → β) (u : Four α) (k : Fin 4) :
    f (position u k) = position (mapFour f u) k := by
  rcases four_cases k with h|h|h|h <;> subst k <;> rfl

private theorem map_reorder {α β : Type} (f : α → β) (u : Four α) (p : Permutation) :
    mapFour f (reorder u p) = reorder (mapFour f u) p := by
  unfold mapFour reorder
  rw [map_position f u p.1.1,map_position f u p.1.2,map_position f u p.2.1,map_position f u p.2.2]
  rfl

private def bitParity (u : Four Bool) := (u.1.1 ^^ u.1.2) ^^ (u.2.1 ^^ u.2.2)
private theorem bitParity_reorder (u : Four Bool) (p : Permutation) (hp : distinct p = true) :
    bitParity (reorder u p) = bitParity u := by
  rcases u with ⟨⟨a,b⟩,c,d⟩; rcases p with ⟨⟨j,k⟩,l,h⟩
  revert hp; revert a b c d j k l h; decide

theorem parity_reorder {n : Nat} (u : Four (Basis n)) (p : Permutation) (hp : p ∈ permutations) :
    parity (reorder u p) = parity u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Four (Bool × Basis n) at u
    change (bitParity (mapFour Prod.fst (reorder u p)), parity (mapFour Prod.snd (reorder u p))) =
      (bitParity (mapFour Prod.fst u), parity (mapFour Prod.snd u))
    rw [map_reorder Prod.fst u p,map_reorder Prod.snd u p,bitParity_reorder _ _ (List.mem_filter.mp hp).2,ih]

private theorem parity_shift {n : Nat} (s : Basis n) (u v : Four (Basis n))
    (h : ∀ k, position v k = xorBasis n s (position u k)) : parity v = parity u := by
  change xorBasis n (xorBasis n (position v 0) (position v 1)) (xorBasis n (position v 2) (position v 3)) = _
  rw [h,h,h,h,xor_pair_shift,xor_pair_shift]
  rfl

theorem nonplane_right_exterior_kernel {C : Type} [CommRing C] {n : Nat} (i half : C)
    (hi : i^4=1) (hhalf : 2*half=1) (u v : Four (Basis n)) (hv : parity v ≠ zero n) :
    exteriorKernel i half u v = 0 := by
  rw [kernel_as_signed_translations _ _ hi hhalf]
  apply zero_sum
  intro p hp
  split
  next h =>
    obtain ⟨hu,s,hs⟩ := (allowed_iff_translation _ _).mp h
    exact False.elim (hv ((parity_reorder v p hp).symm.trans ((parity_shift s u _ hs).trans hu)))
  next => rfl

private theorem simultaneous_reorder {n : Nat} (u v : Four (Basis n)) (p : Permutation)
    (hp : p ∈ permutations) :
    allowedTwirlEntry n (reorder u p) (reorder v p) = allowedTwirlEntry n u v := by
  apply Bool.eq_iff_iff.mpr
  rw [allowed_iff_translation,allowed_iff_translation,parity_reorder u p hp]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨s,fun k => ?_⟩
    obtain ⟨j,e⟩ := permutation_onto p hp k
    simpa only [position_reorder,e] using hs j
  · rintro ⟨s,hs⟩
    exact ⟨s,fun k => by simpa only [position_reorder] using hs (position p k)⟩

private theorem reorder_compose {α : Type} (u : Four α) (p s : Permutation) :
    reorder (reorder u p) s = reorder u (reorder p s) := by
  change ((position (reorder u p) _,position (reorder u p) _),
          (position (reorder u p) _,position (reorder u p) _)) = _
  simp only [position_reorder]; rfl

private theorem permutation_table : permutations.all (fun s =>
    decide ((permutations.map (reorder s)).Perm permutations) &&
    decide ((permutations.map (fun p => reorder p s)).Perm permutations) &&
    permutations.all (fun p => oddPermutation (reorder s p) == (oddPermutation s ^^ oddPermutation p))) = true := by
  decide

private theorem perm_facts (s : Permutation) (hs : s ∈ permutations) :
    (permutations.map (reorder s)).Perm permutations ∧
    (permutations.map (fun p => reorder p s)).Perm permutations ∧
    ∀ p ∈ permutations, oddPermutation (reorder s p) = (oddPermutation s ^^ oddPermutation p) := by
  have h := List.all_eq_true.mp permutation_table s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

private theorem perm_sum {C α : Type} [CommRing C] {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem reindex {C : Type} [CommRing C] (g : Permutation → Permutation)
    (hg : (permutations.map g).Perm permutations) (f : Permutation → C) :
    sumOver permutations f = sumOver permutations (fun p => f (g p)) := by
  simpa only [sumOver,List.map_map,Function.comp_def] using (perm_sum hg f).symm

private theorem sum_congr_mem {C α : Type} [CommRing C] (xs : List α) {f g : α → C}
    (h : ∀ a ∈ xs, f a=g a) : sumOver xs f = sumOver xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem signed_xor {C : Type} [CommRing C] (a b : Bool) (q : C) :
    signed (a ^^ b) q = signed a (signed b q) := by
  cases a <;> cases b <;> simp [signed] <;> grind

private def weight {C : Type} [CommRing C] {n : Nat} (q : C) (u v : Four (Basis n)) (p : Permutation) : C :=
  signed (oddPermutation p) (if allowedTwirlEntry n u (reorder v p) then q else 0)

private theorem kernel_weight {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n)) :
    exteriorKernel i half u v = sumOver permutations (weight (half^n) u v) := by
  rw [kernel_as_signed_translations _ _ hi hhalf]
  apply sumOverCongr
  intro p
  unfold weight
  cases allowedTwirlEntry n u (reorder v p) <;> cases oddPermutation p <;> simp [signed] <;> grind

theorem kernel_reorder_left {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n)) (s : Permutation) (hs : s ∈ permutations) :
    exteriorKernel i half (reorder u s) v = signed (oddPermutation s) (exteriorKernel i half u v) := by
  rw [kernel_weight _ _ hi hhalf,kernel_weight _ _ hi hhalf,← sumSigned,
    reindex (fun p => reorder p s) (perm_facts s hs).2.1 (weight (half^n) (reorder u s) v)]
  apply sum_congr_mem
  intro p hp
  unfold weight
  rw [← reorder_compose, simultaneous_reorder _ _ _ hs,
    (perm_facts p hp).2.2 s hs, Bool.xor_comm, signed_xor]

theorem kernel_reorder_right {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n)) (s : Permutation) (hs : s ∈ permutations) :
    exteriorKernel i half u (reorder v s) = signed (oddPermutation s) (exteriorKernel i half u v) := by
  rw [kernel_weight _ _ hi hhalf,kernel_weight _ _ hi hhalf,← sumSigned,
    reindex (reorder s) (perm_facts s hs).1 (fun p => signed (oddPermutation s) (weight (half^n) u v p))]
  apply sum_congr_mem
  intro p hp
  unfold weight
  rw [reorder_compose,(perm_facts s hs).2.2 p hp,signed_xor]
  cases oddPermutation s <;> simp [signed] <;> grind

theorem kernel_reorder_equal_signs {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n)) (s t : Permutation)
    (hs : s ∈ permutations) (ht : t ∈ permutations) (equalSigns : oddPermutation s = oddPermutation t) :
    exteriorKernel i half (reorder u s) (reorder v t) = exteriorKernel i half u v := by
  rw [kernel_reorder_left _ _ hi hhalf _ _ _ hs,kernel_reorder_right _ _ hi hhalf _ _ _ ht,equalSigns]
  cases oddPermutation t <;> simp [signed] <;> grind

private theorem xor_assoc {n : Nat} (a b c : Basis n) :
    xorBasis n a (xorBasis n b c) = xorBasis n (xorBasis n a b) c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ x y z : Bool, (x ^^ (y ^^ z)) = ((x ^^ y) ^^ z) := by decide
    simp only [xorBasis,h,ih a.2 b.2 c.2]; rfl

theorem parity_zero_frame {n : Nat} (u : Four (Basis n)) (hu : parity u = zero n) :
    u = affinePlaneFrame u.1.1 (xorBasis n u.1.1 u.1.2) (xorBasis n u.1.1 u.2.1) := by
  rcases u with ⟨⟨p,q⟩,r,s⟩
  change xorBasis n (xorBasis n p q) (xorBasis n r s) = zero n at hu
  have opposite := (xor_eq_zero _ _).mp hu
  change ((p,q),(r,s)) = ((p,xorBasis n p (xorBasis n p q)),
    (xorBasis n p (xorBasis n p r), xorBasis n (xorBasis n p (xorBasis n p q)) (xorBasis n p r)))
  rw [xorCancelLeft,xorCancelLeft,xor_assoc,xor_comm q p,xor_comm (xorBasis n p q) r,
    opposite,xorCancelLeft]

private theorem translate_frame {n : Nat} (t x a b : Basis n) :
    PlaneOrientation.translate t (affinePlaneFrame x a b) = affinePlaneFrame (xorBasis n t x) a b := by
  unfold PlaneOrientation.translate affinePlaneFrame
  simp only [xor_assoc]

private theorem position_increasing {n : Nat} (u : Four (Basis n)) (ord : PlaneOrientation.Increasing u)
    (i j : Fin 4) (hij : i<j) :
    PlaneOrientation.label n (position u i) < PlaneOrientation.label n (position u j) := by
  obtain ⟨h₁,h₂,h₃⟩ := ord
  rcases four_cases i with h|h|h|h <;> subst i <;>
    rcases four_cases j with h|h|h|h <;> subst j <;> simp [position] at * <;> omega

/-- Canonical coordinate wedges: any admissible pairing of two increasing
four-tuples forces a pair of translates of the same genuine plane and has
positive normalized entry. The common generators are derived from the row. -/
theorem sorted_supported_kernel {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n))
    (ordU : PlaneOrientation.Increasing u) (ordV : PlaneOrientation.Increasing v)
    (p : Permutation) (hp : p ∈ permutations) (supported : allowedTwirlEntry n u (reorder v p) = true) :
    exteriorKernel i half u v = 4*half^n := by
  obtain ⟨hu,t,ht⟩ := (allowed_iff_translation _ _).mp supported
  let x := u.1.1
  let a := xorBasis n x u.1.2
  let b := xorBasis n x u.2.1
  have row : u = affinePlaneFrame x a b := parity_zero_frame u hu
  have translated : reorder v p = PlaneOrientation.translate t u := by
    exact Prod.ext (Prod.ext (ht 0) (ht 1)) (Prod.ext (ht 2) (ht 3))
  have rowPlane : PlaneOrientation.PlaneRelation u := (xor_eq_zero _ _).mp hu
  have even := PlaneOrientation.translatedSortedPermutationEven u ordU rowPlane
    (position v) (position_increasing v ordV) p t translated
  have ord := ordU
  obtain ⟨h₁,h₂,h₃⟩ := ord
  have ha : a ≠ zero n := by
    intro h
    have he : u.1.1 = u.1.2 := (xor_eq_zero _ _).mp h
    rw [he] at h₁; omega
  have hb : b ≠ zero n := by
    intro h
    have he : u.1.1 = u.2.1 := (xor_eq_zero _ _).mp h
    rw [he] at h₁; omega
  have hab : a≠b := by
    intro h
    have he := congrArg (xorBasis n x) h
    change xorBasis n x (xorBasis n x u.1.2) = xorBasis n x (xorBasis n x u.2.1) at he
    rw [xorCancelLeft,xorCancelLeft] at he
    rw [he] at h₂; omega
  have pairFrame : reorder v p = affinePlaneFrame (xorBasis n t x) a b := translated.trans
    ((congrArg (PlaneOrientation.translate t) row).trans (translate_frame t x a b))
  have lift := kernel_reorder_right i half hi hhalf u v p hp
  rw [even] at lift
  change exteriorKernel i half u (reorder v p) = exteriorKernel i half u v at lift
  calc
    _ = exteriorKernel i half u (reorder v p) := lift.symm
    _ = exteriorKernel i half (affinePlaneFrame x a b) (affinePlaneFrame (xorBasis n t x) a b) :=
      (congrArg (fun w => exteriorKernel i half w (reorder v p)) row).trans
        (congrArg (exteriorKernel i half (affinePlaneFrame x a b)) pairFrame)
    _ = _ := parallel_exterior_kernel i half hi hhalf _ _ a b ha hb hab

/-- This executable test searches the 24 signed assignments without a
dimension bound or a preselected representation of the plane directions. -/
def supportedPair {n : Nat} (u v : Four (Basis n)) : Bool :=
  permutations.any (fun p => allowedTwirlEntry n u (reorder v p))

theorem sorted_kernel_entry {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1)
    (hhalf : 2*half=1) (u v : Four (Basis n)) (ordU : PlaneOrientation.Increasing u)
    (ordV : PlaneOrientation.Increasing v) :
    exteriorKernel i half u v = if supportedPair u v then 4*half^n else 0 := by
  cases h : supportedPair u v with
  | true =>
    obtain ⟨p,hp,he⟩ := List.any_eq_true.mp h
    exact sorted_supported_kernel i half hi hhalf u v ordU ordV p hp he
  | false =>
    rw [kernel_as_signed_translations _ _ hi hhalf]
    apply zero_sum
    intro p hp
    split
    next he =>
      have ht : supportedPair u v = true := List.any_eq_true.mpr ⟨p,hp,he⟩
      simp_all
    next => rfl

end RankSeven.GenericExteriorKernel
