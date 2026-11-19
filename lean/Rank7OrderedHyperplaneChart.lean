import Rank7GenericExteriorKernel

/-! Ordered affine charts for the computational basis. Delete the least significant
nonzero coordinate of the normal. If the normal is zero, use the most significant
coordinate as a fallback to keep the chart maps total. -/

namespace RankSeven.OrderedHyperplaneChart

open RankSeven.Pauli RankSeven.HyperplaneIncidence RankSeven.PlaneOrientation

/-- Insert the missing pivot bit, adjusting the required offset as earlier bits
are read. The first bit of a recursive basis is the most significant one. -/
def site : {n : Nat} → HyperplaneCode (n+1) → Basis n → Basis (n+1)
  | 0, (_,b), _ => (b,())
  | n+1, ((a,v),b), x =>
    if isZero (n+1) v then (b,x)
    else (x.1, site (v, b ^^ (a && x.1)) x.2)

/-- Delete the same pivot. Its position depends only on the normal. -/
def unsite : {n : Nat} → HyperplaneCode (n+1) → Basis (n+1) → Basis n
  | 0, _, _ => ()
  | n+1, ((_,v),b), (c,x) =>
    if isZero (n+1) v then x else (c, unsite (v,b) x)

private theorem unsiteOffset {n : Nat} (v : Basis (n+1)) (b t : Bool) (x : Basis (n+1)) :
    unsite (v,b) x = unsite (v,t) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨a,v⟩; rcases x with ⟨c,x⟩
    simp only [unsite]
    cases hv : isZero (n+1) v
    · exact congrArg (fun w => (c,w)) (ih v x)
    · rfl

theorem unsiteSite {n : Nat} (H : HyperplaneCode (n+1)) (x : Basis n) :
    unsite H (site H x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases H with ⟨⟨a,v⟩,b⟩; rcases x with ⟨c,x⟩
    cases hv : isZero (n+1) v
    · simp [site,unsite,hv]
      exact congrArg (fun w => (c,w)) ((unsiteOffset v b (b ^^ (a && c)) _).trans (ih _ x))
    · simp [site,unsite,hv] <;> rfl

theorem siteInjective {n : Nat} (H : HyperplaneCode (n+1)) {x y : Basis n}
    (e : site H x = site H y) : x=y := by
  simpa only [unsiteSite] using congrArg (unsite H) e

private theorem cancelBit (a b : Bool) : (a ^^ (b ^^ a)) = b := by revert a b; decide

theorem siteIn {n : Nat} (H : HyperplaneCode (n+1)) (proper : H.1 ≠ zero (n+1))
    (x : Basis n) : contains H (site H x) = true := by
  apply beq_iff_eq.mpr
  change dot (n+1) H.1 (site H x) = H.2
  induction n with
  | zero =>
    rcases H with ⟨⟨a,⟨⟩⟩,b⟩
    cases a
    · exact False.elim (proper rfl)
    · simp [site,dot]
  | succ n ih =>
    rcases H with ⟨⟨a,v⟩,b⟩; rcases x with ⟨c,x⟩
    cases hv : isZero (n+1) v
    · have ne : v ≠ zero (n+1) := by
        intro e; have := (isZero_iff _ v).mpr e; simp_all
      simp [site,hv,dot]
      have sub := ih (v,b ^^ (a && c)) ne x
      change dot (n+1) v (site (v,b ^^ (a && c)) x) = (b ^^ (a && c)) at sub
      rw [sub]; exact cancelBit _ _
    · obtain rfl := (isZero_iff _ v).mp hv
      cases a
      · exact False.elim (proper rfl)
      · simp [site,hv,dot]
        rw [dotZero (n+1) (c,x),Bool.xor_false]

theorem siteUnsite {n : Nat} (H : HyperplaneCode (n+1)) (proper : H.1 ≠ zero (n+1))
    (y : Basis (n+1)) (inside : contains H y = true) :
    site H (unsite H y) = y := by
  have e := beq_iff_eq.mp inside
  change dot (n+1) H.1 y = H.2 at e
  clear inside
  induction n with
  | zero =>
    rcases H with ⟨⟨a,⟨⟩⟩,b⟩; rcases y with ⟨c,⟨⟩⟩
    cases a
    · exact False.elim (proper rfl)
    · simp [dot] at e; subst b; rfl
  | succ n ih =>
    rcases H with ⟨⟨a,v⟩,b⟩; rcases y with ⟨c,y⟩
    cases hv : isZero (n+1) v
    · have ne : v ≠ zero (n+1) := by
        intro h; have := (isZero_iff _ v).mpr h; simp_all
      change ((a && c) ^^ dot (n+1) v y) = b at e
      have e' : dot (n+1) v y = (b ^^ (a && c)) := by
        rw [← e]; cases (a && c) <;> cases dot (n+1) v y <;> rfl
      simp [site,unsite,hv]
      rw [unsiteOffset v b (b ^^ (a && c))]
      exact congrArg (fun w => (c,w)) (ih (v,b ^^ (a && c)) ne y e')
    · obtain rfl := (isZero_iff _ v).mp hv
      cases a
      · exact False.elim (proper rfl)
      · simp [dot,dotZero] at e; subst b; simp [site,unsite,hv] <;> rfl

theorem inRangeIff {n : Nat} (H : HyperplaneCode (n+1)) (proper : H.1 ≠ zero (n+1))
    (y : Basis (n+1)) : (∃ x, site H x = y) ↔ contains H y = true := by
  exact ⟨fun ⟨x,e⟩ => e ▸ siteIn H proper x,
    fun h => ⟨unsite H y,siteUnsite H proper y h⟩⟩

private theorem siteInverted {n : Nat} (H : HyperplaneCode (n+1)) (x y : Basis n) :
    inverted (n+1) (site H x) (site H y) = inverted n x y := by
  induction n with
  | zero => rcases H with ⟨v,b⟩; simp [site,inverted]
  | succ n ih =>
    rcases H with ⟨⟨a,v⟩,b⟩; rcases x with ⟨c,x⟩; rcases y with ⟨d,y⟩
    cases hv : isZero (n+1) v
    · cases e : c == d
      · have ne : c ≠ d := by simpa using e
        simp [site,hv,inverted,ne]
      · obtain rfl := beq_iff_eq.mp e
        simpa [site,hv,inverted] using ih (v,b ^^ (a && c)) x y
    · simp [site,hv,inverted] <;> rfl

/-- Both preservation and reflection of the integer labels used to sort wedges. -/
theorem siteLtIff {n : Nat} (H : HyperplaneCode (n+1)) (x y : Basis n) :
    label (n+1) (site H x) < label (n+1) (site H y) ↔ label n x < label n y := by
  rw [←inverted_iff,←inverted_iff,siteInverted]

private theorem offsetBit (a b c s t : Bool) :
    (s != (t != (a && (b ^^ c)))) = ((s ^^ (a && b)) ^^ (t ^^ (a && c))) := by
  revert a b c s t; decide

/-- Two cosets add to the XOR-offset coset by the same parametrization. -/
theorem siteXorOffsets {n : Nat} (v : Basis (n+1)) (s t : Bool) (x y : Basis n) :
    site (v,s ^^ t) (xorBasis n x y) =
      xorBasis (n+1) (site (v,s) x) (site (v,t) y) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨a,v⟩; rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    cases hv : isZero (n+1) v
    · simp [site,hv,xorBasis]
      rw [offsetBit]
      exact congrArg (fun w : Basis (n+1) => (b ^^ c,w))
        (ih v (s ^^ (a && b)) (t ^^ (a && c)) x y)
    · simp [site,hv,xorBasis] <;> rfl

theorem siteTriple {n : Nat} (H : HyperplaneCode (n+1)) (x y z : Basis n) :
    site H (xorBasis n x (xorBasis n y z)) =
      xorBasis (n+1) (site H x) (xorBasis (n+1) (site H y) (site H z)) := by
  rcases H with ⟨v,b⟩
  rw [←siteXorOffsets,←siteXorOffsets]
  simp

/-- Coordinates of the direction map. For a proper normal, these are exactly
the translations preserving the hyperplane. -/
def direction {n : Nat} (H : HyperplaneCode (n+1)) (x : Basis n) : Basis (n+1) :=
  site (H.1,false) x

theorem siteDifference {n : Nat} (H : HyperplaneCode (n+1)) (x y : Basis n) :
    xorBasis (n+1) (site H x) (site H y) = direction H (xorBasis n x y) := by
  rcases H with ⟨v,b⟩
  simpa [direction] using (siteXorOffsets v b b x y).symm

theorem siteTranslation {n : Nat} (H : HyperplaneCode (n+1)) (t x : Basis n) :
    site H (xorBasis n t x) = xorBasis (n+1) (direction H t) (site H x) := by
  rcases H with ⟨v,b⟩
  simpa [direction] using siteXorOffsets v false b t x

theorem directionEqIff {n : Nat} (H : HyperplaneCode (n+1)) (x y : Basis n) :
    direction H x = direction H y ↔ x=y :=
  ⟨siteInjective (H.1,false),congrArg (direction H)⟩

private theorem xorSelf (n : Nat) (x : Basis n) : xorBasis n x x = zero n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩; simp [xorBasis,zero,ih] <;> rfl

theorem directionZero {n : Nat} (H : HyperplaneCode (n+1)) :
    direction H (zero n) = zero (n+1) := by
  have e := siteDifference H (zero n) (zero n)
  simpa only [xorSelf] using e.symm

def siteFour {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n)) :
    Four (Basis (n+1)) :=
  ((site H u.1.1,site H u.1.2),(site H u.2.1,site H u.2.2))

theorem siteIncreasingIff {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n)) :
    Increasing (siteFour H u) ↔ Increasing u := by
  simp only [Increasing,siteFour,siteLtIff]

theorem siteSortingParity {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n)) :
    parity (siteFour H u) = parity u := by
  simp only [parity,inversionCount,siteFour,siteLtIff]

theorem sitePlaneIff {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n)) :
    PlaneRelation (siteFour H u) ↔ PlaneRelation u := by
  simp only [PlaneRelation,siteFour,siteDifference,directionEqIff]

theorem siteVectorParity {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n)) :
    GenericExteriorKernel.parity (siteFour H u) =
      direction H (GenericExteriorKernel.parity u) := by
  simp only [GenericExteriorKernel.parity,siteFour,siteDifference]
  exact (siteXorOffsets H.1 false false _ _).symm

theorem siteSameShiftIff {n : Nat} (H : HyperplaneCode (n+1)) (u v : Four (Basis n)) :
    GenericExteriorKernel.sameShift (siteFour H u) (siteFour H v) ↔
      GenericExteriorKernel.sameShift u v := by
  simp only [GenericExteriorKernel.sameShift,siteFour,siteDifference,directionEqIff]

/-- The physical fourth-copy twirl support bit is unchanged in chart coordinates. -/
theorem siteAllowed {n : Nat} (H : HyperplaneCode (n+1)) (u v : Four (Basis n)) :
    allowedTwirlEntry (n+1) (siteFour H u) (siteFour H v) = allowedTwirlEntry n u v := by
  have eq : allowedTwirlEntry (n+1) (siteFour H u) (siteFour H v) = true ↔
      allowedTwirlEntry n u v = true := by
    rw [GenericExteriorKernel.allowed_iff_parity_shift,GenericExteriorKernel.allowed_iff_parity_shift,
      siteSameShiftIff,siteVectorParity,←directionZero H,directionEqIff]
  cases p : allowedTwirlEntry (n+1) (siteFour H u) (siteFour H v) <;>
    cases q : allowedTwirlEntry n u v <;> simp_all

theorem siteReorder {n : Nat} (H : HyperplaneCode (n+1)) (u : Four (Basis n))
    (p : ExteriorPauliBase.Permutation) :
    GenericExteriorKernel.reorder (siteFour H u) p = siteFour H (GenericExteriorKernel.reorder u p) := by
  have pos (j : Fin 4) : GenericExteriorKernel.position (siteFour H u) j =
      site H (GenericExteriorKernel.position u j) := by
    rcases j with ⟨j,h⟩
    cases j with
    | zero => rfl
    | succ j => cases j with
      | zero => rfl
      | succ j => cases j <;> rfl
  simp only [GenericExteriorKernel.reorder,siteFour] at pos ⊢
  simp only [pos]

/-- The full support test over all determinant permutations gives the same answer
on the two sorted lists before and after the chart embedding. -/
theorem siteSupportedPair {n : Nat} (H : HyperplaneCode (n+1)) (u v : Four (Basis n)) :
    GenericExteriorKernel.supportedPair (siteFour H u) (siteFour H v) =
      GenericExteriorKernel.supportedPair u v := by
  simp only [GenericExteriorKernel.supportedPair,siteReorder,siteAllowed]

end RankSeven.OrderedHyperplaneChart
