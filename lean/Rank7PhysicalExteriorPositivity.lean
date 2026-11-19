import Rank7PhysicalExteriorCompression

/-! Positive semidefiniteness of the normalized physical exterior Pauli kernel. -/
namespace RankSeven.PhysicalExteriorPositivity

open Lean.Grind Pauli HyperplaneIncidence GenericExteriorKernel ExteriorPauliBase
open HyperplaneInduction PhysicalWedges

private theorem fourCases : ∀ k : Fin 4, k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by decide

private theorem composition (p s : Permutation) (hp : p∈permutations) (hs : s∈permutations) :
    reorder s p ∈ permutations := by
  have table : permutations.all (fun s => permutations.all (fun p => decide (reorder s p ∈ permutations))) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp table s hs) p hp)

private theorem inverse (p : Permutation) (hp : p∈permutations) :
    ∃ s∈permutations, ∀ k : Fin 4, position p (position s k)=k := by
  have table : permutations.all (fun p => permutations.any (fun s =>
    decide (∀ k : Fin 4, position p (position s k)=k))) = true := by decide
  obtain ⟨s,hs,h⟩ := List.any_eq_true.mp (List.all_eq_true.mp table p hp)
  exact ⟨s,hs,of_decide_eq_true h⟩

private theorem xorAssoc {n : Nat} (a b c : Basis n) :
    xorBasis n a (xorBasis n b c) = xorBasis n (xorBasis n a b) c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have bit : ∀ a b c : Bool, (a^^(b^^c))=((a^^b)^^c) := by decide
    simp only [xorBasis,bit,ih a.2 b.2 c.2]; rfl

private theorem xorPairs {n : Nat} (a b c : Basis n) :
    xorBasis n (xorBasis n a b) (xorBasis n a c) = xorBasis n b c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have bit : ∀ a b c : Bool, ((a^^b)^^(a^^c))=(b^^c) := by decide
    simp only [xorBasis,bit,ih a.2 b.2 c.2]; rfl

private theorem translatedParity {n : Nat} (u v : Four (Basis n)) (t : Basis n)
    (h : ∀ j : Fin 4, position v j=xorBasis n t (position u j)) : parity v=parity u := by
  change xorBasis n (xorBasis n (position v 0) (position v 1))
    (xorBasis n (position v 2) (position v 3))=_
  rw [h,h,h,h,xorPairs,xorPairs]; rfl

theorem supported_iff {n : Nat} (u v : Four (Basis n)) : supportedPair u v=true ↔
    parity u=zero n ∧ ∃ p∈permutations, ∃ t : Basis n,
      ∀ k : Fin 4, position v (position p k) = xorBasis n t (position u k) := by
  constructor
  · intro h
    obtain ⟨p,hp,allowed⟩ := List.any_eq_true.mp h
    obtain ⟨plane,t,he⟩ := (allowed_iff_translation _ _).mp allowed
    exact ⟨plane,p,hp,t,fun k => by simpa only [position_reorder] using he k⟩
  · rintro ⟨plane,p,hp,t,he⟩
    exact List.any_eq_true.mpr ⟨p,hp,(allowed_iff_translation _ _).mpr
      ⟨plane,t,fun k => by simpa only [position_reorder] using he k⟩⟩

theorem supportedSymm {n : Nat} {u v : Four (Basis n)} (h : supportedPair u v=true) :
    supportedPair v u=true := by
  obtain ⟨plane,p,hp,t,he⟩ := (supported_iff _ _).mp h
  obtain ⟨s,hs,undo⟩ := inverse p hp
  have par := translatedParity u (reorder v p) t (fun k => by rw [position_reorder,he])
  rw [parity_reorder _ _ hp,plane] at par
  refine (supported_iff _ _).mpr ⟨par,s,hs,t,fun k => ?_⟩
  have eq := he (position s k)
  rw [undo] at eq
  rw [eq,xorCancelLeft]

theorem supportedTrans {n : Nat} {u v w : Four (Basis n)}
    (uv : supportedPair u v=true) (vw : supportedPair v w=true) : supportedPair u w=true := by
  obtain ⟨plane,p,hp,t,ht⟩ := (supported_iff _ _).mp uv
  obtain ⟨_,s,hs,r,hr⟩ := (supported_iff _ _).mp vw
  refine (supported_iff _ _).mpr ⟨plane,reorder s p,composition p s hp hs,xorBasis n r t,fun k => ?_⟩
  rw [position_reorder,hr,ht,xorAssoc]

/-- Distinct labels occurring in the finite coordinate list. -/
def classLabels {α β : Type} [DecidableEq β] (tag : α → β) : List α → List β
  | [] => []
  | x::xs => let ks := classLabels tag xs
             if tag x ∈ ks then ks else tag x :: ks

private theorem labelFacts {α β : Type} [DecidableEq β] (tag : α → β) (xs : List α) :
    (classLabels tag xs).Nodup ∧ ∀ x∈xs, tag x ∈ classLabels tag xs := by
  induction xs with
  | nil => exact ⟨List.Pairwise.nil,fun _ h => by cases h⟩
  | cons a xs ih =>
    by_cases h : tag a ∈ classLabels tag xs
    · simp only [classLabels,ite_eq_left h]
      exact ⟨ih.1,fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ h) (ih.2 x)⟩
    · simp only [classLabels,ite_eq_right h]
      refine ⟨List.nodup_cons.mpr ⟨h,ih.1⟩,fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with eq|mem
      · subst x; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.2 x mem)

variable {R α β : Type} [CommRing R]

def classComponent [DecidableEq β] (tag : α → β) (active : α → Bool)
    (z : α → ComplexScalar R) (k : β) (u : α) : ComplexScalar R :=
  if active u=true ∧ tag u=k then z u else 0

private theorem splitWeight [DecidableEq β] (xs : List α) (tag : α → β) (active : α → Bool)
    (q : R) (z : α → ComplexScalar R) (u v : α) (hu : u∈xs) :
    realWeight z (u,v) * (if active u=true ∧ active v=true ∧ tag u=tag v then q else 0) =
      sumOver (classLabels tag xs) (fun k => realWeight (classComponent tag active z k) (u,v)*q) := by
  let f (k : β) := realWeight (classComponent tag active z k) (u,v)*q
  have value : sumOver (classLabels tag xs) f = f (tag u) := by
    calc
      _ = sumOver (classLabels tag xs) (fun k => if tag u=k then f k else 0) := by
        apply sumOverCongr
        intro k
        by_cases e : tag u=k
        · simp [e]
        · simp [f,realWeight,classComponent,e] <;> grind
      _ = _ := sumOnIndex _ _ f (labelFacts tag xs).1 ((labelFacts tag xs).2 u hu)
  change _ = sumOver _ f
  rw [value]
  by_cases eu : active u=true <;> by_cases ev : active v=true <;> by_cases eq : tag u=tag v
  all_goals first | (have reverse := Ne.symm eq; simp [eu,ev,eq,reverse,f,realWeight,classComponent] <;> grind) | (simp [eu,ev,eq,f,realWeight,classComponent] <;> grind)

private theorem factorClass (xs : List α) (z : α → ComplexScalar R) (q : R) :
    sumOver (productIndices xs xs) (fun uv => realWeight z uv*q) =
      ((sumOver xs (fun u => (z u).re))^2 + (sumOver xs (fun u => (z u).im))^2)*q := by
  rw [← sumOverMulRight]
  unfold realWeight
  rw [sumOverAdd,factorProductSum xs xs (fun u => (z u).re) (fun u => (z u).re),
    factorProductSum xs xs (fun u => (z u).im) (fun u => (z u).im)]
  grind

/-- A finite matrix equal to q on active matching labels has a quadratic
form equal to q times the sum of squared complex class amplitudes. -/
theorem classSquareSum [DecidableEq β] (xs : List α) (tag : α → β) (active : α → Bool)
    (q : R) (z : α → ComplexScalar R) :
    quadratic xs (fun uv => if active uv.1=true ∧ active uv.2=true ∧ tag uv.1=tag uv.2 then q else 0) z =
      sumOver (classLabels tag xs) (fun k =>
        ((sumOver xs (fun u => (classComponent tag active z k u).re))^2 +
         (sumOver xs (fun u => (classComponent tag active z k u).im))^2)*q) := by
  unfold quadratic
  calc
    _ = sumOver (productIndices xs xs) (fun uv => sumOver (classLabels tag xs)
        (fun k => realWeight (classComponent tag active z k) uv*q)) := by
      apply congrArg List.sum; apply List.map_congr_left
      rintro ⟨u,v⟩ member
      obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp member
      obtain ⟨_,_,he⟩ := List.mem_map.mp hm
      have eq : a=u := congrArg Prod.fst he
      exact splitWeight xs tag active q z u v (eq ▸ ha)
    _ = _ := by
      rw [sumOverSwap]; apply sumOverCongr; intro k; exact factorClass xs _ q

/-- The indicator row uniquely identifies the parallel-plane class of every
active coordinate. Every inactive coordinate has the zero row. -/
def planeClass {n : Nat} (u v : Coordinate n) : Bool := supportedPair u.val v.val

def activePlane {n : Nat} (u : Coordinate n) : Bool := planeClass u u

theorem supportedClass {n : Nat} (u v : Coordinate n) :
    supportedPair u.val v.val = true ↔ activePlane u=true ∧ activePlane v=true ∧ planeClass u=planeClass v := by
  constructor
  · intro yes
    have rev := supportedSymm yes
    refine ⟨supportedTrans yes rev,supportedTrans rev yes,?_⟩
    funext w
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun h => supportedTrans rev h,fun h => supportedTrans yes h⟩
  · rintro ⟨_,av,eq⟩
    exact (congrFun eq v).trans av

noncomputable local instance {n : Nat} : DecidableEq (Coordinate n → Bool) := Classical.typeDecidableEq _

theorem physicalClassSquareSum {n : Nat} (xs : List (Coordinate n)) (q : R)
    (z : Coordinate n → ComplexScalar R) :
    quadratic xs (fun uv => if supportedPair uv.1.val uv.2.val then q else 0) z =
      sumOver (classLabels planeClass xs) (fun k =>
        ((sumOver xs (fun u => (classComponent planeClass activePlane z k u).re))^2 +
         (sumOver xs (fun u => (classComponent planeClass activePlane z k u).im))^2)*q) := by
  have e : (fun uv : Coordinate n × Coordinate n => if supportedPair uv.1.val uv.2.val then q else 0) =
      (fun uv => if activePlane uv.1=true ∧ activePlane uv.2=true ∧ planeClass uv.1=planeClass uv.2 then q else 0) := by
    funext uv; simp only [supportedClass]
  rw [e]
  exact classSquareSum xs planeClass activePlane q z

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumNonnegative (xs : List α) (f : α → R) (h : ∀ x, 0 ≤ f x) : 0 ≤ sumOver xs f := by
  induction xs with
  | nil => change 0 ≤ (0:R); grind
  | cons x xs ih => change 0 ≤ f x + sumOver xs f; have := h x; grind

theorem supportedKernel_nonnegative {n : Nat} (xs : List (Coordinate n)) (q : R) (hq : 0 ≤ q)
    (z : Coordinate n → ComplexScalar R) :
    0 ≤ quadratic xs (fun uv => if supportedPair uv.1.val uv.2.val then q else 0) z := by
  rw [physicalClassSquareSum]
  apply sumNonnegative; intro k
  apply OrderedRing.mul_nonneg _ hq
  have hr := squareNonnegative (sumOver xs (fun u => (classComponent planeClass activePlane z k u).re))
  have hi := squareNonnegative (sumOver xs (fun u => (classComponent planeClass activePlane z k u).im))
  grind

theorem weightNonnegative (half : R) (unit : 2*half=1) (n : Nat) :
    0 ≤ PhysicalChartRestriction.weight half n := by
  have pos : 0 ≤ half := by grind
  have power : ∀ k : Nat, 0 ≤ half^k := by
    intro k; induction k with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih pos
  exact OrderedRing.mul_nonneg (by grind : 0 ≤ (4:R)) (power n)

/-- Positive semidefiniteness of the determinant-signed, normalized complex
Pauli sum on any finite list of increasing coordinate four-wedges. -/
theorem normalizedPauliKernel_nonnegative {n : Nat} (half : R) (unit : 2*half=1)
    (xs : List (Coordinate n)) (z : Coordinate n → ComplexScalar R) :
    0 ≤ quadratic xs (fun uv => (exteriorKernel ComplexScalar.imaginaryUnit (ComplexScalar.ofReal half)
      uv.1.val uv.2.val).re) z := by
  simp only [PhysicalExteriorCompression.normalizedComplexEntry half unit,ComplexScalar.re_ofReal]
  exact supportedKernel_nonnegative xs _ (weightNonnegative half unit n) z

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem physicalKernel_symmetric {n : Nat} (half : R) (unit : 2*half=1) (u v : Coordinate n) :
    PhysicalExteriorCompression.physicalKernel half (u,v) =
      PhysicalExteriorCompression.physicalKernel half (v,u) := by
  have eq : supportedPair u.val v.val = supportedPair v.val u.val :=
    Bool.eq_iff_iff.mpr ⟨supportedSymm,supportedSymm⟩
  simp only [PhysicalExteriorCompression.physicalKernel_eq half unit,eq]

theorem physicalKernel_nonnegative {n : Nat} (half : R) (unit : 2*half=1)
    (xs : List (Coordinate n)) (z : Coordinate n → ComplexScalar R) :
    0 ≤ quadratic xs (PhysicalExteriorCompression.physicalKernel half) z :=
  normalizedPauliKernel_nonnegative half unit xs z

end RankSeven.PhysicalExteriorPositivity

#print axioms RankSeven.PhysicalExteriorPositivity.physicalClassSquareSum
#print axioms RankSeven.PhysicalExteriorPositivity.physicalKernel_nonnegative
#print axioms RankSeven.PhysicalExteriorPositivity.physicalKernel_symmetric
