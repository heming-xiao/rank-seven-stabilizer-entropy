import Rank7GenericExteriorKernel
import Rank7HyperplaneInduction

/-! Classification of the physical four-wedge defect by its actual sites.
The list of supporting hyperplanes uses increasing normal-code order. -/
namespace RankSeven.PhysicalExteriorSupport

open Lean.Grind RankSeven.Pauli RankSeven.HyperplaneIncidence RankSeven.HyperplaneResolution
open RankSeven.HyperplaneInduction RankSeven.GenericExteriorKernel RankSeven.ExteriorPauliBase
open PlaneOrientation (Increasing)

private theorem fourCases : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide

private theorem xorSelf {n : Nat} (x : Basis n) : xorBasis n x x = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorBasis,zero,ih]; rfl

private theorem xorZero {n : Nat} (x : Basis n) : xorBasis n x (zero n) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => simp [xorBasis,zero,ih]; rfl

private theorem xorComm {n : Nat} (a b : Basis n) : xorBasis n a b = xorBasis n b a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xorBasis,Bool.xor_comm a.1 b.1,ih a.2 b.2]; rfl

private theorem xorEqZero {n : Nat} (x y : Basis n) : xorBasis n x y = zero n ↔ x=y := by
  constructor
  · intro h
    have e := congrArg (xorBasis n x) h
    simpa only [xorCancelLeft,xorZero] using e.symm
  · rintro rfl; exact xorSelf _

private theorem threeEq {n : Nat} (x y z w : Basis n) :
    xorBasis n x y = xorBasis n z w ↔ xorBasis n x (xorBasis n y z) = w := by
  induction n with
  | zero => cases w; exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩; rcases z with ⟨c,z⟩; rcases w with ⟨d,w⟩
    change (a^^b,xorBasis n x y)=(c^^d,xorBasis n z w) ↔
      (a^^(b^^c),xorBasis n x (xorBasis n y z))=(d,w)
    have bit : ∀ a b c d : Bool, (a^^b)=(c^^d) ↔ (a^^(b^^c))=d := by decide
    simp only [Prod.mk.injEq,ih,bit]

def mapSites {α β : Type} (f : α → β) (u : Four α) : Four β :=
  ((f u.1.1,f u.1.2),(f u.2.1,f u.2.2))

private theorem position_map {α β : Type} (f : α → β) (u : Four α) (i : Fin 4) :
    position (mapSites f u) i = f (position u i) := by
  rcases fourCases i with h|h|h|h <;> subst i <;> rfl

private theorem reorder_map {α β : Type} (f : α → β) (u : Four α) (p : Permutation) :
    reorder (mapSites f u) p = mapSites f (reorder u p) := by
  unfold reorder
  rw [position_map,position_map,position_map,position_map]
  rfl

/-- Affinity in a binary affine space is preservation of three-term XOR. -/
def AffineSites {n m : Nat} (f : Basis n → Basis m) : Prop :=
  ∀ x y z, f (xorBasis n x (xorBasis n y z)) = xorBasis m (f x) (xorBasis m (f y) (f z))

theorem supportedPair_map_affine {n m : Nat} (f : Basis n → Basis m)
    (inj : ∀ a b, f a=f b → a=b) (aff : AffineSites f) (u v : Four (Basis n)) :
    supportedPair (mapSites f u) (mapSites f v) = supportedPair u v := by
  have dif (x y z w : Basis n) :
      xorBasis m (f x) (f y) = xorBasis m (f z) (f w) ↔ xorBasis n x y = xorBasis n z w := by
    rw [threeEq,threeEq,← aff]
    exact ⟨inj _ _,congrArg f⟩
  have one (v' : Four (Basis n)) :
      allowedTwirlEntry m (mapSites f u) (mapSites f v') = allowedTwirlEntry n u v' := by
    apply Bool.eq_iff_iff.mpr
    rw [allowed_iff_parity_shift,allowed_iff_parity_shift]
    unfold sameShift parity
    simp only [mapSites,xorEqZero,dif]
  unfold supportedPair
  congr 1
  funext p
  rw [reorder_map,one]

def sites {α : Type} (v : Four α) : List α := [v.1.1,v.1.2,v.2.1,v.2.2]

private theorem sites_reorder {α : Type} (v : Four α) (p : Permutation) (hp : p∈permutations) :
    (sites (reorder v p)).Perm (sites v) := by
  have t : permutations.all (fun p => decide ((sites p).Perm ([0,1,2,3] : List (Fin 4)))) = true := by decide
  exact (_root_.of_decide_eq_true (List.all_eq_true.mp t p hp)).map (position v)

private theorem sorted_unique {n : Nat} (u v : Four (Basis n)) (ordU : Increasing u) (ordV : Increasing v)
    (h : (sites u).Perm (sites v)) : u=v := by
  let r (x y : Basis n) := PlaneOrientation.label n x < PlaneOrientation.label n y
  have sorted (w : Four (Basis n)) (ord : Increasing w) : (sites w).Pairwise r := by
    obtain ⟨a,b,c⟩ := ord
    simp [sites,r,List.pairwise_cons]; omega
  have eq := List.Perm.eq_of_pairwise (le:=r) (fun _ _ _ _ hab hba => by unfold r at *; omega)
    (sorted u ordU) (sorted v ordV) h
  rcases u with ⟨⟨u₀,u₁⟩,u₂,u₃⟩
  rcases v with ⟨⟨v₀,v₁⟩,v₂,v₃⟩
  simp only [sites,List.cons.injEq] at eq
  grind

def inside {n : Nat} (H : HyperplaneCode n) (u : Four (Basis n)) : Bool :=
  (sites u).all (contains H)

private theorem inside_reorder {n : Nat} (H : HyperplaneCode n) (v : Four (Basis n))
    (p : Permutation) (hp : p∈permutations) : inside H (reorder v p) = inside H v := by
  have mem (a : Basis n) : a ∈ sites (reorder v p) ↔ a ∈ sites v := (sites_reorder v p hp).mem_iff
  unfold inside
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h a ha
  · exact h a ((mem a).mpr ha)
  · exact h a ((mem a).mp ha)

private theorem inside_frame {n : Nat} (H : HyperplaneCode n) (x a b : Basis n) :
    inside H (affinePlaneFrame x a b) = true ↔ hasPlane H x a b := by
  simp [inside,sites,affinePlaneFrame,hasPlane,Bool.and_eq_true]

theorem supported_witness {n : Nat} (u v : Four (Basis n)) (h : supportedPair u v=true) :
    ∃ p∈permutations, ∃ t : Basis n,
      parity u = zero n ∧ reorder v p = PlaneOrientation.translate t u := by
  obtain ⟨p,hp,he⟩ := List.any_eq_true.mp h
  obtain ⟨plane,t,aligned⟩ := (allowed_iff_translation _ _).mp he
  exact ⟨p,hp,t,plane,Prod.ext (Prod.ext (aligned 0) (aligned 1)) (Prod.ext (aligned 2) (aligned 3))⟩

theorem supported_diagonal {n : Nat} (u : Four (Basis n)) :
    supportedPair u u = true ↔ parity u = zero n := by
  constructor
  · intro h
    obtain ⟨_,_,_,plane,_⟩ := supported_witness u u h
    exact plane
  · intro h
    have ident : ((0,1),(2,3)) ∈ permutations := by decide
    apply List.any_eq_true.mpr
    refine ⟨_,ident,(allowed_iff_translation _ _).mpr ⟨h,zero n,?_⟩⟩
    intro i
    rw [xorComm,xorZero]; rfl

private theorem point_ext {α : Type} {u v : Four α} (h : ∀ j, position u j = position v j) : u=v :=
  Prod.ext (Prod.ext (h 0) (h 1)) (Prod.ext (h 2) (h 3))

private theorem position_trans {n : Nat} (u : Four (Basis n)) (t : Basis n) (k : Fin 4) :
    position (PlaneOrientation.translate t u) k = xorBasis n t (position u k) := by
  rcases fourCases k with h|h|h|h <;> subst k <;> rfl

private theorem repeatedXor {n : Nat} (p y z : Basis n) :
    xorBasis n (xorBasis n p y) (xorBasis n p z) = xorBasis n y z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have bit : ∀ a b c : Bool, ((a^^b)^^(a^^c))=(b^^c) := by decide
    simp only [xorBasis,bit,ih p.2 y.2 z.2]; rfl

private theorem span_translate_perm {n : Nat} (p a b t : Basis n)
    (ht : t = zero n ∨ t=a ∨ t=b ∨ t=xorBasis n a b) :
    (sites (PlaneOrientation.translate t (affinePlaneFrame p a b))).Perm (sites (affinePlaneFrame p a b)) := by
  have coords : ∃ j, t = planePoint n (zero n) a b j := by
    have za : xorBasis n (zero n) a = a := (xorComm _ _).trans (xorZero _)
    have zb : xorBasis n (zero n) b = b := (xorComm _ _).trans (xorZero _)
    rcases ht with h|h|h|h <;> rw [h]
    · exact ⟨0,position_planeFrame (zero n) a b 0⟩
    · exact ⟨1,za.symm.trans (position_planeFrame (zero n) a b 1)⟩
    · exact ⟨2,zb.symm.trans (position_planeFrame (zero n) a b 2)⟩
    · exact ⟨3,(congrArg (fun x => xorBasis n x b) za.symm).trans (position_planeFrame (zero n) a b 3)⟩
  obtain ⟨j,hj⟩ := coords
  have shift_mem : ∀ j : Fin 4, shiftPermutation j ∈ permutations := by decide
  have pi : ∀ i j : Fin 4, position (shiftPermutation j) i = indexXor j i := by decide
  have eq : PlaneOrientation.translate t (affinePlaneFrame p a b) = reorder (affinePlaneFrame p a b) (shiftPermutation j) := by
    apply point_ext
    intro k
    rw [position_trans,position_reorder,pi,position_planeFrame,position_planeFrame,hj,
      planePoint_difference,xorComm (zero n),xorZero]
  rw [eq]; exact sites_reorder _ _ (shift_mem j)

private theorem site_separations {n : Nat} (u : Four (Basis n)) (ord : Increasing u) :
    u.1.1≠u.1.2 ∧ u.1.1≠u.2.1 ∧ u.1.1≠u.2.2 ∧ u.1.2≠u.2.1 ∧ u.1.2≠u.2.2 ∧ u.2.1≠u.2.2 := by
  obtain ⟨a,b,c⟩ := ord
  constructor
  · intro h; rw [h] at a; omega
  constructor
  · intro h; rw [h] at a; omega
  constructor
  · intro h; rw [h] at a; omega
  constructor
  · intro h; rw [h] at b; omega
  constructor
  · intro h; rw [h] at b; omega
  · intro h; rw [h] at c; omega

/-- Geometric witnesses for the only surviving off-diagonal defect. The
offset lies outside the direction plane, so the two point sets are disjoint. -/
structure ParallelData {n : Nat} (u v : Four (Basis n)) where
  a : Basis n
  b : Basis n
  d : Basis n
  perm : Permutation
  perm_mem : perm ∈ permutations
  row : u=affinePlaneFrame u.1.1 a b
  col : reorder v perm=affinePlaneFrame (xorBasis n u.1.1 d) a b
  ha : a≠zero n
  hb : b≠zero n
  hab : a≠b
  hd : d≠zero n
  hda : d≠a
  hdb : d≠b
  hdab : d≠xorBasis n a b

theorem supported_offdiag {n : Nat} (u v : Four (Basis n)) (ordU : Increasing u) (ordV : Increasing v)
    (ne : u≠v) (yes : supportedPair u v=true) : Nonempty (ParallelData u v) := by
  obtain ⟨perm,hperm,d,hpar,aligned⟩ := supported_witness u v yes
  let p := u.1.1
  let a := xorBasis n p u.1.2
  let b := xorBasis n p u.2.1
  have row : u=affinePlaneFrame p a b := parity_zero_frame _ hpar
  have col : reorder v perm=affinePlaneFrame (xorBasis n p d) a b := by
    calc
      _ = PlaneOrientation.translate d (affinePlaneFrame p a b) := aligned.trans (congrArg (PlaneOrientation.translate d) row)
      _ = _ := by rw [PlaneOrientation.translateGeneratorFrame,xorComm d p]
  obtain ⟨e₁,e₂,_,e₄,_,_⟩ := site_separations u ordU
  have ha : a≠zero n := fun h => e₁ ((xorEqZero _ _).mp h)
  have hb : b≠zero n := fun h => e₂ ((xorEqZero _ _).mp h)
  have hab : a≠b := by
    intro h
    have e := congrArg (xorBasis n p) h
    change xorBasis n p (xorBasis n p u.1.2)=xorBasis n p (xorBasis n p u.2.1) at e
    rw [xorCancelLeft,xorCancelLeft] at e; contradiction
  have outside : ¬ (d=zero n ∨ d=a ∨ d=b ∨ d=xorBasis n a b) := by
    intro h
    have permuted := span_translate_perm p a b d h
    rw [←row] at permuted
    rw [←aligned] at permuted
    have both : (sites v).Perm (sites u) :=
      (sites_reorder v perm hperm).symm.trans permuted
    exact ne (sorted_unique _ _ ordU ordV both.symm)
  exact ⟨⟨a,b,d,perm,hperm,row,col,ha,hb,hab,
    fun h => outside (.inl h),fun h => outside (.inr (.inl h)),
    fun h => outside (.inr (.inr (.inl h))),fun h => outside (.inr (.inr (.inr h)))⟩⟩

private def cubeEq : (n : Nat) → DecidableEq (Basis n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 =>
    letI : DecidableEq (Basis n) := cubeEq n
    inferInstanceAs (DecidableEq (Bool × Basis n))
local instance {n : Nat} : DecidableEq (Basis n) := cubeEq n

def coefficient {R : Type} [CommRing R] {n : Nat} (q : R) (u v : Four (Basis n)) : R :=
  (if u=v then q else 0) - (if supportedPair u v then q else 0)

theorem physical_defect {R : Type} [CommRing R] {n : Nat} (i half : R) (hi : i^4=1)
    (unit : 2*half=1) (u v : Four (Basis n)) (ou : Increasing u) (ov : Increasing v) :
    (if u=v then 4*half^n else 0) - exteriorKernel i half u v =
      coefficient (4*half^n) u v := by
  rw [sorted_kernel_entry i half hi unit u v ou ov]; rfl

private def nonplaneCase {n : Nat} (u : Four (Basis n)) (ord : Increasing u)
    (unsupported : supportedPair u u ≠ true) : EntryCase n :=
  let h := site_separations u ord
  .nonplane u.1.1 u.1.2 u.2.1 u.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (by
    rw [repeatedXor]
    change isZero n (parity u)=false
    cases e : isZero n (parity u)
    · rfl
    · exact False.elim (unsupported ((supported_diagonal _).mpr ((isZero_iff _ _).mp e))))

private def parallelCase {n : Nat} {u v : Four (Basis n)} (d : ParallelData u v) : EntryCase n :=
  .parallel u.1.1 d.a d.b d.d d.ha d.hb d.hab d.hd d.hda d.hdb d.hdab

/-- Both geometric witnesses come from the supported-pair test on the two
actual wedges. Different enclosing hyperplanes need no further choice. -/
noncomputable def pairCase {n : Nat} (u v : Four (Basis n)) (ou : Increasing u) (ov : Increasing v) :
    EntryCase n :=
  if eq : u=v then
    if h : supportedPair u u=true then .silent else nonplaneCase u ou h
  else if h : supportedPair u v=true then
    parallelCase (Classical.choice (supported_offdiag u v ou ov eq h))
  else .silent

theorem parentEntry {R : Type} [CommRing R] {n : Nat} (q : R) (u v : Four (Basis n))
    (ou : Increasing u) (ov : Increasing v) : coefficient q u v = HyperplaneInduction.entry q (pairCase u v ou ov) := by
  by_cases e : u=v
  · subst v
    cases h : supportedPair u u <;> simp [h,pairCase,coefficient,HyperplaneInduction.entry,nonplaneCase] <;> grind
  · cases h : supportedPair u v <;> simp [e,h,pairCase,coefficient,HyperplaneInduction.entry,parallelCase] <;> grind

/-- Enumerate each proper normal once, with the unique offset containing the
first vertex of u. Both four-wedges must belong to the resulting hyperplane. -/
def commonHyperplanes {n : Nat} (u v : Four (Basis n)) : List (HyperplaneCode n) :=
  let code (z : Basis n) := (z,dot n z u.1.1)
  ((qubitIndices n).filter (fun z => !isZero n z && inside (code z) u && inside (code z) v)).map code

private theorem validNormal {n : Nat} (z : Basis n) : (!isZero n z) = true ↔ z≠zero n := by
  cases h : isZero n z
  · simp only [Bool.not_false, true_iff]
    intro e
    have := (isZero_iff _ _).mpr e
    simp_all
  · have eq := (isZero_iff _ _).mp h
    simp [eq]

theorem commonHyperplanes_mem {n : Nat} (u v : Four (Basis n)) (H : HyperplaneCode n) :
    H∈commonHyperplanes u v ↔ H.1≠zero n ∧ inside H u=true ∧ inside H v=true := by
  unfold commonHyperplanes
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    subst H
    have := (List.mem_filter.mp hz).2
    simp only [Bool.and_eq_true,validNormal] at this
    exact ⟨this.1.1,this.1.2,this.2⟩
  · rintro ⟨hn,hu,hv⟩
    have first : contains H u.1.1=true := List.all_eq_true.mp hu _ (by simp [sites])
    have he : (H.1,dot n H.1 u.1.1) = H := Prod.ext rfl (beq_iff_eq.mp first)
    apply List.mem_map.mpr
    refine ⟨H.1,List.mem_filter.mpr ⟨qubitIndicesComplete _,?_⟩,he⟩
    simp only [he,hu,hv,(validNormal _).mpr hn,Bool.and_self]

private theorem support_as_list {n r : Nat} (u v : Four (Basis n)) (rows : Rows n r)
    (h : ∀ H, H∈hyperplanesThrough rows u.1.1 ↔ H.1≠zero n ∧ inside H u=true ∧ inside H v=true) :
    hyperplanesThrough rows u.1.1 = commonHyperplanes u v := by
  unfold hyperplanesThrough commonHyperplanes
  apply congrArg (List.map _)
  apply List.filter_congr
  intro z hz
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,validNormal]
  let H : HyperplaneCode n := (z,dot n z u.1.1)
  have hm : H∈hyperplanesThrough rows u.1.1 ↔ allowedNormal rows z = true := by
    constructor
    · intro he
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp he
      have yz : y=z := congrArg Prod.fst eq
      exact yz ▸ (List.mem_filter.mp hy).2
    · intro he
      exact List.mem_map.mpr ⟨z,List.mem_filter.mpr ⟨hz,he⟩,rfl⟩
  have spec := hm.symm.trans (h H)
  change allowedNormal rows z=true ↔ (_ ∧ inside H u = true) ∧ inside H v = true
  exact spec.trans (and_assoc.symm)

private theorem nonplane_support {n : Nat} (u : Four (Basis n)) (ou : Increasing u)
    (h : supportedPair u u≠true) : support (nonplaneCase u ou h)=commonHyperplanes u u := by
  apply support_as_list
  intro H
  change H ∈ fourPointHyperplanes u.1.1 u.1.2 u.2.1 u.2.2 ↔ _
  rw [memFourPointHyperplanes]
  simp only [inside,sites,List.all_cons,List.all_nil,Bool.and_eq_true]
  grind only

private theorem parallel_support {n : Nat} {u v : Four (Basis n)} (d : ParallelData u v) :
    support (parallelCase d)=commonHyperplanes u v := by
  apply support_as_list
  intro H
  have hu : inside H u = true ↔ hasPlane H u.1.1 d.a d.b :=
    (congrArg (inside H) d.row ▸ inside_frame H u.1.1 d.a d.b)
  have hvc : inside H v = inside H (affinePlaneFrame (xorBasis n u.1.1 d.d) d.a d.b) :=
    (inside_reorder H _ _ d.perm_mem).symm.trans (congrArg (inside H) d.col)
  have hv := inside_frame H (xorBasis n u.1.1 d.d) d.a d.b
  change H ∈ jointSupport u.1.1 d.a d.b d.d ↔ _
  rw [memJointSupport,hu,hvc,hv]

theorem support_list {n : Nat} (u v : Four (Basis n)) (ou : Increasing u) (ov : Increasing v)
    (active : pairCase u v ou ov≠.silent) : support (pairCase u v ou ov) = commonHyperplanes u v := by
  by_cases h : u=v
  · subst v
    by_cases yes : supportedPair u u = true
    · simp [pairCase,yes] at active
    · simpa [pairCase,yes] using nonplane_support u ou yes
  · by_cases yes : supportedPair u v=true
    · simpa [pairCase,h,yes] using parallel_support (Classical.choice (supported_offdiag u v ou ov h yes))
    · simp [pairCase,h,yes] at active

private theorem supportNodup {n : Nat} (c : EntryCase n) : (support c).Nodup := by
  cases c with
  | silent => exact List.Pairwise.nil
  | nonplane p x y z _ _ _ _ _ _ _ => exact HyperplaneIncidence.hyperplanesNodup _ _
  | parallel p a b d _ _ _ _ _ _ _ => exact jointSupportNodup _ _ _ _

private theorem absent {R α : Type} [CommRing R] [DecidableEq α] (xs : List α) (x : α) (q : R)
    (missing : x ∉ xs) : sumOver xs (fun j => if j=x then q else 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    have ne : a≠x := fun e => missing (e ▸ List.mem_cons_self)
    have nt : x∉tail := fun h => missing (List.mem_cons_of_mem a h)
    change (if a=x then q else 0) + sumOver tail _ = 0
    rw [ite_eq_right ne,ih nt]
    grind

theorem localEntry_formula {R : Type} [CommRing R] {n : Nat} (q : R) (u v : Four (Basis n))
    (ou : Increasing u) (ov : Increasing v) (H : HyperplaneCode n) (proper : H.1≠zero n) :
    localEntry q (pairCase u v ou ov) H =
      if inside H u && inside H v then coefficient (2*q) u v else 0 := by
  rw [parentEntry (2*q) u v ou ov]
  by_cases silent : pairCase u v ou ov = .silent
  · rw [silent]
    simp only [localEntry,deposit,support,HyperplaneInduction.entry,sumOver,List.map_nil,List.sum_nil,ite_self]
  have membership : H∈support (pairCase u v ou ov) ↔ (inside H u && inside H v)=true := by
    rw [support_list u v ou ov silent,commonHyperplanes_mem,Bool.and_eq_true]
    simp [proper]
  unfold localEntry deposit
  simp only [id_eq]
  by_cases contained : (inside H u && inside H v)=true
  · simp only [contained,ite_true]
    have ev := sumOnIndex (support (pairCase u v ou ov)) H
      (fun _ => HyperplaneInduction.entry (2*q) (pairCase u v ou ov))
      (supportNodup _) (membership.mpr contained)
    calc
      _ = sumOver (support (pairCase u v ou ov)) (fun j =>
            if H=j then HyperplaneInduction.entry (2*q) (pairCase u v ou ov) else 0) := by
        apply sumOverCongr; intro j
        by_cases eq : H=j
        · subst j; simp
        · simp [eq,Ne.symm eq]
      _ = _ := ev
  · simp only [contained]
    exact absent _ _ _ (fun h => contained (membership.mp h))

end RankSeven.PhysicalExteriorSupport
