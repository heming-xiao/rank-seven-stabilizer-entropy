import Rank7HyperplaneIncidence

/-! Coordinate form of Sierant's (222)–(224) for binary affine hyperplanes.
Use n=k+3, so a plane direction has m=2^(k+1) distinct cosets. -/

namespace RankSeven.HyperplaneResolution

open RankSeven.Pauli RankSeven.HyperplaneIncidence Lean.Grind

private theorem dotRightXor (n : Nat) (v x y : Basis n) :
    dot n v (xorBasis n x y) = (dot n v x ^^ dot n v y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨s,v⟩; rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    simp only [dot,xorBasis,ih]
    generalize dot n v x = q
    generalize dot n v y = t
    revert s b c q t
    decide

private theorem xorFix (b t : Bool) : (b ^^ t) = b ↔ t = false := by revert b t; decide

/-- Direct membership in the four points of the affine plane p+span(a,b). -/
def hasPlane {n : Nat} (H : HyperplaneCode n) (p a b : Basis n) : Prop :=
  contains H p = true ∧ contains H (xorBasis n p a) = true ∧
  contains H (xorBasis n p b) = true ∧ contains H (xorBasis n (xorBasis n p a) b) = true

private theorem planeEquations {n : Nat} (H : HyperplaneCode n) (p a b : Basis n) :
    hasPlane H p a b ↔ dot n H.1 p = H.2 ∧ dot n H.1 a = false ∧ dot n H.1 b = false := by
  unfold hasPlane contains
  simp only [beq_iff_eq,dotRightXor]
  generalize dot n H.1 p = t
  generalize dot n H.1 a = x
  generalize dot n H.1 b = y
  generalize H.2 = s
  revert t x y s
  decide

/-- Supporting hyperplanes of two parallel planes, encoded by their offset d.
Their entries within the all-plus direction block receive exactly one summand
from each member of this nonduplicating list. -/
def jointSupport {n : Nat} (p a b d : Basis n) :=
  hyperplanesThrough (row3 d a b) p

theorem memJointSupport {n : Nat} (p a b d : Basis n) (H : HyperplaneCode n) :
    H ∈ jointSupport p a b d ↔
      H.1 ≠ zero n ∧ hasPlane H p a b ∧ hasPlane H (xorBasis n p d) a b := by
  unfold jointSupport
  rw [fourPointMembership,planeEquations,planeEquations]
  unfold contains
  simp only [beq_iff_eq,dotRightXor]
  generalize dot n H.1 p = x
  generalize dot n H.1 a = y
  generalize dot n H.1 b = z
  generalize dot n H.1 d = v
  generalize H.2 = t
  cases x <;> cases y <;> cases z <;> cases v <;> cases t <;> simp

theorem jointSupportNodup {n : Nat} (p a b d : Basis n) : (jointSupport p a b d).Nodup :=
  hyperplanesNodup _ _

private theorem xorZeroIff (n : Nat) (a b : Basis n) : xorBasis n a b = zero n ↔ a=b := by
  induction n with
  | zero => cases a; cases b; exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ n ih =>
    rcases a with ⟨i,x⟩; rcases b with ⟨j,y⟩
    change (i^^j, xorBasis n x y) = (false,zero n) ↔ (i,x)=(j,y)
    constructor
    · intro h
      have hb := congrArg Prod.fst h
      have ht := (ih x y).mp (congrArg Prod.snd h)
      cases i <;> cases j <;> simp_all
    · intro h
      have hb := congrArg Prod.fst h
      have ht := congrArg Prod.snd h
      change i=j at hb; change x=y at ht
      subst j; subst y
      rw [(ih x x).mpr rfl]; cases i <;> rfl

/-- Exactly the ambient hyperplanes containing two disjoint cosets.
The four inequalities on d say precisely that d is outside {0,a,b,a⊕b}. -/
theorem parallelPairCount {n : Nat} (p a b d : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a ≠ b)
    (hd : d ≠ zero n) (hda : d ≠ a) (hdb : d ≠ b) (hdab : d ≠ xorBasis n a b) :
    (jointSupport p a b d).length = 2^(n-3)-1 := by
  have h := fourPointIncidence p d a b hd ha hb hda hdb hab
  have test : isZero n (xorBasis n d (xorBasis n a b)) = false := by
    cases hz : isZero n (xorBasis n d (xorBasis n a b))
    · rfl
    · exact False.elim (hdab ((xorZeroIff _ _ _).mp ((isZero_iff _ _).mp hz)))
  rw [test] at h
  exact h

/-- Counting diagonal of the coordinate four-wedge restriction in (222), expressed
as the sum of the universal part and the extra plane-only incidence. -/
theorem restrictionDiagonal {k : Nat} (p x y z : Basis (k+3))
    (px : p ≠ x) (py : p ≠ y) (pz : p ≠ z) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) :
    let n := k+3
    let test := isZero n (xorBasis n (xorBasis n p x) (xorBasis n (xorBasis n p y) (xorBasis n p z)))
    (fourPointHyperplanes p x y z).length = (2^k-1) + (if test then 2^k else 0) := by
  dsimp only
  rw [actualFourPointIncidence p x y z px py pz xy xz yz]
  have h₂ : k+3-2=k+1 := by omega
  have h₃ : k+3-3=k := by omega
  have hp : 0 < 2^k := Nat.pow_pos (by decide)
  rw [h₂,h₃,Nat.pow_succ]
  split <;> omega

variable {R : Type} [CommRing R]

local instance : NatCast R := Semiring.natCast

private theorem sumConstant {α : Type} (xs : List α) (value : R) :
    sumOver xs (fun _ => value) = (xs.length : R)*value := by
  induction xs with
  | nil => simp [sumOver]; grind
  | cons x xs ih =>
    change value + sumOver xs _ = ((xs.length+1 : Nat) : R)*value
    rw [ih,Semiring.natCast_succ]; grind

private theorem castMinusOne (m : Nat) (hm : 0 < m) :
    ((m-1 : Nat) : R) = (m:R)-1 := by
  have h : m-1+1=m := by omega
  have hc := congrArg (fun a : Nat => (a:R)) h
  rw [Semiring.natCast_succ] at hc
  grind

private theorem twiceDirections (k : Nat) :
    ((2^(k+1) : Nat) : R) = 2*((2^k : Nat) : R) := by
  rw [Nat.pow_succ,Semiring.natCast_mul]
  have h : ((2:Nat):R) = 2 := by grind
  rw [h]; grind

/-- Diagonal of (223): sum of the 2/m entries of the local all-plus projectors
across all hyperplanes containing a particular plane. The parent entry is 1/m. -/
theorem planeProjectorDiagonal {k : Nat} (p a b : Basis (k+3))
    (ha : a ≠ zero _) (hb : b ≠ zero _) (hab : a ≠ b)
    (q : R) (normalized : ((2^(k+1):Nat):R)*q=1) :
    sumOver (hyperplanesThrough (row2 a b) p) (fun _ => 2*q) =
      1+(((2^(k+1):Nat):R)-2)*q := by
  rw [sumConstant,planeIncidence p a b ha hb hab]
  have h : k+3-2=k+1 := by omega
  rw [h,castMinusOne _ (Nat.pow_pos (by decide))]; grind

/-- Off-diagonal of (223) in one direction block, from the actual incidence of
two parallel disjoint planes, each local entry having weight 2/m. -/
theorem parallelProjectorOffDiagonal {k : Nat} (p a b d : Basis (k+3))
    (ha : a ≠ zero _) (hb : b ≠ zero _) (hab : a ≠ b)
    (hd : d ≠ zero _) (hda : d ≠ a) (hdb : d ≠ b) (hdab : d ≠ xorBasis _ a b)
    (q : R) :
    sumOver (jointSupport p a b d) (fun _ => 2*q) = (((2^(k+1):Nat):R)-2)*q := by
  rw [sumConstant,parallelPairCount p a b d ha hb hab hd hda hdb hdab]
  have h : k+3-3=k := by omega
  rw [h,castMinusOne _ (Nat.pow_pos (by decide)),twiceDirections]; grind

private theorem xorZeroRight (n : Nat) (p : Basis n) : xorBasis n p (zero n) = p := by
  induction n with
  | zero => cases p; rfl
  | succ n ih =>
    rcases p with ⟨b,v⟩
    change (b ^^ false, xorBasis n v (zero n)) = _
    rw [Bool.xor_false,ih]

/-- The diagonal support is exactly the set of hyperplanes containing the
four points of the particular physical plane. -/
theorem memPlaneSupport {n : Nat} (p a b : Basis n) (H : HyperplaneCode n) :
    H ∈ hyperplanesThrough (row2 a b) p ↔ H.1 ≠ zero n ∧ hasPlane H p a b := by
  have e (v : Basis n) : allowedNormal (row3 (zero n) a b) v = allowedNormal (row2 a b) v := by
    simp [allowedNormal,row3,row2,row1,isZero,syndrome,dotZero]
  have same : jointSupport p a b (zero n) = hyperplanesThrough (row2 a b) p := by
    unfold jointSupport hyperplanesThrough
    rw [funext e]
  rw [← same,memJointSupport,xorZeroRight,and_self]

/-- Plane diagonal of (224); the coordinate and all-plus projectors have
local coefficients 1 and 2q on exactly the same supporting hyperplanes. -/
theorem planeDefectDiagonal {k : Nat} (p a b : Basis (k+3)) (q : R) :
    sumOver (hyperplanesThrough (row2 a b) p) (fun _ => 2*q - 2*q) =
      (((2^(k+1):Nat):R)-2)*(q-q) := by
  rw [sumConstant]; grind

/-- Off-diagonal of (224) in a plane direction block. The coordinate
restriction is diagonal, so only the local all-plus projectors contribute. -/
theorem parallelDefectOffDiagonal {k : Nat} (p a b d : Basis (k+3))
    (ha : a ≠ zero _) (hb : b ≠ zero _) (hab : a ≠ b)
    (hd : d ≠ zero _) (hda : d ≠ a) (hdb : d ≠ b) (hdab : d ≠ xorBasis _ a b)
    (q : R) :
    sumOver (jointSupport p a b d) (fun _ => 0-2*q) = (((2^(k+1):Nat):R)-2)*(0-q) := by
  rw [sumConstant,parallelPairCount p a b d ha hb hab hd hda hdb hdab]
  have h : k+3-3=k := by omega
  rw [h,castMinusOne _ (Nat.pow_pos (by decide)),twiceDirections]; grind

/-- Nonplane diagonal of (224) for the actual four coordinates. A wedge
without affine-plane support has zero local and parent all-plus entries. -/
theorem nonplaneDefectDiagonal {k : Nat} (p x y z : Basis (k+3))
    (px : p ≠ x) (py : p ≠ y) (pz : p ≠ z) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (nonplane : isZero (k+3) (xorBasis _ (xorBasis _ p x)
      (xorBasis _ (xorBasis _ p y) (xorBasis _ p z))) = false) (q : R) :
    sumOver (fourPointHyperplanes p x y z) (fun _ => 2*q-0) =
      (((2^(k+1):Nat):R)-2)*(q-0) := by
  rw [sumConstant,restrictionDiagonal p x y z px py pz xy xz yz]
  simp only [nonplane,Bool.false_eq_true,ite_false,Nat.add_zero]
  rw [castMinusOne _ (Nat.pow_pos (by decide)),twiceDirections]; grind


end RankSeven.HyperplaneResolution
