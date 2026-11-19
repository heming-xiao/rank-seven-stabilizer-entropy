import Rank7PauliTwirlEntries

/-! Incidence of affine hyperplanes in the binary cube. Normals and coordinates
use the same recursive qubit basis as the fourth-copy Pauli representation. -/

namespace RankSeven.HyperplaneIncidence

open RankSeven.Pauli

def zero : (n : Nat) → Basis n
  | 0 => ()
  | n+1 => (false, zero n)

def isZero : (n : Nat) → Basis n → Bool
  | 0, _ => true
  | n+1, (b,v) => !b && isZero n v

theorem isZero_iff (n : Nat) (v : Basis n) : isZero n v = true ↔ v = zero n := by
  induction n with
  | zero => cases v; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ k ih =>
    rcases v with ⟨b,v⟩
    cases b
    · change isZero k v = true ↔ (false,v)=(false,zero k)
      rw [ih]
      exact ⟨fun h => h ▸ rfl, fun h => congrArg Prod.snd h⟩
    · change false = true ↔ (true,v) = (false,zero k)
      exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion (congrArg Prod.fst h)⟩

def dot : (n : Nat) → Basis n → Basis n → Bool
  | 0, _, _ => false
  | n+1, (a,x), (b,y) => (a && b) ^^ dot n x y

private theorem dotComm (n : Nat) (x y : Basis n) : dot n x y = dot n y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    simp only [dot, ih x y, Bool.and_comm a b]

theorem dotZero (n : Nat) (v : Basis n) : dot n (zero n) v = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨b,v⟩
    simp [dot,zero,ih]

private theorem dotXorBit (a b c p q : Bool) :
    (((a ^^ b) && c) ^^ (p ^^ q)) = (((a && c) ^^ p) ^^ ((b && c) ^^ q)) := by
  revert a b c p q; decide

theorem dotXor (n : Nat) (a b c : Basis n) :
    dot n (xorBasis n a b) c = (dot n a c ^^ dot n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨a,v⟩; rcases b with ⟨b,w⟩; rcases c with ⟨c,t⟩
    simp only [dot,xorBasis,ih,dotXorBit]

def sign : Bool → Int | false => 1 | true => -1

private theorem signXor (b c : Bool) : sign (b ^^ c) = sign b * sign c := by
  revert b c; decide

private theorem twoHeadSum {α : Type} (xs : List α) (p : Bool × α → Int) :
    sumOver (productIndices [false,true] xs) p =
      sumOver xs (fun x => p (false,x)) + sumOver xs (fun x => p (true,x)) := by
  simp [productIndices, sumOver, List.map_map, Function.comp_def]

private theorem sumHeads (n : Nat) (p : Basis (n+1) → Int) :
    sumOver (qubitIndices (n+1)) p =
    sumOver (qubitIndices n) (fun x => p (false,x)) +
    sumOver (qubitIndices n) (fun x => p (true,x)) := by
  exact twoHeadSum (qubitIndices n) p

/-- Walsh character orthogonality, including the zero frequency. -/
theorem characterSum (n : Nat) (y : Basis n) :
    sumOver (qubitIndices n) (fun x => sign (dot n x y)) =
      (2:Int)^n * (if isZero n y then 1 else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases y with ⟨b,y⟩
    rw [sumHeads]
    cases b <;> simp only [dot, Bool.false_and, Bool.true_and, Bool.false_xor, signXor]
    · simp [isZero, ih, Int.pow_succ]; grind
    · change sumOver (qubitIndices n) (fun x => sign (dot n x y)) +
        sumOver (qubitIndices n) (fun x => (-1 : Int)*sign (dot n x y)) = _
      rw [←sumOverMulLeft]
      simp [isZero]; grind

private theorem sumIndicator {α : Type} (ls : List α) (p : α → Bool) :
    sumOver ls (fun a => if p a then (1:Int) else 0) = (ls.countP p : Int) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    change (if p x then (1:Int) else 0) + sumOver xs _ = _
    rw [ih,List.countP_cons]; cases p x <;> simp <;> omega

private theorem sumZeros {α : Type} (xs : List α) : sumOver xs (fun _ => (0:Int)) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumOver xs _ = 0; rw [ih]; rfl

private theorem zeroCount (n : Nat) :
    sumOver (qubitIndices n) (fun x => if isZero n x then (1:Int) else 0) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumHeads]
    change sumOver (qubitIndices n) (fun x => if isZero n x then (1:Int) else 0) +
      sumOver (qubitIndices n) (fun _ => (0:Int)) = 1
    rw [ih,sumZeros]; rfl

/-- Ordered row vectors encoding the homogeneous linear conditions. -/
def Rows (n : Nat) : Nat → Type
  | 0 => Unit
  | r+1 => Basis n × Rows n r

def combination {n : Nat} : (r : Nat) → Rows n r → Basis r → Basis n
  | 0, _, _ => zero n
  | r+1, (a,rs), (b,t) =>
    if b then xorBasis n a (combination r rs t) else combination r rs t

def syndrome {n : Nat} : (r : Nat) → Rows n r → Basis n → Basis r
  | 0, _, _ => ()
  | r+1, (a,rs), y => (dot n a y, syndrome r rs y)

theorem combinationZero {n : Nat} (r : Nat) (rows : Rows n r) :
    combination r rows (zero r) = zero n := by
  induction r with
  | zero => rfl
  | succ r ih => rcases rows with ⟨a,rs⟩; simp [combination,zero,ih]

theorem pairing {n : Nat} (r : Nat) (rows : Rows n r) (c : Basis r) (x : Basis n) :
    dot r c (syndrome r rows x) = dot n (combination r rows c) x := by
  induction r with
  | zero => exact (dotZero n x).symm
  | succ r ih =>
    rcases rows with ⟨a,rs⟩; rcases c with ⟨b,c⟩
    cases b <;> simp [syndrome,combination,dot,dotXor,ih]

/-- Linear independence in the binary row space, with no rank or fiber-count hypothesis. -/
def Independent {n r : Nat} (rows : Rows n r) : Prop :=
  ∀ c : Basis r, combination r rows c = zero n → c = zero r

private theorem independentIndicator {n r : Nat} (rows : Rows n r) (lin : Independent rows)
    (c : Basis r) : isZero n (combination r rows c) = isZero r c := by
  have eq : isZero n (combination r rows c) = true ↔ isZero r c = true := by
    rw [isZero_iff, isZero_iff]
    exact ⟨lin c, fun h => h ▸ combinationZero r rows⟩
  revert eq; cases isZero n (combination r rows c) <;> cases isZero r c <;> decide

def normalCount {n r : Nat} (rows : Rows n r) : Nat :=
  (qubitIndices n).countP (fun x => isZero r (syndrome r rows x))

/-- Double-count the rectangular Walsh sum by its two orthogonality relations. -/
theorem homogeneousProduct {n r : Nat} (rows : Rows n r) (lin : Independent rows) :
    2^r * normalCount rows = 2^n := by
  have eq : (2:Int)^r * (normalCount rows : Int) = (2:Int)^n := by
    calc
      _ = sumOver (qubitIndices n) (fun x => (2:Int)^r *
            (if isZero r (syndrome r rows x) then 1 else 0)) := by
        rw [←sumOverMulLeft, sumIndicator]; rfl
      _ = sumOver (qubitIndices n) (fun x => sumOver (qubitIndices r)
            (fun c => sign (dot r c (syndrome r rows x)))) := by
        exact sumOverCongr _ (fun x => (characterSum r _).symm)
      _ = sumOver (qubitIndices r) (fun c => sumOver (qubitIndices n)
            (fun x => sign (dot n x (combination r rows c)))) := by
        rw [sumOverSwap]
        apply sumOverCongr; intro c; apply sumOverCongr; intro x
        rw [pairing,dotComm]
      _ = sumOver (qubitIndices r) (fun c => (2:Int)^n *
            (if isZero r c then 1 else 0)) := by
        apply sumOverCongr; intro c
        rw [characterSum, independentIndicator rows lin]
      _ = _ := by rw [←sumOverMulLeft,zeroCount]; grind
  apply Int.ofNat_inj.mp
  have cast : ((2:Nat) : Int) = 2 := rfl
  simpa only [Int.natCast_pow,Int.natCast_mul,cast] using eq

theorem independentRankLe {n r : Nat} (rows : Rows n r) (lin : Independent rows) : r ≤ n := by
  apply (Nat.pow_le_pow_iff_right (a:=2) (by decide)).mp
  apply Nat.le_of_dvd (Nat.pow_pos (by decide))
  exact ⟨_,(homogeneousProduct rows lin).symm⟩

/-- Exactly 2^(n-r) homogeneous normals including zero, in every rank. -/
theorem homogeneousCount {n r : Nat} (rows : Rows n r) (lin : Independent rows) :
    normalCount rows = 2^(n-r) := by
  apply Nat.eq_of_mul_eq_mul_left (n:=2^r) (Nat.pow_pos (by decide))
  rw [homogeneousProduct rows lin, ←Nat.pow_add]
  have := independentRankLe rows lin
  congr 1; omega

private theorem dotRightZero (n : Nat) (v : Basis n) : dot n v (zero n) = false := by
  rw [dotComm,dotZero]

private theorem syndromeZero {n : Nat} (r : Nat) (rows : Rows n r) :
    syndrome r rows (zero n) = zero r := by
  induction r with
  | zero => rfl
  | succ r ih => rcases rows with ⟨a,rs⟩; simp [syndrome,zero,dotRightZero,ih]; rfl

/-- Distinct normal vectors define distinct binary linear forms. -/
theorem dotSeparates (n : Nat) (x y : Basis n)
    (agree : ∀ v, dot n v x = dot n v y) : x = y := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    have head := agree (true,zero n)
    change ((true && a) ^^ dot n (zero n) x) = ((true && b) ^^ dot n (zero n) y) at head
    simp only [Bool.true_and,dotZero,Bool.xor_false] at head
    have tail := ih x y (fun v => by
      have h := agree (false,v)
      change ((false && a) ^^ dot n v x) = ((false && b) ^^ dot n v y) at h
      simpa only [Bool.false_and,Bool.false_xor] using h)
    cases head; cases tail; rfl

private theorem dotRightXor (n : Nat) (v x y : Basis n) :
    dot n v (xorBasis n x y) = (dot n v x ^^ dot n v y) := by
  rw [dotComm n v, dotXor, dotComm n x v,dotComm n y v]

private theorem xorFix (b t : Bool) : (b ^^ t) = b ↔ t = false := by revert b t; decide

/-- The homogeneous equations are equivalent to the hyperplane with normal v
and offset v·origin containing every point of the affine span. -/
theorem spanCriterion {n r : Nat} (rows : Rows n r) (origin v : Basis n) :
    isZero r (syndrome r rows v) = true ↔
      ∀ c : Basis r, dot n v (xorBasis n origin (combination r rows c)) = dot n v origin := by
  rw [isZero_iff]
  constructor
  · intro h c
    rw [dotRightXor, xorFix, dotComm n v (combination r rows c), ←pairing, h, dotRightZero]
  · intro h
    apply dotSeparates
    intro c
    have hx := h c
    rw [dotRightXor,xorFix,dotComm n v (combination r rows c),←pairing] at hx
    rw [hx,dotRightZero]

private theorem countSplit {α : Type} (xs : List α) (p z : α → Bool) :
    xs.countP p = xs.countP (fun a => z a && p a) + xs.countP (fun a => !z a && p a) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.countP_cons]
    cases p a <;> cases z a <;> simp <;> omega

private theorem uniqueZero (n : Nat) : (qubitIndices n).countP (isZero n) = 1 := by
  have h := zeroCount n
  rw [sumIndicator] at h
  omega

def allowedNormal {n r : Nat} (rows : Rows n r) (v : Basis n) : Bool :=
  !isZero n v && isZero r (syndrome r rows v)

theorem nonzeroNormalCount {n r : Nat} (rows : Rows n r) (lin : Independent rows) :
    (qubitIndices n).countP (allowedNormal rows) = 2^(n-r)-1 := by
  let eqs v := isZero r (syndrome r rows v)
  have h := countSplit (qubitIndices n) eqs (isZero n)
  have hz : (qubitIndices n).countP (fun v => isZero n v && eqs v) =
      (qubitIndices n).countP (isZero n) := by
    apply List.countP_congr; intro v _
    cases hv : isZero n v
    · simp
    · have h' := (isZero_iff n v).mp hv
      subst v
      simp [eqs,syndromeZero,isZero_iff]
  rw [hz,uniqueZero] at h
  change normalCount rows = 1 + (qubitIndices n).countP (allowedNormal rows) at h
  rw [homogeneousCount rows lin] at h
  omega

private theorem twoHeadNodup {α : Type} (xs : List α) (h : xs.Nodup) :
    (productIndices [false,true] xs).Nodup := by
  simp only [productIndices,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nodup_append]
  refine ⟨List.Pairwise.map _ (fun a b ne he => ne (congrArg Prod.snd he)) h,
    List.Pairwise.map _ (fun a b ne he => ne (congrArg Prod.snd he)) h,?_⟩
  intro x hx y hy he
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
  exact Bool.noConfusion (congrArg Prod.fst he)

theorem normalsNodup (n : Nat) : (qubitIndices n).Nodup := by
  induction n with
  | zero => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | succ n ih => exact twoHeadNodup _ ih

/-- Binary normal/offset code; its support is the fiber v·x = b. -/
abbrev HyperplaneCode (n : Nat) := Basis n × Bool

def contains {n : Nat} (H : HyperplaneCode n) (x : Basis n) : Bool := dot n H.1 x == H.2

private theorem equalOffsets (a b : Bool) : (false == a) = (false == b) → a=b := by
  revert a b; decide
private theorem equalPairings (a b t : Bool) : (a == t) = (b == t) → a=b := by
  revert a b t; decide

/-- Over F₂ there is no nontrivial projective rescaling of a normal. -/
theorem codesExt {n : Nat} (H K : HyperplaneCode n)
    (same : ∀ x, contains H x = contains K x) : H = K := by
  rcases H with ⟨v,b⟩; rcases K with ⟨u,c⟩
  have h := same (zero n)
  change (dot n v (zero n) == b) = (dot n u (zero n) == c) at h
  simp only [dotRightZero] at h
  have hc := equalOffsets b c h
  subst c
  have hv := dotSeparates n v u (fun x => by
    rw [dotComm n x v,dotComm n x u]
    exact equalPairings _ _ b (same x))
  subst u; rfl

def hyperplanesThrough {n r : Nat} (rows : Rows n r) (origin : Basis n) :
    List (HyperplaneCode n) :=
  ((qubitIndices n).filter (allowedNormal rows)).map (fun v => (v,dot n v origin))

/-- No duplicate hyperplane codes or duplicate geometric supports are counted. -/
theorem hyperplanesNodup {n r : Nat} (rows : Rows n r) (origin : Basis n) :
    (hyperplanesThrough rows origin).Nodup :=
  List.Pairwise.map _ (fun _ _ ne he => ne (congrArg Prod.fst he))
    (List.Pairwise.filter _ (normalsNodup n))

/-- Membership is precisely nonzero normal and containment of the affine span. -/
theorem memHyperplanesThrough {n r : Nat} (rows : Rows n r) (origin : Basis n)
    (H : HyperplaneCode n) :
    H ∈ hyperplanesThrough rows origin ↔ H.1 ≠ zero n ∧
      ∀ c : Basis r, contains H (xorBasis n origin (combination r rows c)) = true := by
  rcases H with ⟨v,b⟩
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := List.mem_map.mp h
    cases he
    have allowed := (List.mem_filter.mp hu).2
    obtain ⟨hn,hs⟩ := Bool.and_eq_true_iff.mp allowed
    constructor
    · intro h
      have eq := (isZero_iff n _).mpr h
      simp [eq] at hn
    · intro c
      exact beq_iff_eq.mpr ((spanCriterion rows origin _).mp hs c)
  · rintro ⟨hn,h⟩
    have hb := beq_iff_eq.mp (h (zero r))
    change dot n v (xorBasis n origin (combination r rows (zero r))) = b at hb
    rw [combinationZero,dotRightXor,dotRightZero,Bool.xor_false] at hb
    subst b
    have hs := (spanCriterion rows origin v).mpr (fun c => beq_iff_eq.mp (h c))
    have nz : isZero n v = false := by
      cases hz : isZero n v
      · rfl
      · exact False.elim (hn ((isZero_iff n v).mp hz))
    apply List.mem_map.mpr
    refine ⟨v,List.mem_filter.mpr ⟨qubitIndicesComplete v,?_⟩,rfl⟩
    simp [allowedNormal,nz,hs]

/-- The hyperplane incidence in (222) and its quotient analogue in (223). -/
theorem affineSpanHyperplaneCount {n r : Nat} (rows : Rows n r) (origin : Basis n)
    (lin : Independent rows) : (hyperplanesThrough rows origin).length = 2^(n-r)-1 := by
  unfold hyperplanesThrough
  rw [List.length_map, ←List.countP_eq_length_filter, nonzeroNormalCount rows lin]

private theorem xorZeroRight (n : Nat) (a : Basis n) : xorBasis n a (zero n) = a := by
  induction n with
  | zero => cases a; rfl
  | succ n ih => rcases a with ⟨b,t⟩; change (b ^^ false, xorBasis n t (zero n)) = _
                 rw [Bool.xor_false,ih]

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

theorem independentExtend {n r : Nat} (a : Basis n) (rs : Rows n r)
    (base : Independent rs) (fresh : ∀ t, a ≠ combination r rs t) :
    Independent (n:=n) (r:=r+1) (a,rs) := by
  rintro ⟨b,t⟩ h
  cases b
  · change combination r rs t = zero n at h
    exact congrArg (fun u => (false,u)) (base t h)
  · change xorBasis n a (combination r rs t) = zero n at h
    exact False.elim (fresh t ((xorZeroIff _ _ _).mp h))

def row0 (n : Nat) : Rows n 0 := ()
def row1 {n : Nat} (a : Basis n) : Rows n 1 := (a,row0 n)
def row2 {n : Nat} (a b : Basis n) : Rows n 2 := (a,row1 b)
def row3 {n : Nat} (a b c : Basis n) : Rows n 3 := (a,row2 b c)

theorem pointIncidence {n : Nat} (origin : Basis n) :
    (hyperplanesThrough (row0 n) origin).length = 2^n-1 := by
  apply affineSpanHyperplaneCount
  intro c _
  cases c; rfl

private theorem independentOne {n : Nat} (a : Basis n) (ha : a ≠ zero n) :
    Independent (row1 a) := by
  apply independentExtend (n:=n) (r:=0)
  · intro c _; cases c; rfl
  · intro t; exact ha

/-- Pair incidence in the quotient space used for the off-diagonal in (223). -/
theorem pairIncidence {n : Nat} (origin a : Basis n) (ha : a ≠ zero n) :
    (hyperplanesThrough (row1 a) origin).length = 2^(n-1)-1 :=
  affineSpanHyperplaneCount (row1 a) origin (independentOne a ha)

private theorem independentTwo {n : Nat} (a b : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a ≠ b) : Independent (row2 a b) := by
  apply independentExtend (n:=n) (r:=1) _ _ (independentOne b hb)
  rintro ⟨t,rest⟩
  cases rest
  cases t
  · exact ha
  · change a ≠ xorBasis n b (zero n)
    rwa [xorZeroRight]

/-- Plane incidence does not require an abstract rank certificate. -/
theorem planeIncidence {n : Nat} (origin a b : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hab : a ≠ b) :
    (hyperplanesThrough (row2 a b) origin).length = 2^(n-2)-1 :=
  affineSpanHyperplaneCount _ _ (independentTwo a b ha hb hab)

private theorem independentThree {n : Nat} (a b c : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hc : c ≠ zero n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (notPlane : a ≠ xorBasis n b c) :
    Independent (row3 a b c) := by
  apply independentExtend (n:=n) (r:=2) _ _ (independentTwo b c hb hc hbc)
  rintro ⟨s,t,rest⟩
  cases rest
  cases s <;> cases t
  · exact ha
  · change a ≠ xorBasis n c (zero n)
    rwa [xorZeroRight]
  · change a ≠ xorBasis n b (zero n)
    rwa [xorZeroRight]
  · change a ≠ xorBasis n b (xorBasis n c (zero n))
    rwa [xorZeroRight]

private theorem tripleZero {a b : Bool} :
    ((! (a ^^ b)) && (!a && (!b && true))) = (!a && (!b && true)) := by revert a b; decide

/-- Plane four-sets and nonplane four-sets in (222), with the actual third
difference tested by XOR. These alternatives exhaust all four distinct
affine points, since their three differences are nonzero and pairwise distinct. -/
theorem fourPointIncidence {n : Nat} (origin a b c : Basis n)
    (ha : a ≠ zero n) (hb : b ≠ zero n) (hc : c ≠ zero n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (hyperplanesThrough (row3 a b c) origin).length =
      if isZero n (xorBasis n a (xorBasis n b c)) then 2^(n-2)-1 else 2^(n-3)-1 := by
  cases hz : isZero n (xorBasis n a (xorBasis n b c))
  · have ne : a ≠ xorBasis n b c := by
      intro h
      have h' := (isZero_iff _ _).mpr ((xorZeroIff _ _ _).mpr h)
      simp [h'] at hz
    exact affineSpanHyperplaneCount _ _ (independentThree a b c ha hb hc hab hac hbc ne)
  · have h' := (xorZeroIff _ _ _).mp ((isZero_iff _ _).mp hz)
    subst a
    have equiv (v : Basis n) :
        allowedNormal (row3 (xorBasis n b c) b c) v = allowedNormal (row2 b c) v := by
      unfold allowedNormal
      simp only [row3,row2,row1,syndrome,isZero,dotXor,tripleZero]
    have equal : hyperplanesThrough (row3 (xorBasis n b c) b c) origin =
        hyperplanesThrough (row2 b c) origin := by
      unfold hyperplanesThrough
      rw [funext equiv]
    rw [equal]
    exact planeIncidence origin b c hb hc hbc

/-- Test a normal/offset code directly on four actual affine points. -/
theorem fourPointMembership {n : Nat} (p a b c : Basis n) (H : HyperplaneCode n) :
    H ∈ hyperplanesThrough (row3 a b c) p ↔ H.1 ≠ zero n ∧ contains H p = true ∧
      contains H (xorBasis n p a) = true ∧ contains H (xorBasis n p b) = true ∧
      contains H (xorBasis n p c) = true := by
  rcases H with ⟨v,t⟩
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := List.mem_map.mp h
    cases he
    have ok := (List.mem_filter.mp hu).2
    change (!isZero n v && (!dot n a v && (!dot n b v && (!dot n c v && true)))) = true at ok
    have hn : isZero n v = false := by simp_all
    have ha : dot n a v = false := by simp_all
    have hb : dot n b v = false := by simp_all
    have hc : dot n c v = false := by simp_all
    have hn' : v ≠ zero n := fun eq => by
      have h' := (isZero_iff n v).mpr eq
      rw [hn] at h'
      contradiction
    refine ⟨hn',?_,?_,?_,?_⟩ <;>
      simp [contains,dotRightXor,dotComm n v a,dotComm n v b,dotComm n v c,ha,hb,hc]
  · rintro ⟨hn,hp,ha,hb,hc⟩
    change (dot n v p == t) = true at hp
    have ht := beq_iff_eq.mp hp
    subst t
    have annihilate (d : Basis n)
        (h : contains (v,dot n v p) (xorBasis n p d) = true) : dot n d v = false := by
      change (dot n v (xorBasis n p d) == dot n v p) = true at h
      have eq := beq_iff_eq.mp h
      rw [dotRightXor,xorFix,dotComm n v d] at eq
      exact eq
    have nz : isZero n v = false := by
      cases hz : isZero n v
      · rfl
      · exact False.elim (hn ((isZero_iff n v).mp hz))
    apply List.mem_map.mpr
    refine ⟨v,List.mem_filter.mpr ⟨qubitIndicesComplete v,?_⟩,rfl⟩
    change (!isZero n v && (!dot n a v && (!dot n b v && (!dot n c v && true)))) = true
    rw [nz,annihilate a ha,annihilate b hb,annihilate c hc]; rfl

private theorem xorCancelBit (a b : Bool) : (a ^^ (a ^^ b)) = b := by revert a b; decide

theorem xorCancelLeft (n : Nat) (a b : Basis n) : xorBasis n a (xorBasis n a b) = b := by
  induction n with
  | zero => cases b; rfl
  | succ n ih =>
    rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩
    simp only [xorBasis,xorCancelBit,ih]; rfl

private theorem xorLeftInjective (n : Nat) (p x y : Basis n)
    (h : xorBasis n p x = xorBasis n p y) : x=y := by
  have h' := congrArg (xorBasis n p) h
  simpa only [xorCancelLeft] using h'

/-- Explicit original points, with no affine-coordinate or independent-basis
hypothesis. The enumerated list is exactly the set of supporting hyperplanes. -/
def fourPointHyperplanes {n : Nat} (p x y z : Basis n) : List (HyperplaneCode n) :=
  hyperplanesThrough (row3 (xorBasis n p x) (xorBasis n p y) (xorBasis n p z)) p

theorem memFourPointHyperplanes {n : Nat} (p x y z : Basis n) (H : HyperplaneCode n) :
    H ∈ fourPointHyperplanes p x y z ↔ H.1 ≠ zero n ∧ contains H p = true ∧
      contains H x = true ∧ contains H y = true ∧ contains H z = true := by
  unfold fourPointHyperplanes
  rw [fourPointMembership]
  simp only [xorCancelLeft]

theorem actualFourPointIncidence {n : Nat} (p x y z : Basis n)
    (px : p ≠ x) (py : p ≠ y) (pz : p ≠ z) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) :
    let a := xorBasis n p x
    let b := xorBasis n p y
    let c := xorBasis n p z
    (fourPointHyperplanes p x y z).length =
      if isZero n (xorBasis n a (xorBasis n b c)) then 2^(n-2)-1 else 2^(n-3)-1 :=
  fourPointIncidence p _ _ _ (fun h => px ((xorZeroIff _ _ _).mp h))
    (fun h => py ((xorZeroIff _ _ _).mp h)) (fun h => pz ((xorZeroIff _ _ _).mp h))
    (fun h => xy (xorLeftInjective _ _ _ _ h)) (fun h => xz (xorLeftInjective _ _ _ _ h))
    (fun h => yz (xorLeftInjective _ _ _ _ h))

end RankSeven.HyperplaneIncidence
