import Rank7UpperCorner

/-! Soundness of the coordinate contractor for the normalized fourth/fifth tie.
All divisions in the executable contractor use the directed grid arithmetic. -/
namespace RankSeven.UpperContractor
open Lean.Grind Interval UpperCorner
attribute [local instance] Ring.intCast Semiring.natCast

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def discount (c d : R) : R := d-(1-d)*c

/-- Necessary inequalities for a spectrum left over by the earlier analytic regions,
with a=b=1, α=1+h+k+q, β=1+k+q and γ=1+q. -/
structure Residual (h k q c d : R) : Prop where
  hNonnegative : 0 ≤ h
  kNonnegative : 0 ≤ k
  qNonnegative : 0 ≤ q
  dPositive : 0 < d
  ordered : d ≤ c
  cUnit : c ≤ 1
  nearCut : 101*d < 100*c
  farCut : 5*c < 9*d
  sharedAlpha : 1+h+k+q < (1+h+k+q)*(1+q)*d
  sharedBeta : (1+k+q)*(1+q) < (1+h+k+q)*(1+q)*d
  lowHead : c-c*q-2*d*k < 0
  productCut : h*q < 160*discount c d
  deltaCut : 61*(k*(h+k+q)) < 1800*discount c d
  tailFloor : 2*d ≤ 3*q

/-- The initial upper slab has d≤3/4 and q≥1/2. -/
theorem twoThirdsFloor {q d : R} (slab : 4*d≤3) (head : 1≤2*q) : 2*d≤3*q := by grind only

theorem cancelLe {x y z : R} (hz : 0<z) (h : z*x≤z*y) : x≤y := by
  by_cases e : x≤y
  · exact e
  · have := OrderedRing.mul_lt_mul_of_pos_left (show y<x by grind only) hz
    grind only

private theorem cancelLt {x y z : R} (hz : 0<z) (h : z*x<z*y) : x<y := by
  by_cases e : x<y
  · exact e
  · have := OrderedRing.mul_le_mul_of_nonneg_left (show y≤x by grind only) (Std.le_of_lt hz)
    grind only

/-- Positive width simultaneously forces dγ>1 and dα>β. -/
theorem sharedWidth {h k q c d : R} (r : Residual h k q c d) :
    1 < d*(1+q) ∧ 1+k+q < d*(1+h+k+q) := by
  have hz := r.hNonnegative
  have kz := r.kNonnegative
  have qz := r.qNonnegative
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  constructor
  · apply cancelLt (z:=1+h+k+q) (by grind only)
    have := r.sharedAlpha; grind only
  · apply cancelLt (z:=1+q) (by grind only)
    have := r.sharedBeta; grind only

theorem quotientEq (x : R) {y : R} (hy : 0<y) : y*(x/y)=x := by
  have inv := Field.mul_inv_cancel (show y≠0 by grind only)
  rw [Field.div_eq_mul_inv]
  grind only

/-- The outward endpoint D(cLower,dUpper) is at least the physical discount. -/
theorem discountEndpoint {c d cLower dUpper : R} (c0 : 0≤c) (cl : cLower≤c)
    (du : d≤dUpper) (du1 : dUpper≤1) : discount c d ≤ discount cLower dUpper := by
  have dm := OrderedRing.mul_nonneg (show 0≤dUpper-d by grind only) c0
  have cm := OrderedRing.mul_nonneg (show 0≤1-dUpper by grind only) (show 0≤c-cLower by grind only)
  unfold discount
  grind only

/-- Real inequalities behind all four new lower endpoint candidates for q,h,k. -/
theorem lowerClamps {h k q c d cLower dLower dUpper : R} (r : Residual h k q c d)
    (clPos : 0<cLower) (cl : cLower≤c) (dl : dLower≤d) (du : d≤dUpper) :
    1/dUpper-1 ≤ q ∧ 1-(2*dUpper*k)/cLower ≤ q ∧ (2/3:R)*dLower ≤ q ∧
    (1/dUpper-1)*(1+k+q) ≤ h ∧ ((1-q)*cLower)/(2*dUpper) ≤ k := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have dp := r.dPositive
  have up : 0<dUpper := by grind only
  have up2 : 0<2*dUpper := by grind only
  have kz := r.kNonnegative
  have qz := r.qNonnegative
  have hz := r.hNonnegative
  have inv := quotientEq (1:R) up
  have dGrowth (x : R) (hx : 0≤x) := OrderedRing.mul_le_mul_of_nonneg_right du hx
  obtain ⟨a,b⟩ := sharedWidth r
  have qGrowth := dGrowth (1+q) (by grind only)
  have hGrowth := dGrowth (1+h+k+q) (by grind only)
  have kGrowth := dGrowth k kz
  have low := r.lowHead
  have bound : (1-q)*cLower ≤ 2*dUpper*k := by
    by_cases sign : 0≤1-q
    · have := OrderedRing.mul_le_mul_of_nonneg_left cl sign
      grind only
    · have first := OrderedRing.mul_nonneg (Std.le_of_lt clPos) (show 0≤q-1 by grind only)
      have second := OrderedRing.mul_nonneg (Std.le_of_lt up) kz
      grind only
  have qc := quotientEq (2*dUpper*k) clPos
  have kc := quotientEq ((1-q)*cLower) up2
  have third := quotientEq (2:R) (show (0:R)<3 by grind only)
  have floor := r.tailFloor
  refine ⟨cancelLe up (by grind only),cancelLe clPos (by grind only),?_,?_,cancelLe up2 (by grind only)⟩
  · apply cancelLe (z:=3) (by grind only)
    have m := congrArg (fun z : R => z*dLower) third
    grind only
  · apply cancelLe up
    have m := congrArg (fun z : R => z*(1+k+q)) inv
    grind only

/-- Dividing the two residual product inequalities by the clipped lower heads. -/
theorem upperClamps {h k q c d cLower dUpper qLower hLower : R} (r : Residual h k q c d)
    (cl : cLower≤c) (du : d≤dUpper) (u1 : dUpper≤1)
    (qlPos : 0<qLower) (hlPos : 0<hLower) (ql : qLower≤q) (hl : hLower≤h) :
    h ≤ (160*discount cLower dUpper)/qLower ∧
    q ≤ (160*discount cLower dUpper)/hLower ∧
    k ≤ (((1800/61:R)*discount cLower dUpper)/(h+q)) := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have pos := r.dPositive
  have order := r.ordered
  have grow := discountEndpoint (show 0≤c by grind only) cl du u1
  have p := r.productCut
  have qh := OrderedRing.mul_le_mul_of_nonneg_right ql r.hNonnegative
  have hq := OrderedRing.mul_le_mul_of_nonneg_right hl r.qNonnegative
  have hpq : 0<h+q := by grind only
  have lim := quotientEq (1800:R) (show (0:R)<61 by grind only)
  have dv := quotientEq ((1800/61:R)*discount cLower dUpper) hpq
  have δ := r.deltaCut
  have kk := OrderedRing.mul_nonneg r.kNonnegative r.kNonnegative
  refine ⟨cancelLe qlPos ?_,cancelLe hlPos ?_,cancelLe hpq ?_⟩
  · rw [quotientEq _ qlPos]; grind only
  · rw [quotientEq _ hlPos]; grind only
  · rw [dv]; apply cancelLe (z:=61) (by grind only)
    have m := congrArg (fun z : R => z*discount cLower dUpper) lim
    grind only

def whole (g : Grid) (n : Nat) : Bounds := Bounds.point (Int.ofNat n*g.scale)

private def endpointDiscount (g : Grid) (box : TailBox) : Bounds :=
  let dh := Bounds.point box.d.hi
  dh.sub (Bounds.mul g ((whole g 1).sub dh) (Bounds.point box.c.lo))

private def lowerHeads (g : Grid) (b : TailBox) : Int × Int × Int :=
  let dh := Bounds.point b.d.hi
  let cl := Bounds.point b.c.lo
  let dl := Bounds.point b.d.lo
  let one := whole g 1
  let floor := (Bounds.div g one dh).sub one
  let twiceD := Bounds.mul g (whole g 2) dh
  let q := max (max (max b.q.lo floor.lo) (one.sub (Bounds.div g (Bounds.mul g twiceD b.k) cl)).lo)
    (Bounds.mul g (Bounds.rational g 2 3) dl).lo
  let h := max b.h.lo (Bounds.mul g floor ((one.add b.k).add b.q)).lo
  let k := max b.k.lo (Bounds.div g (Bounds.mul g (one.sub b.q) cl) twiceD).lo
  (h,k,q)

private def clipped (g : Grid) (b : TailBox) : TailBox :=
  let (hl,kl,ql) := lowerHeads g b
  let limitG := Bounds.mul g (whole g 160) (endpointDiscount g b)
  let limitX := Bounds.mul g (Bounds.rational g 1800 61) (endpointDiscount g b)
  ⟨⟨hl,min b.h.hi (Bounds.div g limitG (Bounds.point ql)).hi⟩,
   ⟨kl,min b.k.hi (Bounds.div g limitX (b.h.add b.q)).hi⟩,
   ⟨ql,min b.q.hi (Bounds.div g limitG (Bounds.point hl)).hi⟩,b.c,b.d⟩

/-- Directed-integer translation of contract_tail, including its early exits. -/
def contract (g : Grid) (b : TailBox) : Option TailBox :=
  let cl := Bounds.point b.c.lo
  let ch := Bounds.point b.c.hi
  let dl := Bounds.point b.d.lo
  let dh := Bounds.point b.d.hi
  if b.c.hi < b.d.lo ∨ 0 ≤ ((Bounds.mul g (Bounds.rational g 101 100) dl).sub ch).lo ∨
      0 ≤ (cl.sub (Bounds.mul g (Bounds.rational g 9 5) dh)).lo ∨ (endpointDiscount g b).hi ≤ 0 then none
  else
    let z := clipped g b
    if z.h.hi < z.h.lo ∨ z.k.hi < z.k.lo ∨ z.q.hi < z.q.lo then none else some z

structure Inside (g : Grid) (b : TailBox) (h k q c d : R) : Prop where
  hInside : b.h.Contains g h
  kInside : b.k.Contains g k
  qInside : b.q.Contains g q
  cInside : b.c.Contains g c
  dInside : b.d.Contains g d

/-- These integer endpoint properties hold on the initial slab and survive
splitting or clipping. They give strict positivity for rounded denominators. -/
structure Valid (g : Grid) (b : TailBox) : Prop where
  cLowerPositive : 0 < b.c.lo
  hLowerPositive : 0 < b.h.lo
  qLowerPositive : 0 < b.q.lo
  dUpperUnit : b.d.hi ≤ g.scale

private theorem castMonotone {a b : Int} (h : a ≤ b) : (Int.cast a : R) ≤ Int.cast b := by
  have natural : (↑(b-a).toNat : Int) = b-a := Int.toNat_of_nonneg (by omega)
  have nonnegative (n : Nat) : (0:R) ≤ Nat.cast n := by
    induction n with
    | zero => grind
    | succ n ih => rw [Semiring.natCast_succ]; have := OrderedRing.zero_lt_one (R:=R); grind only
  have eq := congrArg (Int.cast (R:=R)) natural
  rw [Ring.intCast_natCast,Ring.intCast_sub] at eq
  have := nonnegative (b-a).toNat
  grind only

private theorem castPositive {z : Int} (h : 0<z) : (0:R)<Int.cast z := by
  have low := castMonotone (R:=R) (show 1≤z by omega)
  rw [Ring.intCast_one] at low
  have := OrderedRing.zero_lt_one (R:=R); grind only

private theorem castStrict {a b : Int} (h : a<b) : (Int.cast a : R)<Int.cast b := by
  have p := castPositive (R:=R) (show 0<b-a by omega)
  rw [Ring.intCast_sub] at p; grind only

def value (g : Grid) (i : Int) : R := Int.cast i/Int.cast g.scale

private theorem scaledValue (g : Grid) (i : Int) : (Int.cast g.scale : R)*value g i=Int.cast i :=
  quotientEq _ (castPositive g.positive)

theorem valueLe (g : Grid) {i j : Int} (ij : i≤j) : value (R:=R) g i ≤ value g j := by
  apply cancelLe (castPositive (R:=R) g.positive)
  rw [scaledValue, scaledValue]; exact castMonotone ij

private theorem valueLt (g : Grid) {i j : Int} (ij : i<j) : value (R:=R) g i < value g j := by
  apply cancelLt (castPositive (R:=R) g.positive)
  rw [scaledValue,scaledValue]; exact castStrict ij

theorem valuePos (g : Grid) {i : Int} (hi : 0<i) : (0:R) < value g i := by
  apply cancelLt (castPositive (R:=R) g.positive)
  rw [Semiring.mul_zero,scaledValue]; exact castPositive hi

theorem scaleValue (g : Grid) : value (R:=R) g g.scale=1 := by
  have a := scaledValue (R:=R) g g.scale
  have p := castPositive (R:=R) g.positive
  have one : (Int.cast g.scale : R)*value g g.scale = Int.cast g.scale*1 := by grind only
  have le := cancelLe p (Std.le_of_eq one)
  have ge := cancelLe p (Std.le_of_eq one.symm)
  grind only

theorem insideEndpoints {g : Grid} {b : Bounds} {x : R} :
    b.Contains g x ↔ value g b.lo ≤ x ∧ x ≤ value g b.hi := by
  have p := castPositive (R:=R) g.positive
  constructor
  · intro h
    exact ⟨cancelLe p (by rw [scaledValue]; exact h.1),cancelLe p (by rw [scaledValue]; exact h.2)⟩
  · intro h
    have l := OrderedRing.mul_le_mul_of_nonneg_left h.1 (Std.le_of_lt p)
    have u := OrderedRing.mul_le_mul_of_nonneg_left h.2 (Std.le_of_lt p)
    rw [scaledValue] at l u
    exact ⟨l,u⟩

theorem pointSound (g : Grid) (i : Int) : (Bounds.point i).Contains g (value (R:=R) g i) := by
  simp only [Bounds.Contains,Bounds.point,scaledValue]; exact ⟨Std.le_refl _,Std.le_refl _⟩

theorem wholeSound (g : Grid) (n : Nat) : (whole g n).Contains g (OfNat.ofNat n : R) := by
  have cast : Int.cast (R:=R) (Int.ofNat n) = OfNat.ofNat n := Ring.intCast_ofNat n
  simp only [whole,Bounds.point,Bounds.Contains,Ring.intCast_mul,cast]; grind only

theorem fractionSound (g : Grid) (n d : Nat) (hd : 0<d) :
    (Bounds.rational g (Int.ofNat n) (Int.ofNat d)).Contains g ((OfNat.ofNat n : R)/OfNat.ofNat d) := by
  have dpi : 0<Int.ofNat d := Int.ofNat_lt.mpr hd
  have pos : (0:R) < OfNat.ofNat d := by
    rw [←show Int.cast (R:=R) (Int.ofNat d)=OfNat.ofNat d from Ring.intCast_ofNat d]
    exact castPositive dpi
  apply Bounds.rationalSound dpi
  rw [show Int.cast (R:=R) (Int.ofNat d)=OfNat.ofNat d from Ring.intCast_ofNat d,
    show Int.cast (R:=R) (Int.ofNat n)=OfNat.ofNat n from Ring.intCast_ofNat n]
  exact quotientEq _ pos

theorem divSound {g : Grid} {a b : Bounds} {x y : R}
    (hx : a.Contains g x) (hy : b.Contains g y) (den : 0<b.lo) :
    (Bounds.div g a b).Contains g (x/y) := by
  have low := (insideEndpoints.mp hy).1
  have pos := valuePos (R:=R) g den
  exact Bounds.divSound hx hy den (quotientEq _ (by grind only))

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem maxLower (g : Grid) {i j : Int} {x : R} (a : value g i≤x) (b : value g j≤x) :
    value g (max i j)≤x := by rw [Int.max_def]; split <;> assumption

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem minUpper (g : Grid) {i j : Int} {x : R} (a : x≤value g i) (b : x≤value g j) :
    x≤value g (min i j) := by rw [Int.min_def]; split <;> assumption

private theorem intDenominator {g : Grid} {b : Bounds} {x : R} (hb : b.Contains g x) (pos : 0<x) :
    0<b.hi := by
  by_cases h : 0<b.hi
  · exact h
  · have := Bounds.nonpositive hb (by omega : b.hi≤0); grind only

theorem wholeMulPoint (g : Grid) (n : Nat) (i : Int) :
    Bounds.mul g (whole g n) (Bounds.point i) = Bounds.point (Int.ofNat n*i) := by
  have nonzero : g.scale≠0 := Int.ne_of_gt g.positive
  have reorder : (Int.ofNat n*g.scale)*i=(Int.ofNat n*i)*g.scale := by grind only
  simp only [Bounds.mul,whole,Bounds.point,Int.min_self,Int.max_self,floor,ceil,reorder,
    ←Int.neg_mul,Int.mul_ediv_cancel _ nonzero,Int.neg_neg]

private theorem twicePoint (g : Grid) (i : Int) :
    Bounds.mul g (whole g 2) (Bounds.point i) = Bounds.point (2*i) :=
  wholeMulPoint g 2 i

private theorem lowerSound {g : Grid} {b : TailBox} {h k q c d : R}
    (r : Residual h k q c d) (valid : Valid g b) (inside : Inside g b h k q c d) :
    let (hl,kl,ql) := lowerHeads g b
    value g hl≤h ∧ value g kl≤k ∧ value g ql≤q := by
  let cu := value (R:=R) g b.c.lo
  let dl := value (R:=R) g b.d.lo
  let du := value (R:=R) g b.d.hi
  have realCuts := lowerClamps (cLower:=cu) (dLower:=dl) (dUpper:=du) r (valuePos g valid.cLowerPositive)
    (insideEndpoints.mp inside.cInside).1 (insideEndpoints.mp inside.dInside).1 (insideEndpoints.mp inside.dInside).2
  obtain ⟨qf,qd,qt,hf,kf⟩ := realCuts
  have hd := pointSound (R:=R) g b.d.hi
  have hc := pointSound (R:=R) g b.c.lo
  have positive := intDenominator inside.dInside r.dPositive
  have one := wholeSound (R:=R) g 1
  have td := Bounds.mulSound (wholeSound (R:=R) g 2) hd
  have tc : 0<(Bounds.mul g (whole g 2) (Bounds.point b.d.hi)).lo := by rw [twicePoint]; change 0<2*b.d.hi; omega
  have floor := Bounds.subSound (divSound one hd positive) one
  have head := Bounds.mulSound floor (Bounds.addSound (Bounds.addSound one inside.kInside) inside.qInside)
  have kbound := divSound (Bounds.mulSound (Bounds.subSound one inside.qInside) hc) td tc
  have qbound := Bounds.subSound one (divSound (Bounds.mulSound td inside.kInside) hc valid.cLowerPositive)
  have tail := Bounds.mulSound (fractionSound (R:=R) g 2 3 (by decide)) (pointSound (R:=R) g b.d.lo)
  dsimp only [lowerHeads]
  refine ⟨maxLower g (insideEndpoints.mp inside.hInside).1 (Std.le_trans (insideEndpoints.mp head).1 hf),
    maxLower g (insideEndpoints.mp inside.kInside).1 (Std.le_trans (insideEndpoints.mp kbound).1 kf),?_⟩
  apply maxLower g _ (Std.le_trans (insideEndpoints.mp tail).1 qt)
  apply maxLower g _ (Std.le_trans (insideEndpoints.mp qbound).1 qd)
  exact maxLower g (insideEndpoints.mp inside.qInside).1 (Std.le_trans (insideEndpoints.mp floor).1 qf)

private theorem discountSound (g : Grid) (b : TailBox) :
    (endpointDiscount g b).Contains g (discount (value (R:=R) g b.c.lo) (value g b.d.hi)) :=
  Bounds.subSound (pointSound _ _) (Bounds.mulSound (Bounds.subSound (wholeSound _ 1) (pointSound _ _)) (pointSound _ _))

private theorem headsPositive {g : Grid} {b : TailBox} (v : Valid g b) :
    0<(lowerHeads g b).1 ∧ 0<(lowerHeads g b).2.2 := by
  have h := v.hLowerPositive
  have q := v.qLowerPositive
  dsimp only [lowerHeads]; omega

theorem noEmpty {g : Grid} {b : Bounds} {x : R} (h : b.Contains g x) : b.lo≤b.hi := by
  by_cases sign : b.lo≤b.hi
  · exact sign
  · have := valueLt (R:=R) g (show b.hi<b.lo by omega)
    have := insideEndpoints.mp h; grind only

/-- Rounded clamps preserve every point satisfying the normalized residual premises. -/
theorem clippedSound {g : Grid} {b : TailBox} {h k q c d : R}
    (r : Residual h k q c d) (valid : Valid g b) (inside : Inside g b h k q c d) :
    Inside g (clipped g b) h k q c d := by
  let hl := (lowerHeads g b).1
  let kl := (lowerHeads g b).2.1
  let ql := (lowerHeads g b).2.2
  obtain ⟨lh,lk,lq⟩ := lowerSound r valid inside
  obtain ⟨hpos,qpos⟩ := headsPositive valid
  have du1 : value (R:=R) g b.d.hi≤1 := by
    rw [←scaleValue (R:=R) g]; exact valueLe g valid.dUpperUnit
  have realBounds := upperClamps (cLower:=value (R:=R) g b.c.lo) (dUpper:=value g b.d.hi)
    (hLower:=value g hl) (qLower:=value g ql) r (insideEndpoints.mp inside.cInside).1 (insideEndpoints.mp inside.dInside).2
    du1 (valuePos g qpos) (valuePos g hpos) lq lh
  obtain ⟨hb,qb,kb⟩ := realBounds
  have disc := discountSound (R:=R) g b
  have gl := Bounds.mulSound (wholeSound (R:=R) g 160) disc
  have xl := Bounds.mulSound (fractionSound (R:=R) g 1800 61 (by decide)) disc
  have hh := divSound gl (pointSound (R:=R) g ql) qpos
  have qh := divSound gl (pointSound (R:=R) g hl) hpos
  have pq : 0<(b.h.add b.q).lo := by have := valid.hLowerPositive; have := valid.qLowerPositive; change 0<b.h.lo+b.q.lo; omega
  have kh := divSound xl (Bounds.addSound inside.hInside inside.qInside) pq
  refine ⟨insideEndpoints.mpr ⟨lh,?_⟩,insideEndpoints.mpr ⟨lk,?_⟩,insideEndpoints.mpr ⟨lq,?_⟩,inside.cInside,inside.dInside⟩
  · exact minUpper g (insideEndpoints.mp inside.hInside).2 (Std.le_trans hb (insideEndpoints.mp hh).2)
  · exact minUpper g (insideEndpoints.mp inside.kInside).2 (Std.le_trans kb (insideEndpoints.mp kh).2)
  · exact minUpper g (insideEndpoints.mp inside.qInside).2 (Std.le_trans qb (insideEndpoints.mp qh).2)

private theorem positiveLower {g : Grid} {b : Bounds} {x : R} (hx : b.Contains g x) (hl : 0≤b.lo) : 0≤x := by
  have l := castMonotone (R:=R) hl
  rw [Ring.intCast_zero] at l
  apply cancelLe (castPositive (R:=R) g.positive)
  rw [Semiring.mul_zero]; exact Std.le_trans l hx.1

/-- The contractor returns a box containing the point; all four arithmetic
early exits and the three empty-interval exits are incompatible with it. -/
theorem contractPreserves {g : Grid} {b : TailBox} {h k q c d : R}
    (r : Residual h k q c d) (valid : Valid g b) (inside : Inside g b h k q c d) :
    ∃ z, contract g b = some z ∧ Inside g z h k q c d := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  let dl := value (R:=R) g b.d.lo
  let du := value (R:=R) g b.d.hi
  let cl := value (R:=R) g b.c.lo
  let cu := value (R:=R) g b.c.hi
  have ⟨dlower,dupper⟩ : dl≤d ∧ d≤du := insideEndpoints.mp inside.dInside
  have ⟨clower,cupper⟩ : cl≤c ∧ c≤cu := insideEndpoints.mp inside.cInside
  have limit : du≤1 := by rw [←scaleValue (R:=R) g]; exact valueLe g valid.dUpperUnit
  have cd := r.ordered
  have rejectOrder : ¬b.c.hi < b.d.lo := by
    intro e; have bad : cu < dl := valueLt (R:=R) g e; grind only
  have first := Bounds.subSound
    (Bounds.mulSound (fractionSound (R:=R) g 101 100 (by decide)) (pointSound (R:=R) g b.d.lo))
    (pointSound (R:=R) g b.c.hi)
  have last := Bounds.subSound (pointSound (R:=R) g b.c.lo)
    (Bounds.mulSound (fractionSound (R:=R) g 9 5 (by decide)) (pointSound (R:=R) g b.d.hi))
  have rejectNear : ¬0≤((Bounds.mul g (Bounds.rational g 101 100) (Bounds.point b.d.lo)).sub (Bounds.point b.c.hi)).lo := by
    intro rejected
    have result : 0≤(101/100:R)*dl-cu := positiveLower first rejected
    have scale := OrderedRing.mul_le_mul_of_nonneg_left result (show (0:R)≤100 by grind only)
    have unit := quotientEq (101:R) (show (0:R)<100 by grind only)
    have eq := congrArg (fun t : R => t*dl) unit
    have bound := r.nearCut
    grind only
  have rejectFar : ¬0≤((Bounds.point b.c.lo).sub (Bounds.mul g (Bounds.rational g 9 5) (Bounds.point b.d.hi))).lo := by
    intro rejected
    have result : 0≤cl-(9/5:R)*du := positiveLower last rejected
    have scale := OrderedRing.mul_le_mul_of_nonneg_left result (show (0:R)≤5 by grind only)
    have unit := quotientEq (9:R) (show (0:R)<5 by grind only)
    have eq := congrArg (fun t : R => t*du) unit
    have bound := r.farCut
    grind only
  have rejectDiscount : ¬(endpointDiscount g b).hi≤0 := by
    intro test
    have dp := r.dPositive
    have grow := discountEndpoint (show 0≤c by grind only) clower dupper limit
    have small : discount cl du ≤ 0 := Bounds.nonpositive (discountSound (R:=R) g b) test
    have product := r.productCut
    have nonneg := OrderedRing.mul_nonneg r.hNonnegative r.qNonnegative
    grind only
  have kept := clippedSound r valid inside
  have hValid := noEmpty kept.hInside
  have kValid := noEmpty kept.kInside
  have qValid := noEmpty kept.qInside
  refine ⟨clipped g b,?_,kept⟩
  unfold contract
  rw [ite_eq_right (by exact fun e => e.elim rejectOrder (fun e' => e'.elim rejectNear (fun e'' => e''.elim rejectFar rejectDiscount)))]
  rw [ite_eq_right (by omega)]

/-- All denominators and the endpoint discount domain remain valid on a surviving box. -/
theorem contractValid {g : Grid} {b z : TailBox} (v : Valid g b) (ok : contract g b=some z) :
    Valid g z := by
  dsimp only [contract] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  have e := Option.some.inj ok
  subst z
  exact ⟨v.cLowerPositive,(headsPositive v).1,(headsPositive v).2,v.dUpperUnit⟩

/-- Positive lower heads and the upper bound on d descend to every subbox. -/
theorem validSubbox {g : Grid} {b z : TailBox} (v : Valid g b)
    (hc : b.c.lo≤z.c.lo) (hh : b.h.lo≤z.h.lo) (hq : b.q.lo≤z.q.lo) (hd : z.d.hi≤b.d.hi) :
    Valid g z :=
  ⟨Int.lt_of_lt_of_le v.cLowerPositive hc,Int.lt_of_lt_of_le v.hLowerPositive hh,
    Int.lt_of_lt_of_le v.qLowerPositive hq,Int.le_trans hd v.dUpperUnit⟩

/-- Initial endpoints in the C++ upper traversal, with the dyadic slab supplied separately. -/
def initialBox (dLo dHi : Int) : TailBox :=
  let g := cppGrid
  ⟨⟨(Bounds.rational g 3 5).lo,143*g.scale⟩,
   ⟨0,(Bounds.rational g 33 8).hi⟩,
   ⟨(Bounds.rational g 1 2).lo,(Bounds.rational g 51 4).hi⟩,
   ⟨dLo,min (Bounds.mul g (Bounds.rational g 9 5) (Bounds.point dHi)).hi g.scale⟩,
   ⟨dLo,dHi⟩⟩

theorem initialValid (dLo dHi : Int) (pos : 0<dLo) (unit : dHi≤cppGrid.scale) :
    Valid cppGrid (initialBox dLo dHi) := by
  exact ⟨pos,show 0<(Bounds.rational cppGrid 3 5).lo from by decide,
    show 0<(Bounds.rational cppGrid 1 2).lo from by decide,unit⟩

theorem lowerEndpointNonnegative {g : Grid} {a : Bounds} {x : R}
    (inside : a.Contains g x) (lower : 0≤a.lo) : 0≤x := by
  have gridPos := castPositive (R:=R) g.positive
  have lo := castMonotone (R:=R) lower
  have hx := inside.1
  apply cancelLe gridPos
  grind only

theorem lowerEndpointPositive {g : Grid} {a : Bounds} {x : R}
    (inside : a.Contains g x) (lower : 0<a.lo) : 0<x := by
  have gridPos := castPositive (R:=R) g.positive
  have lo := castPositive (R:=R) lower
  have hx := inside.1
  apply cancelLt gridPos
  grind only

end RankSeven.UpperContractor

#print axioms RankSeven.UpperContractor.sharedWidth
#print axioms RankSeven.UpperContractor.lowerClamps
#print axioms RankSeven.UpperContractor.upperClamps
#print axioms RankSeven.UpperContractor.contractPreserves
#print axioms RankSeven.UpperContractor.contractValid
#print axioms RankSeven.UpperContractor.validSubbox
#print axioms RankSeven.UpperContractor.initialValid
