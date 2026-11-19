import Rank7UpperPairCap
namespace RankSeven.UpperCornerDual
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation
attribute [local instance] Ring.intCast Semiring.natCast
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def slot (w : Wedge7) := w.i.val+w.j.val*(w.j.val-1)/2+w.k.val*(w.k.val-1)*(w.k.val-2)/6+
  w.m.val*(w.m.val-1)*(w.m.val-2)*(w.m.val-3)/24

inductive Side where
  | row (r : Row) | n | v
deriving DecidableEq, Repr

def Side.allowed : Side→Bool | .row r => r.legal | _ => true
def Side.rhs : Side→Int | .row r => r.cap | .n => -4 | .v => -2
def Side.col (s : Side) (w : Wedge7) : Int :=
  let a : Int := if occupied w 0 && occupied w 1 then 1 else 0
  let b : Int := if occupied w 0 && occupied w 2 then 1 else 0
  match s with | .row r => if r.covers w then 1 else 0 | .n => -(a+b) | .v => -a

def val (x : Wedge7→R) (c : Wedge7→Int) := sumOver wedges (fun w => Int.cast (c w)*x w)
def ref (c : Wedge7→Int) : Int := sumOver wedges fun w => if SectorDefectAccounting.planeFlag w then c w else 0

private theorem castLe {a b : Int} (h : a≤b) : (Int.cast a:R)≤Int.cast b := by
  have hn : 0≤b-a := by omega
  have eq := Int.toNat_of_nonneg hn
  have pos : (0:R)≤Nat.cast (b-a).toNat := OrderedRing.natCast_nonneg
  have t := congrArg (Int.cast (R:=R)) eq
  rw [Ring.intCast_natCast,Ring.intCast_sub] at t
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem castSum {α : Type} (xs : List α) (f : α→Int) :
    Int.cast (R:=R) (sumOver xs f)=sumOver xs (fun i => Int.cast (f i)) := by
  induction xs with
  | nil => exact Ring.intCast_zero
  | cons a as ih => change Int.cast (f a+sumOver as f)= _; rw [Ring.intCast_add,ih]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem refEval (c : Wedge7→Int) : val (R:=R) referenceWeight c=Int.cast (ref c) := by
  rw [ref,castSum]; apply sumOverCongr; intro w; unfold referenceWeight
  cases SectorDefectAccounting.planeFlag w <;> simp only [Bool.false_eq_true,ite_false,ite_true,Semiring.mul_one,Semiring.mul_zero,Ring.intCast_zero]

private theorem sideBound (x : Wedge7→R) (rows : RowsHold x) (n0 : 0≤UpperFrameTrace.sharedExcess x) (v0 : 0≤UpperFrameTrace.highExcess x)
    (s : Side) (legal : s.allowed=true) : val x s.col≤Int.cast s.rhs := by
  let flag (j : Fin 7) (w : Wedge7) := occupied w 0 && occupied w j
  let p (j : Fin 7) (w : Wedge7) : R := if flag j w then x w else 0
  have l (j : Fin 7) : sumOver wedges (p j)=PackingPolynomial.link x 0 j := rfl
  cases s with
  | row r =>
    have lim := rows r legal
    change val x (Side.col (.row r)) ≤ Int.cast (r.cap:Int)
    rw [Ring.intCast_natCast]; apply Std.le_trans (Std.le_of_eq ?_) lim
    apply sumOverCongr; intro w
    change Int.cast (if r.covers w then (1:Int) else 0)*x w = _
    by_cases ok : r.covers w=true <;> simp [ok] <;> grind
  | n =>
    have e (w : Wedge7) : Int.cast (Side.col .n w)*x w= -(p 1 w+p 2 w) := by
      dsimp only [Side.col,p,flag]; by_cases u : (occupied w 0 && occupied w 1)=true <;> by_cases v : (occupied w 0 && occupied w 2)=true <;> simp [u,v] <;> grind
    unfold val; rw [sumOverCongr wedges e]
    have minus (w : Wedge7) : -(p 1 w+p 2 w)=(-1)*(p 1 w+p 2 w) := by grind only
    rw [sumOverCongr wedges minus,←sumOverMulLeft,sumOverAdd,l,l]
    change _≤Int.cast (-4:Int); unfold UpperFrameTrace.sharedExcess at n0; grind
  | v =>
    have e (w : Wedge7) : Int.cast (Side.col .v w)*x w=(-1)*(p 1 w) := by
      dsimp only [Side.col,p,flag]; by_cases u : (occupied w 0 && occupied w 1)=true <;> simp [u] <;> grind
    unfold val; rw [sumOverCongr wedges e,←sumOverMulLeft,l]
    change _≤Int.cast (-2:Int); unfold UpperFrameTrace.highExcess at v0; grind

abbrev Price := Nat × Side
def bundleCol (ps : List Price) (w : Wedge7) : Int :=
  sumOver ps fun t => (t.1 : Int)*t.2.col w
def bundleCap (ps : List Price) : Int := sumOver ps fun t => (t.1 : Int)*t.2.rhs
structure Cert where
  coeff : Array Int
  denom : Nat
  prices : List Price
deriving Repr
def Cert.cost (b : Cert) (w : Wedge7) : Int := b.coeff[slot w]?.getD 0

def Cert.check (b : Cert) : Bool :=
  decide (0<b.denom) && b.prices.all (fun t => t.2.allowed) &&
  wedges.all (fun w => decide ((b.denom:Int)*b.cost w≤bundleCol b.prices w)) &&
  decide (bundleCap b.prices ≤ (b.denom:Int)*ref b.cost)

private theorem bundleBound (x : Wedge7→R) (rows : RowsHold x) (n0 : 0≤UpperFrameTrace.sharedExcess x) (v0 : 0≤UpperFrameTrace.highExcess x)
    (ps : List Price) (legal : ps.all (fun t => t.2.allowed)=true) :
    val x (bundleCol ps)≤Int.cast (bundleCap ps) := by
  have each (t : Price) (ht : t ∈ ps) := OrderedRing.mul_le_mul_of_nonneg_left
    (sideBound x rows n0 v0 t.2 (List.all_eq_true.mp legal t ht)) (OrderedRing.natCast_nonneg (a:=t.1) (R:=R))
  have S := UpperOddCut.sumLe ps each
  unfold val bundleCol bundleCap
  simp only [castSum,Ring.intCast_mul,Ring.intCast_natCast,sumOverMulRight]
  rw [sumOverSwap]
  change sumOver ps (fun t => sumOver wedges (fun w => Nat.cast t.1*Int.cast (t.2.col w)*x w)) ≤ _
  have move (t : Price) (w : Wedge7) : Nat.cast t.1*Int.cast (t.2.col w)*x w=Nat.cast t.1*(Int.cast (t.2.col w)*x w) := by grind only
  simp only [move,←sumOverMulLeft]; exact S

theorem certified (b : Cert) (checked : b.check=true) (x : Wedge7→R) (nx : ∀w,0≤x w) (rows : RowsHold x)
    (n0 : 0≤UpperFrameTrace.sharedExcess x) (v0 : 0≤UpperFrameTrace.highExcess x) :
    gain x (fun w => Int.cast (b.cost w))≤0 := by
  have ck := Bool.and_eq_true_iff.mp checked
  have ab := Bool.and_eq_true_iff.mp ck.1
  have t := Bool.and_eq_true_iff.mp ab.1
  have cap := castLe (R:=R) (_root_.of_decide_eq_true ck.2)
  have point := UpperOddCut.sumLe wedges (fun w hw => OrderedRing.mul_le_mul_of_nonneg_right
    (castLe (R:=R) (_root_.of_decide_eq_true (List.all_eq_true.mp ab.2 w hw))) (nx w))
  have rhs := bundleBound x rows n0 v0 b.prices t.2
  rw [Ring.intCast_mul,Ring.intCast_natCast] at cap
  simp only [Ring.intCast_mul,Ring.intCast_natCast,Semiring.mul_assoc,←sumOverMulLeft] at point
  change Nat.cast b.denom*val x b.cost≤val x (bundleCol b.prices) at point
  have positive : (0:R)<Nat.cast b.denom := by
    have d := _root_.of_decide_eq_true t.1
    obtain ⟨k,h⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt d)
    rw [h,Semiring.natCast_succ]; have p : (0:R)≤Nat.cast k := OrderedRing.natCast_nonneg; have := OrderedRing.zero_lt_one (R:=R); grind only
  change val x b.cost-val referenceWeight b.cost≤0
  rw [refEval]
  by_cases ok : val x b.cost≤Int.cast (ref b.cost)
  · grind only
  · have bad := OrderedRing.mul_pos positive (show 0<val x b.cost-Int.cast (ref b.cost) by grind only)
    grind only
end RankSeven.UpperCornerDual
#print axioms RankSeven.UpperCornerDual.certified
