import Rank7UpperContractor

namespace RankSeven.UpperOldRegions

open Lean.Grind Interval UpperCorner UpperContractor
attribute [local instance] Ring.intCast Semiring.natCast

private def integer (g : Grid) (n : Nat) : Bounds := Bounds.point (Int.ofNat n * g.scale)

/-- The exact ten lower-endpoint tests in the upper C++ OldRegion branch.
The final two tests use the strict sign. -/
def accepts (grid : Grid) (box : TailBox) : Bool :=
  let one := integer grid 1
  let g := box.h.mul grid box.q
  let x := (box.h.add box.k).add box.q
  let L := (box.h.add ((integer grid 2).mul grid box.k)).add ((integer grid 3).mul grid box.q)
  let alpha := one.add x
  let beta := one.add (box.k.add box.q)
  let gamma := one.add box.q
  let D := box.d.sub ((one.sub box.d).mul grid box.c)
  let margins := [
    L.sub ((integer grid 5).mul grid g),
    (box.c.sub (box.c.mul grid box.q)).sub (((integer grid 2).mul grid box.d).mul grid box.k),
    (integer grid 3).sub alpha,
    (alpha.add beta).sub (alpha.mul grid beta),
    ((Bounds.rational grid 7 5).mul grid ((one.add box.c).sub box.d)).sub x,
    box.c.sub (((integer grid 96).mul grid box.d).mul grid box.k),
    (alpha.largest (beta.mul grid gamma)).sub ((alpha.mul grid gamma).mul grid box.d),
    (box.c.mul grid box.d).sub (x.mul grid D)]
  margins.any (fun a => decide (0 ≤ a.lo)) ||
    decide (0 < ((box.k.mul grid x).sub ((Bounds.rational grid 1800 61).mul grid D)).lo) ||
    decide (0 < (g.sub ((integer grid 160).mul grid D)).lo)

section Ordered
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def OldCondition (h k q c d : R) : Prop :=
  let x := h+k+q
  let alpha := 1+x
  let beta := 1+(k+q)
  let gamma := 1+q
  let D := discount c d
  5*(h*q) ≤ h+2*k+3*q ∨
  0 ≤ c-c*q-2*d*k ∨
  alpha ≤ 3 ∨
  alpha*beta ≤ alpha+beta ∨
  x ≤ (7/5:R)*(1+c-d) ∨
  96*d*k ≤ c ∨
  (alpha*gamma*d ≤ alpha ∨ alpha*gamma*d ≤ beta*gamma) ∨
  x*D ≤ c*d ∨
  (1800/61:R)*D < k*x ∨
  160*D < h*q

private theorem integerSound (grid : Grid) (n : Nat) : (integer grid n).Contains grid (OfNat.ofNat n : R) := by
  have cast : Int.cast (R:=R) (Int.ofNat n) = OfNat.ofNat n := Ring.intCast_ofNat n
  simp only [integer,Bounds.point,Bounds.Contains,Ring.intCast_mul,cast]
  grind only

private theorem fraction75 (grid : Grid) : (Bounds.rational grid 7 5).Contains grid (7/5:R) :=
  UpperContractor.fractionSound grid 7 5 (by decide)

private theorem fraction180061 (grid : Grid) :
    (Bounds.rational grid 1800 61).Contains grid (1800/61:R) :=
  UpperContractor.fractionSound grid 1800 61 (by decide)

/-- The directed tests certify the actual scalar sign of one of the ten
conditions. This theorem handles rounding and the strict branches. -/
theorem acceptedOldCondition {grid : Grid} {box : TailBox} {h k q c d : R}
    (inside : Inside grid box h k q c d) (accepted : accepts grid box=true) :
    OldCondition h k q c d := by
  classical
  obtain ⟨hh,hk,hq,hc,hd⟩ := inside
  let lo := fun (n : Nat) => integerSound (R:=R) grid n
  let x := h+k+q
  let a := 1+x
  let b := 1+(k+q)
  let t := 1+q
  have X := Bounds.addSound (Bounds.addSound hh hk) hq
  have G := Bounds.mulSound hh hq
  have L := Bounds.addSound (Bounds.addSound hh (Bounds.mulSound (lo 2) hk)) (Bounds.mulSound (lo 3) hq)
  have A := Bounds.addSound (lo 1) X
  have B := Bounds.addSound (lo 1) (Bounds.addSound hk hq)
  have T := Bounds.addSound (lo 1) hq
  have D := Bounds.subSound hd (Bounds.mulSound (Bounds.subSound (lo 1) hd) hc)
  have M1 := Bounds.subSound L (Bounds.mulSound (lo 5) G)
  have M2 := Bounds.subSound (Bounds.subSound hc (Bounds.mulSound hc hq))
    (Bounds.mulSound (Bounds.mulSound (lo 2) hd) hk)
  have M3 := Bounds.subSound (lo 3) A
  have M4 := Bounds.subSound (Bounds.addSound A B) (Bounds.mulSound A B)
  have M5 := Bounds.subSound (Bounds.mulSound (fraction75 (R:=R) grid)
    (Bounds.subSound (Bounds.addSound (lo 1) hc) hd)) X
  have M6 := Bounds.subSound hc (Bounds.mulSound (Bounds.mulSound (lo 96) hd) hk)
  let m := if a≤b*t then b*t else a
  have select : (b*t≤a ∧ m=a) ∨ (a ≤ b*t ∧ m=b*t) := by
    dsimp only [m]
    split <;> grind
  have BtimesT := Bounds.mulSound B T
  have maximum := Bounds.largestSound A BtimesT select
  have M7 := Bounds.subSound maximum (Bounds.mulSound (Bounds.mulSound A T) hd)
  have M8 := Bounds.subSound (Bounds.mulSound hc hd) (Bounds.mulSound X D)
  have M9 := Bounds.subSound (Bounds.mulSound hk X) (Bounds.mulSound (fraction180061 (R:=R) grid) D)
  have M10 := Bounds.subSound G (Bounds.mulSound (lo 160) D)
  unfold accepts at accepted
  simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,decide_eq_true_eq] at accepted
  unfold OldCondition discount
  rcases accepted with (((a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8) | a9) | a10)
  · have s := lowerEndpointNonnegative M1 a1; grind
  · have s := lowerEndpointNonnegative M2 a2; grind
  · have s := lowerEndpointNonnegative M3 a3; grind
  · have s := lowerEndpointNonnegative M4 a4; grind
  · have s := lowerEndpointNonnegative M5 a5; grind
  · have s := lowerEndpointNonnegative M6 a6; grind
  · have s := lowerEndpointNonnegative M7 a7
    rcases select with e | e <;> grind
  · have s := lowerEndpointNonnegative M8 a8; grind
  · have s := lowerEndpointPositive M9 a9; grind
  · have s := lowerEndpointPositive M10 a10; grind

end Ordered
end RankSeven.UpperOldRegions

#print axioms RankSeven.UpperOldRegions.acceptedOldCondition
