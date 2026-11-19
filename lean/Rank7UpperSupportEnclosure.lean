import Rank7UpperPrices
import Rank7UpperWeighted

/-! Exact real meaning of the rounded lower support price used throughout
one upper-tail rectangle. The selected weight is the lower grid endpoint. -/
namespace RankSeven.UpperSupportEnclosure
open Lean.Grind Interval UpperContractor UpperPrices
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

def checkedWeight (inner outer : Bounds) : Option Bounds :=
  let num := (inner.sub outer).positivePart
  let den := inner.add outer
  if 0<den.lo then some (Bounds.point (Bounds.div cppGrid num den).lo) else none

theorem clipped {a : Bounds} {x : R} (hx : a.Contains cppGrid x) :
    a.positivePart.Contains cppGrid (positivePart x) := by
  apply Bounds.positivePartSound hx; unfold positivePart; split <;> grind only

/-- The exact ratio is only an upper limit on the selected weight.
Its lower interval endpoint itself is the common real weight. -/
theorem checkedWeightSound {a b out : Bounds} {x y : R}
    (ha : a.Contains cppGrid x) (hb : b.Contains cppGrid y) (check : checkedWeight a b=some out) :
    out.Contains cppGrid (value (R:=R) cppGrid out.lo) ∧
    0≤value (R:=R) cppGrid out.lo ∧ value (R:=R) cppGrid out.lo≤supportRatio x y ∧ 0<x+y := by
  let num := (a.sub b).positivePart
  let den := a.add b
  let box := Bounds.div cppGrid num den
  have n : num.Contains cppGrid (positivePart (x-y)) := clipped (Bounds.subSound ha hb)
  have d : den.Contains cppGrid (x+y) := Bounds.addSound ha hb
  change (if 0<den.lo then some (Bounds.point box.lo) else none)=some out at check
  split at check
  · rename_i pos
    obtain rfl := (Option.some.inj check).symm
    have ratio : box.Contains cppGrid (supportRatio x y) := divSound n d pos
    have nh : 0≤num.lo := by change 0≤max 0 _; omega
    have dh : 0<den.hi := by have ord := noEmpty d; omega
    have nonnegative : 0≤box.lo := by
      change 0≤floor (num.lo*cppGrid.scale) (if num.lo<0 then den.lo else den.hi)
      rw [ite_eq_right (by omega)]; exact Int.ediv_nonneg (Int.mul_nonneg nh (by decide)) (by omega)
    exact ⟨pointSound _ _,lowerEndpointNonnegative (pointSound (R:=R) cppGrid box.lo) nonnegative,
      (insideEndpoints.mp ratio).1,lowerEndpointPositive d pos⟩
  · contradiction

def price (a b w : Bounds) : Bounds :=
  let halfSquare := Bounds.div cppGrid (w.square cppGrid) (whole cppGrid 2)
  ((w.sub halfSquare).mul cppGrid a).sub ((w.add halfSquare).mul cppGrid b)

theorem priceEnclosed {a b w : Bounds} {x y t : R} (ha : a.Contains cppGrid x) (hb : b.Contains cppGrid y)
    (hw : w.Contains cppGrid t) : (price a b w).Contains cppGrid (supportValue x y t) := by
  have sq := divSound (Bounds.squareSound hw) (wholeSound (R:=R) cppGrid 2) (by decide)
  have answer := Bounds.subSound (Bounds.mulSound (Bounds.subSound hw sq) ha) (Bounds.mulSound (Bounds.addSound hw sq) hb)
  unfold price supportValue
  rw [show t^2=t*t by grind only]
  exact answer

/-- The two literal lower-endpoint weights give nonnegative prices at every
point of the rectangle. -/
theorem commonSupportPrices {ih oh is os cl dl wh ws : Bounds} {I O J P c₀ d₀ c d : R}
    (hi : ih.Contains cppGrid I) (ho : oh.Contains cppGrid O) (hs : is.Contains cppGrid J)
    (ht : os.Contains cppGrid P) (hc : cl.Contains cppGrid c₀) (hd : dl.Contains cppGrid d₀)
    (c₀p : 0≤c₀) (d₀p : 0≤d₀) (cp : c₀≤c) (dp : d₀≤d)
    (i0 : 0≤I) (o0 : 0≤O) (j0 : 0≤J) (p0 : 0≤P)
    (hw : checkedWeight ((ih.mul cppGrid cl).mul cppGrid dl) oh=some wh)
    (sw : checkedWeight (is.mul cppGrid dl) os=some ws) :
    let high := value (R:=R) cppGrid wh.lo
    let shared := value (R:=R) cppGrid ws.lo
    wh.Contains cppGrid high ∧ ws.Contains cppGrid shared ∧
    0≤supportValue (I*c*d) O high ∧ 0≤c*supportValue (J*d) P shared := by
  obtain ⟨ge,g0,gl,gd⟩ := checkedWeightSound (Bounds.mulSound (Bounds.mulSound hi hc) hd) ho hw
  obtain ⟨se,s0,sl,sd⟩ := checkedWeightSound (Bounds.mulSound hs hd) ht sw
  exact ⟨ge,se,rectangleSupports c₀p d₀p cp dp i0 o0 j0 p0 gd sd g0 s0 gl sl⟩

end RankSeven.UpperSupportEnclosure
#print axioms RankSeven.UpperSupportEnclosure.checkedWeightSound
#print axioms RankSeven.UpperSupportEnclosure.priceEnclosed
#print axioms RankSeven.UpperSupportEnclosure.commonSupportPrices
