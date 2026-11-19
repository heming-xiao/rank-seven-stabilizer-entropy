import Rank7UpperCorner
namespace RankSeven.PointProducts
open Interval

/-- Signed endpoint multiplication by a grid point representing an integer.
The endpoint sorting remains correct for inverted input bounds as well. -/
def exactInteger (a : Bounds) (k : Int) : Bounds :=
  ⟨min (a.lo*k) (a.hi*k),max (a.lo*k) (a.hi*k)⟩

theorem exactInteger_eq (g : Grid) (a : Bounds) (k : Int) :
    exactInteger a k=Bounds.mul g a (Bounds.point (k*g.scale)) := by
  unfold exactInteger Bounds.mul Bounds.point floor ceil
  simp only [←Int.mul_assoc]
  have pos := g.positive
  have nonnegative : 0≤g.scale := by omega
  have ne : g.scale≠0 := by omega
  have lower (v w : Int) : min (v*g.scale) (w*g.scale)=min v w*g.scale := by
    by_cases h : v≤w
    · have e := Int.mul_le_mul_of_nonneg_right h nonnegative
      simp [Int.min_def,h,e]
    · have e := Int.mul_le_mul_of_nonneg_right (show w≤v by omega) nonnegative
      rw [Int.min_eq_right e,Int.min_eq_right (by omega)]
  have upper (v w : Int) : max (v*g.scale) (w*g.scale)=max v w*g.scale := by
    by_cases h : v≤w
    · have e := Int.mul_le_mul_of_nonneg_right h nonnegative
      rw [Int.max_eq_right e,Int.max_eq_right h]
    · have e := Int.mul_le_mul_of_nonneg_right (show w≤v by omega) nonnegative
      rw [Int.max_eq_left e,Int.max_eq_left (by omega)]
  simp only [Int.min_self,Int.max_self,lower,upper,←Int.neg_mul,floor,Int.mul_ediv_cancel _ ne,Int.neg_neg]

def quantizedPoint (g : Grid) (a : Bounds) (p : Int) : Bounds :=
  let lo := a.lo*p
  let hi := a.hi*p
  ⟨floor (min lo hi) g.scale,ceil (max lo hi) g.scale⟩
theorem quantizedPoint_eq (g : Grid) (a : Bounds) (p : Int) :
    quantizedPoint g a p=Bounds.mul g a (Bounds.point p) := by
  simp only [quantizedPoint,Bounds.mul,Bounds.point,Int.min_self,Int.max_self]
def byPoint (a b : Bounds) : Bounds :=
  if b.lo=b.hi then
    if b.lo=0 then ⟨0,0⟩
    else if b.lo=134217728 then ⟨min a.lo a.hi,max a.lo a.hi⟩
    else if b.lo=268435456 then exactInteger a 2
    else if b.lo=536870912 then exactInteger a 4
    else quantizedPoint cppGrid a b.lo
  else Bounds.mul cppGrid a b
theorem byPoint_eq (a b : Bounds) : byPoint a b=Bounds.mul cppGrid a b := by
  rcases b with ⟨bl,bh⟩
  unfold byPoint; dsimp only; split
  · rename_i eq; subst bh; split
    · rename_i zero; subst bl; simpa only [exactInteger,Int.mul_zero,Int.zero_mul,Int.min_self,Int.max_self,Bounds.point] using exactInteger_eq cppGrid a 0
    · split
      · rename_i one; subst bl; simpa only [exactInteger,Int.mul_one,Int.one_mul,Bounds.point,show cppGrid.scale=134217728 from rfl] using exactInteger_eq cppGrid a 1
      · split
        · rename_i two; subst bl; exact exactInteger_eq cppGrid a 2
        · split
          · rename_i four; subst bl; exact exactInteger_eq cppGrid a 4
          · exact quantizedPoint_eq _ _ _
  · rfl
end RankSeven.PointProducts
#print axioms RankSeven.PointProducts.byPoint_eq

namespace RankSeven.PointMargin

open Interval

open UpperCorner (TailBox Shifts Ray)
private def grid := cppGrid

private def fraction (n d : Int) : Bounds := Bounds.rational grid n d

local instance : OfNat Bounds n where
  ofNat := Bounds.point (Int.ofNat n * grid.scale)

local instance : Add Bounds := ⟨Bounds.add⟩
local instance : Sub Bounds := ⟨Bounds.sub⟩
local instance : Mul Bounds := ⟨Bounds.mul grid⟩

private def byInteger (a : Bounds) (n : Nat) : Bounds :=
  Bounds.div grid a (Bounds.point (Int.ofNat n * grid.scale))

private def checkedDiv (a b : Bounds) : Option Bounds :=
  if 0 < b.lo then some (Bounds.div grid a b) else none

private def square (a : Bounds) : Bounds := a.square grid

private def supportWeight (inner outer : Bounds) : Option Bounds := do
  let value ← checkedDiv (inner - outer).positivePart (inner + outer)
  return Bounds.point value.lo

private def supportValue (inner outer w : Bounds) : Bounds :=
  let halfSquare := byInteger (square w) 2
  (w - halfSquare) * inner - (w + halfSquare) * outer

/-- Interval evaluation of the upper verifier's two corner margins, in
    corner-major and ray-minor order. Every variable denominator is checked
    before use. The exact rational divisions by literals use positive integers. -/
def usingProducts (mul : Bounds→Bounds→Bounds) (rays : List Ray) (box : TailBox) (shifts : Shifts) : Option (List (List (Int × Int))) := do
  let ⟨h, k, q, c, d⟩ := box
  let ⟨f, u, w⟩ := shifts
  if c.lo < d.hi then none else
    let x := h + k + q
    let y := k + q
    let g := h * q
    let delta := k * x
    let L := h + 2*k + 3*q
    let alpha := 1 + x
    let beta := 1 + y
    let gamma := 1 + q
    let pair := alpha * gamma
    let upperOne := alpha * beta
    let lowerShared := alpha.largest (beta * gamma)
    let h2 := square h
    let q2 := square q
    let k2 := square k
    let g2 := square g
    let d2 := square delta
    let anti := k2 * (k2 + byInteger (h2 + q2) 2)
    let cl := Bounds.point c.lo
    let ch := Bounds.point c.hi
    let dl := Bounds.point d.lo
    let dh := Bounds.point d.hi
    let ws ← supportWeight (pair * dl) lowerShared
    let w1 ← supportWeight (upperOne * cl * dl) pair
    let psiTail := (fraction 1 13).largest
      (square (cl - dh).positivePart + byInteger (square (1 - ch) + square dl) 6)
    let psi := byInteger (h2 + q2) 6 + psiTail
    let oddDen := h2 + 3*q2
    let cubic := x * y * q
    let H := g - h - 3*q - fraction 5 2
    let invRate ← checkedDiv 1 (fraction 4242 25)
    let invGeom ← checkedDiv 1 (fraction 5 2)
    let price := (1 - f) * fraction 200 11
    let g0 := (g - price * (ch - dl)).positivePart
    let qinv ← checkedDiv psi (psi + 12 * square f)
    let s := u * g0 * qinv
    let lambda := (24 * invRate) * s
    let sharedQuad := 12 * u * (2 - u) * square g0 * qinv
    let mu := (24 * invRate) * w * delta
    let highestResidual := delta - mu
    let C := (cubic - lambda * (y + q) - mu * q).positivePart
    let highestQuad := 12 * w * (2 - w) * d2 + anti
    [(cl, dl), (ch, dl), (cl, dh), (ch, dh)].mapM fun (c0, d0) => do
      let dsq := square d0
      let cd := c0 * d0
      let odd := (1 - ch) * (1 + ch - 2*c0) + dl * (2*d0 - dl)
      let tailPrefix := (1 - d0) * (c0 - d0)
      let spread := c0 - d0
      let one := supportValue (upperOne * cd) pair w1
      let shared := c0 * supportValue (pair * d0) lowerShared ws
      let oddShared ← checkedDiv (odd * g2) oddDen
      let physicalShared := byInteger
        ((g2 + sharedQuad + 24*s*price*(ch - dl - spread) + oddShared) * invRate) 12
      let physicalHigh := (highestQuad + byInteger (odd * k2) 2) * invRate * invGeom
      let increment := (dsq * d0 * q).smallest (c0 * C)
      let singleton := cd * L
      let splitDebit := cd * (H - lambda)
      let singleDebit := cd * (g - lambda)
      return rays.map fun r =>
        let cuts := 96 * invRate * ((mul one r.traceOne) + (mul shared r.traceShared))
        let base := (mul physicalShared r.peak) + (mul physicalHigh r.v) + cuts
          + highestResidual * ((mul tailPrefix r.tail) - (mul dsq r.v))
        let splitMargin := base + (mul (cd*k) r.v) - (mul splitDebit r.n)
        let singleMargin := base + (mul singleton r.m) + (mul (square dsq) r.constant) +
          (mul increment r.improvement) - (mul singleDebit r.n)
        (splitMargin.lo, singleMargin.lo)


theorem unmodified (box : TailBox) (s : Shifts) :
    usingProducts (Bounds.mul cppGrid) UpperCorner.rays box s=UpperCorner.margins box s := by rfl
def point := usingProducts PointProducts.byPoint UpperCorner.rays
theorem point_eq (box : TailBox) (s : Shifts) : point box s=UpperCorner.margins box s := by
  unfold point; rw [show PointProducts.byPoint=Bounds.mul cppGrid from
    funext (fun a => funext (fun b => PointProducts.byPoint_eq a b)),unmodified]
end RankSeven.PointMargin
#print axioms RankSeven.PointMargin.point_eq
