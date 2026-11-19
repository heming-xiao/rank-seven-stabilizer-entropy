import Rank7Interval

namespace RankSeven.UpperCorner

open Interval

structure TailBox where
  h : Bounds
  k : Bounds
  q : Bounds
  c : Bounds
  d : Bounds

structure Shifts where
  f : Bounds
  u : Bounds
  w : Bounds

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

structure Ray where
  n : Bounds
  v : Bounds
  m : Bounds
  peak : Bounds
  constant : Bounds
  improvement : Bounds
  tail : Bounds
  traceOne : Bounds
  traceShared : Bounds

def ray (nb vb traceOne traceShared : Bounds) : Ray :=
  let m := nb.largest (byInteger vb 2)
  ⟨nb, vb, m, nb.largest vb,
    ((fraction 5 2 * nb).largest (2 * vb)).largest (2 * nb + vb),
    (2 * nb + vb - 3 * m).positivePart, vb.largest (byInteger nb 2), traceOne, traceShared⟩

def rays : List Ray :=
  [ray 1 0 0 (fraction 1 2),
   ray 1 (fraction 1 2) (fraction 3 8) (fraction 1 2),
   ray 1 (fraction 2 3) (fraction 4 9) (fraction 1 2),
   ray 1 1 (fraction 2 3) (fraction 2 3),
   ray 1 2 (fraction 4 3) (fraction 5 6),
   ray 1 4 (fraction 8 3) (fraction 11 12),
   ray 0 1 (fraction 2 3) 0]

private def supportWeight (inner outer : Bounds) : Option Bounds := do
  let value ← checkedDiv (inner - outer).positivePart (inner + outer)
  return Bounds.point value.lo

private def supportValue (inner outer w : Bounds) : Bounds :=
  let halfSquare := byInteger (square w) 2
  (w - halfSquare) * inner - (w + halfSquare) * outer

/-- Interval evaluation of the upper verifier's two corner margins, in
    corner-major and ray-minor order. Every variable denominator is checked
    before use. The exact rational divisions by literals use positive integers. -/
def margins (box : TailBox) (shifts : Shifts) : Option (List (List (Int × Int))) := do
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
        let cuts := 96 * invRate * (one * r.traceOne + shared * r.traceShared)
        let base := physicalShared * r.peak + physicalHigh * r.v + cuts
          + highestResidual * (tailPrefix * r.tail - dsq * r.v)
        let splitMargin := base + cd*k*r.v - splitDebit*r.n
        let singleMargin := base + singleton*r.m + square dsq*r.constant +
          increment*r.improvement - singleDebit*r.n
        (splitMargin.lo, singleMargin.lo)

def sectorMargins (box : TailBox) (shifts : Shifts) (sector : Nat) :
    Option (List (Int × Int × Int × Int)) := do
  let corners ← margins box shifts
  corners.mapM fun row => do
    let (s₁, t₁) ← row[sector]?
    let (s₂, t₂) ← row[sector + 1]?
    return (s₁, t₁, s₂, t₂)

end RankSeven.UpperCorner
