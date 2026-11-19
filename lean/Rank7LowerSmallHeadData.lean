import Rank7UpperPhysicalInterior
namespace RankSeven.LowerSmallHeadData
open Pauli ExteriorCuts PackingDual
def tags : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
def mon {R : Type} [Lean.Grind.CommRing R] (x y r z : R) : Nat→R
  | 0 => r^4
  | 1 => y*r^3
  | 2 => y^2*r^2
  | 3 => y^3*r
  | 4 => y^4
  | 5 => x*r^3
  | 6 => x*y*r^2
  | 7 => x*y^2*r
  | 8 => x*y^3
  | 9 => x^2*r^2
  | 10 => x^2*y*r
  | 11 => x^2*y^2
  | 12 => x^3*r
  | 13 => x^3*y
  | 14 => x^4
  | 15 => r^3*z
  | 16 => y*r^2*z
  | 17 => y^2*r*z
  | 18 => y^3*z
  | 19 => x*r^2*z
  | 20 => x*y*r*z
  | 21 => x*y^2*z
  | 22 => x^2*r*z
  | 23 => x^2*y*z
  | 24 => x^3*z
  | _ => 0
def coeffRow : Nat → Array Nat
  | 0 => #[1,8,24,32,16,4,24,48,32,6,24,24,4,8,1,0,0,0,0,0,0,0,0,0,0]
  | 1 => #[1,9,30,44,24,5,33,72,52,9,39,42,7,15,2,1,6,12,8,3,12,12,3,6,1]
  | 2 => #[1,9,30,44,24,5,33,72,52,9,39,42,7,15,2,0,0,0,0,0,0,0,0,0,0]
  | 3 => #[1,10,37,60,36,6,44,106,84,13,62,73,12,28,4,1,7,16,12,4,18,20,5,11,2]
  | 4 => #[1,8,24,32,16,5,30,60,40,9,36,36,7,14,2,0,0,0,0,0,0,0,0,0,0]
  | 5 => #[1,9,30,44,24,6,40,88,64,13,57,62,12,26,4,1,6,12,8,4,16,16,5,10,2]
  | 6 => #[1,9,30,44,24,6,40,88,64,13,57,62,12,26,4,0,0,0,0,0,0,0,0,0,0]
  | 7 => #[1,10,37,60,36,7,52,127,102,18,88,106,20,48,8,1,7,16,12,5,23,26,8,18,4]
  | _ => #[]
def cf (s j : Nat) : Nat := (coeffRow s)[j]?.getD 0
def mask (w : Wedge7) := (occupied w 0).toNat+2*(occupied w 1).toNat+4*(occupied w 2).toNat
inductive Corner | off | first | both | mixed deriving DecidableEq,Repr
def tailPrice (k : Corner) (w : Wedge7) : Nat :=
  let f := !occupied w 5
  let g := !occupied w 6
  match k with | .off => (f&&g).toNat | .first => g.toNat | .both => 1 | .mixed => f.toNat+g.toNat
def cost (k : Corner) (j : Nat) (w : Wedge7) := cf (mask w) j * tailPrice k w
def refN (c : Wedge7→Nat) : Nat := (wedges.map (fun w => if SectorDefectAccounting.planeFlag w then c w else 0)).sum
structure Plan where
  denom : Nat
  prices : PackingDual.Prices
def Plan.ok (p : Plan) (c : Wedge7→Nat) : Bool := decide (0<p.denom) && p.prices.all (fun a => a.2.legal) && wedges.all (fun w => decide (p.denom*c w ≤ cover p.prices w)) && decide (priceCap p.prices ≤ p.denom*refN c)
end RankSeven.LowerSmallHeadData
