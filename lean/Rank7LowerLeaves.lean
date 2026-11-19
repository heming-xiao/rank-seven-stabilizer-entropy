import Rank7LowerContractor
import Rank7UpperWeighted

namespace RankSeven.LowerLeaves

open Lean.Grind Interval LowerContractor
open UpperContractor (whole wholeSound fractionSound divSound quotientEq
  lowerEndpointNonnegative lowerEndpointPositive)
open UpperWeighted (larger largerSound)

def acceptsOld (g : Grid) (box : Region) : Bool :=
  let w := whole g
  let mul := Bounds.mul g
  let d := mul box.y ((box.z.add box.y).add box.x)
  let gain := mul box.z box.x
  let b2 := Bounds.square g box.b
  let head := (box.z.add (mul (w 2) box.y)).add (mul (w 3) box.x)
  let width := box.b.sub (w 1)
  decide (0≤(head.sub (mul (w 5) gain)).lo) ||
  decide (0<((mul b2 d).sub (Bounds.rational g 1800 61)).lo) ||
  decide (0<((mul b2 gain).sub (w 160)).lo) ||
  decide (0≤(((w 1).sub box.x).sub (mul (w 2) box.y)).lo) ||
  decide (((mul (w 96) box.y).sub (w 1)).hi≤0) ||
  decide ((box.x.sub (Bounds.div g (Bounds.rational g 2 3) box.b)).hi≤0) ||
  decide ((box.x.sub width).hi≤0) ||
  decide ((box.z.sub (mul width (((w 1).add box.x).add box.y))).hi≤0)

def weightedPrice (g : Grid) (box : Region) (w : Bounds) : Bounds :=
  let C := whole g
  let mul := Bounds.mul g
  let sq := Bounds.square g
  let d := mul box.y ((box.z.add box.y).add box.x)
  let gain := mul box.z box.x
  let z2 := sq box.z
  let y2 := sq box.y
  let x2 := sq box.x
  let anti := mul y2 (y2.add (Bounds.div g (z2.add x2) (C 2)))
  let shifted := mul (mul (mul (C 12) w) ((C 2).sub w)) (sq d)
  let high := mul (shifted.add anti) (Bounds.div g (C 1) (Bounds.rational g 5 2))
  let reserve := (Bounds.div g (sq gain) (C 24)).largest (Bounds.div g (sq x2) (C 72))
  let payment := mul (sq box.b) (high.add reserve)
  (payment.add (mul (C 168) box.y)).sub (mul ((C 168).sub (mul (C 24) w)) d)

def weightedShifts (g : Grid) : List Bounds :=
  [Bounds.rational g 5 4, Bounds.rational g 3 2, whole g 1, Bounds.rational g 7 4]

def acceptsWeighted (g : Grid) (box : Region) : Bool :=
  (weightedShifts g).any (fun w => decide (0<(weightedPrice g box w).lo))

section Ordered

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

def OldCondition (z y x b : R) : Prop :=
  let d := y*(z+y+x)
  let gain := z*x
  5*gain≤z+2*y+3*x ∨
  (1800/61:R)<b*b*d ∨
  160<b*b*gain ∨
  x+2*y≤1 ∨
  96*y≤1 ∨
  x≤(2/3:R)/b ∨
  x≤b-1 ∨
  z≤(b-1)*(1+x+y)

noncomputable def weightedMargin (z y x b w : R) : R :=
  let d := y*(z+y+x)
  let gain := z*x
  let anti := (y*y)*(y*y+(z*z+x*x)/2)
  let high := (12*w*(2-w)*(d*d)+anti)*(1/(5/2:R))
  let reserve := larger (gain*gain/24) ((x*x)*(x*x)/72)
  b*b*(high+reserve)+168*y-(168-24*w)*d

/-- Integer old-region acceptance certifies at least one of the eight real guards. -/
theorem acceptedOldCondition {g : Grid} {box : Region} {z y x b : R}
    (valid : Valid g box) (inside : Inside g box z y x b) (accepted : acceptsOld g box=true) :
    OldCondition z y x b := by
  have bPositive : 0<box.b.lo := Int.lt_of_lt_of_le g.positive valid.bLower
  obtain ⟨zz,yy,xx,bb⟩ := inside
  let N := wholeSound (R:=R) g
  have D := Bounds.mulSound yy (Bounds.addSound (Bounds.addSound zz yy) xx)
  have G := Bounds.mulSound zz xx
  have B := Bounds.squareSound bb
  have L := Bounds.addSound (Bounds.addSound zz (Bounds.mulSound (N 2) yy)) (Bounds.mulSound (N 3) xx)
  have W := Bounds.subSound bb (N 1)
  have m1 := Bounds.subSound L (Bounds.mulSound (N 5) G)
  have m2 := Bounds.subSound (Bounds.mulSound B D) (fractionSound (R:=R) g 1800 61 (by decide))
  have m3 := Bounds.subSound (Bounds.mulSound B G) (N 160)
  have m4 := Bounds.subSound (Bounds.subSound (N 1) xx) (Bounds.mulSound (N 2) yy)
  have m5 := Bounds.subSound (Bounds.mulSound (N 96) yy) (N 1)
  have m6 := Bounds.subSound xx (divSound (fractionSound (R:=R) g 2 3 (by decide)) bb bPositive)
  have m7 := Bounds.subSound xx W
  have m8 := Bounds.subSound zz (Bounds.mulSound W (Bounds.addSound (Bounds.addSound (N 1) xx) yy))
  unfold acceptsOld at accepted
  simp only [Bool.or_eq_true,decide_eq_true_eq] at accepted
  unfold OldCondition
  rcases accepted with (((((((a1 | a2) | a3) | a4) | a5) | a6) | a7) | a8)
  · have := lowerEndpointNonnegative m1 a1; grind only
  · have := lowerEndpointPositive m2 a2; grind only
  · have := lowerEndpointPositive m3 a3; grind only
  · have := lowerEndpointNonnegative m4 a4; grind only
  · have := Bounds.nonpositive m5 a5; grind only
  · have := Bounds.nonpositive m6 a6; grind only
  · have := Bounds.nonpositive m7 a7; grind only
  · have := Bounds.nonpositive m8 a8; grind only

/-- Every operation in the lower weighted leaf is enclosed by the actual
C++ interval evaluation. -/
theorem weightedPriceSound {box : Region} {shift : Bounds} {z y x b w : R}
    (inside : Inside cppGrid box z y x b) (u : shift.Contains cppGrid w) :
    (weightedPrice cppGrid box shift).Contains cppGrid (weightedMargin z y x b w) := by
  obtain ⟨zz,yy,xx,bb⟩ := inside
  let N := wholeSound (R:=R) cppGrid
  have D := Bounds.mulSound yy (Bounds.addSound (Bounds.addSound zz yy) xx)
  have G := Bounds.mulSound zz xx
  have B := Bounds.squareSound bb
  have Z2 := Bounds.squareSound zz
  have Y2 := Bounds.squareSound yy
  have X2 := Bounds.squareSound xx
  have halves := divSound (Bounds.addSound Z2 X2) (N 2) (by decide)
  have anti := Bounds.mulSound Y2 (Bounds.addSound Y2 halves)
  have shifted := Bounds.mulSound (Bounds.mulSound (Bounds.mulSound (N 12) u) (Bounds.subSound (N 2) u))
    (Bounds.squareSound D)
  have ig := divSound (N 1) (fractionSound (R:=R) cppGrid 5 2 (by decide)) (by decide)
  have high := Bounds.mulSound (Bounds.addSound shifted anti) ig
  have reserve := largerSound (divSound (Bounds.squareSound G) (N 24) (by decide))
    (divSound (Bounds.squareSound X2) (N 72) (by decide))
  have payment := Bounds.mulSound B (Bounds.addSound high reserve)
  exact Bounds.subSound (Bounds.addSound payment (Bounds.mulSound (N 168) yy))
    (Bounds.mulSound (Bounds.subSound (N 168) (Bounds.mulSound (N 24) u)) D)

theorem acceptedWeightedMargin {box : Region} {z y x b : R}
    (inside : Inside cppGrid box z y x b) (accepted : acceptsWeighted cppGrid box=true) :
    ∃ w : R, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ 0<weightedMargin z y x b w := by
  obtain ⟨shift,mem,positive⟩ := List.any_eq_true.mp accepted
  have cases : shift=Bounds.rational cppGrid 5 4 ∨ shift=Bounds.rational cppGrid 3 2 ∨
      shift=whole cppGrid 1 ∨ shift=Bounds.rational cppGrid 7 4 := by
    simpa [weightedShifts] using mem
  obtain ⟨w,hW,bounded⟩ :
      ∃ w : R, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ shift.Contains cppGrid w := by
    rcases cases with rfl | rfl | rfl | rfl
    · exact ⟨5/4,Or.inl rfl,fractionSound cppGrid 5 4 (by decide)⟩
    · exact ⟨3/2,Or.inr (Or.inl rfl),fractionSound cppGrid 3 2 (by decide)⟩
    · exact ⟨1,Or.inr (Or.inr (Or.inl rfl)),wholeSound cppGrid 1⟩
    · exact ⟨7/4,Or.inr (Or.inr (Or.inr rfl)),fractionSound cppGrid 7 4 (by decide)⟩
  exact ⟨w,hW,lowerEndpointPositive (weightedPriceSound inside bounded) (_root_.of_decide_eq_true positive)⟩

/-- Failure of the real guards yields the exact scalar residual consumed by
the lower contractor. The application to physical counterexamples is separate. -/
theorem residualOfOldFailure {z y x b : R} (head : 1≤2*x) (y0 : 0≤y) (z0 : 0≤z)
    (b0 : 0<b) (failure : ¬OldCondition z y x b) : Residual z y x b := by
  unfold OldCondition at failure
  dsimp only at failure
  have tail : (2/3:R)/b<x := by grind only
  have scaled := OrderedRing.mul_lt_mul_of_pos_left tail b0
  rw [quotientEq _ b0] at scaled
  have divThree := quotientEq (2:R) (show (0:R)<3 by grind only)
  have tailMultiply := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt scaled) (show (0:R)≤3 by grind only)
  have cap : b*b*(y*(z+y+x))≤(1800/61:R) := by grind only
  have divSixtyOne := quotientEq (1800:R) (show (0:R)<61 by grind only)
  have scaledCap := OrderedRing.mul_le_mul_of_nonneg_left cap (show (0:R)≤61 by grind only)
  exact ⟨head,y0,z0,by grind only,by grind only,by grind only,
    by grind only,by grind only,by grind only⟩

end Ordered
end RankSeven.LowerLeaves

#print axioms RankSeven.LowerLeaves.acceptedOldCondition
#print axioms RankSeven.LowerLeaves.weightedPriceSound
#print axioms RankSeven.LowerLeaves.acceptedWeightedMargin
#print axioms RankSeven.LowerLeaves.residualOfOldFailure
