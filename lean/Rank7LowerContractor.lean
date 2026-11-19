import Rank7UpperContractor

namespace RankSeven.LowerContractor

open Lean.Grind Interval
open UpperContractor (whole wholeSound wholeMulPoint value valuePos insideEndpoints
  pointSound fractionSound divSound quotientEq cancelLe maxLower minUpper noEmpty)

structure Region where
  z : Bounds
  y : Bounds
  x : Bounds
  b : Bounds
  deriving DecidableEq

private def raise (a : Bounds) (endpoint : Int) : Bounds :=
  ⟨max a.lo endpoint,a.hi⟩

private def lower (a : Bounds) (endpoint : Int) : Bounds :=
  ⟨a.lo,min a.hi endpoint⟩

private def cutX (g : Grid) (box : Region) : Bounds :=
  let tail := Bounds.div g (Bounds.rational g 2 3) (Bounds.point box.b.hi)
  let width := (Bounds.point box.b.lo).sub (whole g 1)
  raise (raise box.x tail.lo) width.lo

private def sharedHead (g : Grid) (box : Region) (x : Bounds) : Bounds :=
  Bounds.mul g ((Bounds.point box.b.lo).sub (whole g 1)) (((whole g 1).add x).add box.y)

private def lowHead (g : Grid) (box : Region) (x : Bounds) : Bounds :=
  let num := (Bounds.mul g (whole g 2) box.y).add (Bounds.mul g (whole g 3) x)
  let den := (Bounds.mul g (whole g 5) (Bounds.point x.hi)).sub (whole g 1)
  Bounds.div g num den

private def cutZ (g : Grid) (box : Region) (x : Bounds) : Bounds :=
  raise (raise box.z (sharedHead g box x).lo) (lowHead g box x).lo

private def deltaLimit (g : Grid) (b : Bounds) : Bounds :=
  Bounds.div g (Bounds.rational g 1800 61) (Bounds.square g (Bounds.point b.lo))

private def productLimit (g : Grid) (b : Bounds) : Bounds :=
  Bounds.div g (whole g 160) (Bounds.square g (Bounds.point b.lo))

private def clipped (g : Grid) (box : Region) (z x : Bounds) : Region :=
  let cap := deltaLimit g box.b
  let prod := productLimit g box.b
  let zx := (Bounds.point z.lo).add (Bounds.point x.lo)
  let y := lower box.y (Bounds.div g cap zx).hi
  let z' := lower z (Bounds.div g prod (Bounds.point x.lo)).hi
  let x' := lower x (Bounds.div g prod (Bounds.point z.lo)).hi
  if 0<box.y.lo then
    let quotient := (Bounds.div g cap (Bounds.point box.y.lo)).sub (Bounds.point box.y.lo)
    ⟨lower z' (quotient.sub (Bounds.point x.lo)).hi,y,
      lower x' (quotient.sub (Bounds.point z.lo)).hi,box.b⟩
  else ⟨z',y,x',box.b⟩

/-- The two pruning tests and every directed operation of the lower C++ contractor. -/
def reduce (g : Grid) (box : Region) : Option Region :=
  let x := cutX g box
  let z := cutZ g box x
  if x.hi<x.lo ∨ z.hi<z.lo then none else
  let out := clipped g box z x
  if out.z.hi<out.z.lo ∨ out.y.hi<out.y.lo ∨ out.x.hi<out.x.lo then none else some out

structure Valid (g : Grid) (box : Region) : Prop where
  bLower : g.scale≤box.b.lo
  zPositive : 0<box.z.lo
  xPositive : 0<box.x.lo

/-- A surviving contraction keeps the lower endpoint invariants. -/
theorem reduceValid {g : Grid} {box out : Region} (valid : Valid g box)
    (reduced : reduce g box=some out) : Valid g out := by
  dsimp only [reduce] at reduced
  split at reduced
  · contradiction
  split at reduced
  · contradiction
  have e := Option.some.inj reduced
  subst out
  have xpos := valid.xPositive
  have zpos := valid.zPositive
  dsimp only [clipped]
  split <;> constructor
  all_goals first
    | exact valid.bLower
    | dsimp only [cutX,cutZ,raise,lower]; omega

/-- The six inclusive root boxes in the order used by the lower C++ driver. -/
def initial (slab : Fin 6) : Region :=
  let g := cppGrid
  let r := Bounds.rational g
  let points := [r 4 3,r 5 4,r 6 5,r 23 20,r 11 10,r 21 20,r 101 100]
  let left := points[slab.val+1]'(by exact Nat.succ_lt_succ slab.isLt)
  let right := points[slab.val]'(by exact Nat.lt_trans slab.isLt (by decide : 6<7))
  ⟨⟨(r 3 5).lo,190*g.scale⟩,⟨(r 1 96).lo,(r 11 2).hi⟩,
    ⟨(r 1 2).lo,17*g.scale⟩,⟨left.lo,right.hi⟩⟩

theorem initialValid (slab : Fin 6) : Valid cppGrid (initial slab) := by
  constructor <;> revert slab <;> decide

section Ordered

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

structure Inside (g : Grid) (box : Region) (z y x b : R) : Prop where
  zInside : box.z.Contains g z
  yInside : box.y.Contains g y
  xInside : box.x.Contains g x
  bInside : box.b.Contains g b

/-- Necessary inequalities in the surviving lower slab, in C++ coordinates. -/
structure Residual (z y x b : R) : Prop where
  xHead : 1≤2*x
  yNonnegative : 0≤y
  zNonnegative : 0≤z
  tail : 2≤3*b*x
  xShared : b-1≤x
  zShared : (b-1)*(1+x+y)≤z
  headWeight : z+2*y+3*x≤5*z*x
  deltaCap : 61*(b*b*(y*(z+y+x)))≤1800
  productCap : b*b*(z*x)≤160

private theorem raiseSound {g : Grid} {a : Bounds} {n : Int} {x : R}
    (inside : a.Contains g x) (bound : value g n≤x) :
    (raise a n).Contains g x :=
  insideEndpoints.mpr ⟨maxLower g (insideEndpoints.mp inside).1 bound,(insideEndpoints.mp inside).2⟩

private theorem lowerSound {g : Grid} {a : Bounds} {n : Int} {x : R}
    (inside : a.Contains g x) (bound : x≤value g n) :
    (lower a n).Contains g x :=
  insideEndpoints.mpr ⟨(insideEndpoints.mp inside).1,minUpper g (insideEndpoints.mp inside).2 bound⟩

/-- The real inequalities behind all the lower endpoint candidates. -/
theorem lowerClamps {z y x b bl bu xu : R} (r : Residual z y x b)
    (blb : bl≤b) (bbu : b≤bu) (bu0 : 0<bu) (xxu : x≤xu) :
    ((2/3:R)/bu≤x ∧ bl-1≤x) ∧
      ((bl-1)*(1+x+y)≤z ∧ (2*y+3*x)/(5*xu-1)≤z) := by
  have no := r.xHead
  have yz := r.yNonnegative
  have zz := r.zNonnegative
  have tail := r.tail
  have xShared := r.xShared
  have zShared := r.zShared
  have head := r.headWeight
  have t0 := OrderedRing.mul_le_mul_of_nonneg_right bbu (show 0≤x by grind only)
  have btail := quotientEq ((2/3:R)) bu0
  have third := quotientEq (2:R) (show (0:R)<3 by grind only)
  have keep : (2/3:R)≤bu*x := by
    apply cancelLe (z:=(3:R)) (by grind only)
    grind only
  have zWidth := OrderedRing.mul_le_mul_of_nonneg_right blb (show 0≤1+x+y by grind only)
  have xWide := OrderedRing.mul_le_mul_of_nonneg_right xxu zz
  have den : 0<5*xu-1 := by grind only
  have zQuote := quotientEq (2*y+3*x) den
  refine ⟨⟨cancelLe bu0 (by grind only),by grind only⟩,
    ⟨by grind only,cancelLe den (by grind only)⟩⟩

/-- The old residual price evaluated at the smaller fifth probability
limits both products on the real point. -/
theorem productCaps {z y x b bl : R} (r : Residual z y x b) (bl0 : 0<bl) (blb : bl≤b) :
    y*(z+y+x)≤(1800/61:R)/(bl*bl) ∧ z*x≤160/(bl*bl) := by
  have xx := r.xHead
  have yy := r.yNonnegative
  have zz := r.zNonnegative
  have lowSq := OrderedRing.mul_pos bl0 bl0
  have highSq : bl*bl≤b*b := by
    have diff := OrderedRing.mul_nonneg (show 0≤b-bl by grind only) (show 0≤b+bl by grind only)
    grind only
  have limitingD := r.deltaCap
  have limitingG := r.productCap
  have D := OrderedRing.mul_le_mul_of_nonneg_right highSq
    (OrderedRing.mul_nonneg yy (show 0≤z+y+x by grind only))
  have G := OrderedRing.mul_le_mul_of_nonneg_right highSq
    (OrderedRing.mul_nonneg zz (show 0≤x by grind only))
  have divD := quotientEq (1800/61:R) lowSq
  have divG := quotientEq (160:R) lowSq
  have factor := quotientEq (1800:R) (show (0:R)<61 by grind only)
  constructor
  · apply cancelLe lowSq
    rw [divD]
    apply cancelLe (z:=(61:R)) (by grind only)
    have scaled := OrderedRing.mul_le_mul_of_nonneg_left D (show (0:R)≤61 by grind only)
    grind only
  · apply cancelLe lowSq
    rw [divG]
    grind only

theorem upperClamps {z y x b zl xl G D : R} (r : Residual z y x b)
    (z0 : 0<zl) (x0 : 0<xl) (zLower : zl≤z) (xLower : xl≤x)
    (gCap : z*x≤G) (dCap : y*(z+y+x)≤D) :
    z≤G/xl ∧ x≤G/zl ∧ y≤D/(zl+xl) := by
  have yy := r.yNonnegative
  have zz := r.zNonnegative
  have qz := OrderedRing.mul_le_mul_of_nonneg_left xLower zz
  have zq := OrderedRing.mul_le_mul_of_nonneg_right zLower (show 0≤x by grind only)
  have yr := OrderedRing.mul_le_mul_of_nonneg_left (show zl+xl≤z+y+x by grind only) yy
  have s0 : 0<zl+xl := by grind only
  refine ⟨cancelLe x0 ?_,cancelLe z0 ?_,cancelLe s0 ?_⟩
  · rw [quotientEq _ x0]; grind only
  · rw [quotientEq _ z0]; grind only
  · rw [quotientEq _ s0]; grind only

theorem positiveYClamps {z y x b zl xl yl D : R} (r : Residual z y x b)
    (y0 : 0<yl) (yLower : yl≤y) (zLower : zl≤z) (xLower : xl≤x)
    (dCap : y*(z+y+x)≤D) :
    z≤D/yl-yl-xl ∧ x≤D/yl-yl-zl := by
  have zz := r.zNonnegative
  have xx := r.xHead
  have bound := OrderedRing.mul_le_mul_of_nonneg_right yLower (show 0≤z+y+x by grind only)
  have dz := OrderedRing.mul_le_mul_of_nonneg_left (show z+yl+xl≤z+y+x by grind only) (Std.le_of_lt y0)
  have dx := OrderedRing.mul_le_mul_of_nonneg_left (show x+yl+zl≤z+y+x by grind only) (Std.le_of_lt y0)
  have quot := quotientEq D y0
  have zCut : z+yl+xl≤D/yl := cancelLe y0 (by rw [quot]; grind only)
  have xCut : x+yl+zl≤D/yl := cancelLe y0 (by rw [quot]; grind only)
  grind only


private theorem squareDenominator (g : Grid) {i : Int} (h : g.scale≤i) :
    0<(Bounds.square g (Bounds.point i)).lo := by
  have pos := g.positive
  have i0 : 0≤i := by omega
  have prod := Int.mul_le_mul_of_nonneg_right h i0
  have once := Int.mul_le_mul_of_nonneg_left (show 1≤i by omega) (show 0≤g.scale by omega)
  unfold Bounds.square Bounds.absolute Bounds.point floor
  dsimp only
  rw [Int.max_eq_left (show -i≤i by omega),Int.max_eq_right i0]
  have e : 1≤i*i/g.scale := (Int.le_ediv_iff_mul_le pos).mpr (by grind only)
  omega

private theorem lowerCoordinates {g : Grid} {box : Region} {z y x b : R}
    (r : Residual z y x b) (valid : Valid g box) (inside : Inside g box z y x b) :
    let X := cutX g box
    X.Contains g x ∧ (cutZ g box X).Contains g z := by
  let bl := value (R:=R) g box.b.lo
  let bu := value (R:=R) g box.b.hi
  let xu := value (R:=R) g box.x.hi
  have bUpward := noEmpty inside.bInside
  have bHi : 0<box.b.hi := by have := valid.bLower; have := g.positive; omega
  have limits := lowerClamps r (insideEndpoints.mp inside.bInside).1
    (insideEndpoints.mp inside.bInside).2 (valuePos g bHi) (insideEndpoints.mp inside.xInside).2
  have bMin : (Bounds.point box.b.lo).Contains g bl := pointSound g _
  have bMax : (Bounds.point box.b.hi).Contains g bu := pointSound g _
  let one := wholeSound (R:=R) g 1
  have xTail := divSound (fractionSound (R:=R) g 2 3 (by decide)) bMax bHi
  have width := Bounds.subSound bMin one
  have X : (cutX g box).Contains g x :=
    raiseSound (raiseSound inside.xInside (Std.le_trans (insideEndpoints.mp xTail).1 limits.1.1))
      (Std.le_trans (insideEndpoints.mp width).1 limits.1.2)
  have shared := Bounds.mulSound width (Bounds.addSound (Bounds.addSound one X) inside.yInside)
  have xMax : (Bounds.point box.x.hi).Contains g xu := pointSound g _
  have numerator := Bounds.addSound
    (Bounds.mulSound (wholeSound (R:=R) g 2) inside.yInside)
    (Bounds.mulSound (wholeSound (R:=R) g 3) X)
  have denominator := Bounds.subSound (Bounds.mulSound (wholeSound (R:=R) g 5) xMax) one
  have denPoint :
      (((Bounds.mul g (whole g 5) (Bounds.point box.x.hi)).sub (whole g 1)).lo) =
      (((Bounds.mul g (whole g 5) (Bounds.point box.x.hi)).sub (whole g 1)).hi) := by
    rw [wholeMulPoint]; rfl
  have denPos : 0<((Bounds.mul g (whole g 5) (Bounds.point box.x.hi)).sub (whole g 1)).lo := by
    by_cases pos : 0<((Bounds.mul g (whole g 5) (Bounds.point box.x.hi)).sub (whole g 1)).lo
    · exact pos
    · have nonpositive := Bounds.nonpositive denominator (by omega)
      have low := r.xHead
      have xHi := (insideEndpoints.mp inside.xInside).2
      change x≤xu at xHi
      grind only
  have lowest := divSound numerator denominator denPos
  have Z := raiseSound
    (raiseSound inside.zInside (Std.le_trans (insideEndpoints.mp shared).1 limits.2.1))
    (Std.le_trans (insideEndpoints.mp lowest).1 limits.2.2)
  exact ⟨X,Z⟩

private theorem clippedPreserves {g : Grid} {box : Region} {z y x b : R}
    (r : Residual z y x b) (valid : Valid g box) (inside : Inside g box z y x b) :
    let X := cutX g box
    let Z := cutZ g box X
    Inside g (clipped g box Z X) z y x b := by
  let X := cutX g box
  let Z := cutZ g box X
  have ⟨hX,hZ⟩ := lowerCoordinates r valid inside
  have Xpos : 0<X.lo := by
    have := valid.xPositive
    dsimp only [X,cutX,raise]; omega
  have Zpos : 0<Z.lo := by
    have := valid.zPositive
    dsimp only [Z,cutZ,raise]; omega
  let xl := value (R:=R) g X.lo
  let zl := value (R:=R) g Z.lo
  let bl := value (R:=R) g box.b.lo
  have xLow : xl≤x := (insideEndpoints.mp hX).1
  have zLow : zl≤z := (insideEndpoints.mp hZ).1
  have bPos : 0<box.b.lo := by have := valid.bLower; have := g.positive; omega
  have bLow : bl≤b := (insideEndpoints.mp inside.bInside).1
  have bPoint : (Bounds.point box.b.lo).Contains g bl := pointSound _ _
  have square := Bounds.squareSound bPoint
  have sqPos := squareDenominator g valid.bLower
  have dInside := divSound (fractionSound (R:=R) g 1800 61 (by decide)) square sqPos
  have gInside := divSound (wholeSound (R:=R) g 160) square sqPos
  have ⟨dCap,gCap⟩ := productCaps r (valuePos g bPos) bLow
  have ⟨zr,xr,yr⟩ := upperClamps r (valuePos g Zpos) (valuePos g Xpos) zLow xLow gCap dCap
  have xPoint : (Bounds.point X.lo).Contains g xl := pointSound _ _
  have zPoint : (Bounds.point Z.lo).Contains g zl := pointSound _ _
  have sumPos : 0<((Bounds.point Z.lo).add (Bounds.point X.lo)).lo := by
    change 0<Z.lo+X.lo
    omega
  have zTop := divSound gInside xPoint Xpos
  have xTop := divSound gInside zPoint Zpos
  have yTop := divSound dInside (Bounds.addSound zPoint xPoint) sumPos
  have zOut := lowerSound hZ (Std.le_trans zr (insideEndpoints.mp zTop).2)
  have xOut := lowerSound hX (Std.le_trans xr (insideEndpoints.mp xTop).2)
  have yOut := lowerSound inside.yInside (Std.le_trans yr (insideEndpoints.mp yTop).2)
  change Inside g (clipped g box Z X) z y x b
  unfold clipped
  dsimp only
  split
  · rename_i ypos
    let yl := value (R:=R) g box.y.lo
    have yLow : yl≤y := (insideEndpoints.mp inside.yInside).1
    have yPoint : (Bounds.point box.y.lo).Contains g yl := pointSound _ _
    have ⟨za,xa⟩ := positiveYClamps r (valuePos g ypos) yLow zLow xLow dCap
    have quotient := Bounds.subSound (divSound dInside yPoint ypos) yPoint
    exact ⟨lowerSound zOut (Std.le_trans za (insideEndpoints.mp (Bounds.subSound quotient xPoint)).2),
      yOut,lowerSound xOut (Std.le_trans xa (insideEndpoints.mp (Bounds.subSound quotient zPoint)).2),
      inside.bInside⟩
  · exact ⟨zOut,yOut,xOut,inside.bInside⟩

/-- The actual lower C++ contractor preserves every point satisfying
the normalized residual, so neither of its empty-box exits can lose
such a point. -/
theorem reducePreserves {g : Grid} {box : Region} {z y x b : R}
    (r : Residual z y x b) (valid : Valid g box) (inside : Inside g box z y x b) :
    ∃ out, reduce g box=some out ∧ Inside g out z y x b := by
  let X := cutX g box
  let Z := cutZ g box X
  have ⟨hX,hZ⟩ := lowerCoordinates r valid inside
  have kept := clippedPreserves r valid inside
  refine ⟨clipped g box Z X,?_,kept⟩
  have first : ¬(X.hi<X.lo ∨ Z.hi<Z.lo) := by
    have xOrdered : X.lo≤X.hi := noEmpty hX
    have zOrdered : Z.lo≤Z.hi := noEmpty hZ
    omega
  have final : ¬((clipped g box Z X).z.hi<(clipped g box Z X).z.lo ∨
      (clipped g box Z X).y.hi<(clipped g box Z X).y.lo ∨
      (clipped g box Z X).x.hi<(clipped g box Z X).x.lo) := by
    have zo : (clipped g box Z X).z.lo≤(clipped g box Z X).z.hi := noEmpty kept.zInside
    have yo : (clipped g box Z X).y.lo≤(clipped g box Z X).y.hi := noEmpty kept.yInside
    have xo : (clipped g box Z X).x.lo≤(clipped g box Z X).x.hi := noEmpty kept.xInside
    omega
  unfold reduce
  dsimp only
  rw [ite_eq_right first,ite_eq_right final]

end Ordered
end RankSeven.LowerContractor

#print axioms RankSeven.LowerContractor.lowerClamps
#print axioms RankSeven.LowerContractor.productCaps
#print axioms RankSeven.LowerContractor.upperClamps
#print axioms RankSeven.LowerContractor.positiveYClamps
#print axioms RankSeven.LowerContractor.reducePreserves

#print axioms RankSeven.LowerContractor.reduceValid
#print axioms RankSeven.LowerContractor.initialValid
