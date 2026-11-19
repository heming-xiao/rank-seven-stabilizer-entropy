import Rank7LowerLeaves
import Rank7UpperReplay

namespace RankSeven.LowerCorner

open Interval LowerContractor
open UpperCorner (Shifts rays)
open UpperContractor (whole)

private def grid := cppGrid
private def fraction (n d : Int) := Bounds.rational grid n d

local instance : OfNat Bounds n where
  ofNat := whole grid n

local instance : Add Bounds := ⟨Bounds.add⟩
local instance : Sub Bounds := ⟨Bounds.sub⟩
local instance : Mul Bounds := ⟨Bounds.mul grid⟩

private def divide (a b : Bounds) : Option Bounds :=
  if 0<b.lo then some (Bounds.div grid a b) else none

private def byInteger (a : Bounds) (n : Nat) := Bounds.div grid a (whole grid n)

def shifts : List Shifts :=
  [0, fraction 1 2, 1].flatMap fun f =>
    [fraction 5 4, fraction 3 2, 1, fraction 3 4].flatMap fun u =>
      LowerLeaves.weightedShifts grid |>.map fun w => ⟨f,u,w⟩

/-- Square-root conjugate quotients used by the shared cut. -/
def sharedWidths (box : Region) : Option (Bounds × Bounds) := do
  let ⟨z,y,x,b⟩ := box
  let square := Bounds.square grid
  let alpha := 1+(z+y+x)
  let beta := 1+(y+x)
  let gamma := 1+x
  let bBeta := b*beta
  if alpha.lo<0 ∨ gamma.lo<0 ∨ b.lo<0 ∨ bBeta.lo<0 then none else
    let first ← divide (alpha * square (gamma-b).positivePart) (square (gamma.root grid+b.root grid))
    let second ← divide (gamma * square (z-(b-1)*beta).positivePart) (square (alpha.root grid+bBeta.root grid))
    return (first,second)

structure Prices (T : Type) where
  cut : T
  h : T
  shared : T
  leftBonus : T
  high : T
  weightedDelta : T
  lambda : T
  completion : T
  xOverB : T
  bSquare : T

def preparePrices (box : Region) (shift : Shifts) : Option (Prices Bounds) := do
  let ⟨z,y,x,b⟩ := box
  let square := Bounds.square grid
  let X := z+y+x
  let G := z*x
  let D := y*X
  let b2 := square b
  let (widthA,widthB) ← sharedWidths box
  let invRate := Bounds.div grid 1 (fraction 4242 25)
  let invGeom := Bounds.div grid 1 (fraction 5 2)
  let price := 24*invRate
  let cut := (96*invRate) * widthA.smallest widthB
  let fixedH := z*(x-1)-3*x-fraction 5 2
  let x2 := square x
  let z2 := square z
  let y2 := square y
  let anti := y2*(y2+byInteger (z2+x2) 2)
  let norm := z2+x2
  let tax := (1-shift.f)*fraction 200 11
  let normDen := norm+72*square shift.f
  if b.lo≤0 ∨ normDen.lo≤0 ∨ b2.lo≤0 then none else
    let invB := Bounds.div grid 1 b
    let G0 := (G-tax*(1-invB)).positivePart
    let invQ := Bounds.div grid norm normDen
    let s := shift.u*(G0*invQ)
    let lambda := price*s
    let shared := (byInteger (square G) 12+shift.u*(2-shift.u)*(square G0*invQ))*b2*invRate
    let extra := 2*s*tax*b*(b-1)*invRate
    let rho := 1-price*shift.w
    let high := b2*(12*shift.w*(2-shift.w)*square D+anti)*invGeom*invRate
    let C := (x*X*(x+rho*y)-lambda*(y+2*x)).positivePart
    some ⟨cut,fixedH,shared,extra,high,rho*D,lambda,C,Bounds.div grid x b,b2⟩

def leafPair (box : Region) (prepared : Prices Bounds) (right : Bool) (ray : UpperCorner.Ray) :
    Bounds × Bounds :=
  let ⟨z,y,x,b⟩ := box
  let c := if right then b else 1
  let S := prepared.shared+(if right then (0:Bounds) else prepared.leftBonus)
  let pre := (b-1)*(c-1)
  let geometric := prepared.xOverB.smallest (c*b*prepared.completion)
  let constant := Bounds.div grid ray.constant prepared.bSquare
  let trace := c*prepared.cut*ray.traceShared
  let fixedSingle := trace+c*(z*(ray.m-x*ray.n)+(2*y+3*x)*ray.m)+constant
  let fixedSplit := trace+c*(y*ray.v-prepared.h*ray.n)
  let common := S*ray.peak+prepared.high*ray.v+
    prepared.weightedDelta*(pre*ray.tail-ray.v)+c*prepared.lambda*ray.n
  (common+fixedSplit,common+fixedSingle+geometric*ray.improvement)

/-- The two directed shared-branch endpoint rows in the C++ order.
Any unavailable denominator or square root makes the candidate fail. -/
def margins (box : Region) (shift : Shifts) : Option (List (List (Int × Int))) := do
  let prepared ← preparePrices box shift
  return [false,true].map fun right => rays.map fun ray =>
    let (split,single) := leafPair box prepared right ray
    (split.lo,single.lo)

abbrev sectorPass := UpperReplay.adjacentSectorPass 2

def accepts (box : Region) : Bool :=
  (UpperReplay.remainingSectorsBy 2 (margins box) shifts (List.range 6)).isEmpty

theorem acceptedWitness {box : Region} (accepted : accepts box=true) (sector : Fin 6) :
    ∃ s ∈ shifts, ∃ rows, margins box s=some rows ∧ sectorPass rows sector=true :=
  UpperReplay.sectorWitnessBy (List.mem_range.mpr sector.isLt) (List.isEmpty_iff.mp accepted)


section Ordered

open Lean.Grind
open UpperPrices (positivePart)
open UpperContractor (wholeSound divSound quotientEq cancelLe lowerEndpointPositive)

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

/-- Nonnegative square roots of the four actual normalized radicands. -/
structure Roots (z y x b : R) where
  alpha : R
  gamma : R
  fifth : R
  betaFifth : R
  alphaNonnegative : 0≤alpha
  gammaNonnegative : 0≤gamma
  fifthNonnegative : 0≤fifth
  betaFifthNonnegative : 0≤betaFifth
  alphaSq : alpha*alpha=1+(z+y+x)
  gammaSq : gamma*gamma=1+x
  fifthSq : fifth*fifth=b
  betaFifthSq : betaFifth*betaFifth=b*(1+(y+x))

noncomputable def gap (a b : R) : R :=
  positivePart (a-b)*positivePart (a-b)

private theorem positivePartEnclosed {a : Bounds} {x : R} (h : a.Contains grid x) :
    a.positivePart.Contains grid (positivePart x) := by
  apply Bounds.positivePartSound h
  unfold positivePart
  split <;> grind only

private theorem scaledPositivePart (a t : R) (t0 : 0<t) :
    positivePart (a*t)=positivePart a*t := by
  classical
  unfold positivePart
  by_cases pos : 0≤a
  · have p := OrderedRing.mul_nonneg pos (Std.le_of_lt t0)
    simp only [pos,p,ite_true]
  · have p := OrderedRing.mul_neg_of_neg_of_pos (show a<0 by grind only) t0
    simp only [pos,show ¬0≤a*t from by grind only,ite_false,Semiring.zero_mul]

/-- The squared conjugate denominator gives the actual positive-part root
gap, with no use of an approximate square root in the identity. -/
theorem conjugateWidth (a p q : R) (p0 : 0≤p) (q0 : 0≤q)
    (den0 : 0<(p+q)*(p+q)) :
    (a*gap (p*p) (q*q))/((p+q)*(p+q))=a*gap p q := by
  have sumNon : 0≤p+q := by grind only
  have positive : 0<p+q := by
    by_cases h : 0<p+q
    · exact h
    · have z : p+q=0 := by grind only
      rw [z] at den0
      grind only
  have numerator : p*p-q*q=(p-q)*(p+q) := by grind only
  have exactMul : a*gap (p*p) (q*q)=((p+q)*(p+q))*(a*gap p q) := by
    unfold gap
    rw [numerator,scaledPositivePart _ _ positive]
    grind only
  have denominator := quotientEq (a*gap (p*p) (q*q)) den0
  have eq : ((p+q)*(p+q))*((a*gap (p*p) (q*q))/((p+q)*(p+q))) =
      ((p+q)*(p+q))*(a*gap p q) := denominator.trans exactMul
  have left := cancelLe den0 (Std.le_of_eq eq)
  have right := cancelLe den0 (Std.le_of_eq eq.symm)
  grind only

private theorem checkedWidth {out coeff difference a b : Bounds} {m p q : R}
    (mc : coeff.Contains grid m) (dc : difference.Contains grid (p*p-q*q))
    (pa : (a.root grid).Contains grid p) (pb : (b.root grid).Contains grid q)
    (p0 : 0≤p) (q0 : 0≤q)
    (check : divide (coeff * Bounds.square grid difference.positivePart)
      (Bounds.square grid (a.root grid+b.root grid))=some out) :
    out.Contains grid (m*gap p q) := by
  have num := Bounds.mulSound mc (Bounds.squareSound (positivePartEnclosed dc))
  have den := Bounds.squareSound (Bounds.addSound pa pb)
  unfold divide at check
  split at check
  · rename_i positive
    have rounded := divSound num den positive
    have exactValue := conjugateWidth m p q p0 q0 (lowerEndpointPositive den positive)
    rw [←exactValue,←Option.some.inj check]
    exact rounded
  · contradiction

/-- Both integer shared-cut quotients enclose their respective exact
square-root gap prices at every point inside the box. -/
theorem sharedWidthsEnclosed {box : Region} {a bWidth : Bounds} {z y x b : R}
    (inside : Inside grid box z y x b) (roots : Roots z y x b)
    (computed : sharedWidths box=some (a,bWidth)) :
    a.Contains grid ((1+(z+y+x))*gap roots.gamma roots.fifth) ∧
      bWidth.Contains grid ((1+x)*gap roots.alpha roots.betaFifth) := by
  let alpha := (1:Bounds)+(box.z+box.y+box.x)
  let beta := (1:Bounds)+(box.y+box.x)
  let gamma := (1:Bounds)+box.x
  let bBeta := box.b*beta
  let denA := Bounds.square grid (gamma.root grid+box.b.root grid)
  let denB := Bounds.square grid (alpha.root grid+bBeta.root grid)
  let numA := alpha*Bounds.square grid (gamma-box.b).positivePart
  let numB := gamma*Bounds.square grid (box.z-(box.b-1)*beta).positivePart
  have changeEval : (if alpha.lo<0 ∨ gamma.lo<0 ∨ box.b.lo<0 ∨ bBeta.lo<0 then none
      else do
        let first ← divide numA denA
        let second ← divide numB denB
        return (first,second))=some (a,bWidth) := computed
  split at changeEval
  · contradiction
  · rename_i good
    have alphaPos : 0≤alpha.lo := by grind only
    have gammaPos : 0≤gamma.lo := by grind only
    have bPos : 0≤box.b.lo := by grind only
    have bBetaPos : 0≤bBeta.lo := by grind only
    have one := wholeSound (R:=R) grid 1
    have A : alpha.Contains grid (1+(z+y+x)) :=
      Bounds.addSound one (Bounds.addSound (Bounds.addSound inside.zInside inside.yInside) inside.xInside)
    have B : beta.Contains grid (1+(y+x)) := Bounds.addSound one (Bounds.addSound inside.yInside inside.xInside)
    have G : gamma.Contains grid (1+x) := Bounds.addSound one inside.xInside
    have BB : bBeta.Contains grid (b*(1+(y+x))) := Bounds.mulSound inside.bInside B
    have raizA := Bounds.rootSound A alphaPos roots.alphaNonnegative roots.alphaSq
    have raizG := Bounds.rootSound G gammaPos roots.gammaNonnegative roots.gammaSq
    have raizB := Bounds.rootSound inside.bInside bPos roots.fifthNonnegative roots.fifthSq
    have raizBB := Bounds.rootSound BB bBetaPos roots.betaFifthNonnegative roots.betaFifthSq
    have difA : (gamma-box.b).Contains grid (roots.gamma*roots.gamma-roots.fifth*roots.fifth) := by
      rw [roots.gammaSq,roots.fifthSq]
      exact Bounds.subSound G inside.bInside
    have difB : (box.z-(box.b-1)*beta).Contains grid (roots.alpha*roots.alpha-roots.betaFifth*roots.betaFifth) := by
      rw [roots.alphaSq,roots.betaFifthSq,show 1+(z+y+x)-b*(1+(y+x))=z-(b-1)*(1+(y+x)) by grind only]
      exact Bounds.subSound inside.zInside (Bounds.mulSound (Bounds.subSound inside.bInside one) B)
    cases hA : divide numA denA with
    | none => simp [hA] at changeEval
    | some first =>
      cases hB : divide numB denB with
      | none => simp [hA,hB] at changeEval
      | some second =>
        have pair : (first,second)=(a,bWidth) := by simpa [hA,hB] using changeEval
        obtain ⟨ea,eb⟩ := Prod.mk.inj pair
        subst a
        subst bWidth
        exact ⟨checkedWidth A difA raizG raizB roots.gammaNonnegative roots.fifthNonnegative hA,
          checkedWidth G difB raizA raizBB roots.alphaNonnegative roots.betaFifthNonnegative hB⟩


private noncomputable def smaller (a b : R) : R := by
  classical
  exact if a≤b then a else b

private theorem smallerEnclosed {a b : Bounds} {x y : R}
    (hx : a.Contains grid x) (hy : b.Contains grid y) :
    (a.smallest b).Contains grid (smaller x y) := by
  apply Bounds.smallestSound hx hy
  unfold smaller
  split <;> grind only

noncomputable def realPrices (z y x b f u w wa wb : R) : Prices R :=
  let X := z+y+x
  let G := z*x
  let D := y*X
  let b2 := b*b
  let invRate := 1/(4242/25:R)
  let invGeom := 1/(5/2:R)
  let price := 24*invRate
  let cut := (96*invRate)*smaller wa wb
  let fixedH := z*(x-1)-3*x-5/2
  let x2 := x*x
  let z2 := z*z
  let y2 := y*y
  let anti := y2*(y2+(z2+x2)/2)
  let norm := z2+x2
  let tax := (1-f)*(200/11)
  let G0 := positivePart (G-tax*(1-1/b))
  let invQ := norm/(norm+72*(f*f))
  let s := u*(G0*invQ)
  let lambda := price*s
  let shared := ((G*G)/12+u*(2-u)*((G0*G0)*invQ))*b2*invRate
  let extra := 2*s*tax*b*(b-1)*invRate
  let rho := 1-price*w
  let high := b2*(12*w*(2-w)*(D*D)+anti)*invGeom*invRate
  let C := positivePart (x*X*(x+rho*y)-lambda*(y+2*x))
  ⟨cut,fixedH,shared,extra,high,rho*D,lambda,C,x/b,b2⟩

structure PriceEnclosure (bounds : Prices Bounds) (value : Prices R) : Prop where
  cut : bounds.cut.Contains grid value.cut
  h : bounds.h.Contains grid value.h
  shared : bounds.shared.Contains grid value.shared
  leftBonus : bounds.leftBonus.Contains grid value.leftBonus
  high : bounds.high.Contains grid value.high
  weightedDelta : bounds.weightedDelta.Contains grid value.weightedDelta
  lambda : bounds.lambda.Contains grid value.lambda
  completion : bounds.completion.Contains grid value.completion
  xOverB : bounds.xOverB.Contains grid value.xOverB
  bSquare : bounds.bSquare.Contains grid value.bSquare
  bSquarePositive : 0<bounds.bSquare.lo

/-- Every common price at the two endpoints encloses its actual real value,
with a common choice of the three shift parameters. -/
theorem preparedPricesEnclosed {box : Region} {shift : Shifts} {prepared : Prices Bounds}
    {z y x b f u w : R} (inside : Inside grid box z y x b) (roots : Roots z y x b)
    (hf : shift.f.Contains grid f) (hu : shift.u.Contains grid u) (hw : shift.w.Contains grid w)
    (computed : preparePrices box shift=some prepared) :
    PriceEnclosure prepared (realPrices z y x b f u w
      ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)) := by
  cases widths : sharedWidths box with
  | none =>
    cases box
    simp [preparePrices,widths] at computed
  | some ws =>
    obtain ⟨wa,wb⟩ := ws
    have ⟨waSound,wbSound⟩ := sharedWidthsEnclosed inside roots widths
    cases box with
    | mk zb yb xb bb =>
      simp only [preparePrices,widths] at computed
      split at computed
      · contradiction
      · rename_i valid
        let N := wholeSound (R:=R) grid
        let F := fun a d hd => UpperContractor.fractionSound (R:=R) grid a d hd
        obtain ⟨zI,yI,xI,bI⟩ := inside
        have bPos : 0<bb.lo := by grind only
        have denPos : 0<((Bounds.square grid zb+Bounds.square grid xb)+72*Bounds.square grid shift.f).lo := by
          grind only
        have b2Pos : 0<(Bounds.square grid bb).lo := by grind only
        have X := Bounds.addSound (Bounds.addSound zI yI) xI
        have gI := Bounds.mulSound zI xI
        have dI := Bounds.mulSound yI X
        have b2 := Bounds.squareSound bI
        have invRate := divSound (N 1) (F 4242 25 (by decide)) (by decide)
        have invGeom := divSound (N 1) (F 5 2 (by decide)) (by decide)
        have price := Bounds.mulSound (N 24) invRate
        have cut := Bounds.mulSound (Bounds.mulSound (N 96) invRate) (smallerEnclosed waSound wbSound)
        have fixedH := Bounds.subSound (Bounds.subSound (Bounds.mulSound zI (Bounds.subSound xI (N 1)))
          (Bounds.mulSound (N 3) xI)) (F 5 2 (by decide))
        have x2 := Bounds.squareSound xI
        have z2 := Bounds.squareSound zI
        have y2 := Bounds.squareSound yI
        have anti := Bounds.mulSound y2 (Bounds.addSound y2
          (divSound (Bounds.addSound z2 x2) (N 2) (by decide)))
        have norm := Bounds.addSound z2 x2
        have tax := Bounds.mulSound (Bounds.subSound (N 1) hf) (F 200 11 (by decide))
        have G0 := positivePartEnclosed (Bounds.subSound gI (Bounds.mulSound tax
          (Bounds.subSound (N 1) (divSound (N 1) bI bPos))))
        have invQ := divSound norm (Bounds.addSound norm (Bounds.mulSound (N 72) (Bounds.squareSound hf))) denPos
        have shifted := Bounds.mulSound hu (Bounds.mulSound G0 invQ)
        have lambda := Bounds.mulSound price shifted
        have shared := Bounds.mulSound (Bounds.mulSound (Bounds.addSound
          (divSound (Bounds.squareSound gI) (N 12) (by decide))
          (Bounds.mulSound (Bounds.mulSound hu (Bounds.subSound (N 2) hu))
            (Bounds.mulSound (Bounds.squareSound G0) invQ))) b2) invRate
        have extra := Bounds.mulSound (Bounds.mulSound (Bounds.mulSound (Bounds.mulSound (Bounds.mulSound
          (N 2) shifted) tax) bI) (Bounds.subSound bI (N 1))) invRate
        have rho := Bounds.subSound (N 1) (Bounds.mulSound price hw)
        have hw2 := Bounds.mulSound (Bounds.mulSound (Bounds.mulSound (N 12) hw) (Bounds.subSound (N 2) hw))
          (Bounds.squareSound dI)
        have high := Bounds.mulSound (Bounds.mulSound (Bounds.mulSound b2 (Bounds.addSound hw2 anti)) invGeom) invRate
        have completion := positivePartEnclosed (Bounds.subSound (Bounds.mulSound (Bounds.mulSound xI X)
          (Bounds.addSound xI (Bounds.mulSound rho yI)))
          (Bounds.mulSound lambda (Bounds.addSound yI (Bounds.mulSound (N 2) xI))))
        rw [←Option.some.inj computed]
        exact ⟨cut,fixedH,shared,extra,high,Bounds.mulSound rho dI,lambda,completion,divSound xI bI bPos,b2,b2Pos⟩


structure RealRay (R : Type) where
  n : R
  v : R
  m : R
  peak : R
  constant : R
  improvement : R
  tail : R
  traceShared : R

open UpperWeighted (larger largerSound)

noncomputable def realRay (n v trace : R) : RealRay R :=
  let m := larger n (v/2)
  ⟨n,v,m,larger n v,larger (larger ((5/2:R)*n) (2*v)) (2*n+v),
    positivePart (2*n+v-3*m),larger v (n/2),trace⟩

structure RayEnclosure (bounds : UpperCorner.Ray) (value : RealRay R) : Prop where
  n : bounds.n.Contains grid value.n
  v : bounds.v.Contains grid value.v
  m : bounds.m.Contains grid value.m
  peak : bounds.peak.Contains grid value.peak
  constant : bounds.constant.Contains grid value.constant
  improvement : bounds.improvement.Contains grid value.improvement
  tail : bounds.tail.Contains grid value.tail
  traceShared : bounds.traceShared.Contains grid value.traceShared

private theorem rayEnclosed {n v ct ot : Bounds} {nR vR trace : R}
    (hn : n.Contains grid nR) (hv : v.Contains grid vR) (ht : ct.Contains grid trace) :
    RayEnclosure (UpperCorner.ray n v ot ct) (realRay nR vR trace) := by
  let N := wholeSound (R:=R) grid
  have m := largerSound hn (divSound hv (N 2) (by decide))
  have z := Bounds.addSound (Bounds.mulSound (N 2) hn) hv
  have constant := largerSound
    (largerSound (Bounds.mulSound (UpperContractor.fractionSound (R:=R) grid 5 2 (by decide)) hn)
      (Bounds.mulSound (N 2) hv)) z
  have improvement := positivePartEnclosed (Bounds.subSound z (Bounds.mulSound (N 3) m))
  exact ⟨hn,hv,m,largerSound hn hv,constant,improvement,largerSound hv (divSound hn (N 2) (by decide)),ht⟩

def rayAt (j : Fin 7) : UpperCorner.Ray := rays[j.val]'j.isLt

noncomputable def realRayAt (j : Fin 7) : RealRay R :=
  let rayList := [realRay 1 0 (1/2:R),realRay 1 (1/2) (1/2),realRay 1 (2/3) (1/2),
    realRay 1 1 (2/3),realRay 1 2 (5/6),realRay 1 4 (11/12),realRay 0 1 0]
  rayList[j.val]'j.isLt

theorem sevenRaysEnclosed (j : Fin 7) : RayEnclosure (rayAt j) (realRayAt (R:=R) j) := by
  have cases : ∀ i : Fin 7, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by decide
  rcases cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply rayEnclosed <;>
      first | exact wholeSound _ _ | exact UpperContractor.fractionSound _ _ _ (by decide)

noncomputable def realLeafPair (z y x b : R) (priced : Prices R) (right : Bool) (ray : RealRay R) :
    R × R :=
  let c := if right then b else 1
  let S := priced.shared+(if right then 0 else priced.leftBonus)
  let pre := (b-1)*(c-1)
  let geometric := smaller priced.xOverB (c*b*priced.completion)
  let constant := ray.constant/priced.bSquare
  let trace := c*priced.cut*ray.traceShared
  let fixedSingle := trace+c*(z*(ray.m-x*ray.n)+(2*y+3*x)*ray.m)+constant
  let fixedSplit := trace+c*(y*ray.v-priced.h*ray.n)
  let common := S*ray.peak+priced.high*ray.v+
    priced.weightedDelta*(pre*ray.tail-ray.v)+c*priced.lambda*ray.n
  (common+fixedSplit,common+fixedSingle+geometric*ray.improvement)

theorem leafPairEnclosed {box : Region} {prepared : Prices Bounds} {priced : Prices R}
    {z y x b : R} (inside : Inside grid box z y x b) (data : PriceEnclosure prepared priced)
    (right : Bool) {ray : UpperCorner.Ray} {real : RealRay R} (r : RayEnclosure ray real) :
    let bound := leafPair box prepared right ray
    let actual := realLeafPair z y x b priced right real
    bound.1.Contains grid actual.1 ∧ bound.2.Contains grid actual.2 := by
  let N := wholeSound (R:=R) grid
  obtain ⟨zI,yI,xI,bI⟩ := inside
  let c := if right then b else 1
  have C : (if right then box.b else (1:Bounds)).Contains grid c := by
    cases right
    · exact N 1
    · exact bI
  have bonus : (if right then (0:Bounds) else prepared.leftBonus).Contains grid
      (if right then (0:R) else priced.leftBonus) := by
    cases right
    · exact data.leftBonus
    · exact N 0
  have S := Bounds.addSound data.shared bonus
  have prefixBound := Bounds.mulSound (Bounds.subSound bI (N 1)) (Bounds.subSound C (N 1))
  have geometric := smallerEnclosed data.xOverB
    (Bounds.mulSound (Bounds.mulSound C bI) data.completion)
  have constant := divSound r.constant data.bSquare data.bSquarePositive
  have trace := Bounds.mulSound (Bounds.mulSound C data.cut) r.traceShared
  have singleTerm := Bounds.addSound (Bounds.mulSound zI (Bounds.subSound r.m (Bounds.mulSound xI r.n)))
    (Bounds.mulSound (Bounds.addSound (Bounds.mulSound (N 2) yI) (Bounds.mulSound (N 3) xI)) r.m)
  have fixedSingle := Bounds.addSound (Bounds.addSound trace (Bounds.mulSound C singleTerm)) constant
  have fixedSplit := Bounds.addSound trace (Bounds.mulSound C
    (Bounds.subSound (Bounds.mulSound yI r.v) (Bounds.mulSound data.h r.n)))
  have common := Bounds.addSound (Bounds.addSound (Bounds.addSound
    (Bounds.mulSound S r.peak) (Bounds.mulSound data.high r.v))
    (Bounds.mulSound data.weightedDelta (Bounds.subSound (Bounds.mulSound prefixBound r.tail) r.v)))
    (Bounds.mulSound (Bounds.mulSound C data.lambda) r.n)
  exact ⟨Bounds.addSound common fixedSplit,
    Bounds.addSound (Bounds.addSound common fixedSingle) (Bounds.mulSound geometric r.improvement)⟩

/-- Both margins at both endpoints and all seven rays enclose the actual
real expressions, for every successfully evaluated box and common shift. -/
theorem marginsEnclosed {box : Region} {shift : Shifts} {rows : List (List (Int × Int))}
    {z y x b f u w : R} (inside : Inside grid box z y x b) (roots : Roots z y x b)
    (hf : shift.f.Contains grid f) (hu : shift.u.Contains grid u) (hw : shift.w.Contains grid w)
    (computed : margins box shift=some rows) :
    ∃ prepared, preparePrices box shift=some prepared ∧
      rows=([false,true].map fun right => rays.map fun ray =>
        let (split,single) := leafPair box prepared right ray
        (split.lo,single.lo)) ∧
      ∀ (right : Bool) (j : Fin 7),
        let bound := leafPair box prepared right (rayAt j)
        let prices := realPrices z y x b f u w
          ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)
        let actual := realLeafPair z y x b prices right (realRayAt j)
        bound.1.Contains grid actual.1 ∧ bound.2.Contains grid actual.2 := by
  cases hd : preparePrices box shift with
  | none => simp [margins,hd] at computed
  | some data =>
    have shape := Option.some.inj (by simpa [margins,hd] using computed.symm)
    refine ⟨data,rfl,shape,?_⟩
    intro right j
    exact leafPairEnclosed inside (preparedPricesEnclosed inside roots hf hu hw hd)
      right (sevenRaysEnclosed j)


/-- At either normalized endpoint a sector accepted by the integer test
has a common nonnegative combination of its two real boundary-ray margins. -/
theorem acceptedRealSector {box : Region} {shift : Shifts} {rows : List (List (Int × Int))}
    {z y x b f u w : R} (inside : Inside grid box z y x b) (roots : Roots z y x b)
    (hf : shift.f.Contains grid f) (hu : shift.u.Contains grid u) (hw : shift.w.Contains grid w)
    (computed : margins box shift=some rows) (sector : Fin 6)
    (accepted : sectorPass rows sector.val=true) (right : Bool) :
    let p := realPrices z y x b f u w
      ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)
    let lo : Fin 7 := ⟨sector.val, Nat.lt_trans sector.isLt (by decide : 6<7)⟩
    let hi : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
    let a := realLeafPair z y x b p right (realRayAt lo)
    let b' := realLeafPair z y x b p right (realRayAt hi)
    ∃ s t : R, 0≤s ∧ 0≤t ∧ 0<s*a.1+t*a.2 ∧ 0<s*b'.1+t*b'.2 := by
  obtain ⟨prepared,_,shape,contains⟩ := marginsEnclosed inside roots hf hu hw computed
  let lo : Fin 7 := ⟨sector.val,Nat.lt_trans sector.isLt (by decide : 6<7)⟩
  let hi : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
  let numbers (ray : UpperCorner.Ray) :=
    let (first,second) := leafPair box prepared right ray
    (first.lo,second.lo)
  let selected := rays.map numbers
  have selectedMem : selected ∈ rows := by
    rw [shape]
    exact List.mem_map.mpr ⟨right,by cases right <;> simp,rfl⟩
  have all : (rows.all fun row =>
      match row[sector.val]?, row[sector.val+1]? with
      | some (s1,t1), some (s2,t2) => blend s1 t1 s2 t2
      | _, _ => false)=true := (Bool.and_eq_true_iff.mp accepted).2
  have chosen := List.all_eq_true.mp all selected selectedMem
  have first : selected[sector.val]?=some (numbers (rayAt lo)) := by
    unfold selected
    rw [List.getElem?_map,List.getElem?_eq_getElem (show sector.val<rays.length from lo.isLt)]
    rfl
  have second : selected[sector.val+1]?=some (numbers (rayAt hi)) := by
    unfold selected
    rw [List.getElem?_map,List.getElem?_eq_getElem (show sector.val+1<rays.length from hi.isLt)]
    rfl
  rw [first,second] at chosen
  obtain ⟨a,b₀⟩ := contains right lo
  obtain ⟨c,d⟩ := contains right hi
  exact blendEnclosed (grid:=grid) chosen a.1 b₀.1 c.1 d.1


theorem shiftEnclosed (shift : Shifts) (member : shift ∈ shifts) :
    ∃ f u w : R,
      (f=0 ∨ f=1/2 ∨ f=1) ∧
      (u=5/4 ∨ u=3/2 ∨ u=1 ∨ u=3/4) ∧
      (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧
      shift.f.Contains grid f ∧ shift.u.Contains grid u ∧ shift.w.Contains grid w := by
  obtain ⟨fBox,fIn,uMember⟩ := List.mem_flatMap.mp member
  obtain ⟨uBox,uIn,wMember⟩ := List.mem_flatMap.mp uMember
  obtain ⟨wBox,wIn,rfl⟩ := List.mem_map.mp wMember
  let N := wholeSound (R:=R) grid
  let F := fun a d pos => UpperContractor.fractionSound (R:=R) grid a d pos
  have fs : fBox=0 ∨ fBox=fraction 1 2 ∨ fBox=1 := by simpa using fIn
  have us : uBox=fraction 5 4 ∨ uBox=fraction 3 2 ∨ uBox=1 ∨ uBox=fraction 3 4 := by simpa using uIn
  have ws : wBox=fraction 5 4 ∨ wBox=fraction 3 2 ∨ wBox=whole grid 1 ∨ wBox=fraction 7 4 := by
    simpa [LowerLeaves.weightedShifts,fraction] using wIn
  obtain ⟨f,fChoice,hf⟩ : ∃ f : R, (f=0 ∨ f=1/2 ∨ f=1) ∧ fBox.Contains grid f := by
    rcases fs with rfl | rfl | rfl
    · exact ⟨0,Or.inl rfl,N 0⟩
    · exact ⟨1/2,Or.inr (Or.inl rfl),F 1 2 (by decide)⟩
    · exact ⟨1,Or.inr (Or.inr rfl),N 1⟩
  obtain ⟨u,uChoice,hu⟩ : ∃ u : R, (u=5/4 ∨ u=3/2 ∨ u=1 ∨ u=3/4) ∧ uBox.Contains grid u := by
    rcases us with rfl | rfl | rfl | rfl
    · exact ⟨5/4,Or.inl rfl,F 5 4 (by decide)⟩
    · exact ⟨3/2,Or.inr (Or.inl rfl),F 3 2 (by decide)⟩
    · exact ⟨1,Or.inr (Or.inr (Or.inl rfl)),N 1⟩
    · exact ⟨3/4,Or.inr (Or.inr (Or.inr rfl)),F 3 4 (by decide)⟩
  obtain ⟨w,wChoice,hw⟩ : ∃ w : R, (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧ wBox.Contains grid w := by
    rcases ws with rfl | rfl | rfl | rfl
    · exact ⟨5/4,Or.inl rfl,F 5 4 (by decide)⟩
    · exact ⟨3/2,Or.inr (Or.inl rfl),F 3 2 (by decide)⟩
    · exact ⟨1,Or.inr (Or.inr (Or.inl rfl)),N 1⟩
    · exact ⟨7/4,Or.inr (Or.inr (Or.inr rfl)),F 7 4 (by decide)⟩
  exact ⟨f,u,w,fChoice,uChoice,wChoice,hf,hu,hw⟩


/-- Shared acceptance supplies actual real shift choices and positive
mixes at both endpoints of every adjacent ray sector. -/
theorem acceptedSharedSector {box : Region} {z y x b : R}
    (inside : Inside grid box z y x b) (roots : Roots z y x b)
    (accepted : accepts box=true) (sector : Fin 6) :
    ∃ f u w : R,
      (f=0 ∨ f=1/2 ∨ f=1) ∧
      (u=5/4 ∨ u=3/2 ∨ u=1 ∨ u=3/4) ∧
      (w=5/4 ∨ w=3/2 ∨ w=1 ∨ w=7/4) ∧
      ∀ right : Bool,
        let p := realPrices z y x b f u w
          ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)
        let lo : Fin 7 := ⟨sector.val,Nat.lt_trans sector.isLt (by decide : 6<7)⟩
        let hi : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
        let a := realLeafPair z y x b p right (realRayAt lo)
        let b' := realLeafPair z y x b p right (realRayAt hi)
        ∃ s t : R, 0≤s ∧ 0≤t ∧ 0<s*a.1+t*a.2 ∧ 0<s*b'.1+t*b'.2 := by
  obtain ⟨shift,hShift,rows,computed,passed⟩ := acceptedWitness accepted sector
  obtain ⟨f,u,w,fOpt,uOpt,wOpt,hf,hu,hw⟩ := shiftEnclosed (R:=R) shift hShift
  exact ⟨f,u,w,fOpt,uOpt,wOpt,fun side => acceptedRealSector inside roots hf hu hw
    computed sector passed side⟩

end Ordered

end RankSeven.LowerCorner

#print axioms RankSeven.LowerCorner.acceptedWitness

#print axioms RankSeven.LowerCorner.conjugateWidth
#print axioms RankSeven.LowerCorner.sharedWidthsEnclosed

#print axioms RankSeven.LowerCorner.preparedPricesEnclosed

#print axioms RankSeven.LowerCorner.marginsEnclosed

#print axioms RankSeven.LowerCorner.acceptedRealSector

#print axioms RankSeven.LowerCorner.shiftEnclosed

#print axioms RankSeven.LowerCorner.acceptedSharedSector
