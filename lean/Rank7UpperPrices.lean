import Rank7UpperAnalytic
import Rank7Interval

/-! A fixed shared shift and a common lower price for the fourth-tie tail rectangle. -/
namespace RankSeven.UpperPrices
open Lean.Grind Interval

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def positivePart (z : R) : R := by classical exact if 0≤z then z else 0

private theorem positivePartNonnegative (z : R) : 0≤positivePart z := by
  unfold positivePart; split <;> grind only

private theorem quotientEq (x : R) {y : R} (p : 0<y) : y*(x/y)=x := by
  have := Field.mul_inv_cancel (show y≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

private theorem cancelLe {x y z : R} (p : 0<z) (e : z*x≤z*y) : x≤y := by
  by_cases h : x≤y
  · exact h
  · have := OrderedRing.mul_lt_mul_of_pos_left (show y<x by grind only) p; grind only

private theorem quotientNonneg {x y : R} (hx : 0≤x) (hy : 0<y) : 0≤x/y := by
  apply cancelLe hy
  rw [Semiring.mul_zero,quotientEq _ hy]; exact hx

def alphaPrice (f : R) : R := (1-f)*(200/11)
def penalty (psi f : R) : R := 1+12*f^2/psi
def penaltyInverse (psi f : R) : R := psi/(psi+12*f^2)

noncomputable def clippedGain (g price upperSpread : R) : R := positivePart (g-price*upperSpread)

noncomputable def shift (u g price upperSpread psi f : R) : R :=
  u*clippedGain g price upperSpread*penaltyInverse psi f

def commonPayment (u g0 qinv s price upperSpread c d : R) : R :=
  12*u*(2-u)*g0^2*qinv+24*s*price*(upperSpread-(c-d))

def sourcePayment (g s price psi f c d : R) : R :=
  12*s*(2*(g-price*(c-d))-penalty psi f*s)

theorem alphaPriceNonnegative {f : R} (hf : f≤1) : 0≤alphaPrice f := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  exact OrderedRing.mul_nonneg (show 0≤1-f by grind only) (quotientNonneg (by grind only) (by grind only))

/-- The inverse used in C++ is exactly 1/Q and lies in (0,1]. -/
theorem penaltyNormalization {psi f : R} (hp : 0<psi) :
    1≤penalty psi f ∧ 0<penaltyInverse psi f ∧ penaltyInverse psi f≤1 ∧
    penalty psi f*penaltyInverse psi f=1 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have sq := squareNonnegative f
  have D : 0<psi+12*f^2 := by grind only
  have rank := quotientEq (12*f^2) hp
  have inv := quotientEq psi D
  have nn := quotientNonneg (show 0≤12*f^2 by grind only) hp
  have pos : 0<penaltyInverse psi f := by
    by_cases pos : 0<penaltyInverse psi f
    · exact pos
    · have contrad := OrderedRing.mul_le_mul_of_nonneg_left (show penaltyInverse psi f≤0 by grind only) (Std.le_of_lt D)
      change (psi+12*f^2)*(psi/(psi+12*f^2))≤(psi+12*f^2)*0 at contrad
      grind only
  refine ⟨by unfold penalty; grind only,pos,?_,?_⟩
  · apply cancelLe D; unfold penaltyInverse; rw [inv,Semiring.mul_one]; grind only
  · unfold penalty penaltyInverse
    have c0 := congrArg (fun z : R => z*(psi/(psi+12*f^2))) rank
    have c1 := congrArg (fun z : R => z*psi) inv
    have c2 := congrArg (fun z : R => z*(12*f^2/psi)) inv
    have left : psi*((1+12*f^2/psi)*(psi/(psi+12*f^2))) = psi*1 := by grind only
    have a := cancelLe hp (Std.le_of_eq left)
    have b := cancelLe hp (Std.le_of_eq left.symm)
    grind only

/-- Increasing the true reserve Ψ can only reduce the quadratic debit. -/
theorem penaltyAntitone {psi0 psi f : R} (positive : 0<psi0) (floor : psi0≤psi) :
    penalty psi f≤penalty psi0 f := by
  have pp : 0<psi := by grind only
  have sq := squareNonnegative f
  have f0 := quotientNonneg (show 0≤12*f^2 by grind only) positive
  have order := OrderedRing.mul_le_mul_of_nonneg_right floor f0
  rw [quotientEq _ positive] at order
  have divided : (12*f^2)/psi ≤ (12*f^2)/psi0 := by
    apply cancelLe pp; rw [quotientEq _ pp]; exact order
  unfold penalty; grind only

theorem shiftAdmissible {g price upperSpread psi f u : R} (hp : 0<psi) (gu : 0≤g)
    (price0 : 0≤price) (spread0 : 0≤upperSpread) (u0 : 0≤u) (uCap : 2*u≤3) :
    0≤shift u g price upperSpread psi f ∧ 2*shift u g price upperSpread psi f≤3*g := by
  let g0 := clippedGain g price upperSpread
  have nn : 0≤g0 := positivePartNonnegative _
  have cost := OrderedRing.mul_nonneg price0 spread0
  have cap : g0≤g := by dsimp [g0,clippedGain,positivePart]; split <;> grind only
  obtain ⟨_,ip,iu,_⟩ := penaltyNormalization (f:=f) hp
  have un := OrderedRing.mul_nonneg u0 nn
  have s0 := OrderedRing.mul_nonneg un (Std.le_of_lt ip)
  have bound := OrderedRing.mul_le_mul_of_nonneg_left iu un
  have right := OrderedRing.mul_le_mul_of_nonneg_right uCap nn
  change 0≤u*g0*penaltyInverse psi f ∧ 2*(u*g0*penaltyInverse psi f)≤3*g
  exact ⟨s0,by grind only⟩

/-- Exact evaluation with the common reserve Ψ₀. The positive-part case with
a nonpositive head gain has zero shift and zero payment on the whole rectangle. -/
theorem commonPaymentExact (u g price upperSpread psi0 f c d : R) (positive : 0<psi0) :
    let g0 := clippedGain g price upperSpread
    let inv := penaltyInverse psi0 f
    let s := shift u g price upperSpread psi0 f
    sourcePayment g s price psi0 f c d = commonPayment u g0 inv s price upperSpread c d := by
  let inv := penaltyInverse psi0 f
  have unit : penalty psi0 f*inv=1 := (penaltyNormalization positive).2.2.2
  dsimp only [sourcePayment,commonPayment,shift,clippedGain,positivePart]
  split
  · have cancel (x : R) : penalty psi0 f*inv*x=x := by rw [unit,Semiring.one_mul]
    have m := cancel (u^2*(g-price*upperSpread)^2*inv)
    dsimp only [inv] at m
    grind only
  · grind only

theorem sourceMonotone {g s price psi0 psi f c d : R}
    (positive : 0<psi0) (floor : psi0≤psi) :
    sourcePayment g s price psi0 f c d ≤ sourcePayment g s price psi f c d := by
  have p := penaltyAntitone (f:=f) positive floor
  have mult := OrderedRing.mul_le_mul_of_nonneg_right p (squareNonnegative s)
  unfold sourcePayment
  grind only

/-- Fixed rectangle parameters certify every tail point, including clipped zero gain. -/
theorem sharedShiftCertificate {u g cLo cHi dLo c d psi0 psi f : R}
    (hp : 0<psi0) (floor : psi0≤psi) (g0 : 0≤g) (_f0 : 0≤f) (f1 : f≤1)
    (u0 : 0≤u) (uCap : 2*u≤3) (rect : dLo≤cLo) (ordered : cLo≤c) (cu : c≤cHi) (dl : dLo≤d) :
    let price := alphaPrice f
    let gain := clippedGain g price (cHi-dLo)
    let inv := penaltyInverse psi0 f
    let s := shift u g price (cHi-dLo) psi0 f
    let affine := commonPayment u gain inv s price (cHi-dLo) c d
    0≤s ∧ 2*s≤3*g ∧ 0≤affine ∧ affine≤sourcePayment g s price psi f c d := by
  let price := alphaPrice f
  let gain := clippedGain g price (cHi-dLo)
  let inv := penaltyInverse psi0 f
  let s := shift u g price (cHi-dLo) psi0 f
  have p0 : 0≤price := alphaPriceNonnegative f1
  have spread : 0≤cHi-dLo := by grind only
  obtain ⟨ss,sc⟩ := shiftAdmissible (f:=f) hp g0 p0 spread u0 uCap
  have us := OrderedRing.mul_nonneg u0 (show 0≤2-u by have := OrderedRing.zero_lt_one (R:=R); grind only)
  have quad := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg us (squareNonnegative gain))
    (Std.le_of_lt (penaltyNormalization (f:=f) hp).2.1)
  have slope := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg ss p0) (show 0≤(cHi-dLo)-(c-d) by grind only)
  refine ⟨ss,sc,?_,?_⟩
  · change 0≤12*u*(2-u)*gain^2*penaltyInverse psi0 f+24*s*price*((cHi-dLo)-(c-d))
    change 0≤s*price*((cHi-dLo)-(c-d)) at slope
    grind only
  · rw [←commonPaymentExact _ _ _ _ _ _ _ _ hp]
    exact sourceMonotone hp floor

/-- The common reserve actually used by the checker, combining the global
1/13 floor with the tighter interval floor when it applies. -/
noncomputable def rectangleReserve (h q cLo cHi dLo dHi : R) : R := by
  classical
  let localFloor := (positivePart (cLo-dHi))^2+((1-cHi)^2+dLo^2)/6
  exact (h^2+q^2)/6 + if 1/13≤localFloor then localFloor else 1/13

def actualReserve (h q c d : R) : R := (c-d)^2+(h^2+q^2+(1-c)^2+d^2)/6

private theorem squareGrowth {a b : R} (aNonneg : 0≤a) (greater : a≤b) : a^2≤b^2 := by
  have h := OrderedRing.mul_nonneg (show 0≤b-a by grind only) (show 0≤b+a by grind only)
  grind only

/-- The corner-based reserve is strictly positive and is valid for every
ordered point in the rectangle. No positive gap between c and d is needed. -/
theorem reserveBounds {h q cLo cHi dLo dHi c d : R}
    (cl : cLo≤c) (cu : c≤cHi) (du : d≤dHi) (dl : dLo≤d) (dl0 : 0≤dLo)
    (cu1 : cHi≤1) (ordered : d≤c) :
    0<rectangleReserve h q cLo cHi dLo dHi ∧ rectangleReserve h q cLo cHi dLo dHi≤actualReserve h q c d := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have six : (0:R)<6 := by grind only
  have thirteen : (0:R)<13 := by grind only
  have global := UpperCorner.psiTailFloor c d
  have frac := quotientEq (1:R) thirteen
  have headN := quotientNonneg (show 0≤h^2+q^2 by have := squareNonnegative h; have := squareNonnegative q; grind only) six
  have headE := quotientEq (h^2+q^2) six
  have physicalE := quotientEq (h^2+q^2+(1-c)^2+d^2) six
  have localE := quotientEq ((1-cHi)^2+dLo^2) six
  have posFrac : (0:R)<1/13 := by
    by_cases e : (0:R)<1/13
    · exact e
    · have := OrderedRing.mul_le_mul_of_nonneg_left (show (1:R)/13≤0 by grind only) (Std.le_of_lt thirteen)
      grind only
  have g0 : (h^2+q^2)/6 + 1/13 ≤ actualReserve h q c d := by
    unfold actualReserve; grind only
  have headGap : positivePart (cLo-dHi)≤c-d := by
    unfold positivePart; split <;> grind only
  have floorGap := squareGrowth (positivePartNonnegative _) headGap
  have floorC := squareGrowth (show 0≤1-cHi by grind only) (show 1-cHi≤1-c by grind only)
  have floorD := squareGrowth dl0 dl
  have localVal : (h^2+q^2)/6 + ((positivePart (cLo-dHi))^2+((1-cHi)^2+dLo^2)/6) ≤ actualReserve h q c d := by
    unfold actualReserve; grind only
  dsimp only [rectangleReserve]; split <;> grind only

/-- The shared inverse penalty matches the quotient by Q as well as the
Ψ/(Ψ+12f²) implementation. -/
theorem shiftEqQuotient {u g price spread psi f : R} (hp : 0<psi) :
    shift u g price spread psi f = (u*clippedGain g price spread)/penalty psi f := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  obtain ⟨lower,_,_,unit⟩ := penaltyNormalization (f:=f) hp
  have positive : 0<penalty psi f := by grind only
  have right := quotientEq (u*clippedGain g price spread) positive
  have left := congrArg (fun z : R => z*(u*clippedGain g price spread)) unit
  have eq : penalty psi f * shift u g price spread psi f = penalty psi f*((u*clippedGain g price spread)/penalty psi f) := by
    unfold shift; grind only
  exact Std.le_antisymm (cancelLe positive (Std.le_of_eq eq)) (cancelLe positive (Std.le_of_eq eq.symm))

private theorem supportValuePositive (inside outside : R) (sumPos : 0<inside+outside) :
    0≤positivePart (inside-outside)/(inside+outside) := quotientNonneg (positivePartNonnegative _) sumPos

noncomputable def supportRatio (inside outside : R) : R := positivePart (inside-outside)/(inside+outside)

/-- The exact maximizing support ratio grows with the inside endpoint; this
also covers zero support at the lower corner. -/
theorem supportRatioMonotone {inside0 inside outside : R}
    (increase : inside0≤inside) (outsideNonneg : 0≤outside) (den : 0<inside0+outside) :
    supportRatio inside0 outside≤supportRatio inside outside := by
  have den' : 0<inside+outside := by grind only
  by_cases active : 0≤inside0-outside
  · have active' : 0≤inside-outside := by grind only
    simp only [supportRatio,positivePart,ite_eq_left active,ite_eq_left active']
    let d0 := inside0+outside
    let d1 := inside+outside
    let w0 := (inside0-outside)/d0
    let w := (inside-outside)/d1
    have e0 : d0*w0=inside0-outside := quotientEq _ den
    have e : d1*w=inside-outside := quotientEq _ den'
    have a := congrArg (fun t : R => d1*t) e0
    have b := congrArg (fun t : R => d0*t) e
    have positive := OrderedRing.mul_nonneg outsideNonneg (show 0≤inside-inside0 by grind only)
    apply cancelLe (z:=d0) den; apply cancelLe (z:=d1) den'
    change d1*(d0*w0)≤d1*(d0*w)
    rw [e0]; have right : d1*(d0*w) = d0*(inside-outside) := by grind only
    rw [right]; dsimp [d0,d1]; grind only
  · unfold supportRatio at *
    rw [show positivePart (inside0-outside)=0 by simp [positivePart,active],Field.div_eq_mul_inv,Semiring.zero_mul]
    exact supportValuePositive inside outside den'

/-- An outward lower support weight at one corner remains a valid nonnegative
common lower price throughout the rectangle. -/
theorem supportPriceNonnegative {inside0 inside outside w : R} (increase : inside0≤inside)
    (outsideNonneg : 0≤outside) (den : 0<inside0+outside) (w0 : 0≤w) (admissible : w≤supportRatio inside0 outside) :
    0≤UpperCorner.twiceSupport inside outside w := by
  have den' : 0<inside+outside := by grind only
  have wle := Std.le_trans admissible (supportRatioMonotone increase outsideNonneg den)
  apply UpperCorner.supportNonnegative _ _ _ w0 (Std.le_of_lt den')
  by_cases active : 0≤inside-outside
  · right
    have b := OrderedRing.mul_le_mul_of_nonneg_left wle (Std.le_of_lt den')
    simp only [supportRatio,positivePart,ite_eq_left active] at b
    rw [quotientEq _ den'] at b
    grind only
  · left
    simp only [supportRatio,positivePart,ite_eq_right active,Field.div_eq_mul_inv,Semiring.zero_mul] at wle
    grind only

/-- On the actual interval rectangle, the fixed choice of Ψ₀ and the shift s
works uniformly at each tail point, with no auxiliary reserve hypothesis. -/
theorem sharedShiftOnBox {h q g cLo cHi dLo dHi c d u f : R}
    (cl : cLo≤c) (cu : c≤cHi) (du : d≤dHi) (dl : dLo≤d) (dl0 : 0≤dLo)
    (cu1 : cHi≤1) (ordered : d≤c) (cornerOrder : dLo≤cLo)
    (hg : 0≤g) (f0 : 0≤f) (f1 : f≤1) (u0 : 0≤u) (uCap : 2*u≤3) :
    let ps := rectangleReserve h q cLo cHi dLo dHi
    let price := alphaPrice f
    let gain := clippedGain g price (cHi-dLo)
    let s := shift u g price (cHi-dLo) ps f
    let paid := commonPayment u gain (penaltyInverse ps f) s price (cHi-dLo) c d
    0<ps ∧ 0≤s ∧ 2*s≤3*g ∧ 0≤paid ∧ paid≤sourcePayment g s price (actualReserve h q c d) f c d := by
  obtain ⟨pos,lower⟩ := reserveBounds (h:=h) (q:=q) cl cu du dl dl0 cu1 ordered
  exact ⟨pos,sharedShiftCertificate pos lower hg f0 f1 u0 uCap cornerOrder cl cu dl⟩

/-- Explicitly evaluate the clipping branch even when the uncorrected gain is negative. -/
theorem clippedZero {u g price spread psi f c d : R} (off : g≤price*spread) :
    let g0 := clippedGain g price spread
    let s := shift u g price spread psi f
    g0=0 ∧ s=0 ∧ commonPayment u g0 (penaltyInverse psi f) s price spread c d=0 := by
  have zero : clippedGain g price spread=0 := by
    unfold clippedGain positivePart; split <;> grind only
  dsimp only [shift]; rw [zero]; unfold commonPayment; grind only

def supportValue (inner outer w : R) : R :=
  (w-w^2/2)*inner-(w+w^2/2)*outer

def oddTangent (cHi dLo c d : R) : R := (1-cHi)*(1+cHi-2*c)+dLo*(2*d-dLo)

/-- Coefficients of the lower price at fixed heads, ray, support weights, and shift.
Only the two compression supports contribute to the c*d coefficient. -/
def pricePolynomial (base slope oddWeight cHi dLo
    highestWeight highestInside highestOutside highestSupport
    sharedWeight sharedInside sharedOutside sharedSupport : R) : Bilinear R :=
  ⟨base+slope*(cHi-dLo)+oddWeight*((1-cHi)*(1+cHi)-dLo^2)
      -highestWeight*(highestSupport+highestSupport^2/2)*highestOutside,
    -slope-2*(1-cHi)*oddWeight-sharedWeight*(sharedSupport+sharedSupport^2/2)*sharedOutside,
    slope+2*dLo*oddWeight,
    highestWeight*(highestSupport-highestSupport^2/2)*highestInside+
      sharedWeight*(sharedSupport-sharedSupport^2/2)*sharedInside⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem pricePolynomialEval (base slope oddWeight cHi dLo A I O wh B J T ws c d : R) :
    (pricePolynomial base slope oddWeight cHi dLo A I O wh B J T ws).eval c d =
    base+slope*((cHi-dLo)-(c-d))+oddWeight*oddTangent cHi dLo c d+
      A*supportValue (I*c*d) O wh+B*c*supportValue (J*d) T ws := by
  unfold pricePolynomial Bilinear.eval oddTangent supportValue; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- The complete common physical lower price in the corner checker is multiaffine.
The denominators, trace factors, heads and shifts in this identity are shared
across all four corners. -/
theorem checkerPriceMultiaffine (g h k q sharedQuad s price cHi dLo highestQuad
    invRate invGeom peak v highTrace sharedTrace highInside highOutside
    sharedInside sharedOutside highSupport sharedSupport : R) :
    ∃ p : Bilinear R, ∀ c d,
      let odd := oddTangent cHi dLo c d
      let physicalShared := ((g^2+sharedQuad+24*s*price*((cHi-dLo)-(c-d))+
        odd*g^2/(h^2+3*q^2))*invRate)/12
      let physicalHigh := (highestQuad+odd*k^2/2)*invRate*invGeom
      let cuts := 96*invRate*(supportValue (highInside*c*d) highOutside highSupport*highTrace+
        c*supportValue (sharedInside*d) sharedOutside sharedSupport*sharedTrace)
      p.eval c d=physicalShared*peak+physicalHigh*v+cuts := by
  let a := invRate*peak/12
  let b := invRate*invGeom*v
  refine ⟨pricePolynomial ((g^2+sharedQuad)*a+highestQuad*b) (24*s*price*a)
    ((g^2/(h^2+3*q^2))*a+(k^2/2)*b) cHi dLo
    (96*invRate*highTrace) highInside highOutside highSupport
    (96*invRate*sharedTrace) sharedInside sharedOutside sharedSupport,?_⟩
  intro c d
  rw [pricePolynomialEval]
  dsimp only [a,b]
  simp only [Field.div_eq_mul_inv]
  grind only

/-- Lower-left support weights are valid simultaneously for the highest inside
endpoint proportional to c*d and the shared inside endpoint proportional to d. -/
theorem rectangleSupports {cLo dLo c d highInside highOutside sharedInside sharedOutside wh ws : R}
    (cLo0 : 0≤cLo) (dLo0 : 0≤dLo) (cl : cLo≤c) (dl : dLo≤d)
    (hi0 : 0≤highInside) (ho0 : 0≤highOutside) (si0 : 0≤sharedInside) (so0 : 0≤sharedOutside)
    (hd : 0<highInside*cLo*dLo+highOutside) (sd : 0<sharedInside*dLo+sharedOutside)
    (wh0 : 0≤wh) (ws0 : 0≤ws)
    (whLower : wh≤supportRatio (highInside*cLo*dLo) highOutside)
    (wsLower : ws≤supportRatio (sharedInside*dLo) sharedOutside) :
    0≤supportValue (highInside*c*d) highOutside wh ∧ 0≤c*supportValue (sharedInside*d) sharedOutside ws := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have twice (i o w : R) : UpperCorner.twiceSupport i o w=2*supportValue i o w := by
    have e := quotientEq (w^2) (show (0:R)<2 by grind only)
    unfold UpperCorner.twiceSupport supportValue; grind only
  have s : sharedInside*dLo≤sharedInside*d := OrderedRing.mul_le_mul_of_nonneg_left dl si0
  have h1 := OrderedRing.mul_le_mul_of_nonneg_right (OrderedRing.mul_le_mul_of_nonneg_left cl hi0) dLo0
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left dl (OrderedRing.mul_nonneg hi0 (show 0≤c by grind only))
  have h := supportPriceNonnegative (Std.le_trans h1 h2) ho0 hd wh0 whLower
  have t := supportPriceNonnegative s so0 sd ws0 wsLower
  rw [twice] at h t
  exact ⟨by grind only,OrderedRing.mul_nonneg (show 0≤c by grind only) (by grind only)⟩

end RankSeven.UpperPrices

#print axioms RankSeven.UpperPrices.penaltyNormalization
#print axioms RankSeven.UpperPrices.commonPaymentExact
#print axioms RankSeven.UpperPrices.sourceMonotone
#print axioms RankSeven.UpperPrices.reserveBounds
#print axioms RankSeven.UpperPrices.sharedShiftOnBox
#print axioms RankSeven.UpperPrices.clippedZero
#print axioms RankSeven.UpperPrices.supportRatioMonotone
#print axioms RankSeven.UpperPrices.rectangleSupports
#print axioms RankSeven.UpperPrices.checkerPriceMultiaffine
