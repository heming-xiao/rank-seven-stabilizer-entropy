import Rank7UpperContractor
import Rank7UpperPrices

namespace RankSeven.UpperWeighted

open Lean.Grind Interval UpperCorner UpperContractor
open UpperPrices (positivePart)

def price (grid : Grid) (box : TailBox) (shift : Bounds) : Option Bounds :=
  let H := whole grid
  let product := Bounds.mul grid
  let square := Bounds.square grid
  let x := (box.h.add box.k).add box.q
  let g := product box.h box.q
  let delta := product box.k x
  let alpha := (H 1).add x
  let beta := (H 1).add (box.k.add box.q)
  let gamma := (H 1).add box.q
  let a := product (product (product alpha beta) box.c) box.d
  let b := product alpha gamma
  let denominator := product (H 2) (a.add b)
  if 0 < denominator.lo then
    let cut := Bounds.div grid (product (H 1) (square (a.sub b).positivePart)) denominator
    let invGeom := Bounds.div grid (H 1) (Bounds.rational grid 5 2)
    let remainder := Bounds.div grid ((square box.h).add (square box.q)) (H 2)
    let anti := product (square box.k) ((square box.k).add remainder)
    let highest := product
      ((product (product (product (H 12) shift) ((H 2).sub shift)) (square delta)).add anti)
      invGeom
    let reserve := (Bounds.div grid (square g) (H 24)).largest
      (Bounds.div grid (square (square box.q)) (H 72))
    let payment := (highest.add reserve).add (product (H 64) cut)
    let D := box.d.sub (product ((H 1).sub box.d) box.c)
    let debit := (product (product ((H 168).sub (product (H 24) shift)) delta) D).sub
      (product (product (product (H 168) box.k) box.c) box.d)
    some (payment.sub debit)
  else none

def shifts (grid : Grid) : List Bounds :=
  [whole grid 1, Bounds.rational grid 5 4, Bounds.rational grid 3 2]

def accepts (grid : Grid) (box : TailBox) : Bool :=
  (shifts grid).any fun u => match price grid box u with
    | some margin => decide (0 < margin.lo)
    | none => false

section Ordered

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def larger (x y : R) : R := by
  classical exact if y ≤ x then x else y

noncomputable def gapPrice (inner outer : R) : R :=
  (positivePart (inner-outer) * positivePart (inner-outer))/(2*(inner+outer))

noncomputable def margin (h k q c d u : R) : R :=
  let x := h+k+q
  let g := h*q
  let delta := k*x
  let alpha := 1+x
  let beta := 1+(k+q)
  let gamma := 1+q
  let cut := gapPrice (alpha*beta*c*d) (alpha*gamma)
  let anti := (k*k)*(k*k+(h*h+q*q)/2)
  let highest := (12*u*(2-u)*(delta*delta)+anti)*(1/(5/2:R))
  let reserve := larger ((g*g)/24) (((q*q)*(q*q))/72)
  let payment := highest+reserve+64*cut
  let debit := (168-24*u)*delta*discount c d-168*k*c*d
  payment-debit

private theorem divValue (a b : R) (nonzero : b ≠ 0) : b*(a/b)=a := by
  have inv := Field.mul_inv_cancel nonzero
  rw [Field.div_eq_mul_inv]
  grind only

private theorem clipSound {g : Grid} {a : Bounds} {x : R} (hx : a.Contains g x) :
    a.positivePart.Contains g (positivePart x) := by
  apply Bounds.positivePartSound hx
  unfold positivePart
  split <;> grind only

theorem largerSound {g : Grid} {a b : Bounds} {x y : R}
    (hx : a.Contains g x) (hy : b.Contains g y) :
    (a.largest b).Contains g (larger x y) := by
  apply Bounds.largestSound hx hy
  unfold larger
  split <;> grind only

/-- Outward rounding of every operation in the C++ weighted branch. -/
theorem priceSound {box : TailBox} {shift result : Bounds} {h k q c d u : R}
    (inside : Inside cppGrid box h k q c d) (shiftInside : shift.Contains cppGrid u)
    (computed : price cppGrid box shift=some result) :
    result.Contains cppGrid (margin h k q c d u) := by
  obtain ⟨hh,hk,hq,hc,hd⟩ := inside
  let N := wholeSound (R:=R) cppGrid
  have X := Bounds.addSound (Bounds.addSound hh hk) hq
  have G := Bounds.mulSound hh hq
  have Δ := Bounds.mulSound hk X
  have A := Bounds.addSound (N 1) X
  have B := Bounds.addSound (N 1) (Bounds.addSound hk hq)
  have C := Bounds.addSound (N 1) hq
  have I := Bounds.mulSound (Bounds.mulSound (Bounds.mulSound A B) hc) hd
  have O := Bounds.mulSound A C
  have den := Bounds.mulSound (N 2) (Bounds.addSound I O)
  unfold price at computed
  dsimp only at computed
  split at computed
  case isFalse => contradiction
  case isTrue guard =>
    injection computed with eq
    rw [←eq]
    have cut := UpperContractor.divSound
      (Bounds.mulSound (N 1) (Bounds.squareSound (clipSound (Bounds.subSound I O)))) den guard
    simp only [Semiring.one_mul] at cut
    have invGeom := UpperContractor.divSound (N 1)
      (fractionSound (R:=R) cppGrid 5 2 (by decide)) (by decide)
    have k2 := Bounds.squareSound hk
    have q2 := Bounds.squareSound hq
    have remainder := UpperContractor.divSound (Bounds.addSound (Bounds.squareSound hh) q2)
      (N 2) (by decide)
    have anti := Bounds.mulSound k2 (Bounds.addSound k2 remainder)
    have shiftPay := Bounds.mulSound
      (Bounds.mulSound (Bounds.mulSound (N 12) shiftInside) (Bounds.subSound (N 2) shiftInside))
      (Bounds.squareSound Δ)
    have highest := Bounds.mulSound (Bounds.addSound shiftPay anti) invGeom
    have reserve := largerSound
      (UpperContractor.divSound (Bounds.squareSound G) (N 24) (by decide))
      (UpperContractor.divSound (Bounds.squareSound q2) (N 72) (by decide))
    have payment := Bounds.addSound (Bounds.addSound highest reserve) (Bounds.mulSound (N 64) cut)
    have D := Bounds.subSound hd (Bounds.mulSound (Bounds.subSound (N 1) hd) hc)
    have debit := Bounds.subSound
      (Bounds.mulSound (Bounds.mulSound (Bounds.subSound (N 168) (Bounds.mulSound (N 24) shiftInside))
        Δ) D)
      (Bounds.mulSound (Bounds.mulSound (Bounds.mulSound (N 168) hk) hc) hd)
    exact Bounds.subSound payment debit

/-- The integer test certifies a strictly positive analytic weighted margin
for an actual one of the three rational shifts in the upper verifier. -/
theorem acceptedMargin {box : TailBox} {h k q c d : R}
    (inside : Inside cppGrid box h k q c d) (accepted : accepts cppGrid box=true) :
    ∃ u : R, (u=1 ∨ u=5/4 ∨ u=3/2) ∧ 0<margin h k q c d u := by
  obtain ⟨shift, hm, hs⟩ := List.any_eq_true.mp accepted
  have cases : shift=whole cppGrid 1 ∨ shift=Bounds.rational cppGrid 5 4 ∨
      shift=Bounds.rational cppGrid 3 2 := by simpa [shifts] using hm
  obtain ⟨u, value, contained⟩ :
      ∃ u : R, (u=1 ∨ u=5/4 ∨ u=3/2) ∧ shift.Contains cppGrid u := by
    rcases cases with rfl | rfl | rfl
    · exact ⟨1,Or.inl rfl,wholeSound cppGrid 1⟩
    · exact ⟨5/4,Or.inr (Or.inl rfl),fractionSound cppGrid 5 4 (by decide)⟩
    · exact ⟨3/2,Or.inr (Or.inr rfl),fractionSound cppGrid 3 2 (by decide)⟩
  refine ⟨u,value,?_⟩
  cases hp : price cppGrid box shift with
  | none => simp [hp] at hs
  | some result =>
    simp only [hp, decide_eq_true_eq] at hs
    exact lowerEndpointPositive (priceSound inside contained hp) hs

/-- The rational price used by the checker is a lower bound on the
squared positive-part square-root gap in the physical cut. -/
theorem gapPriceLeSquareRootGap (inner outer p q : R)
    (hp : 0≤p) (hq : 0≤q) (rootP : p*p=inner) (rootQ : q*q=outer)
    (nonzero : 0<inner+outer) :
    gapPrice inner outer ≤ positivePart (p-q)*positivePart (p-q) := by
  have den : 0<2*(inner+outer) := by grind only
  have scaled := divValue
    (positivePart (inner-outer)*positivePart (inner-outer)) (2*(inner+outer))
    (by grind only)
  have lp : p≤q → inner≤outer := by
    intro order
    have nn := OrderedRing.mul_nonneg (show 0≤q-p by grind only) (show 0≤q+p by grind only)
    grind only
  have lq : q≤p → outer≤inner := by
    intro order
    have nn := OrderedRing.mul_nonneg (show 0≤p-q by grind only) (show 0≤p+q by grind only)
    grind only
  have comparison : positivePart (inner-outer)*positivePart (inner-outer) ≤
      2*(inner+outer)*(positivePart (p-q)*positivePart (p-q)) := by
    classical
    unfold positivePart
    by_cases order : q≤p
    · have hi := lq order
      simp only [show 0≤p-q from by grind only,show 0≤inner-outer from by grind only,ite_true]
      rw [←rootP, ←rootQ]
      have sq : 0≤(p-q)*(p-q) := by
        have := RankSeven.squareNonnegative (p-q)
        grind only
      have fourth := OrderedRing.mul_nonneg sq sq
      calc
        _ ≤ (p*p-q*q)*(p*p-q*q)+(p-q)*(p-q)*((p-q)*(p-q)) := by grind only
        _ = _ := by grind only
    · have hi := lp (by grind only)
      have hneg : ¬0≤p-q := by grind only
      split <;> grind only
  unfold gapPrice
  by_cases bound : (positivePart (inner-outer)*positivePart (inner-outer))/(2*(inner+outer)) ≤
      positivePart (p-q)*positivePart (p-q)
  · exact bound
  · have greater : positivePart (p-q)*positivePart (p-q) <
        (positivePart (inner-outer)*positivePart (inner-outer))/(2*(inner+outer)) := by grind only
    have opposite := OrderedRing.mul_lt_mul_of_pos_left greater den
    rw [scaled] at opposite
    grind only


/-- Failure of the unit-shift arithmetic comparison forces the strict
quadratic and quartic residual inequalities. Positivity of the completion
term supplies strictness even when the comparison margin equals zero. -/
theorem failedUnitPolynomialBounds {h k q c d : R}
    (h0 : 0≤h) (k0 : 0<k) (q0 : 0≤q) (c0 : 0<c) (d0 : 0<d)
    (failed : margin h k q c d 1≤0) :
    let delta := k*(h+k+q)
    let D := discount c d
    let g := h*q
    0<D ∧ 0<delta ∧ 2928*delta^2+25*g^2<86400*D*delta ∧
      8784*delta^2+25*q^4<259200*D*delta := by
  let x := h+k+q
  let delta := k*x
  let D := discount c d
  let g := h*q
  let r := k*k+(h*h+q*q)/2
  let higher := (12*delta*delta+k*k*r)*(1/(5/2:R))
  let G := (g*g)/24
  let Q := ((q*q)*(q*q))/72
  let inner := (1+x)*(1+(k+q))*c*d
  let outer := (1+x)*(1+q)
  have deltaPos : 0<delta := OrderedRing.mul_pos k0 (by unfold x; grind only)
  have completePos := OrderedRing.mul_pos
    (OrderedRing.mul_pos k0 c0) d0
  have pInner : 0<inner := by
    apply OrderedRing.mul_pos _ d0
    apply OrderedRing.mul_pos _ c0
    exact OrderedRing.mul_pos (show (0:R)<1+x by unfold x; grind only) (by grind only)
  have pOuter : 0<outer := OrderedRing.mul_pos (by unfold x; grind only) (by grind only)
  have sumPos : 0<2*(inner+outer) := by grind only
  have cut0 : 0≤gapPrice inner outer := by
    let a := positivePart (inner-outer)
    have product := RankSeven.squareNonnegative a
    have scale := divValue (a*a) (2*(inner+outer)) (by grind only)
    by_cases nz : 0≤gapPrice inner outer
    · exact nz
    · have below : gapPrice inner outer<0 := by grind only
      have strict := OrderedRing.mul_lt_mul_of_pos_left below sumPos
      change 2*(inner+outer)*(a*a/(2*(inner+outer)))<2*(inner+outer)*0 at strict
      rw [scale] at strict
      grind only
  have reserve : G≤larger G Q ∧ Q≤larger G Q := by
    unfold larger
    split <;> grind only
  have rScale : 2*r=2*k*k+h*h+q*q := by
    have halfSum := divValue (h*h+q*q) (2:R) (by grind only)
    unfold r
    grind only
  have variance : x^2≤5*r := by
    have first := RankSeven.squareNonnegative (h-2*k)
    have second := RankSeven.squareNonnegative (q-2*k)
    have third := RankSeven.squareNonnegative (h-q)
    unfold x
    grind only
  have kSq := RankSeven.squareNonnegative k
  have lowerAnti := OrderedRing.mul_le_mul_of_nonneg_left variance kSq
  have invNorm : 5*(1/(5/2:R))=2 := by
    have fifth := divValue (5:R) 2 (by grind only)
    have inv := divValue (1:R) (5/2:R) (by
      intro zero
      rw [zero] at fifth
      grind only)
    have multiplied := congrArg (fun a : R => a*(1/(5/2:R))) fifth
    grind only
  have higherScale : 122*delta^2 ≤ 25*higher := by
    have product := congrArg (fun a : R => 5*(12*delta*delta+k*k*r)*a) invNorm
    dsimp only [higher,delta] at *
    grind only
  have failed' : higher+larger G Q+64*gapPrice inner outer ≤144*delta*D-168*k*c*d := by
    unfold margin at failed
    dsimp only at failed
    dsimp only [higher, G, Q, g, inner, outer, delta, x, D, r]
    grind only
  have caseG : higher+G<144*delta*D := by grind only [reserve.1]
  have caseQ : higher+Q<144*delta*D := by grind only [reserve.2]
  have scaleG := OrderedRing.mul_lt_mul_of_pos_left caseG (show (0:R)<600 by grind only)
  have scaleQ := OrderedRing.mul_lt_mul_of_pos_left caseQ (show (0:R)<1800 by grind only)
  have Gclear : 24*G=g*g := divValue _ _ (by grind only)
  have Qclear : 72*Q=q^4 := by
    have step := divValue ((q*q)*(q*q)) (72:R) (by grind only)
    dsimp only [Q]
    grind only
  have gResult : 2928*delta^2+25*g^2<86400*D*delta := by grind only
  have qResult : 8784*delta^2+25*q^4<259200*D*delta := by grind only
  have Dpos : 0<D := by
    by_cases pos : 0<D
    · exact pos
    · have dWeak : 0≤-D := by grind only
      have nonpositive := OrderedRing.mul_nonneg dWeak (Std.le_of_lt deltaPos)
      have deltaSq := RankSeven.squareNonnegative delta
      have gSq := RankSeven.squareNonnegative g
      grind only
  exact ⟨Dpos,deltaPos,gResult,qResult⟩

end Ordered
end RankSeven.UpperWeighted

#print axioms RankSeven.UpperWeighted.priceSound
#print axioms RankSeven.UpperWeighted.acceptedMargin
#print axioms RankSeven.UpperWeighted.gapPriceLeSquareRootGap

#print axioms RankSeven.UpperWeighted.failedUnitPolynomialBounds
