import Rank7UpperEndpoint

/-! The real corner table uses the same reserve, shift, support prices and
physical multiaffine contribution as the analytic box argument. -/
namespace RankSeven.UpperEndpointPrices
open Lean.Grind UpperEndpoint UpperPrices
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable abbrev H (p : Inputs R) := heads realArithmetic p
noncomputable abbrev invRate : R := 1/(4242/25:R)
noncomputable abbrev invGeom : R := 1/(5/2:R)
noncomputable abbrev P (p : Inputs R) := prices realArithmetic p (H p) invRate ((H p).psi/(H p).den)
noncomputable abbrev K (p : Inputs R) (wh ws c d : R) := supports realArithmetic p (H p) wh ws c d
noncomputable abbrev B (p : Inputs R) (wh ws c d : R) :=
  chargeAt realArithmetic p (H p) (P p) (K p wh ws c d) invRate invGeom
    ((K p wh ws c d).odd*(H p).g2/(H p).oddDen) c d

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sq (x : R) : x*x=x^2 := by grind only

omit [LT R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem reserveMatches (p : Inputs R) : (H p).psi=rectangleReserve p.h p.q p.cl p.ch p.dl p.dh := by
  classical
  let floor : R := (positivePart (p.cl-p.dh))^2+((1-p.ch)^2+p.dl^2)/6
  change (p.h*p.h+p.q*p.q)/6+UpperWeighted.larger (1/13:R)
    (positivePart (p.cl-p.dh)*positivePart (p.cl-p.dh)+((1-p.ch)*(1-p.ch)+p.dl*p.dl)/6)=_
  simp only [sq]; unfold rectangleReserve UpperWeighted.larger
  change _+(if floor≤1/13 then 1/13 else floor)=_+(if 1/13≤floor then floor else 1/13)
  apply congrArg (fun z : R => (p.h^2+p.q^2)/6+z)
  split <;> split
  · exact Std.le_antisymm ‹1/13≤floor› ‹floor≤1/13›
  · rfl
  · rfl
  · exact False.elim (‹¬floor≤1/13› (Std.le_of_not_ge ‹¬1/13≤floor›))

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem penaltyMatches (p : Inputs R) : (H p).psi/(H p).den=penaltyInverse (H p).psi p.f := by
  change _/((H p).psi+12*(p.f*p.f))=_; rw [sq]; rfl

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem gainMatches (p : Inputs R) :
    (H p).clipped=clippedGain (p.h*p.q) (alphaPrice p.f) (p.ch-p.dl) := rfl

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem shiftMatches (p : Inputs R) :
    (P p).shift=shift p.u (p.h*p.q) (alphaPrice p.f) (p.ch-p.dl) (H p).psi p.f := by
  change p.u*(H p).clipped*((H p).psi/(H p).den)=_; rw [penaltyMatches]; rfl

noncomputable def paid (p : Inputs R) (c d : R) :=
  (P p).sharedQuad+24*(P p).shift*(H p).tax*((p.ch-p.dl)-(c-d))

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem paidMatches (p : Inputs R) (c d : R) : paid p c d=
    commonPayment p.u (H p).clipped (penaltyInverse (H p).psi p.f) (P p).shift (H p).tax (p.ch-p.dl) c d := by
  change 12*p.u*(2-p.u)*((H p).clipped*(H p).clipped)*((H p).psi/(H p).den)+_=_
  rw [sq,penaltyMatches]; rfl

/-- Physical payment at any ordered point dominates the shift and the scalar
shared payment computed for the whole endpoint rectangle. -/
theorem physicalShiftAndPayment (p : Inputs R) (c d : R) (cl : p.cl≤c) (cu : c≤p.ch) (du : d≤p.dh)
    (dl : p.dl≤d) (dl0 : 0≤p.dl) (cu1 : p.ch≤1) (ordered : d≤c) (cornerOrder : p.dl≤p.cl)
    (g0 : 0≤p.h*p.q) (f0 : 0≤p.f) (f1 : p.f≤1) (u0 : 0≤p.u) (uc : 2*p.u≤3) :
    0<(H p).psi ∧ 0≤(P p).shift ∧ 2*(P p).shift≤3*p.h*p.q ∧ 0≤paid p c d ∧
      paid p c d≤sourcePayment (p.h*p.q) (P p).shift (alphaPrice p.f) (actualReserve p.h p.q c d) p.f c d := by
  have v := sharedShiftOnBox (h:=p.h) (q:=p.q) cl cu du dl dl0 cu1 ordered cornerOrder g0 f0 f1 u0 uc
  rw [paidMatches,shiftMatches,gainMatches,reserveMatches]
  rw [show 3*p.h*p.q=3*(p.h*p.q) by grind only]
  exact v

noncomputable def physicalPrice (p : Inputs R) (wh ws c d : R) (r : RayData R) : R :=
  let A := B p wh ws c d
  let e := K p wh ws c d
  A.physicalShared*r.peak+A.physicalHigh*r.v+96*invRate*(e.one*r.traceOne+e.shared*r.traceShared)

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- The literal physical term in the replay leaf is multiaffine in c and d. -/
theorem physicalPriceMultiaffine (p : Inputs R) (wh ws : R) (r : RayData R) :
    ∃ poly : Interval.Bilinear R,∀ c d,poly.eval c d=physicalPrice p wh ws c d r := by
  obtain ⟨poly,law⟩ := checkerPriceMultiaffine (H p).g p.h p.k p.q (P p).sharedQuad (P p).shift
    (H p).tax p.ch p.dl (P p).highQuad invRate invGeom r.peak r.v r.traceOne r.traceShared
    (H p).highInside (H p).pair (H p).pair (H p).lowOutside wh ws
  refine ⟨poly,?_⟩; intro c d
  have t := law c d
  dsimp only at t
  rw [←sq,←sq,←sq,←sq,show (H p).highInside*c*d=(H p).highInside*(c*d) by grind only] at t
  exact t

/-- The two support terms in the checked leaf are nonnegative throughout
the rectangle, including the clipped zero-weight case. -/
theorem supportTerms (p : Inputs R) (wh ws c d : R) (valid : WeightLimits p wh ws)
    (cl0 : 0≤p.cl) (dl0 : 0≤p.dl) (cl : p.cl≤c) (dl : p.dl≤d)
    (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q) :
    0≤(K p wh ws c d).one ∧ 0≤(K p wh ws c d).shared := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have a0 : 0≤1+(p.h+p.k+p.q) := by grind only
  have b0 : 0≤1+(p.k+p.q) := by grind only
  have g0 : 0≤1+p.q := by grind only
  have pair : 0≤(H p).pair := OrderedRing.mul_nonneg a0 g0
  have high : 0≤(H p).highInside := OrderedRing.mul_nonneg a0 b0
  have out : 0≤(H p).lowOutside := by
    change 0≤UpperWeighted.larger (1+(p.h+p.k+p.q)) ((1+(p.k+p.q))*(1+p.q))
    have bg := OrderedRing.mul_nonneg b0 g0; unfold UpperWeighted.larger; split <;> assumption
  have t := rectangleSupports cl0 dl0 cl dl high pair pair out valid.highDenPositive valid.sharedDenPositive
    valid.highNonnegative valid.sharedNonnegative valid.highUpper valid.sharedUpper
  rw [show (H p).highInside*c*d=(H p).highInside*(c*d) by grind only] at t; exact t


omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- The physical polynomial appears with coefficient one in both reported
margins; the remaining terms are the two geometric debit formulas. -/
theorem realMarginsDecomposed (p : Inputs R) (wh ws c d : R) (j : Fin 7) :
    let r := rayAt realArithmetic j
    let e := K p wh ws c d
    let A := B p wh ws c d
    let base := physicalPrice p wh ws c d r+(P p).residual*(e.tailPrefix*r.tail-e.dsq*r.v)
    let m := realRead p wh ws c d j
    m.splitMargin=base+e.cd*p.k*r.v-A.splitDebit*r.n ∧
      m.singleMargin=base+A.singleton*r.m+(e.dsq*e.dsq)*r.constant+A.increment*r.improvement-A.singleDebit*r.n :=
  ⟨rfl,rfl⟩

end RankSeven.UpperEndpointPrices
#print axioms RankSeven.UpperEndpointPrices.physicalShiftAndPayment
#print axioms RankSeven.UpperEndpointPrices.physicalPriceMultiaffine
#print axioms RankSeven.UpperEndpointPrices.supportTerms
#print axioms RankSeven.UpperEndpointPrices.realMarginsDecomposed
