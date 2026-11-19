import Rank7RealTiedCutPrice
import Rank7LowerCertifiedFrameReplay
import Rank7LowerPhysicalGainScale

namespace RankSeven.RealLowerCutPrice
open Pauli ExteriorCuts Compression RealTiedCutPrice

private theorem atPoint (xs : List Wedge7) (nd : xs.Nodup) (a : Wedge7) (z : ℝ) :
    Pauli.sumOver xs (fun b => if b=a then z else 0) = if a ∈ xs then z else 0 := by
  induction xs with
  | nil => simp [Pauli.sumOver]
  | cons b xs ih =>
    have free := (List.nodup_cons.mp nd).1
    have tail := ih (List.nodup_cons.mp nd).2
    change (if b=a then z else 0)+Pauli.sumOver xs _=_
    rw [tail]
    by_cases eq : b=a
    · subst b; simp [free]
    · have rev : a≠b := Ne.symm eq
      by_cases mem : a∈xs <;> simp_all

private theorem posMax (a : ℝ) : pos a=max a 0 := by
  unfold pos
  split
  · exact (max_eq_left ‹_›).symm
  · exact (max_eq_right (le_of_not_ge ‹_›)).symm

private theorem sqrtSq {s t : ℝ} (t0 : 0≤t) (h : t^2=s) : Real.sqrt s=t := by rw [←h,Real.sqrt_sq t0]

/-- The full nominal shared interval on the tied chart, including the
physical price of its one possible entering wedge. -/
theorem fullWidth (E : HermitianEntries Wedge7 ℝ) (effect : E.IsCoordinateEffect wedges)
    (half s α β γ c d : ℝ) (h2 : 2*half=1)
    (low : s≤cutCost wedges (fun w => w.level.low) (rowSlack wedges (fun w => E.realPart w w) E.mass) E.mass)
    (hg : 1≤γ) (gb : γ≤β) (ba : β≤α) (d0 : 0≤d) (dc : d≤c) (c1 : c≤1) :
    let t := weights α β γ c d
    let a := amplitude (fun i => Real.sqrt (t i))
    let l := Real.sqrt (c*max α (β*γ))
    let u := Real.sqrt (α*γ*c*d)
    (pos (u-l))^2*s-γ*(α-β)*d*(1-c)/2*E.realPart UpperFrameGain.entering UpperFrameGain.entering≤
      SectorDefectAccounting.compressionLoss a E := by
  let a := amplitude (fun i => Real.sqrt (weights α β γ c d i))
  let l := Real.sqrt (c*max α (β*γ)); let u := Real.sqrt (α*γ*c*d)
  let h := Real.sqrt (α*γ); let j := Real.sqrt (α*β*c*d)
  let charge := γ*(α-β)*d*(1-c)/2
  let diag (w : Wedge7) := E.realPart w w
  let slack := rowSlack wedges diag E.mass
  let costs (w : Wedge7) := outsideTax l u h j (a w) w.level*(diag w*(1-diag w))
  let charged (w : Wedge7) := if w=UpperFrameGain.entering then charge*diag w else 0
  have ⟨apart,inside,tax⟩ := chartGeometry α β γ c d hg gb ba d0 dc c1
  have row : ∀ w,0≤slack w := E.effectRowSlack wedges wedgesNodup memWedges effect
  have crossed := crossedCuts wedges Wedge7.level a slack diag E.mass l u h j half h2
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) apart inside row E.massNonnegative E.massSymmetric
    (fun w => E.rowCap wedges wedgesNodup w (memWedges w) (row w))
  let L := cutCost wedges (fun w => w.level.low) slack E.mass
  let H := cutCost wedges (fun w => w.level.high) slack E.mass
  have loss := E.realLossEqHalf wedges a half h2
  change (pos (u-l))^2*L+(pos (j-h))^2*H-sumOver wedges costs≤diagonalLoss wedges a slack+half*squaredGapCost wedges a E.mass at crossed
  rw [loss] at crossed
  have g0 : 0≤γ := by linarith
  have charge0 : 0≤charge := by dsimp [charge]; positivity
  have each (w : Wedge7) : costs w≤charged w := by
    obtain ⟨p,q⟩ := E.effectDiagonalBounds wedges wedgesNodup effect w (memWedges w)
    change 0≤diag w at p; change diag w≤1 at q
    have bound := mul_le_mul_of_nonneg_right (tax w) (mul_nonneg p (sub_nonneg.mpr q))
    change costs w≤(if w=UpperFrameGain.entering then charge else 0)*(diag w*(1-diag w)) at bound
    by_cases eq : w=UpperFrameGain.entering
    · simp only [charged,ite_eq_left eq] at *
      exact le_trans bound (mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (diag w)]) charge0)
    · simpa only [charged,ite_eq_right eq,zero_mul] using bound
  have total := Compression.sumOverNonnegative wedges (fun w => charged w-costs w)
    (fun w _ => sub_nonneg.mpr (each w))
  rw [Compression.sumOverSub] at total
  have paid : sumOver wedges charged=charge*diag UpperFrameGain.entering := by
    have eq : charged=fun w => if w=UpperFrameGain.entering then charge*diag UpperFrameGain.entering else 0 := by
      funext w; by_cases h : w=UpperFrameGain.entering <;> simp [charged,h]
    rw [eq,atPoint wedges wedgesNodup,ite_eq_left (memWedges _)]
  rw [paid] at total
  have lowPay := mul_le_mul_of_nonneg_left low (sq_nonneg (pos (u-l)))
  change (pos (u-l))^2*s≤(pos (u-l))^2*L at lowPay
  have high : 0≤H := by
    unfold H cutCost
    apply add_nonneg
    · apply Compression.sumOverNonnegative
      intro i _
      cases v : i.level.high <;> simp [indicator,v,row i]
    · apply Compression.sumOverNonnegative
      intro i _
      apply Compression.sumOverNonnegative
      intro j _
      cases v : i.level.high <;> cases f : j.level.high <;> simp [crossing,indicator,v,f,E.massNonnegative i j]
  have add := mul_nonneg (sq_nonneg (pos (j-h))) high
  change (pos (u-l))^2*s-charge*diag UpperFrameGain.entering≤diagonalLoss wedges a diag-E.realQuadraticTrace wedges a
  linarith only [total,lowPay,add,crossed]

private theorem posMul (a b : ℝ) (p : 0≤a) : pos (a*b)=a*pos b := by
  rw [posMax,posMax,mul_max_of_nonneg _ _ p,mul_zero]

private theorem posGap (a b : ℝ) : LowerCorner.gap a b=(pos (a-b))^2 := by
  change UpperPrices.positivePart (a-b)*UpperPrices.positivePart (a-b)=(pos (a-b))^2
  unfold pos UpperPrices.positivePart
  split <;> ring

/-- The literal two reported lower radicand widths equal the full
shared-interval squared width, including a vanishing width. -/
theorem rootWidth {z y x b c : ℝ} (roots : LowerCorner.Roots z y x b)
    (cb : 1≤c ∧ c≤b) :
    let α := 1+(z+y+x); let β := 1+(y+x); let γ := 1+x
    let cc := c/b; let d := 1/b
    let l := Real.sqrt (cc*max α (β*γ)); let u := Real.sqrt (α*γ*cc*d)
    b^2*(pos (u-l))^2=c*min (α*LowerCorner.gap roots.gamma roots.fifth)
      (γ*LowerCorner.gap roots.alpha roots.betaFifth) := by
  let α := 1+(z+y+x); let β := 1+(y+x); let γ := 1+x
  let A := roots.alpha; let G := roots.gamma; let F := roots.fifth; let B := roots.betaFifth
  let C := Real.sqrt c
  have bp : 0<b := by linarith [cb.1,cb.2]
  have c0 : 0≤c := by linarith [cb.1]
  have C0 : 0≤C := Real.sqrt_nonneg _
  have C2 : C^2=c := Real.sq_sqrt c0
  have A0 : 0≤A := roots.alphaNonnegative
  have G0 : 0≤G := roots.gammaNonnegative
  have F0 : 0≤F := roots.fifthNonnegative
  have B0 : 0≤B := roots.betaFifthNonnegative
  have A2 : A^2=α := by simpa only [pow_two] using roots.alphaSq
  have G2 : G^2=γ := by simpa only [pow_two] using roots.gammaSq
  have F2 : F^2=b := by simpa only [pow_two] using roots.fifthSq
  have B2 : B^2=b*β := by simpa only [pow_two] using roots.betaFifthSq
  have ul : Real.sqrt (α*γ*(c/b)*(1/b))=(C/b)*(A*G) := by
    apply sqrtSq (by positivity)
    rw [mul_pow,div_pow,mul_pow,C2,A2,G2]; field_simp
  have candidates : (Real.sqrt ((c/b)*α)=(C/b)*(A*F)) ∧
      (Real.sqrt ((c/b)*(β*γ))=(C/b)*(G*B)) := by
    constructor
    · apply sqrtSq (by positivity)
      rw [mul_pow,div_pow,mul_pow,C2,A2,F2]; field_simp
    · apply sqrtSq (by positivity)
      rw [mul_pow,div_pow,mul_pow,C2,G2,B2]; field_simp
  have cbl : 0≤c/b := by positivity
  have lo : Real.sqrt ((c/b)*max α (β*γ))=max (C/b*(A*F)) (C/b*(G*B)) := by
    rw [←candidates.1,←candidates.2,mul_max_of_nonneg _ _ cbl]
    rcases le_total ((c/b)*α) ((c/b)*(β*γ)) with h|h
    · rw [max_eq_right h,max_eq_right (Real.sqrt_le_sqrt h)]
    · rw [max_eq_left h,max_eq_left (Real.sqrt_le_sqrt h)]
  have gapA : b^2*(pos (C/b*(A*G)-C/b*(A*F)))^2=c*(α*LowerCorner.gap G F) := by
    rw [show C/b*(A*G)-C/b*(A*F)=(C/b*A)*(G-F) by ring,posMul _ _ (by positivity),posGap]
    rw [←C2,←A2]; field_simp
  have gapG : b^2*(pos (C/b*(A*G)-C/b*(G*B)))^2=c*(γ*LowerCorner.gap A B) := by
    rw [show C/b*(A*G)-C/b*(G*B)=(C/b*G)*(A-B) by ring,posMul _ _ (by positivity),posGap]
    rw [←C2,←G2]; field_simp
  have monotone (a e t : ℝ) (le : a≤e) : (pos (t-e))^2≤(pos (t-a))^2 := by
    rw [posMax,posMax]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 (sub_le_sub_left le t)) 2
  change b^2*(pos (Real.sqrt (α*γ*(c/b)*(1/b))-Real.sqrt ((c/b)*max α (β*γ))))^2=c*min (α*LowerCorner.gap G F) (γ*LowerCorner.gap A B)
  rw [ul,lo,mul_min_of_nonneg _ _ c0,←gapA,←gapG]
  rcases le_total (C/b*(A*F)) (C/b*(G*B)) with h|h
  · rw [max_eq_right h,min_eq_right (mul_le_mul_of_nonneg_left (monotone _ _ _ h) (sq_nonneg b))]
  · rw [max_eq_left h,min_eq_left (mul_le_mul_of_nonneg_left (monotone _ _ _ h) (sq_nonneg b))]

theorem actualShared (half : ℝ) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤UpperFrameTrace.sharedExcess (PackingPolynomial.physicalWeights half unit k A))
    (v0 : 0≤UpperFrameTrace.highExcess (PackingPolynomial.physicalWeights half unit k A))
    (z y x b c : ℝ) (roots : LowerCorner.Roots z y x b) (cb : 1≤c ∧ c≤b)
    (z0 : 0≤z) (y0 : 0≤y) (x0 : 0≤x) :
    let α := 1+(z+y+x); let β := 1+(y+x); let γ := 1+x
    let V := min (α*LowerCorner.gap roots.gamma roots.fifth) (γ*LowerCorner.gap roots.alpha roots.betaFifth)
    let diag := PackingPolynomial.physicalWeights half unit k A
    let s := UpperFrameTrace.sharedFraction diag
    let E := PhysicalCompressionEffect.physicalEntries half unit k A
    c*V*(s*(1-s))-γ*z*(b-c)/2*diag UpperFrameGain.entering≤
      b^2*SectorDefectAccounting.compressionLoss (amplitude (fun i => Real.sqrt (weights α β γ (c/b) (1/b) i))) E := by
  let α := 1+(z+y+x); let β := 1+(y+x); let γ := 1+x
  let V := min (α*LowerCorner.gap roots.gamma roots.fifth) (γ*LowerCorner.gap roots.alpha roots.betaFifth)
  let E := PhysicalCompressionEffect.physicalEntries half unit k A
  let diag := PackingPolynomial.physicalWeights half unit k A
  let s := UpperFrameTrace.sharedFraction diag
  let T := s*(1-s)
  have traces := RealUpperCutPrice.actualTracePrices half unit k A orth n0 v0
  have ⟨d0,dc,c1⟩ := LowerExteriorScale.orderedRatios b c cb
  have bounds := fullWidth E (PhysicalCompressionEffect.rankSevenPhysicalEffect half unit k A orth) half T α β γ (c/b) (1/b)
    unit traces.1 (by dsimp [γ]; linarith) (by dsimp [β,γ]; linarith) (by dsimp [α,β]; linarith) d0 dc c1
  let l := Real.sqrt ((c/b)*max α (β*γ)); let u := Real.sqrt (α*γ*(c/b)*(1/b))
  let D := SectorDefectAccounting.compressionLoss (amplitude (fun i => Real.sqrt (weights α β γ (c/b) (1/b) i))) E
  change (pos (u-l))^2*T-γ*(α-β)*(1/b)*(1-c/b)/2*diag UpperFrameGain.entering≤D at bounds
  have width := rootWidth roots cb
  change b^2*(pos (u-l))^2=c*V at width
  have bp : 0<b := by linarith only [cb.1,cb.2]
  have cross : b^2*(γ*(α-β)*(1/b)*(1-c/b)/2)=γ*z*(b-c)/2 := by
    dsimp only [α,β]; field_simp; ring
  have pay := mul_le_mul_of_nonneg_left bounds (sq_nonneg b)
  change c*V*T-γ*z*(b-c)/2*diag UpperFrameGain.entering≤b^2*D
  rw [← width,← cross]; linarith only [pay]

end RankSeven.RealLowerCutPrice
#print axioms RankSeven.RealLowerCutPrice.fullWidth
#print axioms RankSeven.RealLowerCutPrice.rootWidth
#print axioms RankSeven.RealLowerCutPrice.actualShared