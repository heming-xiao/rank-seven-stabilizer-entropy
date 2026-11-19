import Rank7RealCutSpectrum
import Rank7UpperFrameTrace
import Rank7UpperPairCap

namespace RankSeven.RealUpperCutPrice

open Pauli ExteriorCuts Compression CutTrace
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries rankSevenPhysicalEffect)
open PackingPolynomial (physicalWeights link)
open UpperFrameTrace (sharedCut sharedFraction sharedExcess highExcess traceOffsets)

private theorem traceDiagSum (entries : HermitianEntries Wedge7 ℝ)
    (xs : List Wedge7) (keep : Wedge7 → Bool) :
    (trace (xs.filter keep) (matrix entries)).re =
      sumOver xs (fun w => if keep w then entries.realPart w w else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : keep a <;>
      simp [trace, sumOver, h, ComplexScalar.re_add, matrix] at ih ⊢ <;>
      rw [ih]

private theorem lowLabels (w : Wedge7) :
    w.level.low = (PackingDual.occupied w 0 && (PackingDual.occupied w 1 || PackingDual.occupied w 2)) :=
  (show ∀ z ∈ wedges, z.level.low =
      (PackingDual.occupied z 0 && (PackingDual.occupied z 1 || PackingDual.occupied z 2)) by decide)
    w (memWedges w)

private theorem highLabels (w : Wedge7) :
    w.level.high = (PackingDual.occupied w 0 && PackingDual.occupied w 1) :=
  (show ∀ z ∈ wedges, z.level.high = (PackingDual.occupied z 0 && PackingDual.occupied z 1) by decide)
    w (memWedges w)

private theorem entryTraceOffsets (E : HermitianEntries Wedge7 ℝ) :
    let x := fun w : Wedge7 => E.realPart w w
    (trace (wedges.filter (fun w => w.level.low)) (matrix E)).re = 3 + sharedFraction x ∧
      (trace (wedges.filter (fun w => w.level.high)) (matrix E)).re = 2 + highExcess x := by
  let x := fun w : Wedge7 => E.realPart w w
  constructor
  · calc
      _ = sumOver wedges (fun w => if w.level.low then x w else 0) :=
        traceDiagSum E wedges (fun w => w.level.low)
      _ = sharedCut x := sumOverCongr wedges (fun w => by rw [lowLabels])
      _ = _ := (traceOffsets x).2
  · calc
      _ = sumOver wedges (fun w => if w.level.high then x w else 0) :=
        traceDiagSum E wedges (fun w => w.level.high)
      _ = link x 0 1 := sumOverCongr wedges (fun w => by rw [highLabels])
      _ = _ := (traceOffsets x).1

private theorem pricesOfEffect (E : HermitianEntries Wedge7 ℝ) (effect : E.IsCoordinateEffect wedges)
    (s v : ℝ) (s0 : 0 ≤ s) (s1 : s ≤ 1) (v0 : 0 ≤ v) (v1 : v < 1)
    (shared : (trace (wedges.filter (fun w => w.level.low)) (matrix E)).re = 3+s)
    (highest : (trace (wedges.filter (fun w => w.level.high)) (matrix E)).re = 2+v) :
    let slack := rowSlack wedges (fun w => E.realPart w w) E.mass
    s*(1-s)≤cutCost wedges (fun w => w.level.low) slack E.mass ∧
      v*(1-v)≤cutCost wedges (fun w => w.level.high) slack E.mass := by
  have highPrice := RealCutSpectrum.cutCostLower E wedges wedgesNodup
    (fun w => w.level.high) effect 2 v v0 v1 highest
  refine ⟨?_, highPrice⟩
  by_cases strict : s < 1
  · exact RealCutSpectrum.cutCostLower E wedges wedgesNodup (fun w => w.level.low)
      effect 3 s s0 strict shared
  · have one : s=1 := le_antisymm s1 (le_of_not_gt strict)
    have whole : (trace (wedges.filter (fun w => w.level.low)) (matrix E)).re = (4:ℕ) + (0:ℝ) := by
      rw [shared, one]
      norm_num
    have price := RealCutSpectrum.cutCostLower E wedges wedgesNodup (fun w => w.level.low)
      effect 4 0 (by norm_num) (by norm_num) whole
    simpa only [one, sub_self, mul_zero, zero_mul] using price

private theorem excessRange (x : ℝ) (h : 3*x≤7) : x-2 < 1 := by linarith only [h]

private theorem pricesFromPacking (E : HermitianEntries Wedge7 ℝ) (effect : E.IsCoordinateEffect wedges)
    (sharedRange :
      let x := fun w : Wedge7 => E.realPart w w
      2*sharedExcess x≤1 ∧ 0≤sharedFraction x ∧ sharedFraction x≤1 ∧
      sharedExcess x*(1-sharedExcess x)≤sharedFraction x*(1-sharedFraction x))
    (cap : 3*link (fun w => E.realPart w w) 0 1≤7)
    (v0 : 0≤highExcess (fun w => E.realPart w w)) :
    let x := fun w : Wedge7 => E.realPart w w
    let slack := rowSlack wedges x E.mass
    let s := sharedFraction x
    let v := highExcess x
    s*(1-s)≤cutCost wedges (fun w => w.level.low) slack E.mass ∧
      v*(1-v)≤cutCost wedges (fun w => w.level.high) slack E.mass := by
  let x := fun w : Wedge7 => E.realPart w w
  have offsets := entryTraceOffsets E
  exact pricesOfEffect E effect (sharedFraction x) (highExcess x)
    sharedRange.2.1 sharedRange.2.2.1 v0 (excessRange _ cap) offsets.1 offsets.2

set_option maxHeartbeats 750000 in
set_option linter.constructorNameAsVariable false in
/-- The actual nested rank-seven cuts pay their fractional trace prices.
The upper endpoints come from the physical packing and pair bounds. -/
theorem actualTracePrices (half : ℝ) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar ℝ) (orth : OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A))
    (v0 : 0≤highExcess (physicalWeights half unit k A)) :
    let E := physicalEntries half unit k A
    let x := fun w : Wedge7 => E.realPart w w
    let slack := rowSlack wedges x E.mass
    let s := sharedFraction x
    let v := highExcess x
    s*(1-s)≤cutCost wedges (fun w => w.level.low) slack E.mass ∧
      v*(1-v)≤cutCost wedges (fun w => w.level.high) slack E.mass :=
  pricesFromPacking (physicalEntries half unit k A)
    (rankSevenPhysicalEffect half unit k A orth)
    (UpperFrameTrace.physicalSharedTrace half unit k A orth n0)
    (UpperPairCap.physicalPairCap half unit k A orth) v0

/-- The linear support price uses squared endpoints and is bounded by the
squared positive amplitude width, including when the interval is inactive. -/
theorem supportLeWidth (lo up weight : ℝ) (hl : 0≤lo) (hu : 0≤up) (hw : 0≤weight) :
    UpperPrices.supportValue (up^2) (lo^2) weight ≤ (pos (up-lo))^2 := by
  by_cases active : lo≤up
  · rw [pos, ite_eq_left (sub_nonneg.mpr active)]
    unfold UpperPrices.supportValue
    nlinarith [sq_nonneg (up-lo-weight*up), sq_nonneg (up-lo-weight*lo)]
  · have gap : up^2-lo^2≤0 := by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge active)) (add_nonneg hu hl)]
    rw [pos, ite_eq_right (show ¬ 0≤up-lo by exact fun h => active (sub_nonneg.mp h))]
    unfold UpperPrices.supportValue
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hw gap,
      mul_nonneg (sq_nonneg weight) (add_nonneg (sq_nonneg up) (sq_nonneg lo))]

/-- Both nonnegative-coefficient support prices can be charged to the
same compression loss, with the nominal outside tax recorded once. -/
theorem supportedCompression (E : HermitianEntries Wedge7 ℝ) (effect : E.IsCoordinateEffect wedges)
    (half s v : ℝ) (unit : 2*half=1) (s0 : 0≤s) (v0 : 0≤v)
    (lowPrice : s≤cutCost wedges (fun w => w.level.low)
      (rowSlack wedges (fun w => E.realPart w w) E.mass) E.mass)
    (highPrice : v≤cutCost wedges (fun w => w.level.high)
      (rowSlack wedges (fun w => E.realPart w w) E.mass) E.mass)
    (a : Wedge7 → ℝ) (loS upS loH upH ws wh : ℝ)
    (ls : 0≤loS) (us : 0≤upS) (lh : 0≤loH) (uh : 0≤upH)
    (separate : upS≤loH) (inside : ∀ w, insideBounds w.level upS upH (a w))
    (ws0 : 0≤ws) (wh0 : 0≤wh) :
    UpperPrices.supportValue (upS^2) (loS^2) ws * s +
      UpperPrices.supportValue (upH^2) (loH^2) wh * v -
      sumOver wedges (fun w => outsideTax loS upS loH upH (a w) w.level *
        (E.realPart w w*(1-E.realPart w w))) ≤ SectorDefectAccounting.compressionLoss a E := by
  classical
  let x := fun w : Wedge7 => E.realPart w w
  let slack := rowSlack wedges x E.mass
  have row : ∀ w, 0≤slack w := E.effectRowSlack wedges wedgesNodup memWedges effect
  have crossed := ExteriorCuts.crossedCuts wedges Wedge7.level a slack x E.mass
    loS upS loH upH half unit ls lh separate inside row E.massNonnegative E.massSymmetric
    (fun w => E.rowCap wedges wedgesNodup w (memWedges w) (row w))
  change _≤diagonalLoss wedges a slack + half*squaredGapCost wedges a E.mass at crossed
  have loss : diagonalLoss wedges a slack + half*squaredGapCost wedges a E.mass =
      diagonalLoss wedges a x-E.realQuadraticTrace wedges a :=
    E.realLossEqHalf wedges a half unit
  rw [loss] at crossed
  have hs := le_trans
    (mul_le_mul_of_nonneg_right (supportLeWidth loS upS ws ls us ws0) s0)
    (mul_le_mul_of_nonneg_left lowPrice (sq_nonneg (pos (upS-loS))))
  have hv := le_trans
    (mul_le_mul_of_nonneg_right (supportLeWidth loH upH wh lh uh wh0) v0)
    (mul_le_mul_of_nonneg_left highPrice (sq_nonneg (pos (upH-loH))))
  exact le_trans (sub_le_sub_right (add_le_add hs hv) _) crossed

end RankSeven.RealUpperCutPrice

#print axioms RankSeven.RealUpperCutPrice.actualTracePrices
#print axioms RankSeven.RealUpperCutPrice.supportedCompression

