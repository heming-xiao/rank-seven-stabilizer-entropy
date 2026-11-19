import Rank7UpperCertifiedExterior

/-! The complete physical upper replay implication on the normalized upper slab. -/
namespace RankSeven.UpperCertifiedFrameReplay
open Lean.Grind Interval ExteriorCuts UpperEndpoint UpperEndpointPrices UpperFrameGain UpperPhysicalInterior UpperFrameTrace
open UpperReplay UpperContractor PackingPolynomial

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def Outcome (z : Fin 5→R) (x : Wedge7→R) : Prop :=
  let n := sharedExcess x
  let v := highExcess x
  let sf := sharedFraction x
  UpperOldRegions.OldCondition (z 0) (z 1) (z 2) (z 3) (z 4) ∨
    (∃ u : R,(u=1∨u=5/4∨u=3/2) ∧ 0<UpperWeighted.margin (z 0) (z 1) (z 2) (z 3) (z 4) u) ∨
    ∃ region,TailRectangle region ∧ Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) ∧ ∃ f u w wh ws : R,
      let p := realInputs region (z 0) (z 1) (z 2) f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧
      corrected (spectrum (z 0) (z 1) (z 2)) x (P p).lambda (mu p) (cross p) (z 3) (z 4) <
        physicalPrice p wh ws (z 3) (z 4) (trueRay n v (v*(1-v)) (sf*(1-sf)))

theorem frameReplay (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4)) (headFloor : 1≤2*z 2)
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (fuel depth : Nat) (box : Box 5) (valid : Valid cppGrid (fromBox box)) (domain : TailRectangle (fromBox box))
    (inside : box.Contains cppGrid z) (success : verifier.replay fuel depth box=true) :
    Outcome z (physicalWeights half unit k A) := by
  obtain ⟨nx,rows⟩ := physicalRows half unit k A orth
  exact UpperPairReplay.actualFrameReplay z res half unit k A orth n0 v0 positive
    (fun _ ins dom => UpperCertifiedExterior.exteriorEstimates res headFloor ins dom _ nx rows n0 v0)
    fuel depth box valid domain inside success

theorem initialHeadFloor {lo hi : Int} (z : Fin 5→R)
    (inside : (TailBox.toBox (initial lo hi)).Contains cppGrid z) : 1≤2*z 2 := by
  let b := Bounds.rational cppGrid (1:Int) 2
  have same : b.hi=b.lo := by decide
  have half := (insideEndpoints.mp (fractionSound (R:=R) cppGrid 1 2 (by decide))).2
  change (1:R)/2≤value cppGrid b.hi at half
  rw [same] at half
  have low : value cppGrid b.lo≤z 2 := (insideEndpoints.mp (inside 2)).1
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have h := UpperContractor.quotientEq (1:R) (show (0:R)<2 by grind only)
  grind only

/-- The physical proof consumes the executable Boolean of a single initial slab. -/
theorem checkedSlab (lo hi : Int) (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (low : 0<(Bounds.rational cppGrid lo 256).lo) (high : (Bounds.rational cppGrid hi 256).hi≤cppGrid.scale)
    (inside : (TailBox.toBox (initial lo hi)).Contains cppGrid z) (success : UpperReplay.replay lo hi=true) :
    Outcome z (physicalWeights half unit k A) := by
  apply frameReplay z res (initialHeadFloor z inside) half unit k A orth n0 v0 positive 73 0 (TailBox.toBox (initial lo hi))
  · rw [fromToBox]; exact initialValid _ _ low high
  · rw [fromToBox]; exact UpperPhysicalReplay.initialRectangle _ _ (Int.le_of_lt low)
  · exact inside
  · exact success

end RankSeven.UpperCertifiedFrameReplay
#print axioms RankSeven.UpperCertifiedFrameReplay.frameReplay
#print axioms RankSeven.UpperCertifiedFrameReplay.checkedSlab