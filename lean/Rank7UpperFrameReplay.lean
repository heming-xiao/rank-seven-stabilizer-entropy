import Rank7UpperFrameTrace

/-! Direct replay conclusion in the physical frame link coordinates. -/
namespace RankSeven.UpperFrameReplay
open Lean.Grind Interval UpperEndpoint UpperEndpointPrices UpperFrameGain UpperPhysicalInterior UpperFrameTrace UpperReplay UpperContractor
open PackingPolynomial (physicalWeights link)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem actualFrameReplay (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (pairCap : 3*link (physicalWeights half unit k A) 0 1≤7)
    (exterior : ∀ region,Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) → TailRectangle region →
      ∀ f u w : R,ShiftValues f u w →
      ExteriorEstimates (realInputs region (z 0) (z 1) (z 2) f u w) (physicalWeights half unit k A)
        (sharedExcess (physicalWeights half unit k A)) (highExcess (physicalWeights half unit k A)))
    (fuel depth : Nat) (box : Box 5) (valid : Valid cppGrid (fromBox box)) (domain : TailRectangle (fromBox box))
    (inside : box.Contains cppGrid z) (success : verifier.replay fuel depth box=true) :
    let x := physicalWeights half unit k A
    let n := sharedExcess x
    let v := highExcess x
    let sf := sharedFraction x
    UpperOldRegions.OldCondition (z 0) (z 1) (z 2) (z 3) (z 4) ∨
    (∃ u : R,(u=1∨u=5/4∨u=3/2) ∧ 0<UpperWeighted.margin (z 0) (z 1) (z 2) (z 3) (z 4) u) ∨
    ∃ region,TailRectangle region ∧ Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) ∧ ∃ f u w wh ws : R,
      let p := realInputs region (z 0) (z 1) (z 2) f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧
      corrected (spectrum (z 0) (z 1) (z 2)) x (P p).lambda (mu p) (cross p) (z 3) (z 4) <
        physicalPrice p wh ws (z 3) (z 4) (trueRay n v (v*(1-v)) (sf*(1-sf))) := by
  obtain ⟨cap,_,_,shared⟩ := physicalSharedTrace half unit k A orth n0
  have high : 3*highExcess (physicalWeights half unit k A)≤1 := by unfold highExcess; grind only
  exact UpperPhysicalReplay.replayPhysicalInterior z res half unit k A _ _ _ _ n0 v0 positive cap high
    (Std.le_refl _) shared exterior fuel depth box valid domain inside success

end RankSeven.UpperFrameReplay
#print axioms RankSeven.UpperFrameReplay.actualFrameReplay
