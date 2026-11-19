import Rank7UpperDomainFrontier

namespace RankSeven.DomainFrontierFrame
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner
open UpperPhysicalInterior UpperPhysicalReplay UpperFrameTrace UpperFrameGain
open UpperEndpoint UpperEndpointPrices UpperDomainFrontier
open PackingPolynomial (physicalWeights)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def FrameOutcome (z : Fin 5→R) (half : R) (unit : 2*half=1) (k : Nat)
    (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R) : Prop :=
    let x := physicalWeights half unit k A
    let n := sharedExcess x
    let v := highExcess x
    let sf := sharedFraction x
    UpperOldRegions.OldCondition (z 0) (z 1) (z 2) (z 3) (z 4) ∨
    (∃ u : R, (u=1∨u=5/4∨u=3/2) ∧ 0<UpperWeighted.margin (z 0) (z 1) (z 2) (z 3) (z 4) u) ∨
    ∃ region, TailRectangle region ∧ Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) ∧
      ∃ f u w wh ws : R, let p := realInputs region (z 0) (z 1) (z 2) f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧
      corrected (spectrum (z 0) (z 1) (z 2)) x (P p).lambda (mu p) (cross p) (z 3) (z 4) <
        physicalPrice p wh ws (z 3) (z 4) (trueRay n v (v*(1-v)) (sf*(1-sf)))

theorem frameOrFrontier (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A))
    (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (exterior : ∀ region, Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) → TailRectangle region →
      ∀ f u w : R, ShiftValues f u w →
      ExteriorEstimates (realInputs region (z 0) (z 1) (z 2) f u w) (physicalWeights half unit k A)
        (sharedExcess (physicalWeights half unit k A)) (highExcess (physicalWeights half unit k A)))
    {root : TailBox} {front : List TailBox}
    (cert : Accounts R root front) (v : Valid cppGrid root) (d : TailRectangle root)
    (inside : Here root z) : FrameOutcome z half unit k A ∨ OpenPoint front z := by
  rcases cert z res v d inside with resolved|openCase
  · apply Or.inl
    rcases resolved with old|weighted|⟨region,rDomain,rInside,witness⟩
    · exact Or.inl old
    · exact Or.inr (Or.inl weighted)
    · exact Or.inr (Or.inr ⟨region,rDomain,rInside,
    actualFrameInterior half unit k A orth rInside rDomain witness
      res.hNonnegative res.kNonnegative res.qNonnegative n0 v0 positive
      (UpperPairCap.physicalPairCap half unit k A orth) (exterior region rInside rDomain)⟩)
  · exact Or.inr openCase
end RankSeven.DomainFrontierFrame
#print axioms RankSeven.DomainFrontierFrame.frameOrFrontier
