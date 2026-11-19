import Rank7UpperCoveredTree
import Rank7UpperPairCap

namespace RankSeven.UpperCoveredFrame

open Lean.Grind Interval UpperContractor UpperCorner UpperReplay
open UpperPhysicalInterior UpperPhysicalReplay UpperFrameTrace UpperFrameGain
open UpperEndpoint UpperEndpointPrices UpperCoveredTree

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem bandWitness {b : TailBox} {ids : List Nat} {h k q c d : R} (n : Nat)
    (res : Residual h k q c d) (valid : Valid cppGrid b)
    (domain : TailRectangle b) (inside : Inside cppGrid b h k q c d)
    (pass : CollarBatch.Bands.check n b ids=true) :
    ∃ z, TailRectangle z ∧ Inside cppGrid z h k q c d ∧ Witnesses z := by
  induction n generalizing b with
  | zero =>
    obtain ⟨z, contracted, contain⟩ := contractPreserves res valid inside
    change CollarBatch.batchCheck b ids=true at pass
    rw [CollarBatch.batchCheck, contracted] at pass
    have zDomain := contractRectangle domain contracted
    exact ⟨CollarBatch.collar cppGrid z, zDomain,
      CollarBatch.collarContains (Std.le_of_lt res.nearCut) contain,
      acceptedCornersWitness (HintReplay.hintedCornersSound _ _ pass)⟩
  | succ n ih =>
    change (CollarBatch.Bands.check n (CollarBatch.Bands.left b) ids &&
      CollarBatch.Bands.check n (CollarBatch.Bands.right b) ids)=true at pass
    obtain ⟨lp,rp⟩ := Bool.and_eq_true_iff.mp pass
    rcases CollarBatch.Bands.covered inside with il|ir
    · exact ih (b := CollarBatch.Bands.left b)
        ⟨valid.cLowerPositive,valid.hLowerPositive,valid.qLowerPositive,
        Int.le_trans (Int.min_le_left _ _) valid.dUpperUnit⟩ domain il lp
    · have endpoints := noEmpty inside.dInside
      have lo : b.d.lo≤CollarBatch.Bands.midpoint b := by
        unfold CollarBatch.Bands.midpoint
        rw [Int.min_def]
        split <;> omega
      exact ih (b := CollarBatch.Bands.right b)
        ⟨valid.cLowerPositive,valid.hLowerPositive,valid.qLowerPositive,valid.dUpperUnit⟩
        ⟨Int.le_trans domain.1 lo,domain.2⟩ ir rp

theorem childRectangles {b l r : TailBox} (valid : Valid cppGrid b)
    (domain : TailRectangle b) (children : HintShards.children b=some (l,r)) :
    TailRectangle l ∧ TailRectangle r := by
  unfold HintShards.children at children
  cases hc : contract cppGrid b with
  | none =>
    have absent : verifier.contract (TailBox.toBox b)=none := by simp [verifier,fromToBox,hc]
    simp [absent] at children
  | some z =>
    have present : verifier.contract (TailBox.toBox b)=some (TailBox.toBox z) := by
      simp [verifier,fromToBox,hc]
    simp only [present] at children
    cases sp : (TailBox.toBox z).trySplit (verifier.axis (TailBox.toBox z)) with
    | none => simp [sp] at children
    | some pair =>
      obtain ⟨left,right⟩ := pair
      have same : (fromBox left,fromBox right)=(l,r) := by simpa [sp] using children
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      have vz : Valid cppGrid (fromBox (TailBox.toBox z)) :=
        (fromToBox z).symm ▸ contractValid valid hc
      have dz : TailRectangle (fromBox (TailBox.toBox z)) :=
        (fromToBox z).symm ▸ contractRectangle domain hc
      obtain ⟨leftProp,rightProp⟩ := childDomain vz dz sp
      exact ⟨leftProp.2,rightProp.2⟩

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem toCoordinates {x : Fin 5 → R} {b : TailBox}
    (inside : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4)) :
    (TailBox.toBox b).Contains cppGrid x := by
  intro i
  have cases : ∀ j : Fin 5,j=0∨j=1∨j=2∨j=3∨j=4 := by decide
  rcases cases i with rfl|rfl|rfl|rfl|rfl
  · exact inside.hInside
  · exact inside.kInside
  · exact inside.qInside
  · exact inside.cInside
  · exact inside.dInside

/-- Every accepted corner leaf, including a banded leaf, retains the tail
endpoints needed by the actual frame comparison. -/
theorem checkWithDomain (x : Fin 5 → R) (P : Prop)
    (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4))
    (old : UpperOldRegions.OldCondition (x 0) (x 1) (x 2) (x 3) (x 4) → P)
    (weighted : ∀ u : R, (u=1∨u=5/4∨u=3/2) →
      0<UpperWeighted.margin (x 0) (x 1) (x 2) (x 3) (x 4) u → P)
    (corner : ∀ region, TailRectangle region →
      Inside cppGrid region (x 0) (x 1) (x 2) (x 3) (x 4) → Witnesses region → P)
    (plan : Plan) (b : TailBox) (depth : Nat) (valid : Valid cppGrid b)
    (domain : TailRectangle b) (inside : Inside cppGrid b (x 0) (x 1) (x 2) (x 3) (x 4))
    (pass : check plan b depth=true) : P := by
  induction plan generalizing b depth with
  | ordinary fuel hint =>
    obtain ⟨z,lvl,dz,iz,ready⟩ := coveringLeaf x res fuel depth (TailBox.toBox b)
      ((fromToBox b).symm ▸ valid) ((fromToBox b).symm ▸ domain)
      (toCoordinates inside) (HintReplay.checkSound _ _ _ hint pass)
    unfold UpperReplay.compare at ready
    split at ready
    · exact old (UpperOldRegions.acceptedOldCondition iz ‹_›)
    · split at ready
      · obtain ⟨u, h, pos⟩ := UpperWeighted.acceptedMargin iz ‹_›
        exact weighted u h pos
      · split at ready
        · rename_i corners
          exact corner z dz iz (acceptedCornersWitness (Bool.and_eq_true_iff.mp corners).2)
        · exact False.elim (ready rfl)
  | bands n ids =>
    obtain ⟨z,dz,iz,rows⟩ := bandWitness n res valid domain inside pass
    exact corner z dz iz rows
  | split lp rp leftIH rightIH =>
    unfold check at pass
    cases eq : HintShards.children b with
    | none => simp [eq] at pass
    | some pair =>
      obtain ⟨left,right⟩ := pair
      simp only [eq,Bool.and_eq_true] at pass
      obtain ⟨ld,rd⟩ := childRectangles valid domain eq
      rcases childrenCover res valid inside eq with ⟨v,i⟩|⟨v,i⟩
      · exact leftIH _ _ v ld i pass.1
      · exact rightIH _ _ v rd i pass.2

open PackingPolynomial (physicalWeights)

/-- Mixed scalar certificates reach the physical-frame comparison with the
sharp pair cap supplied by the orthonormal frame. -/
theorem actualFrameCovered (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A))
    (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (exterior : ∀ region, Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) → TailRectangle region →
      ∀ f u w : R, ShiftValues f u w →
      ExteriorEstimates (realInputs region (z 0) (z 1) (z 2) f u w) (physicalWeights half unit k A)
        (sharedExcess (physicalWeights half unit k A)) (highExcess (physicalWeights half unit k A)))
    (plan : Plan) (b : TailBox) (depth : Nat) (valid : Valid cppGrid b) (domain : TailRectangle b)
    (inside : Inside cppGrid b (z 0) (z 1) (z 2) (z 3) (z 4)) (pass : check plan b depth=true) :
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
        physicalPrice p wh ws (z 3) (z 4) (trueRay n v (v*(1-v)) (sf*(1-sf))) := by
  refine checkWithDomain z _ res Or.inl (fun u hu hp => Or.inr (Or.inl ⟨u,hu,hp⟩))
    ?_ plan b depth valid domain inside pass
  intro region rDomain rInside witness
  exact Or.inr (Or.inr ⟨region,rDomain,rInside,
    actualFrameInterior half unit k A orth rInside rDomain witness
      res.hNonnegative res.kNonnegative res.qNonnegative n0 v0 positive
      (UpperPairCap.physicalPairCap half unit k A orth) (exterior region rInside rDomain)⟩)

end RankSeven.UpperCoveredFrame

#print axioms RankSeven.UpperCoveredFrame.checkWithDomain
#print axioms RankSeven.UpperCoveredFrame.actualFrameCovered
