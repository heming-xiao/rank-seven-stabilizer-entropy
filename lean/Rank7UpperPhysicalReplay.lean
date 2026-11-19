import Rank7UpperPhysicalInterior

/-! Tail endpoints of the initial slab retain their physical domain at every
accepted shared leaf, including after contraction and splitting. -/
namespace RankSeven.UpperPhysicalReplay
open Lean.Grind Interval UpperCorner UpperContractor UpperReplay UpperPhysicalInterior UpperEndpoint UpperEndpointPrices UpperFrameGain
open ExteriorCuts (Wedge7)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem initialRectangle (lo hi : Int) (nonnegative : 0≤lo) : TailRectangle (initialBox lo hi) :=
  ⟨nonnegative,Int.min_le_right _ _⟩

private theorem tailPreserved {g : Grid} {a b : TailBox} (pass : contract g a=some b) :
    b.c=a.c ∧ b.d=a.d := by
  unfold contract at pass; dsimp only at pass; split at pass
  · contradiction
  · split at pass
    · contradiction
    · obtain rfl := (Option.some.inj pass).symm; exact ⟨rfl,rfl⟩

theorem contractRectangle {g : Grid} {a b : TailBox} (dom : TailRectangle a)
    (pass : contract g a=some b) : TailRectangle b := by
  have tails := tailPreserved pass
  exact ⟨tails.2 ▸ dom.1,tails.1 ▸ dom.2⟩

theorem childDomain {b l r : Box 5} {i} (ok : Valid cppGrid (fromBox b)) (dom : TailRectangle (fromBox b))
    (cut : b.trySplit i=some (l,r)) :
    (Valid cppGrid (fromBox l) ∧ TailRectangle (fromBox l)) ∧ (Valid cppGrid (fromBox r) ∧ TailRectangle (fromBox r)) := by
  have c := splitLimits cut 3; have d := splitLimits cut 4
  have h := splitLimits cut 0; have q := splitLimits cut 2
  exact ⟨⟨validSubbox ok c.1 h.1 q.1 d.2.1,Std.le_trans dom.1 d.1,Std.le_trans c.2.1 dom.2⟩,
    ⟨validSubbox ok c.2.2.1 h.2.2.1 q.2.2.1 d.2.2.2,Std.le_trans dom.1 d.2.2.1,Std.le_trans c.2.2.2 dom.2⟩⟩

/-- A successful replay contains the fixed point in one accepted leaf of
the original traversal, and that leaf retains physical tail endpoints. -/
theorem coveringLeaf (x : Fin 5→R) (res : Residual (x 0) (x 1) (x 2) (x 3) (x 4))
    (fuel depth : Nat) (box : Box 5) (ok : Valid cppGrid (fromBox box)) (dom : TailRectangle (fromBox box))
    (inside : box.Contains cppGrid x) (success : verifier.replay fuel depth box=true) :
    ∃ z e,TailRectangle z ∧ Inside cppGrid z (x 0) (x 1) (x 2) (x 3) (x 4) ∧ compare e z ≠ .unresolved := by
  induction fuel generalizing depth box with
  | zero => simp [BoxVerifier.replay] at success
  | succ fuel ih =>
    have here : Inside cppGrid (fromBox box) (x 0) (x 1) (x 2) (x 3) (x 4) :=
      ⟨inside 0,inside 1,inside 2,inside 3,inside 4⟩
    obtain ⟨z,hz,zi⟩ := contractPreserves res ok here
    have zd := contractRectangle dom hz
    have narrowed : verifier.contract box=some (TailBox.toBox z) := by simp [verifier,hz]
    rw [BoxVerifier.replay,narrowed] at success
    cases ready : verifier.accept depth (TailBox.toBox z) with
    | true => exact ⟨z,depth,zd,zi,by simpa [verifier,fromToBox] using ready⟩
    | false =>
      simp only [ready,Bool.false_eq_true,ite_false] at success
      have valid : Valid cppGrid (fromBox (TailBox.toBox z)) := (fromToBox z).symm ▸ contractValid ok hz
      have d₀ : TailRectangle (fromBox (TailBox.toBox z)) := (fromToBox z).symm ▸ zd
      have inBox : (TailBox.toBox z).Contains cppGrid x := by
        intro i
        have cs : ∀ i : Fin 5,i=0∨i=1∨i=2∨i=3∨i=4 := by decide
        rcases cs i with rfl|rfl|rfl|rfl|rfl
        · exact zi.hInside
        · exact zi.kInside
        · exact zi.qInside
        · exact zi.cInside
        · exact zi.dInside
      cases cut : (TailBox.toBox z).trySplit (verifier.axis (TailBox.toBox z)) with
      | none => simp [cut] at success
      | some pair =>
        obtain ⟨l,r⟩ := pair
        simp only [cut,Bool.and_eq_true] at success
        obtain ⟨lh,rh⟩ := childDomain valid d₀ cut
        rcases Box.coverBySplit cut inBox with hl|hr
        · exact ih (depth+1) l lh.1 lh.2 hl success.1
        · exact ih (depth+1) r rh.1 rh.2 hr success.2

/-- Real-valued output of the shared branch in the actual replay, holding
the physical wedge weights fixed at the supplied complex frame. -/
theorem replayPhysicalInterior (z : Fin 5→R) (res : Residual (z 0) (z 1) (z 2) (z 3) (z 4))
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (n v t₁ tₛ : R) (n0 : 0≤n) (v0 : 0≤v) (pos : 0<n+v) (nc : 2*n≤1) (vc : 3*v≤1)
    (tOne : v*(1-v)≤t₁) (tShared : n*(1-n)≤tₛ)
    (exterior : ∀ box,Inside cppGrid box (z 0) (z 1) (z 2) (z 3) (z 4) → TailRectangle box →
      ∀ f u w : R,ShiftValues f u w → ExteriorEstimates (realInputs box (z 0) (z 1) (z 2) f u w)
        (PackingPolynomial.physicalWeights half unit k A) n v)
    (fuel depth : Nat) (box : Box 5) (ok : Valid cppGrid (fromBox box)) (dom : TailRectangle (fromBox box))
    (inside : box.Contains cppGrid z) (pass : verifier.replay fuel depth box=true) :
    UpperOldRegions.OldCondition (z 0) (z 1) (z 2) (z 3) (z 4) ∨
    (∃ u : R,(u=1∨u=5/4∨u=3/2) ∧ 0<UpperWeighted.margin (z 0) (z 1) (z 2) (z 3) (z 4) u) ∨
    ∃ region,TailRectangle region ∧ Inside cppGrid region (z 0) (z 1) (z 2) (z 3) (z 4) ∧ ∃ f u w wh ws : R,
      let p := realInputs region (z 0) (z 1) (z 2) f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧
      corrected (spectrum (z 0) (z 1) (z 2)) (PackingPolynomial.physicalWeights half unit k A)
        (P p).lambda (mu p) (cross p) (z 3) (z 4) < physicalPrice p wh ws (z 3) (z 4) (trueRay n v t₁ tₛ) := by
  obtain ⟨region,e,domain,zi,accepted⟩ := coveringLeaf z res fuel depth box ok dom inside pass
  unfold UpperReplay.compare at accepted; split at accepted
  · exact Or.inl (UpperOldRegions.acceptedOldCondition zi ‹_›)
  · split at accepted
    · exact Or.inr (Or.inl (UpperWeighted.acceptedMargin zi ‹_›))
    · split at accepted
      · rename_i corners
        have actual := acceptedCornersWitness (Bool.and_eq_true_iff.mp corners).2
        exact Or.inr (Or.inr ⟨region,domain,zi,frameInterior _ zi domain actual res.hNonnegative res.kNonnegative
          res.qNonnegative n0 v0 pos nc vc tOne tShared (exterior region zi domain)⟩)
      · exact False.elim (accepted rfl)

end RankSeven.UpperPhysicalReplay
#print axioms RankSeven.UpperPhysicalReplay.coveringLeaf
#print axioms RankSeven.UpperPhysicalReplay.replayPhysicalInterior
