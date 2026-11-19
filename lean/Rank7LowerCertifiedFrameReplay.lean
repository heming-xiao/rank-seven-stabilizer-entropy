import Rank7LowerAffinePayment

namespace RankSeven.LowerCertifiedFrameReplay
open Lean.Grind Interval UpperInterior UpperFrameTrace LowerContractor LowerCorner LowerSignedExterior LowerAffinePayment
open PackingPolynomial (physicalWeights)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def Witnesses (box : Region) : Prop := ∀ j : Fin 6,∃ s∈LowerCorner.shifts,∃ rows,
  LowerCorner.margins box s=some rows ∧ LowerCorner.sectorPass rows j.val=true

def Shared (z y x b c : R) (roots : Roots z y x b) (weights : ExteriorCuts.Wedge7→R) : Prop :=
  ∃ f u w : R,(f=0∨f=1/2∨f=1) ∧ (u=5/4∨u=3/2∨u=1∨u=3/4) ∧ (w=5/4∨w=3/2∨w=1∨w=7/4) ∧
    let p := realPrices z y x b f u w ((1+(z+y+x))*gap roots.gamma roots.fifth) ((1+x)*gap roots.alpha roots.betaFifth)
    let sf := sharedFraction weights
    let r := realRay (sharedExcess weights) (highExcess weights) (sf*(1-sf))
    gainAt z y x b c w p weights<physicalPayment b c (bonusSlope z x b f u) p r

theorem sharedInterior {box : Region} {z y x b : R} (c : R) (roots : Roots z y x b)
    (res : LowerContractor.Residual z y x b) (cb : 1≤c ∧ c≤b) (inside : Inside cppGrid box z y x b)
    (witness : Witnesses box)
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A)) :
    Shared z y x b c roots (physicalWeights half unit k A) := by
  let weights := physicalWeights half unit k A
  let n := sharedExcess weights
  let v := highExcess weights
  let sf := sharedFraction weights
  obtain ⟨j,a,e,ha,he,nz,nr,vr⟩ := UpperRayCones.cover n v n0 v0 positive
  let sector := sectorRay j a e
  obtain ⟨shift,sm,rows,computed,passed⟩ := witness j
  obtain ⟨f,u,w,fs,us,ws,hf,hu,hw⟩ := LowerCorner.shiftEnclosed (R:=R) shift sm
  let wa := (1+(z+y+x))*gap roots.gamma roots.fifth
  let wb := (1+x)*gap roots.alpha roots.betaFifth
  let p := realPrices z y x b f u w wa wb
  obtain ⟨nc,_,_,sc⟩ := physicalSharedTrace half unit k A orth n0
  have pair := UpperPairCap.physicalPairCap half unit k A orth
  have vc : 3*v≤1 := by change 3*(PackingPolynomial.link weights 0 1-2)≤1; change 3*PackingPolynomial.link weights 0 1≤7 at pair; grind only
  have size := (UpperRayCones.traceBounds j a e ha he (nr ▸ nc) (vr ▸ vc)).2
  change sector.traceShared≤sector.n*(1-sector.n) at size
  change sector.n=n at nr; change sector.v=v at vr
  rw [nr] at size
  have shared : sector.traceShared≤sf*(1-sf) := Std.le_trans size sc
  have cut : 0≤p.cut := actualCutNonnegative z y x b f u w roots res.zNonnegative res.yNonnegative res.xHead
  have b1 : 1≤b := Std.le_trans cb.1 cb.2
  refine ⟨f,u,w,fs,us,ws,?_⟩
  apply interpolate z y x b c f u w wa wb _ _ cb
  intro side
  obtain ⟨s,t,s0,t0,lo,hi⟩ := LowerCorner.acceptedRealSector inside roots hf hu hw computed j passed side
  have pos := LowerPhysicalRay.sectorPositive z y x b p j a e ha he nz side ⟨s,t,s0,t0,lo,hi⟩
  change 0<(realLeafPair z y x b p side (realRay sector.n sector.v sector.traceShared)).1 ∨
      0<(realLeafPair z y x b p side (realRay sector.n sector.v sector.traceShared)).2 at pos
  rw [nr,vr] at pos
  have bounds := physicalLeaf z y x b f u w wa wb sector.traceShared side half unit k A orth n0 v0 res b1 fs us ws
  let F := gainAt z y x b (endpoint b side) w p weights
  let small := realRay n v sector.traceShared
  let full := realRay n v (sf*(1-sf))
  change (realLeafPair z y x b p side small).1≤payment b p side small-F ∧
    (realLeafPair z y x b p side small).2≤payment b p side small-F at bounds
  have gain : F<payment b p side small := by
    rcases pos with h|h
    · change 0<(realLeafPair z y x b p side small).1 at h; grind only
    · change 0<(realLeafPair z y x b p side small).2 at h; grind only
  have ep : 0≤endpoint b side := by cases side <;> dsimp [endpoint] <;> have := OrderedRing.zero_lt_one (R:=R) <;> grind only
  have charge := OrderedRing.mul_le_mul_of_nonneg_left shared (OrderedRing.mul_nonneg ep cut)
  change F<payment b p side full
  apply Std.lt_of_lt_of_le gain
  change _+endpoint b side*p.cut*sector.traceShared≤_+endpoint b side*p.cut*(sf*(1-sf))
  have plus (a b c : R) (ord : a≤b) : c+a≤c+b := by grind only
  exact plus _ _ _ charge

def Outcome (z y x b c : R) (roots : Roots z y x b) (weights : ExteriorCuts.Wedge7→R) : Prop :=
  LowerLeaves.OldCondition z y x b ∨
    (∃ w : R,(w=5/4∨w=3/2∨w=1∨w=7/4) ∧ 0<LowerLeaves.weightedMargin z y x b w) ∨
    Shared z y x b c roots weights

theorem checkedSlab (slab : Fin 6) (t : Fin 4→R) (c : R) (roots : Roots (t 0) (t 1) (t 2) (t 3))
    (res : LowerContractor.Residual (t 0) (t 1) (t 2) (t 3)) (cb : 1≤c ∧ c≤t 3)
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (positive : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (inside : (LowerReplay.toBox (initial slab)).Contains cppGrid t) (success : LowerReplay.replay slab=true) :
    Outcome (t 0) (t 1) (t 2) (t 3) c roots (physicalWeights half unit k A) := by
  apply LowerReplay.replayRegion t _ res (fun h => Or.inl h) (fun w hw h => Or.inr (Or.inl ⟨w,hw,h⟩))
    (fun _ ins passed => Or.inr (Or.inr (sharedInterior c roots res cb ins passed half unit k A orth n0 v0 positive)))
    76 0 (LowerReplay.toBox (initial slab)) _ inside success
  rw [LowerReplay.fromToBox]; exact initialValid slab

end RankSeven.LowerCertifiedFrameReplay
#print axioms RankSeven.LowerCertifiedFrameReplay.sharedInterior
#print axioms RankSeven.LowerCertifiedFrameReplay.checkedSlab