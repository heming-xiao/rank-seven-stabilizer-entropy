import Rank7ReserveMixedNorm
import Rank7PackingDual

/-! Six-mode polarization, the disjoint rank-six reserve, and the
direct bound on the large shared-Gram branch. -/
namespace RankSeven.SixModeProbe
open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram PauliReserveSlots WeightedProbeShift
open ExteriorCuts (Wedge7 wedges)
open SectorDefectAccounting (wedgePairs)
open ProjectedProbeOverlap (weightedFourWedge complementaryPair complementaryWeight)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

def sixWedge {k : Nat} (half : R) (h2 : 2*half=1) (A : Basis (k+3) → Fin 7 → ComplexScalar R) :=
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  weightedFourWedge 0 1 (cut 5) (fun w => E.realPart w w)+weightedFourWedge 0 2 (cut 5) (fun w => E.realPart w w)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem sixScore {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    matchingScore A (cut 5) p=sixVertexMass A p := by
  let L := wedgePairs (List.finRange 7)
  let S := (List.finRange 7).filter (fun i => i.val<6)
  let sel (e : Fin 7×Fin 7) := decide (e.1≤5 ∧ e.2≤5)
  have eq : wedgePairs S=L.filter sel := by decide
  have filt (xs : List (Fin 7×Fin 7)) : sumOver (xs.filter sel) (fun e => pairWeight A p e.1 e.2)=
      sumOver xs (fun e => cut 5 e.1*cut 5 e.2*pairWeight A p e.1 e.2) := by
    induction xs with
    | nil => rfl
    | cons e xs ih =>
      rw [List.filter_cons]
      by_cases h : e.1≤5 <;> by_cases q : e.2≤5 <;> simp [sel,cut,h,q,sumOver] at ih ⊢ <;> grind only
  change sumOver L _=sumOver (wedgePairs S) _
  rw [eq]; exact (filt L).symm

theorem sixPolarization (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let M := physicalPayment half h2 k A mu
    let os := MixedDefect.oddWords (k+3)
    let Z := densityCoordinates half A (cut 5)
    2*hs os (sharedProbe half A) Z=2+sixWedge half h2 A-M.sixMass := by
  let n := k+3
  let os := MixedDefect.oddWords n
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W i := weightedFourWedge 0 i (cut 5) (fun w => E.realPart w w)
  let Z := densityCoordinates half A (cut 5)
  let U i := pairCoordinates half A 0 i
  let P i (p : Word n) := pairWeight A p 0 i
  let S := sixVertexMass A
  have sq : (fun i => (cut (R:=R) 5 i)^2)=cut 5 := by funext i; unfold cut; split <;> grind only
  have e (i : Fin 7) (hn : 0≠i) (hi : i≤5) :
      2*hs os (U i) Z=1+W i-oddAverage half (fun p => P i p*S p) := by
    have h := ProjectedProbeOverlap.pairPaymentIdentity half third h2 h3 k A (cut 5) orth 0 i hn
    dsimp only at h; rw [sq] at h
    have one (j : Fin 7) (hj : j≤5) : cut (R:=R) 5 j=1 := ite_eq_left hj
    rw [one 0 (by decide),one i hi] at h; simp only [sixScore,Semiring.one_pow] at h
    change _=1*1+W i-oddAverage half (fun p => P i p*S p) at h; rw [Semiring.one_mul] at h; exact h
  have shared : hs os (sharedProbe half A) Z=hs os (U 1) Z+hs os (U 2) Z := by
    unfold hs; simp only [sharedProbe,Semiring.right_distrib,sumOverAdd]; dsimp only [U]; grind only
  have av : oddAverage half (fun p => (P 1 p+P 2 p)*S p)=oddAverage half (fun p => P 1 p*S p)+oddAverage half (fun p => P 2 p*S p) := by
    unfold oddAverage; simp only [Semiring.right_distrib,sumOverAdd]; grind only
  have e1 := e 1 (by decide) (by decide); have e2 := e 2 (by decide) (by decide)
  change 2*hs os (sharedProbe half A) Z=2+(W 1+W 2)-oddAverage half (fun p => (P 1 p+P 2 p)*S p)
  rw [shared,av]; grind only

private def pairCount (i j u v y z : Fin 7) : Nat :=
  if ((u=i ∧ v=j) ∨ (u=j ∧ v=i)) ∧ y≤5 ∧ z≤5 then 1 else 0

private def compCount (i j : Fin 7) (w : Wedge7) :=
  pairCount i j w.i w.j w.k w.m+pairCount i j w.i w.k w.j w.m+
  pairCount i j w.i w.m w.j w.k+pairCount i j w.j w.k w.i w.m+
  pairCount i j w.j w.m w.i w.k+pairCount i j w.k w.m w.i w.j

private def directed (w : Wedge7) := (PackingDual.Row.directed 6 0).covers w
private def triple (w : Wedge7) := PhysicalCutCapacities.covers ((0,1),2) w

private theorem countTable : wedges.all (fun w =>
    decide (compCount 0 1 w+compCount 0 2 w≤(if directed w then 1 else 0)+(if triple w then 1 else 0)))=true := by decide

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem castCount (i j : Fin 7) (w : Wedge7) :
    complementaryWeight i j (cut (R:=R) 5) w=Nat.cast (compCount i j w) := by
  have one (u v y z : Fin 7) :
      complementaryPair i j u v (cut (R:=R) 5 y*cut 5 z)=Nat.cast (pairCount i j u v y z) := by
    by_cases h : (u=i ∧ v=j) ∨ (u=j ∧ v=i) <;> by_cases a : y≤5 <;> by_cases b : z≤5 <;>
      simp [complementaryPair,pairCount,h,a,b,cut] <;> grind only
  simp only [complementaryWeight,compCount,one,Semiring.natCast_add]

private theorem sumLe {α : Type} (xs : List α) (f g : α → R) (h : ∀ i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have e := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at e; grind only

/-- One directed wedge row and the always valid leading-triple row
suffice for the six-mode comparison W₆≤3. -/
theorem sixWedgeLeThree (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (row : PackingDual.rowMass (fun w => (PhysicalCompressionEffect.physicalEntries half h2 k A).realPart w w) (.directed 6 0)≤2) :
    sixWedge half h2 A≤3 := by
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let f := fun w => E.realPart w w
  have nx (w : Wedge7) : 0≤f w := (Compression.HermitianEntries.effectDiagonalBounds E wedges ExteriorCuts.wedgesNodup
    (PhysicalCompressionEffect.rankSevenPhysicalEffect half h2 k A orth) w (ExteriorCuts.memWedges w)).1
  have tri := PhysicalCutCapacities.physicalTripleCapacity half h2 k A orth 0 1 2 (by decide) (by decide)
  have mono {a b : Nat} (h : a≤b) : (Nat.cast a:R)≤Nat.cast b := by
    have q := Nat.add_sub_of_le h
    have non : (0:R)≤Nat.cast (b-a) := OrderedRing.natCast_nonneg
    conv => rhs; rw [←q,Semiring.natCast_add]
    grind only
  have each (w : Wedge7) (hw : w∈wedges) :
      complementaryWeight 0 1 (cut 5) w*f w+complementaryWeight 0 2 (cut 5) w*f w≤
      (if directed w then f w else 0)+(if triple w then f w else 0) := by
    have h := mono (_root_.of_decide_eq_true (List.all_eq_true.mp countTable w hw))
    have r := OrderedRing.mul_le_mul_of_nonneg_right h (nx w)
    rw [castCount,castCount]
    cases a : directed w <;> cases b : triple w <;> simp only [a,b,ite_true,Bool.false_eq_true,ite_false,Semiring.natCast_add,
      Semiring.natCast_one,Semiring.natCast_zero] at r ⊢ <;> grind only
  have total := sumLe wedges _ _ each
  rw [sumOverAdd,sumOverAdd] at total
  change sumOver wedges (fun w => if directed w then f w else 0)≤2 at row
  change sumOver wedges (fun w => if triple w then f w else 0)≤1 at tri
  change sumOver wedges (fun w => complementaryWeight 0 1 (cut 5) w*f w)+sumOver wedges (fun w => complementaryWeight 0 2 (cut 5) w*f w)≤3
  grind only

theorem largeKappaSix (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (large : 11≤200*(physicalPayment half h2 k A mu).kappa) :
    11*(physicalPayment half h2 k A mu).sixMass≤55+200*(physicalPayment half h2 k A mu).kappa := by
  have e := weightedSixMassLeSix half h2 k A mu orth; grind only

private theorem hsCauchy {α : Type} (xs : List α) (f g : α×α → R) :
    (hs xs f g)^2≤hs xs f f*hs xs g g := by
  have sums (ys : List (α×α)) :
      pairing (ys.map (fun e => (f e,g e)))=sumOver ys (fun e => f e*g e) ∧
      leftNorm (ys.map (fun e => (f e,g e)))=sumOver ys (fun e => f e*f e) ∧
      rightNorm (ys.map (fun e => (f e,g e)))=sumOver ys (fun e => g e*g e) := by
    induction ys with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons y ys ih =>
      simp only [List.map_cons,pairing,leftNorm,rightNorm,ih.1,ih.2.1,ih.2.2,sumOver,List.sum_cons]; grind only
  let es := wedgePairs xs
  have e := pairingCauchySchwarz (es.map fun p => (f p,g p))
  rw [(sums es).1,(sums es).2.1,(sums es).2.2] at e
  change (2*sumOver es (fun p => f p*g p))^2≤(2*sumOver es (fun p => f p*f p))*(2*sumOver es (fun p => g p*g p))
  grind only

/-- The weighted rank-six excess is controlled by the shared Gram and the
rank-six anticommuting reserve. This uses only the indicated directed row. -/
theorem sixExcessSquared (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (row : PackingDual.rowMass (fun w => (PhysicalCompressionEffect.physicalEntries half h2 k A).realPart w w) (.directed 6 0)≤2)
    (excess : 5≤(physicalPayment half h2 k A mu).sixMass) :
    let M := physicalPayment half h2 k A mu
    (M.sixMass-5)^2≤M.kappa*(2*reserve half A (cut 5) (cut 5)) := by
  let os := MixedDefect.oddWords (k+3)
  let M := physicalPayment half h2 k A mu
  let U := sharedProbe half A
  let Z := densityCoordinates half A (cut 5)
  have w := sixWedgeLeThree half h2 k A orth row
  have pol := sixPolarization half third h2 h3 k A mu orth
  change 2*hs os U Z=2+sixWedge half h2 A-M.sixMass at pol
  have a : M.sixMass-5≤ -(2*hs os U Z) := by grind only
  have b : 0≤ -(2*hs os U Z)+(M.sixMass-5) := by change 5≤M.sixMass at excess; grind only
  have q := OrderedRing.mul_nonneg (show 0≤ -(2*hs os U Z)-(M.sixMass-5) by grind only) b
  have cs := hsCauchy os U Z
  have gram := (physicalJointGram half third h2 h3 k A orth).1
  change 2*hs os U U=M.kappa at gram
  have rk := ReserveMixedNorm.spectralCutReserve half inv24 h2 h24 k A 5 orth
  change hs os Z Z≤reserve half A (cut 5) (cut 5) at rk
  have prod := OrderedRing.mul_le_mul_of_nonneg_left rk (hsNonnegative os U)
  change _≤M.kappa*(2*reserve half A (cut 5) (cut 5)); rw [←gram]; grind only

end RankSeven.SixModeProbe

#print axioms RankSeven.SixModeProbe.sixScore
#print axioms RankSeven.SixModeProbe.sixPolarization
#print axioms RankSeven.SixModeProbe.sixWedgeLeThree
#print axioms RankSeven.SixModeProbe.largeKappaSix
#print axioms RankSeven.SixModeProbe.sixExcessSquared

