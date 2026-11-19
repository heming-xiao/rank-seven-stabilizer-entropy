import Rank7PauliMatchingPrices

/-! Weighted two-probe receipt for the actual Pauli defects and basic
order relations of the normalized matching moments. -/
namespace RankSeven.WeightedProbeShift
open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram PauliMatchingPrices
open MixedDefect (oddWords)
open PhysicalDefectAssembly (pairedState pairedDensity frameDefects physicalSectorTerms)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

/-- Normalized odd-Pauli moments and the two resulting polarization prices. -/
structure Payment (R : Type) where
  kappa : R
  kappaOne : R
  cross : R
  emptyMass : R
  sixMass : R
  highest : R
  shared : R

def physicalPayment (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) : Payment R :=
  let t := fun i => (mu i)^2
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W i := ProjectedProbeOverlap.weightedFourWedge 0 i t (fun w => E.realPart w w)
  let p1 := fun p => pairWeight A p 0 1
  let p := fun w => p1 w+pairWeight A w 0 2
  let κ := oddAverage half (fun w => p w*(1-p w))
  let κ1 := oddAverage half (fun w => p1 w*(1-p1 w))
  let cross := oddAverage half (fun w => p1 w*(1-p w))
  let empty := oddAverage half (fun w => p w*(1-p w-pairWeight A w 1 2))
  let six := oddAverage half (fun w => p w*sixVertexMass A w)
  ⟨κ,κ1,cross,empty,six,W 1-referencePair t+leadingGap t*κ1,
    W 1+W 2-referenceShared t+sharedGap t*κ+leadingGap t*cross+emptyGap t*empty-tailGap t*(six-5)⟩

/-- Both probes draw on the same remaining mixed square. -/
def Payment.receipt (m : Payment R) (s t : R) :=
  24*s*m.shared+24*t*m.highest-12*s^2*m.kappa-12*t^2*m.kappaOne-24*s*t*m.cross

theorem physicalSquareReceipt (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) (s t : R) (hs0 : 0≤s) (ht0 : 0≤t) :
    (physicalPayment half h2 k A mu).receipt s t ≤
      24*hs (oddWords (k+3)) (densityCoordinates half A mu) (densityCoordinates half A mu) := by
  let M := physicalPayment half h2 k A mu
  let os := oddWords (k+3)
  let L := densityCoordinates half A mu
  let U := sharedProbe half A
  let V := pairCoordinates half A 0 1
  have bound := physicalProbePayments half third h2 h3 k A mu orth sort
  change M.highest≤2*hs os V L ∧ M.shared≤2*hs os U L at bound
  have G := physicalJointGram half third h2 h3 k A orth
  change 2*hs os U U=M.kappa ∧ 2*hs os V V=M.kappaOne ∧ 2*hs os U V=M.cross at G
  have a := OrderedRing.mul_le_mul_of_nonneg_left bound.1 ht0
  have b := OrderedRing.mul_le_mul_of_nonneg_left bound.2 hs0
  have n := hsNonnegative os (shifted L U V s t)
  change M.receipt s t≤24*hs os L L
  rw [jointShiftIdentity os L U V s t]
  unfold Payment.receipt
  rw [←G.1,←G.2.1,←G.2.2]; grind only

/-- Lower bound on the full physical defect, retaining the three other
exact residual terms and the jointly shifted weighted payment. -/
theorem physicalDefectReceipt (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) (s t : R) (hs0 : 0≤s) (ht0 : 0≤t) :
    let n := k+3
    let d := (2:R)^n
    let di := half^n
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    d^2*SectorDefectAccounting.symmetricDefect di (physicalSectorTerms half inv24 k A mu)+
      4*d*MixedDefect.curvature (oddWords n) SymmetricDefect.anti K+
      2*di^2*(PhysicalAntiQuartic.antiMass c).re+(physicalPayment half h2 k A mu).receipt s t≤
      frameDefects half inv24 k A mu := by
  have e := physicalSquareReceipt half third h2 h3 k A mu orth sort s t hs0 ht0
  dsimp only; rw [physicalJointResidual half inv24 h2 h24 k A mu orth]
  grind only

private theorem averageNonnegative (half : R) (h2 : 2*half=1) {n : Nat} (f : Word n → R)
    (hf : ∀ p∈oddWords n,0≤f p) : 0≤oddAverage half f := by
  have hh : 0≤half := by grind only
  have pos (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hh
  exact OrderedRing.mul_nonneg (by have := pos n; grind only) (Compression.sumOverNonnegative (oddWords n) f hf)

private theorem averageLe (half : R) (h2 : 2*half=1) {n : Nat} (f g : Word n → R)
    (h : ∀ p∈oddWords n, f p≤g p) : oddAverage half f≤oddAverage half g := by
  have e := averageNonnegative half h2 (fun p => g p-f p) (fun p hp => by have := h p hp; grind only)
  unfold oddAverage at *; rw [Compression.sumOverSub] at e; grind only

theorem leadingTriangle {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (p : Word n) (hp : p∈oddWords n) :
    pairWeight A p 0 1+pairWeight A p 0 2+pairWeight A p 1 2≤1 := by
  have e := physicalOddRows A orth p hp .headThree
  have l : SectorDefectAccounting.wedgePairs OddSet.headThree.labels=[(0,1),(0,2),(1,2)] := by decide
  simp only [mass,l,OddSet.cap,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at e
  grind only

/-- The physical shared/highest cross Gram is nonnegative, bounded by
both diagonal Grams, and the uncovered leading-triangle mass is nonnegative. -/
theorem physicalMomentOrder (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let M := physicalPayment half h2 k A mu
    0≤M.cross ∧ M.cross≤M.kappa ∧ M.cross≤M.kappaOne ∧ 0≤M.emptyMass := by
  let os := oddWords (k+3)
  let P1 p := pairWeight A p 0 1
  let P2 p := pairWeight A p 0 2
  let P p := P1 p+P2 p
  let T p := pairWeight A p 1 2
  have h1 (p) : 0≤P1 p := normSq_nonnegative _
  have h2' (p) : 0≤P2 p := normSq_nonnegative _
  have hm (p) : 0≤T p := normSq_nonnegative _
  have v (p) (hp : p∈os) : 0≤P p ∧ 0≤1-P p ∧ P1 p≤P p ∧ 0≤1-P p-T p := by
    have tr := leadingTriangle A orth p hp
    change P1 p+P2 p+T p≤1 at tr
    have := h1 p; have := h2' p; have := hm p; dsimp only [P]; grind only
  refine ⟨averageNonnegative half h2 _ (fun p hp => OrderedRing.mul_nonneg (h1 p) (v p hp).2.1),?_,?_,?_⟩
  · apply averageLe half h2; intro p hp
    exact OrderedRing.mul_le_mul_of_nonneg_right (v p hp).2.2.1 (v p hp).2.1
  · apply averageLe half h2; intro p hp
    exact OrderedRing.mul_le_mul_of_nonneg_left (by have := (v p hp).2.2.1; grind only) (h1 p)
  · exact averageNonnegative half h2 _ (fun p hp => OrderedRing.mul_nonneg (v p hp).1 (v p hp).2.2.2)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem massSplit (x : Fin 7 → Fin 7 → R) :
    mass x (SectorDefectAccounting.wedgePairs OddSet.allSeven.labels) =
      massSix x+(x 0 6+x 1 6+x 2 6+x 3 6+x 4 6+x 5 6) := by
  let a := (List.finRange 7).filter (fun i => i.val<6)
  have labels : a=[0,1,2,3,4,5] := by decide
  change mass x (SectorDefectAccounting.wedgePairs OddSet.allSeven.labels)=mass x (SectorDefectAccounting.wedgePairs a)+_
  rw [labels]
  simp only [OddSet.labels,SectorDefectAccounting.wedgePairs,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    mass,sumOver,List.sum_cons,List.sum_nil]; grind only

/-- The six-vertex mass is at most three for each individual odd Pauli. -/
theorem sixMassLeThree {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (p : Word n) (hp : p∈oddWords n) : sixVertexMass A p≤3 := by
  let x := pairWeight A p
  have e := physicalOddRows A orth p hp .allSeven
  change mass x (SectorDefectAccounting.wedgePairs OddSet.allSeven.labels)≤3 at e
  rw [massSplit] at e
  have h (i : Fin 7) : 0≤x i 6 := normSq_nonnegative _
  have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
  change massSix x ≤ 3; grind only

/-- The six-vertex contribution charged in the shared price is at most
six after averaging against the common-leading-label pair weight. -/
theorem weightedSixMassLeSix (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    (physicalPayment half h2 k A mu).sixMass≤6 := by
  let P₁ p := pairWeight A p 0 1
  let P₂ p := pairWeight A p 0 2
  let P p := P₁ p+P₂ p
  have e := averageLe half h2 (fun p => P p*sixVertexMass A p) (fun p => P p*3) (fun p hp => by
    have n1 : 0≤P₁ p := normSq_nonnegative _
    have n2 : 0≤P₂ p := normSq_nonnegative _
    exact OrderedRing.mul_le_mul_of_nonneg_left (sixMassLeThree A orth p hp) (by dsimp only [P]; grind only))
  have a : oddAverage half P₁=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have b : oddAverage half P₂=1 := pairWeightAverage half h2 A orth 0 2 (by decide)
  have ab : oddAverage half (fun p => P p*3)=3*(oddAverage half P₁+oddAverage half P₂) := by
    unfold oddAverage P; rw [←sumOverMulRight,sumOverAdd]; grind only
  rw [ab,a,b] at e
  change oddAverage half (fun p => P p*sixVertexMass A p)≤6; grind only

end RankSeven.WeightedProbeShift

#print axioms RankSeven.WeightedProbeShift.physicalSquareReceipt
#print axioms RankSeven.WeightedProbeShift.physicalDefectReceipt
#print axioms RankSeven.WeightedProbeShift.physicalMomentOrder
#print axioms RankSeven.WeightedProbeShift.sixMassLeThree
#print axioms RankSeven.WeightedProbeShift.weightedSixMassLeSix
