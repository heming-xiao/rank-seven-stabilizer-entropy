import Rank7UpperPhysicalReplay

/-! Actual shared-link and triple-row inputs to upper trace interpolation. -/
namespace RankSeven.UpperFrameTrace
open Lean.Grind Pauli ExteriorCuts PackingDual PackingPolynomial
attribute [local instance] Semiring.natCast
variable {R : Type} [CommRing R]
def sharedExcess (x : Wedge7→R) := link x 0 1+link x 0 2-4
def highExcess (x : Wedge7→R) := link x 0 1-2
def missingTriple (x : Wedge7→R) := 1-rowMass x (.triple 0 1 2)
def sharedFraction (x : Wedge7→R) := sharedExcess x+missingTriple x

private theorem blockIdentity (x : Wedge7→R) :
    score x (blockCost2 .two_shared_plus_x)=2*(2*(link x 0 1+link x 0 2)-rowMass x (.triple 0 1 2)) := by
  unfold score link rowMass
  rw [←sumOverAdd,sumOverMulLeft,←Compression.sumOverSub]
  rw [sumOverMulLeft]
  apply sumOverCongr; intro w
  unfold blockCost2 Row.covers
  dsimp only
  by_cases h0 : occupied w 0=true <;> by_cases h1 : occupied w 1=true <;> by_cases h2 : occupied w 2=true <;> simp_all <;> grind

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem sharedTraceCaps (x : Wedge7→R) (nx : ∀ w,0≤x w) (rows : RowsHold x) (n0 : 0≤sharedExcess x) :
    0≤missingTriple x ∧ 2*sharedExcess x+missingTriple x≤1 ∧ 2*sharedExcess x≤1 ∧
    0≤sharedFraction x ∧ sharedFraction x≤1 ∧
    sharedExcess x*(1-sharedExcess x)≤sharedFraction x*(1-sharedFraction x) := by
  have triple := rows (.triple 0 1 2) (by decide)
  change _≤Nat.cast 1 at triple
  rw [Semiring.natCast_one] at triple
  have bound := uniformBlockBound x nx rows .two_shared_plus_x
  rw [blockIdentity] at bound
  change _≤2*Nat.cast 8 at bound
  have eight : (Nat.cast 8:R)=8 := by grind
  rw [eight] at bound
  have gap : 0≤missingTriple x := by unfold missingTriple; grind only
  have count : 2*sharedExcess x+missingTriple x≤1 := by unfold sharedExcess missingTriple; grind only
  have plus := OrderedRing.mul_nonneg gap (show 0≤1-2*sharedExcess x-missingTriple x by grind only)
  unfold sharedFraction; exact ⟨gap,count,by grind only,by grind only,by grind only,by grind only⟩

theorem physicalSharedTrace (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (n0 : 0≤sharedExcess (physicalWeights half unit k A)) :
    let x := physicalWeights half unit k A
    2*sharedExcess x≤1 ∧ 0≤sharedFraction x ∧ sharedFraction x≤1 ∧
      sharedExcess x*(1-sharedExcess x)≤sharedFraction x*(1-sharedFraction x) := by
  obtain ⟨nx,rows⟩ := physicalRows half unit k A orth
  exact (sharedTraceCaps _ nx rows n0).2.2


def sharedCut (x : Wedge7→R) := sumOver wedges (fun w => if occupied w 0 && (occupied w 1 || occupied w 2) then x w else 0)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem traceOffsets (x : Wedge7→R) : link x 0 1=2+highExcess x ∧ sharedCut x=3+sharedFraction x := by
  have union : sharedCut x=link x 0 1+link x 0 2-rowMass x (.triple 0 1 2) := by
    unfold sharedCut link rowMass; rw [←sumOverAdd,←Compression.sumOverSub]; apply sumOverCongr; intro w
    dsimp only [Row.covers]
    by_cases h0 : occupied w 0=true <;> by_cases h1 : occupied w 1=true <;> by_cases h2 : occupied w 2=true <;> simp_all <;> grind only
  unfold highExcess sharedFraction sharedExcess missingTriple; constructor <;> grind only

end RankSeven.UpperFrameTrace

namespace RankSeven.UpperFrameTrace
open Lean.Grind Pauli ExteriorCuts PackingPolynomial Interval UpperContractor UpperEndpoint UpperEndpointPrices UpperPhysicalInterior UpperFrameGain
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Fixed orthonormal frame version with the two actual leading excesses
and the trace products of their respective leading cuts. -/
theorem actualFrameInterior (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) {box : UpperCorner.TailBox} {h g q c d : R}
    (inside : Inside cppGrid box h g q c d) (domain : TailRectangle box) (rows : Witnesses box)
    (h0 : 0≤h) (k0 : 0≤g) (q0 : 0≤q)
    (n0 : 0≤sharedExcess (physicalWeights half unit k A)) (v0 : 0≤highExcess (physicalWeights half unit k A))
    (pos : 0<sharedExcess (physicalWeights half unit k A)+highExcess (physicalWeights half unit k A))
    (pairCap : 3*link (physicalWeights half unit k A) 0 1≤7)
    (exterior : ∀ f u w : R,ShiftValues f u w →
      ExteriorEstimates (realInputs box h g q f u w) (physicalWeights half unit k A)
        (sharedExcess (physicalWeights half unit k A)) (highExcess (physicalWeights half unit k A))) :
    let x := physicalWeights half unit k A
    let n := sharedExcess x
    let v := highExcess x
    let z := sharedFraction x
    ∃ f u w wh ws : R,let p := realInputs box h g q f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧ corrected (spectrum h g q) x (P p).lambda (mu p) (cross p) c d <
        physicalPrice p wh ws c d (trueRay n v (v*(1-v)) (z*(1-z))) := by
  obtain ⟨cap,_,_,shared⟩ := physicalSharedTrace half unit k A orth n0
  have high : 3*highExcess (physicalWeights half unit k A)≤1 := by unfold highExcess; grind only
  exact frameInterior _ inside domain rows h0 k0 q0 n0 v0 pos cap high (Std.le_refl _) shared exterior

end RankSeven.UpperFrameTrace
#print axioms RankSeven.UpperFrameTrace.traceOffsets
#print axioms RankSeven.UpperFrameTrace.actualFrameInterior

#print axioms RankSeven.UpperFrameTrace.physicalSharedTrace
