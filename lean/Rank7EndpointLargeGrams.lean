import Rank7HighestAnchorCommutation

namespace RankSeven.EndpointLargeGrams

open Lean.Grind Pauli ComplexScalar PackingPolynomial UpperFrameTrace
open PhysicalCompressionEffect (OrthonormalFrame)
open UpperEndpoint UpperEndpointPrices UpperPhysicalInterior UpperFrameGain
open WeightedProbeShift (physicalPayment)
open PhysicalCutCapacities (rowMass coordinateMass massReorder)
open ExteriorCuts (Wedge7 wedges)
open PackingDual (occupied)
open FrameExteriorSector (sourceTuple)
open GenericExteriorKernel (reorder)
open PhysicalTailBlend (unshiftedDefects)
open PhysicalDefectAssembly (frameDefects)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private def exchange (v : Fin 7) : Fin 7 := if v=1 then 2 else if v=2 then 1 else v
private def filterAt (i : Fin 7) := wedges.filter (fun w => occupied w 0 && occupied w i)
private def sortOrder (w : Wedge7) : ExteriorPauliBase.Permutation := if occupied w 2 then ((0,2),(1,3)) else ((0,1),(2,3))
private def image (w : Wedge7) := reorder (PhysicalWedges.mapFourSites exchange (sourceTuple w)) (sortOrder w)
private theorem mapped : (filterAt 1).map image=(filterAt 2).map sourceTuple := by decide

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem filtered (x : Wedge7→R) (i : Fin 7) : link x 0 i=sumOver (filterAt i) x := by
  have q (xs : List Wedge7) : sumOver xs (fun w => if occupied w 0 && occupied w i then x w else 0)=
      sumOver (xs.filter (fun w => occupied w 0 && occupied w i)) x := by
    induction xs with
    | nil => rfl
    | cons w ws ih => cases e : occupied w 0 && occupied w i <;> simp [sumOver,e] at ih ⊢ <;> grind only
  exact q wedges

theorem secondPairCap (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : OrthonormalFrame A) : 3*link (physicalWeights half h2 k A) 0 2≤7 := by
  let B t i := A t (exchange i)
  have inj : ∀i j : Fin 7,exchange i=exchange j → i=j := by decide
  have orthB : OrthonormalFrame B := by
    intro i j; change sumOver _ (fun t => star (A t (exchange i))*A t (exchange j))=_
    rw [orth]; by_cases h : i=j; · simp [h]
    · have ne : exchange i≠exchange j := fun u => h (inj i j u); simp [h,ne]
  let q := 3*(4*half^(k+3))
  let f := physicalWeights half h2 k A
  let g := physicalWeights half h2 k B
  let Q u := 2*rowMass half A u
  have same (w : Wedge7) : Q (image w)=q*g w := by
    have good : sortOrder w∈ExteriorPauliBase.permutations := by unfold sortOrder; split <;> decide
    have a := massReorder half h2 A (PhysicalWedges.mapFourSites exchange (sourceTuple w)) (sortOrder w) good
    change Q (image w)=2*rowMass half B (sourceTuple w) at a
    exact a.trans (coordinateMass half h2 k B w)
  have eq := congrArg (fun ls => sumOver ls Q) mapped
  simp only [sumOver,List.map_map,Function.comp_def] at eq
  change sumOver (filterAt 1) (fun w => Q (image w))=sumOver (filterAt 2) (fun w => Q (sourceTuple w)) at eq
  have norm (w : Wedge7) : Q (sourceTuple w)=q*f w := coordinateMass half h2 k A w
  simp only [same,norm,←sumOverMulLeft,←filtered] at eq
  have cap := UpperPairCap.physicalPairCap half h2 k B orthB
  change 3*link g 0 1≤7 at cap
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have pp (n : Nat) : 0<half^n := by
    induction n with
    | zero => rw [Semiring.pow_zero]; exact one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)
  have pos : 0<q := by have := pp (k+3); unfold q; grind only
  have h : link g 0 1=link f 0 2 := by
    by_cases yes : link g 0 1=link f 0 2
    · exact yes
    · by_cases lt : link g 0 1<link f 0 2
      · have bad := OrderedRing.mul_lt_mul_of_pos_left lt pos; grind only
      · have bad := OrderedRing.mul_lt_mul_of_pos_left (show link f 0 2<link g 0 1 by grind only) pos; grind only
  rw [h] at cap; exact cap

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem largeShared (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (large : 1≤18*(physicalPayment half h2 k A mu).kappa) :
    let x := physicalWeights half h2 k A
    (trueRay (sharedExcess x) (highExcess x) 0 0).peak≤12*(physicalPayment half h2 k A mu).kappa := by
  have a := UpperPairCap.physicalPairCap half h2 k A orth
  have b := secondPairCap half h2 k A orth
  let x := physicalWeights half h2 k A
  change 3*link x 0 1≤7 at a; change 3*link x 0 2≤7 at b
  change UpperWeighted.larger (link x 0 1+link x 0 2-4) (link x 0 1-2)≤_
  unfold UpperWeighted.larger; split <;> grind only

/-- On the two large-Gram branches the literal endpoint price has no geometric premises. -/
theorem largeFramePrice (half inv24 third : F) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (weights : Fin 7 → F) (orth : OrthonormalFrame A)
    (p : Inputs F) (wh ws c d : F) (chart : (fun i => (weights i)^2)=tail (spectrum p.h p.k p.q) c d)
    (cl : p.cl≤c) (cu : c≤p.ch) (du : d≤p.dh) (dl : p.dl≤d) (dl0 : 0≤p.dl)
    (cu1 : p.ch≤1) (ordered : d≤c) (cornerOrder : p.dl≤p.cl) (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q)
    (f0 : 0≤p.f) (f1 : p.f≤1) (u0 : 0≤p.u) (uc : 2*p.u≤3) (w0 : 0≤p.w) (wc : 4*p.w≤7)
    (largeSharedGram : 1≤18*(physicalPayment half h2 k A weights).kappa)
    (largeHighestGram : 2≤15*(physicalPayment half h2 k A weights).kappaOne) (traceOne traceShared : F) :
    let x := physicalWeights half h2 k A
    let head := spectrum p.h p.k p.q
    let U i := weightedProbe head x i c d
    let ray := trueRay (sharedExcess x) (highExcess x) traceOne traceShared
    let K := UpperEndpointPrices.K p wh ws c d
    physicalPrice p wh ws c d ray+(P p).lambda*(U 1+U 2)+UpperPhysicalInterior.mu p*U 1≤
      invRate*(frameDefects half inv24 k A weights-unshiftedDefects half inv24 k A weights)+
        96*invRate*(K.one*traceOne+K.shared*traceShared) :=
  PhysicalEndpointPrice.physicalPriceOnFrame half inv24 third h2 h24 h3 k A weights orth p wh ws c d chart cl cu du dl dl0 cu1 ordered cornerOrder h0 k0 q0 f0 f1 u0 uc w0 wc
    (largeShared half h2 k A weights orth largeSharedGram)
    (HighestAnchorSelection.largeGram half h2 k A weights orth largeHighestGram) traceOne traceShared

end Field

end RankSeven.EndpointLargeGrams

#print axioms RankSeven.EndpointLargeGrams.secondPairCap
#print axioms RankSeven.EndpointLargeGrams.largeShared
#print axioms RankSeven.EndpointLargeGrams.largeFramePrice

