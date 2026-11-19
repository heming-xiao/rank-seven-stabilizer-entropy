import Rank7HighestChartAction

namespace RankSeven.HighestChartMinorTrace

open Lean.Grind Pauli ComplexScalar SymmetricDefect GenericExteriorKernel
open FourCopySectors (rawBlock coefficient Equivariant PermutedList tensorEquivariant)
open PhysicalPairedReduction (dagger)
open ExteriorCuts (Wedge7)
open FrameExteriorSector (sourceTuple framedWord)
open HighestCharacterChart HighestChartAction HighestAnchorPauliTrace
open HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform CharacterFourOrbits
variable {R I J K : Type} [CommRing R]
local notation "C" => ComplexScalar R

def blade (U : I→J→C) := rawBlock .antisymmetric (tensorFour U)

private theorem daggerAlt (U : I→J→C) :
    dagger (blade U)=rawBlock .antisymmetric (dagger (tensorFour U)) := by
  funext u v
  rw [AlternatingTrace.alternatingRight _ (by
    intro p hp a b
    exact congrArg star (tensorEquivariant U p hp b a)) u v]
  change star (FourCopySectors.act (coefficient .antisymmetric) (fun z=>tensorFour U z u) v)=_
  unfold FourCopySectors.act; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro p
  rw [star_mul]; exact congrArg (fun z=>z*star (tensorFour U (reorder v p) u)) ((scalarConjugation (R:=R)).fixesInteger _)

theorem bladeGram (xs : List I) (perm : PermutedList (fourIndices xs)) (U : I→J→C) (V : I→K→C)
    (j : Four J) (k : Four K) :
    matMul (fourIndices xs) (dagger (blade U)) (blade V) j k=
      24*rawBlock .antisymmetric (tensorFour (matMul xs (dagger U) V)) j k := by
  let B:=fourIndices xs
  let X:=dagger (tensorFour U)
  let Y:=tensorFour V
  have eqv : Equivariant X:= fun p hp a b=>congrArg star (tensorEquivariant U p hp b a)
  have e : matMul B (dagger (blade U)) (blade V)=
      rawBlock .antisymmetric (rawBlock .antisymmetric (matMul B X Y)) := by
    rw [daggerAlt]; change matMul B (rawBlock .antisymmetric X) (rawBlock .antisymmetric Y)=_
    rw [←FourCopySectors.blockLeft,←FourCopySectors.blockRight B perm .antisymmetric X Y eqv]
  have dg : dagger (tensorFour U)=tensorFour (dagger U) := by
    unfold dagger; rw [PhysicalPairedReduction.conjugateFour,←fourTranspose]
  have scaled:=FourCopySectors.actProduct .antisymmetric .antisymmetric (fun a=>matMul B X Y a k) j
  change rawBlock .antisymmetric (rawBlock .antisymmetric (matMul B X Y)) j k=_ at scaled
  have q : matMul B X Y=tensorFour (matMul xs (dagger U) V) := by unfold X Y B; rw [dg,←fourMatMul]
  rw [e,scaled,ite_eq_left rfl]; change 24*rawBlock .antisymmetric (matMul B X Y) j k=_; rw [q]

def columns {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c : Word n) (i : Basis n)
    (A : Basis n→J→C) (b : Line T) (j : J) := analysis half F T c i (fun r=>A r j) b

def moved {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c : Word n) (i : Basis n)
    (A : Basis n→J→C) (p : Word n) (b : Line T) (j : J) := analysis half F T c i (act p (fun r=>A r j)) b

private theorem bladeScale (z : C) (M : J→K→C) : blade (fun j k=>z*M j k)=fun j k=>z^4*blade M j k := by
  funext j k; unfold blade rawBlock FourCopySectors.act
  rw [sumOverMulLeft]; apply sumOverCongr; intro p; unfold tensorFour tensor; grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem physicalBladeGram {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (p : Word n) (w : Wedge7) :
    let h:=(block half F c i i).re
    let U:=columns half F T c i A
    let V:=moved half F T c i A p
    let x:=sourceTuple w
    sumOver (fourIndices T.reps.attach) (fun r=>star (blade U r x)*blade V r x)=
      24*(ofReal h)^4*wordExpectation A p w := by
  classical
  let h:=(block half F c i i).re
  let U:=columns half F T c i A
  let V:=moved half F T c i A p
  let x:=sourceTuple w
  have m : matMul T.reps.attach (dagger U) V=(fun j k=>ofReal h*framedWord A p j k) := by
    funext j k; exact chartGram half h2 F T c i (fun r=>A r j) (act p (fun r=>A r k))
  have e:=bladeGram T.reps.attach (FourCopySectors.fullPermuted _ (linesNodup T) (fun r=>List.mem_attach _ _)) U V x x
  rw [m] at e
  change _=24*blade (fun j k=>ofReal h*framedWord A p j k) x x at e
  rw [bladeScale] at e
  change _=24*((ofReal h)^4*rawBlock .antisymmetric (tensorFour (framedWord A p)) x x) at e
  rw [AlternatingTrace.alternatingSortedEntry _ (tensorEquivariant _) w w,FrameExteriorSector.tensorExteriorSector,←wordExpectationMinor] at e
  change sumOver _ (fun r=>star (blade U r x)*blade V r x)=24*((ofReal h)^4)*wordExpectation A p w
  exact e.trans (by grind only)

def fourMap {A D : Type} (f : A→D) (r : Four A) : Four D := ((f r.1.1,f r.1.2),(f r.2.1,f r.2.2))
def fourProduct {A : Type} (f : A→C) (r : Four A) := (f r.1.1*f r.1.2)*(f r.2.1*f r.2.2)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem movedBlade {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c p : Word n) (i : Basis n)
    (A : Basis n→J→C) (r : Four (Line T)) (x : Four J) :
    blade (moved half F T c i A p) r x=
      fourProduct (fun u=>star (step F T c p u)) r*blade (columns half F T c i A) (fourMap (shift T p) r) x := by
  unfold blade
  rw [AlternatingTrace.alternatingRight _ (tensorEquivariant _) r,
    AlternatingTrace.alternatingRight _ (tensorEquivariant _) (fourMap (shift T p) r)]
  unfold FourCopySectors.act; rw [sumOverMulLeft]
  apply sumOverCongr; intro σ
  unfold tensorFour tensor moved fourProduct fourMap columns
  simp only [analysisAction]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem fourStepUnit {n} {G : MaximalFamily n} (F : Lift G) (T : Transversal G) (c p : Word n) (r : Four (Line T)) :
    normSq (fourProduct (R:=R) (fun u=>star (step F T c p u)) r)=1 := by
  unfold fourProduct; simp only [normSq_mul,normSq_star,stepUnit,Semiring.one_mul]

/-- The computational alternating Pauli minor is exactly the expectation of the
involutive, unit-phase character action on its actual exterior amplitude. -/
theorem wordOrbitTrace {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (p : Word n) (w : Wedge7) :
    let h:=(block half F c i i).re
    let D:=fun r=>blade (columns half F T c i A) r (sourceTuple w)
    sumOver (fourIndices T.reps.attach) (fun r=>(star (D r)*(fourProduct (fun u=>star (step F T c p u)) r*D (fourMap (shift T p) r))).re)=
      24*h^4*(wordExpectation A p w).re := by
  have e:=congrArg ComplexScalar.re (physicalBladeGram half h2 F T c i A p w)
  rw [(HighestCosetFourier.realSum _ _).1] at e
  simp only [movedBlade] at e
  refine e.trans ?_
  let h:=(block half F c i i).re
  let z:=wordExpectation A p w
  change ((24*(ofReal h)^4)*z).re=24*h^4*z.re
  rw [←PhysicalPairedReduction.realEmbeddingPow]
  have cc : (24:C)=ofReal (24:R):=rfl
  rw [cc]; simp only [re_mul,im_mul,re_ofReal,im_ofReal]; grind only

end RankSeven.HighestChartMinorTrace

#print axioms RankSeven.HighestChartMinorTrace.bladeGram
#print axioms RankSeven.HighestChartMinorTrace.physicalBladeGram
#print axioms RankSeven.HighestChartMinorTrace.movedBlade
#print axioms RankSeven.HighestChartMinorTrace.fourStepUnit
#print axioms RankSeven.HighestChartMinorTrace.wordOrbitTrace

