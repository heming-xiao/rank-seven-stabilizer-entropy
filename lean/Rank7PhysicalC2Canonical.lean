import Rank7PhysicalC2Projected

/-! The orthogonal-complement test removes every projection from the
individual free readouts, so the occupation bound can use raw coordinates. -/
namespace RankSeven.PhysicalC2Canonical
open Lean.Grind Pauli ComplexScalar
open PhysicalCutCapacities (Triple triples)
open PhysicalTwoHoleOccupancy (modeGram gram3 raise3 lower3 Alt3)
open PhysicalC2Projected (free)
variable {R I : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
def coordinate [DecidableEq I] (i t : I) : ComplexScalar R := if t=i then 1 else 0
theorem lowerFree [DecidableEq I] (is : List I) (x y : I → ComplexScalar R) (i : I)
    (F : I → I → I → ComplexScalar R) (xn : ∀a b,lower3 is x F a b=0) (yn : ∀a b,lower3 is y F a b=0) :
    lower3 is (free x y i) F=lower3 is (coordinate i) F := by
  funext a b
  have row (t : I) : free x y i t*F a b t=coordinate i t*F a b t-star (x i)*(x t*F a b t)-star (y i)*(y t*F a b t) := by
    have eq : PhysicalC2Projected.delta (R:=R) i t=coordinate i t := by
      by_cases h : i=t
      · subst t; rfl
      · simp [PhysicalC2Projected.delta,coordinate,h,Ne.symm h]
    unfold free; rw [eq]; grind only
  unfold lower3 at xn yn ⊢; rw [sumOverCongr is row]; simp only [Compression.sumOverSub,←sumOverMulLeft,xn,yn,Semiring.mul_zero]; grind only

theorem readoutFreeEqualsCoordinate [DecidableEq I] (is : List I) (x y : I → ComplexScalar R) (i : I)
    (E : I → I → ComplexScalar R) (F : I → I → I → ComplexScalar R) (alt : Alt3 F)
    (xn : ∀a b,lower3 is x F a b=0) (yn : ∀a b,lower3 is y F a b=0) :
    gram3 is (raise3 (free x y i) E) F=gram3 is (raise3 (coordinate i) E) F := by
  rw [PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt,PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt,lowerFree is x y i F xn yn]
section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
theorem canonicalAdjointOnComplement {n} (half : R) (unit : 2*half=1) (x y : Basis n → ComplexScalar R)
    (hx : modeGram (qubitIndices n) x x=1) (hy : modeGram (qubitIndices n) y y=1) (xy : modeGram (qubitIndices n) x y=0)
    (F : Basis n → Basis n → Basis n → ComplexScalar R) (alt : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) :
    sumOver (qubitIndices n) (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq
      (gram3 (qubitIndices n) (raise3 (coordinate i) (PhysicalC2Adjoint.twoColumn half x y p)) F)))≤
    36*half^n * sumOver (triples (qubitIndices n)) (fun u => normSq (F u.1.1 u.1.2 u.2)) := by
  simpa only [readoutFreeEqualsCoordinate _ x y _ _ F alt xn yn] using
    PhysicalC2Projected.physicalProjectedAdjoint half unit x y hx hy xy F
end Order
end RankSeven.PhysicalC2Canonical
#print axioms RankSeven.PhysicalC2Canonical.canonicalAdjointOnComplement
