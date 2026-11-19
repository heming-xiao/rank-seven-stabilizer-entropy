import Rank7PhysicalTwoHoleAdjointTransport
import Rank7PhysicalC2Projected

/-! Replacing each canonical precursor by its orthogonal projection on the
two-mode complement in the actual physical transport intertwinings. -/
namespace RankSeven.PhysicalProjectedTransport
open Lean.Grind Pauli ComplexScalar
open PhysicalTwoHoleOccupancy (gram3 gram2 Alt3 lower3 raise3)
open PhysicalTwoHoleAdjointTransport (coord col1 col2 singleCol doubleCut columnCut linkAfterSingle gAfterC)
open PhysicalC2Projected (free delta dot project)
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem pick {n : Nat} (i : Basis n) (f : Basis n→ComplexScalar R) :
    sumOver (qubitIndices n) (fun t => delta i t*f t)=f i := by
  rw [←ExteriorPauliBase.sumOnIndex _ i f (HyperplaneIncidence.normalsNodup _) (qubitIndicesComplete _)]
  apply sumOverCongr; intro t; unfold delta; split <;> grind only
private theorem deltaCoord {n : Nat} (i t : Basis n) : delta (R:=R) i t=coord i t := by
  by_cases e : i=t
  · subst t; simp [delta,coord]
  · simp [delta,coord,e,Ne.symm e]
private theorem zeroSum {I C : Type} [CommRing C] (ls : List I) : sumOver ls (fun _ => (0:C))=0 := by
  induction ls with | nil => rfl | cons x xs ih => change 0+sumOver xs _=0; rw [ih]; grind only

theorem lowerCanonical {n : Nat} (F : Basis n→Basis n→Basis n→ComplexScalar R) (i a b : Basis n) :
    lower3 (qubitIndices n) (coord i) F a b=F a b i := by
  unfold lower3; rw [←pick i (F a b)]; apply sumOverCongr; intro t; rw [deltaCoord]

theorem lowerFree {n : Nat} (x y : Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (i a b : Basis n) :
    lower3 (qubitIndices n) (free x y i) F a b=F a b i := by
  let L := qubitIndices n
  have term (t : Basis n) : free x y i t*F a b t = delta i t*F a b t -star (x i)*(x t*F a b t)-star (y i)*(y t*F a b t) := by unfold free; grind only
  unfold lower3; rw [sumOverCongr _ term,Compression.sumOverSub,Compression.sumOverSub,←sumOverMulLeft,←sumOverMulLeft,pick]
  change F a b i- star (x i)*lower3 L x F a b-star (y i)*lower3 L y F a b=F a b i
  rw [xn,yn]; grind only

def coordRead {n : Nat} (E : Basis n→Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R) (z : Basis n) :=
    gram3 (qubitIndices n) (raise3 (coord z) E) F

private theorem readCanonical {n : Nat} (E : Basis n→Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R)
    (af : Alt3 F) (z : Basis n) : coordRead E F z = 3*gram2 (qubitIndices n) E (fun a b => F a b z) := by
  rw [coordRead,PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ af]
  rw [show lower3 (qubitIndices n) (coord z) F=(fun a b => F a b z) from funext (fun a => funext (lowerCanonical F z a))]

theorem readoutFreeEqualsCoordinate {n : Nat} (x y : Basis n→ComplexScalar R) (E : Basis n→Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (i : Basis n) :
    gram3 (qubitIndices n) (raise3 (free x y i) E) F=coordRead E F i := by
  rw [readCanonical E F af,PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ af]
  rw [show lower3 (qubitIndices n) (free x y i) F=(fun a b => F a b i) from funext (fun a => funext (lowerFree x y F xn yn i a))]

private theorem readoutOrth {n : Nat} (x : Basis n→ComplexScalar R) (E : Basis n→Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) : dot (qubitIndices n) x (coordRead E F)=0 := by
  let L := qubitIndices n
  have eq (z : Basis n) : x z*coordRead E F z=3*(x z*gram2 L E (fun a b => F a b z)) := by rw [readCanonical E F af]; grind only
  rw [dot,sumOverCongr _ eq,←sumOverMulLeft]
  apply Eq.trans (congrArg ((3:ComplexScalar R)*·) (a₂:=0) ?_)
  · grind only
  unfold gram2 PhysicalTwoHoleOccupancy.sum2
  simp only [sumOverMulLeft]
  rw [sumOverSwap]; have inner (a : Basis n) : sumOver L (fun z => sumOver L (fun b => x z*(star (E a b)*F a b z)))=0 := by
    rw [sumOverSwap]
    have each (b : Basis n) : sumOver L (fun z => x z*(star (E a b)*F a b z))=0 := by
      have term (z : Basis n) : x z*(star (E a b)*F a b z)=star (E a b)*(x z*F a b z) := by grind only
      rw [sumOverCongr _ term,←sumOverMulLeft]
      change star (E a b)*lower3 L x F a b=0; rw [xn]; grind only
    rw [sumOverCongr L each,zeroSum]
  change sumOver L (fun a => sumOver L (fun z => sumOver L (fun b => x z*(star (E a b)*F a b z))))=0
  rw [sumOverCongr L inner,zeroSum]

def projectedG {n : Nat} (half : R) (x y g : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (b : Basis n×Basis n) :=
  sumOver (qubitIndices n) (fun z => sumOver (MixedDefect.oddWords n) (fun p =>
    doubleCut half (fun a => star (g a)) (fun a => star (free x y z a)) p b*
      gram3 (qubitIndices n) (raise3 (free x y z) (col2 half x y p)) F))

theorem projectedComposition {n : Nat} (half : R) (x y g : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0)
    (b : Basis n×Basis n) : projectedG half x y g F b=gAfterC half x y g F b := by
  let L := qubitIndices n
  unfold projectedG gAfterC; rw [sumOverSwap,sumOverSwap L (MixedDefect.oddWords n)]
  apply sumOverCongr; intro p
  let E := col2 half x y p
  let W (z : Basis n) := columnCut half (fun a => star (g a)) p (b,z)
  change sumOver L (fun z => sumOver L (fun a => star (free x y z a)*W a)*gram3 L (raise3 (free x y z) E) F)=sumOver L (fun z => W z*coordRead E F z)
  have read (i : Basis n) : gram3 L (raise3 (free x y i) E) F=coordRead E F i := readoutFreeEqualsCoordinate x y E F af xn yn i
  simp only [read,sumOverMulRight]
  rw [sumOverSwap]; apply sumOverCongr; intro a
  have term (z : Basis n) : star (free x y z a)*W a*coordRead E F z=W a*(star (free x y z a)*coordRead E F z) := by grind only
  rw [sumOverCongr L term,←sumOverMulLeft,PhysicalC2Projected.coefficientProjection L (HyperplaneIncidence.normalsNodup _) (fun i => qubitIndicesComplete i) x y (coordRead E F)]
  rw [project,readoutOrth x E F af xn,readoutOrth y E F af yn]; grind only

/-- Both adjoint intertwinings for the projected computational Parseval
family, in the same coordinates as the physical two-hole norm bound. -/
theorem physicalProjectedIntertwinings {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (b : Basis n×Basis n) :
    projectedG half x y x F b=linkAfterSingle half x y (singleCol half x y) F b ∧
    projectedG half x y y F b=linkAfterSingle half x y (singleCol half y x) F b := by
  rw [projectedComposition half x y x F af xn yn,projectedComposition half x y y F af xn yn]
  exact PhysicalTwoHoleAdjointTransport.physicalAdjointIntertwinings half unit x y F af xn yn b

end RankSeven.PhysicalProjectedTransport
#print axioms RankSeven.PhysicalProjectedTransport.physicalProjectedIntertwinings
