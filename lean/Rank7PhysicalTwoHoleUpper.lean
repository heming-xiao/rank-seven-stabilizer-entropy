import Rank7ComplexFiniteRangeBound
import Rank7FiveFaceCapacity
import Rank7PhysicalWaveReproduction
import Rank7PhysicalTwoHoleEigen

/-! Physical two-hole Bessel assembly on the alternating, x,y-free
grade-three test space and the projected computational precursor family. -/
namespace RankSeven.PhysicalTwoHoleUpper
open Lean.Grind Pauli ComplexScalar
open PhysicalCutCapacities (Triple triples)
open PhysicalTwoHoleOccupancy (modeGram gram3 gram2 Alt3 lower3 lower2 raise3 residual sum3)
open PhysicalTwoHoleAdjointTransport (singleCol col2 col1)
open PhysicalUniformOccupation (wave)
open ComplexFiniteRangeBound (mass costs)
attribute [local instance] Ring.intCast
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
variable {R : Type} [CommRing R]

abbrev Field3 (R : Type) (n : Nat) := Basis n→Basis n→Basis n→ComplexScalar R

def slice {n : Nat} (x y : Basis n→ComplexScalar R) (F : Field3 R n) :=
  Alt3 F ∧ (∀a b,lower3 (qubitIndices n) x F a b=0) ∧ (∀a b,lower3 (qubitIndices n) y F a b=0)
def energy {n : Nat} (F : Field3 R n) :=
  sumOver (triples (qubitIndices n)) (fun u => normSq (F u.1.1 u.1.2 u.2))
def combine {n : Nat} (a w : Field3 R n) (i j k : Basis n) :=
  ofReal (energy a)*w i j k-gram3 (qubitIndices n) a w*a i j k

private theorem productSum {I J C : Type} [CommRing C] (xs : List I) (ys : List J) (f : I×J→C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun a => sumOver ys (fun b => f (a,b))) := by
  rw [productIndices,sumOverFlatMap]; apply sumOverCongr; intro a; simp only [sumOver,List.map_map,Function.comp_def]
private theorem threeRows {n : Nat} (u v : Field3 R n) : gram3 (qubitIndices n) u v=
    sumOver (triples (qubitIndices n)) (fun t => star (u t.1.1 t.1.2 t.2)*v t.1.1 t.1.2 t.2) := by
  simp only [gram3,sum3,triples,productSum]
private theorem gramSym {n : Nat} (a b : Field3 R n) : gram3 (qubitIndices n) b a=star (gram3 (qubitIndices n) a b) := by
  rw [threeRows,threeRows,ComplexExterior.starSumOver]; apply sumOverCongr; intro t; simp only [star_mul,star_star]; grind only
private theorem realSum {I : Type} (L : List I) (f : I→R) : sumOver L (fun i => ofReal (f i))=ofReal (sumOver L f) := by
  induction L with | nil => rfl | cons a L ih => change ofReal (f a)+sumOver L _=ofReal (f a+sumOver L _); rw [ih]; apply ComplexScalar.ext <;> simp <;> grind
private theorem gramSelf {n : Nat} (u : Field3 R n) : gram3 (qubitIndices n) u u=ofReal (energy u) := by
  simp only [threeRows,star_mul_self,realSum,energy]
private theorem gramCombination {n : Nat} (a c w : Field3 R n) :
    gram3 (qubitIndices n) c (combine a w)=ofReal (energy a)*gram3 (qubitIndices n) c w-
      gram3 (qubitIndices n) a w*gram3 (qubitIndices n) c a := by
  let H := gram3 (R:=R) (qubitIndices n)
  let A : ComplexScalar R := ofReal (energy a)
  let B := H a w
  change gram3 (qubitIndices n) c (fun i j k => A*w i j k-B*a i j k)=A*gram3 (qubitIndices n) c w-B*gram3 (qubitIndices n) c a
  simp only [threeRows]; rw [sumOverMulLeft,sumOverMulLeft,←Compression.sumOverSub]; apply sumOverCongr; intro t; grind only
private theorem starSub (a b : ComplexScalar R) : star (a-b)=star a-star b := by
  apply ComplexScalar.ext <;> simp <;> grind only
private theorem gramCombinationLeft {n : Nat} (a c w : Field3 R n) :
    gram3 (qubitIndices n) (combine a c) w=ofReal (energy a)*gram3 (qubitIndices n) c w-
      star (gram3 (qubitIndices n) a c)*gram3 (qubitIndices n) a w := by
  rw [gramSym w (combine a c),gramCombination,starSub,star_mul,star_mul,star_ofReal,←gramSym,←gramSym,←gramSym]

private theorem sliceCombination {n : Nat} (x y : Basis n→ComplexScalar R) (a w : Field3 R n)
    (pa : slice x y a) (pw : slice x y w) : slice x y (combine a w) := by
  have cut (z : Basis n→ComplexScalar R) (ca : ∀i j,lower3 (qubitIndices n) z a i j=0) (cw : ∀i j,lower3 (qubitIndices n) z w i j=0) (i j : Basis n) :
      lower3 (qubitIndices n) z (combine a w) i j=0 := by
    let A : ComplexScalar R := ofReal (energy a); let B := gram3 (qubitIndices n) a w
    have row (k : Basis n) : z k*combine a w i j k=A*(z k*w i j k)-B*(z k*a i j k) := by change z k*(A*_ - B*_)=_; grind only
    change sumOver (qubitIndices n) (fun k => z k*combine a w i j k)=0
    rw [sumOverCongr _ row,Compression.sumOverSub,←sumOverMulLeft,←sumOverMulLeft]
    change A*lower3 (qubitIndices n) z w i j-B*lower3 (qubitIndices n) z a i j=0
    rw [cw,ca]; grind only
  refine ⟨⟨?_,?_⟩,cut _ pa.2.1 pw.2.1,cut _ pa.2.2 pw.2.2⟩
  · intro i j k; unfold combine; rw [pa.1.1 i j k,pw.1.1 i j k]; grind only
  · intro i j k; unfold combine; rw [pa.1.2 i j k,pw.1.2 i j k]; grind only

noncomputable def unitWord {n : Nat} (p q : Word n) : ComplexScalar R := if p=q then 1 else 0
theorem unitWave {n : Nat} (half : R) (p : Word n) (hp : p∈MixedDefect.oddWords n) (u : Four (Basis n)) :
    wave half (unitWord p) u=WedgeSquareIntertwiner.wedgeSquareColumn half p u := by
  unfold wave; rw [←ExteriorPauliBase.sumOnIndex _ p (fun q => WedgeSquareIntertwiner.wedgeSquareColumn half q u) (MixedDefect.oddWordsNodup _) hp]
  apply sumOverCongr; intro q; unfold unitWord; split <;> grind only

theorem singleIsWave {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    singleCol half x y p=PhysicalTwoHoleOccupancy.oneOccupied half x y (unitWord p) := by
  unfold singleCol PhysicalTwoHoleOccupancy.oneOccupied
  congr 1; funext a b c
  simp only [col1,PhysicalTwoHoleAdjointTransport.columnCut,PhysicalTwoHoleOccupancy.anchored,PhysicalUniformOccupation.oneHole,unitWave half p hp]

private theorem modeReverse {I : Type} (L : List I) (x y : I→ComplexScalar R) : star (modeGram L x y)=modeGram L y x := by
  simp only [modeGram,ComplexExterior.starSumOver,star_mul,star_star]; apply sumOverCongr; intro a; grind only

private theorem innerSlice {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (hy : modeGram (qubitIndices n) y y=1) (xy : modeGram (qubitIndices n) x y=0) (f : Word n→ComplexScalar R) :
    slice x y (PhysicalTwoHoleOccupancy.oneOccupied half x y f) := by
  let L := qubitIndices n
  let h := PhysicalTwoHoleOccupancy.anchored half x f
  let e := lower3 L y h
  have ah : Alt3 h := PhysicalTwoHoleOccupancy.anchoredAlternating _ _ _
  have ae : PhysicalTwoHoleOccupancy.Alt2 e := PhysicalTwoHoleOccupancy.lowerAlt L y ah
  have ar := PhysicalTwoHoleOccupancy.raiseAlt y ae
  have zerosY (a : Basis n) : lower2 L y e a=0 := PhysicalTwoHoleOccupancy.lowerSquared half unit L y h ah a
  have zerosX (a : Basis n) : lower2 L x e a=0 := by
    have swap (b : Basis n) : e a b= -lower3 L x (PhysicalTwoHoleOccupancy.anchored half y f) a b := PhysicalTwoHoleOccupancy.physicalTwoHoleSkew _ _ _ _ _ _
    have m := PhysicalTwoHoleOccupancy.lowerSquared half unit L x _ (PhysicalTwoHoleOccupancy.anchoredAlternating half y f) a
    change sumOver L (fun b => x b*e a b)=0
    have row (b : Basis n) : x b*e a b= -(x b*lower3 L x (PhysicalTwoHoleOccupancy.anchored half y f) a b) := by rw [swap]; grind only
    rw [sumOverCongr L row]; have neg (v : Basis n→ComplexScalar R) (ls : List (Basis n)) : sumOver ls (fun i => -v i)= -sumOver ls v := by
      induction ls with | nil => change 0= -0; grind only | cons i ls ih => change -v i+sumOver ls _= -(v i+sumOver ls _); rw [ih]; grind only
    rw [neg]; change -lower2 L x (lower3 L x _) a=0; rw [m]; grind only
  have cut (z : Basis n→ComplexScalar R) (a b : Basis n) : lower3 L z (residual L y h) a b=lower3 L z h a b-lower3 L z (raise3 y e) a b := by
    change sumOver L (fun t => z t*(h a b t-raise3 y e a b t))=sumOver L (fun t => z t*h a b t)-sumOver L (fun t => z t*raise3 y e a b t)
    rw [←Compression.sumOverSub]; apply sumOverCongr; intro t; grind only
  have yx : modeGram L y x=0 := by
    rw [←modeReverse,xy]; exact star_ofReal (0:R)
  change Alt3 (residual L y h) ∧ (∀a b,lower3 L x (residual L y h) a b=0) ∧ (∀a b,lower3 L y (residual L y h) a b=0)
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro a b c; unfold residual; change h b a c-raise3 y e b a c= -(h a b c-raise3 y e a b c)
    rw [ar.1 a b c,ah.1 a b c]; grind only
  · intro a b c; unfold residual; change h a c b-raise3 y e a c b= -(h a b c-raise3 y e a b c)
    rw [ar.2 a b c,ah.2 a b c]; grind only
  · intro a b
    have self : lower3 L x h a b=0 := PhysicalTwoHoleOccupancy.fromTwice half unit (PhysicalTwoHoleOccupancy.physicalTwoHoleSkew half x x f a b)
    rw [cut,PhysicalTwoHoleOccupancy.lowerRaise,zerosX,zerosX,PhysicalTwoHoleOccupancy.modeFlip,yx,self]; grind only
  · intro a b
    rw [cut,PhysicalTwoHoleOccupancy.lowerRaise,zerosY,zerosY,PhysicalTwoHoleOccupancy.modeFlip,hy]
    change e a b-(_*0-_*0+1*e a b)=0; grind only

def singleRows {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) : List (Field3 R n) :=
  (MixedDefect.oddWords n).map (singleCol half x y)++(MixedDefect.oddWords n).map (singleCol half y x)
noncomputable def freeRows {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) : List (Field3 R n) :=
  (qubitIndices n).flatMap (fun i => (MixedDefect.oddWords n).map (PhysicalTwoHoleEigen.freeCol half x y i))

private theorem appendSum {I C : Type} [CommRing C] (xs ys : List I) (f : I→C) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons x xs ih => change f x+sumOver (xs++ys) f=(f x+sumOver xs f)+sumOver ys f; rw [ih]; grind only
private theorem mappedSum {I J C : Type} [CommRing C] (xs : List I) (g : I→J) (f : J→C) :
    sumOver (xs.map g) f=sumOver xs (fun i => f (g i)) := by simp only [sumOver,List.map_map,Function.comp_def]
private theorem splitRows {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) {C : Type} [CommRing C] (f : Field3 R n→C) :
    sumOver (singleRows half x y) f=
      sumOver (MixedDefect.oddWords n) (fun p => f (singleCol half x y p))+
      sumOver (MixedDefect.oddWords n) (fun p => f (singleCol half y x p)) := by
  simp only [singleRows,appendSum,mappedSum]
private theorem splitFree {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) {C : Type} [CommRing C] (f : Field3 R n→C) :
    sumOver (freeRows half x y) f=sumOver (qubitIndices n) (fun i =>
      sumOver (MixedDefect.oddWords n) (fun p => f (PhysicalTwoHoleEigen.freeCol half x y i p))) := by
  simp only [freeRows,sumOverFlatMap,mappedSum]
private theorem onSingles {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (G : Field3 R n→Prop)
    (xyRows : ∀p∈MixedDefect.oddWords n,G (singleCol half x y p))
    (yxRows : ∀p∈MixedDefect.oddWords n,G (singleCol half y x p)) :
    ∀a∈singleRows half x y,G a := by
  intro a ha
  rcases List.mem_append.mp ha with l | r
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp l; exact xyRows p hp
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp r; exact yxRows p hp

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
private theorem energyNonnegative {n : Nat} (F : Field3 R n) : 0≤energy F :=
  Compression.sumOverNonnegative _ _ (fun _ _ => normSq_nonnegative _)
private theorem energyNull {n : Nat} (a : Field3 R n) (ha : energy a=0) (w : Field3 R n) : gram3 (qubitIndices n) a w=0 := by
  let L := qubitIndices n
  have atZero (i j k : Basis n) : a i j k=0 := by
    by_cases zero : a i j k=0
    · exact zero
    · have mem : ((i,j),k)∈triples L := List.mem_flatMap.mpr ⟨(i,j),HyperplaneInduction.pairMember (qubitIndicesComplete i) (qubitIndicesComplete j),List.mem_map.mpr ⟨k,qubitIndicesComplete k,rfl⟩⟩
      have pos : 0<energy a := ComplexExterior.sumPositiveAt (triples L) (fun t => normSq (a t.1.1 t.1.2 t.2))
        (fun _ => normSq_nonnegative _) ((i,j),k) mem (normSq_positive _ zero)
      grind only
  rw [threeRows]; simp only [atZero,show star (0:ComplexScalar R)=0 from star_ofReal (0:R),Semiring.zero_mul]
  have zs (ls : List (Triple (Basis n))) : sumOver ls (fun _ => (0:ComplexScalar R))=0 := by
    induction ls with
    | nil => rfl
    | cons t ls ih => change 0+sumOver ls _=0; rw [ih]; grind only
  exact zs _

/-- The full physical Gram bound on the alternating grade-three test space. -/
theorem physicalTwoHoleUpper (half : R) (unit : 2*half=1) (n : Nat) : FiveFaceCapacity.TwoHoleUpper half n := by
  intro x y xx yy xy F af xn yn
  let L := qubitIndices n
  let H := gram3 (R:=R) L
  let first := singleRows half x y
  let other := freeRows half x y
  have yx : modeGram L y x=0 := by rw [←modeReverse,xy]; exact star_ofReal (0:R)
  have inside : ∀a∈first,slice x y a := by
    apply onSingles
    · intro p hp; rw [singleIsWave half x y p hp]; exact innerSlice half unit x y yy xy _
    · intro p hp; rw [singleIsWave half y x p hp]
      have h := innerSlice half unit y x xx yx (unitWord p)
      exact ⟨h.1,h.2.2,h.2.1⟩
  have observation (a w : Field3 R n) :
      mass H first a w+mass H other a w=PhysicalTwoHoleEigen.totalGram half x y a w := by
    unfold mass first other; rw [splitRows,splitFree]; rfl
  have eigen : ∀a∈first,∀w,slice x y w→mass H first a w+mass H other a w=ofReal (36*half^n)*H a w := by
    apply onSingles
    · intro p hp w hw; rw [observation]; exact PhysicalTwoHoleEigen.physicalEigenX half unit x y xx yy xy w hw.1 hw.2.1 hw.2.2 p hp
    · intro p hp w hw; rw [observation]; exact PhysicalTwoHoleEigen.physicalEigenY half unit x y xx yy xy w hw.1 hw.2.1 hw.2.2 p hp
  have upper (w : Field3 R n) (_ : slice x y w) : costs H other w≤36*half^n*energy w := by
    unfold costs other; rw [splitFree]; exact PhysicalC2Projected.physicalProjectedAdjoint half unit x y xx yy xy w
  have result := ComplexFiniteRangeBound.besselFromEigenRows H energy (slice x y) combine gramSym energyNonnegative
    gramSelf energyNull gramCombination gramCombinationLeft (sliceCombination x y) first other (36*half^n)
    inside eigen upper F ⟨af,xn,yn⟩
  unfold costs first other at result; rw [splitRows,splitFree] at result
  exact result

/-- Every omitted pair in an orthonormal complex seven-frame has physical diagonal mass at most one. -/
theorem physicalOmittedPairCapacity (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (a b : Fin 7) (ab : a<b) :
    PackingDual.rowMass (fun w => (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w) (.omitPair a b)≤1 :=
  FiveFaceCapacity.omittedPairOfTwoHole half unit k (physicalTwoHoleUpper half unit (k+3)) A orth a b ab
end Order
end RankSeven.PhysicalTwoHoleUpper

#print axioms RankSeven.PhysicalTwoHoleUpper.physicalTwoHoleUpper
#print axioms RankSeven.PhysicalTwoHoleUpper.physicalOmittedPairCapacity
