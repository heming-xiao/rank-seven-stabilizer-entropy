import Rank7PhysicalTwoHoleOccupancy

/-! The pair-exchange intertwinings for the actual single- and double-
occupation tensors, including conjugation of the two exchanged covectors. -/
namespace RankSeven.PhysicalTwoHoleExchange
open Lean.Grind Pauli ComplexScalar
open PhysicalTwoHoleOccupancy
open PhysicalUniformOccupation (wave)
open PhysicalHopping (PlaneField)
variable {R : Type} [CommRing R]

def conjugate {I : Type} (x : I→ComplexScalar R) (a : I) := star (x a)

private theorem productSum {I J C : Type} [CommRing C] (xs : List I) (ys : List J) (h : I×J→C) :
    sumOver (productIndices xs ys) h=sumOver xs (fun a => sumOver ys (fun b => h (a,b))) := by
  rw [productIndices,sumOverFlatMap]; apply sumOverCongr; intro a; simp only [sumOver,List.map_map,Function.comp_def]
private theorem pairTerm {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f : Word n→ComplexScalar R) (a b : Basis n) :
    PhysicalHopping.contract (fun k => y k.1*x k.2) (wave half f) (a,b) = twoOccupied half x y f a b := by
  unfold PhysicalHopping.contract PhysicalHopping.edges twoOccupied lower3 anchored PhysicalUniformOccupation.oneHole
  rw [productSum]; apply sumOverCongr; intro c; rw [sumOverMulLeft]; apply sumOverCongr; intro d
  have eq : wave half f ((c,d),(a,b))=wave half f ((a,b),(c,d)) :=
    FiveFrameContractions.waveReorder half f ((a,b),(c,d)) ((2,3),(0,1)) (by decide)
  change y c*x d*wave half f ((c,d),(a,b))=y c*(x d*wave half f ((a,b),(c,d)))
  rw [eq]; grind only

/-- Polarized double contractions of actual Pauli columns obey the
conjugate-pair exchange in ordered two-coordinate normalization. -/
theorem physicalPairGram {n : Nat} (half : R) (x y h k : Basis n→ComplexScalar R) (f g : Word n→ComplexScalar R) :
    gram2 (qubitIndices n) (twoOccupied half x y f) (twoOccupied half h k g)=
    gram2 (qubitIndices n) (twoOccupied half (conjugate h) (conjugate k) f)
      (twoOccupied half (conjugate x) (conjugate y) g) := by
  have field (c : Word n→ComplexScalar R) : PlaneField (wave half c) :=
    PhysicalHopping.fieldCombination _ _ _ (fun p _ => PhysicalHopping.pauliColumnField half p)
  have eq := PhysicalHopping.complexPairExchange (field f) (field g) (fun p => y p.1*x p.2) (fun p => k p.1*h p.2)
  simp only [PhysicalHopping.pairing,PhysicalHopping.edges,productSum,gram2,sum2] at eq ⊢
  have ct (x y : Basis n→ComplexScalar R) (k : Word n→ComplexScalar R) (a b : Basis n) :
      PhysicalHopping.contract (fun p => star (y p.1*x p.2)) (wave half k) (a,b)=twoOccupied half (conjugate x) (conjugate y) k a b := by
    simp only [star_mul]; exact pairTerm half (conjugate x) (conjugate y) k a b
  simpa only [ct,pairTerm] using eq

/-- Lemma 12, the double-occupation component: its Gram kernel is the
same for the two coordinatewise conjugated modes. -/
theorem doubleGramConjugate {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f g : Word n→ComplexScalar R) :
    gram2 (qubitIndices n) (twoOccupied half (conjugate x) (conjugate y) f) (twoOccupied half (conjugate x) (conjugate y) g)=
    gram2 (qubitIndices n) (twoOccupied half x y f) (twoOccupied half x y g) := (physicalPairGram half x y x y f g).symm

private theorem gramZero3 {n : Nat} (half : R) (x y r : Basis n→ComplexScalar R)
    (rh : modeGram (qubitIndices n) r y=0) (f : Word n→ComplexScalar R)
    (e : Basis n→Basis n→ComplexScalar R) (alt : Alt2 e)
    (null : ∀a,lower2 (qubitIndices n) y e a=0) :
    gram3 (qubitIndices n) (oneOccupied half x y f) (raise3 r e)=
    3*gram2 (qubitIndices n) (twoOccupied half x r f) e := by
  let L := qubitIndices n
  have z (a b : Basis n) : lower3 L y (raise3 r e) a b=0 := by
    rw [lowerRaise,modeFlip,rh,null,null]; grind only
  change gram3 L (residual L y (anchored half x f)) (raise3 r e)=_
  rw [subtractLeft,creationAdjoint L r _ _ (anchoredAlternating _ _ _),creationAdjointLeft L y _ _ (raiseAlt r alt),zeroGramRight L z]
  change 3*gram2 L (twoOccupied half x r f) e-3*0=_; grind only

private theorem noX {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R) (g : Word n→ComplexScalar R) (a : Basis n) :
    lower2 (qubitIndices n) x (twoOccupied half x y g) a=0 := by
  let L := qubitIndices n
  change sumOver L (fun b => x b*lower3 L y (anchored half x g) a b)=0
  have swap (b : Basis n) : lower3 L y (anchored half x g) a b= -lower3 L x (anchored half y g) a b := physicalTwoHoleSkew _ _ _ _ _ _
  simp only [swap,Ring.mul_neg]
  have z := lowerSquared half unit L x (anchored half y g) (anchoredAlternating _ _ _) a
  change sumOver L (fun b => -(x b*lower3 L x (anchored half y g) a b))=0
  have neg (xs : List (Basis n)) (v : Basis n→ComplexScalar R) : sumOver xs (fun b => -v b)= -sumOver xs v := by
    induction xs with | nil => change 0= -0; grind only | cons b xs ih => change -v b+sumOver xs _= -(v b+sumOver xs _); rw [ih]; grind only
  rw [neg]; change -lower2 L x (lower3 L x (anchored half y g)) a=0; rw [z]; grind only

/-- Both pair-exchange intertwinings of (204), on an arbitrary physical
free leg orthogonal to the two fixed modes. The factor three converts an
ordered triple pairing to an ordered pair pairing. -/
theorem physicalIntertwinings204 {n : Nat} (half : R) (unit : 2*half=1) (x y r : Basis n→ComplexScalar R)
    (rx : modeGram (qubitIndices n) r x=0) (ry : modeGram (qubitIndices n) r y=0)
    (f g : Word n→ComplexScalar R) :
    let L := qubitIndices n
    let C2 := raise3 r (twoOccupied half x y g)
    let link := twoOccupied half (conjugate x) (conjugate y) f
    gram3 L (oneOccupied half x y f) C2=3*gram2 L link (twoOccupied half (conjugate x) (conjugate r) g) ∧
    gram3 L (oneOccupied half y x f) C2=3*gram2 L link (twoOccupied half (conjugate y) (conjugate r) g) := by
  let L := qubitIndices n
  have alt := lowerAlt L y (anchoredAlternating half x g)
  constructor
  · rw [gramZero3 half x y r ry f (twoOccupied half x y g) alt (lowerSquared half unit L y _ (anchoredAlternating _ _ _)),
      physicalPairGram half x r x y f g]
  · rw [gramZero3 half y x r rx f (twoOccupied half x y g) alt (noX half unit x y g),
      physicalPairGram half y r x y f g]

end RankSeven.PhysicalTwoHoleExchange
#print axioms RankSeven.PhysicalTwoHoleExchange.physicalIntertwinings204
