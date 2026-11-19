import Rank7TwoHolePhysicalTransportIdentity
import Rank7PhysicalTwoHoleOccupancy

/-! Coefficients of the second intertwining on actual Pauli columns.
The input vector of grade three is tested on each ordered coordinate. -/
namespace RankSeven.PhysicalTwoHoleAdjointTransport
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel
open PhysicalCutCapacities (Triple extend)
open PhysicalUniformOccupation (oneHole)
open WedgeSquareIntertwiner (wedgeSquareColumn)
open PhysicalTwoHoleTransport (commonMode direct physicalBilinearTransport)
variable {R : Type} [CommRing R]
attribute [local instance] Ring.intCast

private theorem halfC (half : R) (unit : 2*half=1) : 2*ofReal half=(1:ComplexScalar R) := by
  change ofReal (2:R)*ofReal half=ofReal (1:R)
  apply ComplexScalar.ext <;> simp <;> grind only

def columnGram {n : Nat} (half : R) (u v : Four (Basis n)) :=
    sumOver (MixedDefect.oddWords n) (fun p => wedgeSquareColumn half p u*star (wedgeSquareColumn half p v))

private theorem columnGramKernel {n : Nat} (half : R) (unit : 2*half=1) (u v : Four (Basis n)) :
    columnGram half u v=(3*ofReal half)*exteriorKernel imaginaryUnit (ofReal half) u v := by
  have weight := WedgeSquareIntertwiner.physicalWedgeSquareGram half unit u v
  change 2*columnGram half u v=_ at weight
  have scaled := congrArg (fun z => ofReal half*z) weight
  have hh := halfC half unit
  rw [←Semiring.mul_assoc,CommSemiring.mul_comm (ofReal half) 2,hh,Semiring.one_mul] at scaled
  rw [scaled]; grind only

private def weighted {I : Type} (L : List I) (x y : I→ComplexScalar R) (F : I→I→I→ComplexScalar R) :=
  sumOver L (fun l => star (y l)*sumOver L (fun j => sumOver L (fun k => (star (x j)*star (x k))*F j k l)))

private theorem weightCongr {I : Type} (L : List I) (x y : I→ComplexScalar R) (F G : I→I→I→ComplexScalar R)
    (eq : ∀j k l,F j k l=G j k l) : weighted L x y F=weighted L x y G := by
  rw [show F=G from funext (fun j => funext (fun k => funext (eq j k)))]
private theorem weightScale {I : Type} (L : List I) (x y : I→ComplexScalar R) (F : I→I→I→ComplexScalar R)
    (q : ComplexScalar R) : weighted L x y (fun j k l => q*F j k l)=q*weighted L x y F := by
  unfold weighted; rw [sumOverMulLeft]; apply sumOverCongr; intro l
  have eq (j k : I) : (star (x j)*star (x k))*(q*F j k l) = q*((star (x j)*star (x k))*F j k l) := by grind only
  simp only [eq,←sumOverMulLeft]; grind only
private theorem weightThree {I : Type} (L : List I) (x y : I→ComplexScalar R) (F G H : I→I→I→ComplexScalar R) :
    weighted L x y F-weighted L x y G+weighted L x y H=weighted L x y (fun j k l => F j k l-G j k l+H j k l) := by
  unfold weighted
  have dist (a b c d : ComplexScalar R) : a*(b-c+d)=a*b-a*c+a*d := by grind only
  simp only [dist,sumOverAdd,Compression.sumOverSub]

private theorem orient {n : Nat} (half : R) (unit : 2*half=1) (b s : Basis n×Basis n) (z j k l : Basis n) :
    columnGram half (b,(z,j)) (s,(l,k))=(3*ofReal half)*exteriorKernel imaginaryUnit (ofReal half) ((j,z),b) ((k,l),s) := by
  rw [columnGramKernel half unit]
  have eq := kernel_reorder_equal_signs (n:=n) (imaginaryUnit (R:=R)) (ofReal half) imaginaryUnit_fourth (halfC half unit)
    (b,(z,j)) (s,(l,k)) ((3,2),(0,1)) ((3,2),(0,1)) (by decide) (by decide) rfl
  exact congrArg ((3*ofReal half)*·) eq.symm

private theorem orientDirect {n : Nat} (half : R) (unit : 2*half=1) (b : Basis n×Basis n) (s : Triple (Basis n)) (j k l : Basis n) :
    columnGram half (b,(l,j)) (s.1,(s.2,k))=(3*ofReal half)*direct imaginaryUnit (ofReal half) b s j k l := by
  rw [columnGramKernel half unit]
  have eq := kernel_reorder_equal_signs (n:=n) (imaginaryUnit (R:=R)) (ofReal half) imaginaryUnit_fourth (halfC half unit)
    (b,(l,j)) (s.1,(s.2,k)) ((3,2),(0,1)) ((3,0),(1,2)) (by decide) (by decide) (by decide)
  exact congrArg ((3*ofReal half)*·) eq.symm

private def columnLeg {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (b s : Basis n × Basis n) (z : Basis n) :=
  weighted (qubitIndices n) x y (fun j k l => columnGram half (b,(z,j)) (s,(l,k)))
private def columnDirect {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (b : Basis n × Basis n) (s : Triple (Basis n)) :=
  weighted (qubitIndices n) x y (fun j k l => columnGram half (b,(l,j)) (s.1,(s.2,k)))

private theorem threeLegs {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (b : Basis n × Basis n) (s : Triple (Basis n)) :
    columnLeg half x y b (s.1.2,s.2) s.1.1-columnLeg half x y b (s.1.1,s.2) s.1.2+
    columnLeg half x y b s.1 s.2=columnDirect half x y b s := by
  let L := qubitIndices n
  let h := ofReal half
  let K := exteriorKernel (imaginaryUnit (R:=R)) h (n:=n)
  unfold columnLeg columnDirect
  rw [weightThree,weightCongr _ _ _ _ (fun j k l => (3*h)*commonMode imaginaryUnit h b s j k l) (by
    intro j k l; simp only [orient half unit]; unfold commonMode; dsimp only [h]; grind only),
    weightCongr _ _ _ (fun j k l => columnGram half (b,(l,j)) (s.1,(s.2,k))) _ (orientDirect half unit b s),
    weightScale,weightScale]
  apply congrArg ((3*h)*·)
  exact physicalBilinearTransport imaginaryUnit h imaginaryUnit_fourth (halfC half unit) b s (fun t => star (x t)) (fun t => star (y t))

private theorem sink {P I C : Type} [CommRing C] (ps : List P) (L : List I) (f : P→I→I→I→C) :
    sumOver ps (fun p => sumOver L (fun a => sumOver L (fun b => sumOver L (f p a b))))=
    sumOver L (fun a => sumOver L (fun b => sumOver L (fun c => sumOver ps (fun p => f p a b c)))) := by
  rw [sumOverSwap]; apply sumOverCongr; intro a; rw [sumOverSwap]; apply sumOverCongr; intro b; rw [sumOverSwap]

def columnCut {n : Nat} (half : R) (x : Basis n→ComplexScalar R) (p : Word n) (s : Triple (Basis n)) :=
  oneHole x (wedgeSquareColumn half p) s
def doubleCut {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (s : Basis n × Basis n) :=
  sumOver (qubitIndices n) (fun l => y l*columnCut half x p (s,l))

def mixedAdjointEntry {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (b s : Basis n × Basis n) (z : Basis n) :=
  sumOver (MixedDefect.oddWords n) (fun p =>
    columnCut half (fun a => star (x a)) p (b,z)*star (doubleCut half x y p s))
def directAdjointEntry {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (b : Basis n × Basis n) (s : Triple (Basis n)) :=
  sumOver (MixedDefect.oddWords n) (fun p =>
    doubleCut half (fun a => star (x a)) (fun a => star (y a)) p b*star (columnCut half x p s))

private theorem mixedExpansion {n : Nat} (half : R) (x y : Basis n→ComplexScalar R)
    (b s : Basis n × Basis n) (z : Basis n) : mixedAdjointEntry half x y b s z=columnLeg half x y b s z := by
  unfold mixedAdjointEntry columnLeg weighted columnGram doubleCut columnCut oneHole
  simp only [ComplexExterior.starSumOver,star_mul,sumOverMulRight,sumOverMulLeft]
  rw [sink]; apply sumOverCongr; intro l; rw [sumOverSwap]; apply sumOverCongr; intro j; apply sumOverCongr; intro k; apply sumOverCongr; intro p
  simp only [extend]; grind only

private theorem directExpansion {n : Nat} (half : R) (x y : Basis n→ComplexScalar R)
    (b : Basis n × Basis n) (s : Triple (Basis n)) : directAdjointEntry half x y b s=columnDirect half x y b s := by
  unfold directAdjointEntry columnDirect weighted columnGram doubleCut columnCut oneHole
  simp only [ComplexExterior.starSumOver,star_mul,sumOverMulRight,sumOverMulLeft,←Semiring.mul_assoc]
  rw [sink,sumOverSwap]; apply sumOverCongr; intro l; rw [sumOverSwap]; apply sumOverCongr; intro j; apply sumOverCongr; intro k; apply sumOverCongr; intro p
  simp only [extend]; grind only

/-- Coefficient of the actual physical Pauli-column adjoint intertwining
at a triple input and pair output. The three terms are the three insertion
positions of the coordinate precursor in the double-occupancy synthesis. -/
theorem physicalAdjointTransportEntry {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (b : Basis n × Basis n) (s : Triple (Basis n)) :
    mixedAdjointEntry half x y b (s.1.2,s.2) s.1.1-mixedAdjointEntry half x y b (s.1.1,s.2) s.1.2+
      mixedAdjointEntry half x y b s.1 s.2=directAdjointEntry half x y b s := by
  simp only [mixedExpansion,directExpansion]; exact threeLegs half unit x y b s

open PhysicalTwoHoleOccupancy (gram3 raise3 lower3 residual Alt3 sum3)
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def coord {n : Nat} (z a : Basis n) : ComplexScalar R := if a=z then 1 else 0

private theorem scaleCoord {n : Nat} (s : Basis n) (F : Basis n→ComplexScalar R) :
    sumOver (qubitIndices n) (fun z => coord z s*F z)=F s := by
  rw [←ExteriorPauliBase.sumOnIndex (qubitIndices n) s F (HyperplaneIncidence.normalsNodup n) (qubitIndicesComplete _)]
  apply sumOverCongr; intro z; unfold coord; split <;> grind only

def col2 {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (a b : Basis n) :=
  doubleCut half x y p (a,b)
def col1 {n : Nat} (half : R) (x : Basis n→ComplexScalar R) (p : Word n) (a b c : Basis n) :=
  columnCut half x p ((a,b),c)
def singleCol {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) :=
  residual (qubitIndices n) y (col1 half x p)

private theorem insertions {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (b : Basis n × Basis n) (s : Triple (Basis n)) :
    sumOver (qubitIndices n) (fun z => sumOver (MixedDefect.oddWords n) (fun p =>
      columnCut half (fun a => star (x a)) p (b,z) * star (raise3 (coord z) (col2 half x y p) s.1.1 s.1.2 s.2))) =
      directAdjointEntry half x y b s := by
  rw [←physicalAdjointTransportEntry half unit x y b s,sumOverSwap]
  unfold mixedAdjointEntry; rw [←Compression.sumOverSub,←sumOverAdd]
  apply sumOverCongr; intro p
  let E := col2 half x y p
  let H (z : Basis n) := columnCut half (fun a => star (x a)) p (b,z)
  let L := qubitIndices n
  have each (z : Basis n) : H z*star (raise3 (coord z) E s.1.1 s.1.2 s.2)=
      coord z s.1.1*(H z*star (E s.1.2 s.2))-coord z s.1.2*(H z*star (E s.1.1 s.2))+coord z s.2*(H z*star (E s.1.1 s.1.2)) := by
    have sub (u v : ComplexScalar R) : star (u-v)=star u-star v := by apply ComplexScalar.ext <;> simp <;> grind
    rw [raise3,star_add,sub,star_mul,star_mul,star_mul,star_star,star_star,star_star]; grind only
  change sumOver L (fun z => H z*star (raise3 (coord z) E s.1.1 s.1.2 s.2))=_
  rw [sumOverCongr L each,sumOverAdd,Compression.sumOverSub]
  dsimp only [L]; rw [scaleCoord,scaleCoord,scaleCoord]; rfl

/-- Pauli-synthesis coefficient of the coordinate-mode composition G_x C₂†,
using ordered grade-three pairing. -/
def gAfterC {n : Nat} (half : R) (x y g : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (b : Basis n × Basis n) :=
  sumOver (qubitIndices n) (fun z => sumOver (MixedDefect.oddWords n) (fun p =>
    columnCut half (fun a => star (g a)) p (b,z) * gram3 (qubitIndices n) (raise3 (coord z) (col2 half x y p)) F))
def linkAfterSingle {n : Nat} (half : R) (x y : Basis n→ComplexScalar R)
    (Z : Word n→Basis n→Basis n→Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R)
    (b : Basis n × Basis n) :=
  sumOver (MixedDefect.oddWords n) (fun p => doubleCut half (fun a => star (x a)) (fun a => star (y a)) p b * gram3 (qubitIndices n) (Z p) F)

private theorem sumThroughThree {I U C : Type} [CommRing C] (is : List I) (L : List U)
    (H : I → U → U → U → C) :
    sumOver is (fun i => sum3 L (H i))=sum3 L (fun a b c => sumOver is (fun i => H i a b c)) := sink is L H

private theorem rawGramTransport {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (b : Basis n × Basis n) :
    gAfterC half x y x F b=linkAfterSingle half x y (col1 half x) F b := by
  unfold gAfterC linkAfterSingle gram3
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  have mul3 (c : ComplexScalar R) (G : Basis n→Basis n→Basis n→ComplexScalar R) :
      c*sum3 L G=sum3 L (fun a b t => c*G a b t) := by simp only [sum3,sumOverMulLeft]
  change sumOver L (fun z => sumOver P (fun p => _ * sum3 L _))=sumOver P (fun p => _*sum3 L _)
  simp only [mul3,sumThroughThree]
  unfold sum3; apply sumOverCongr; intro a; apply sumOverCongr; intro c; apply sumOverCongr; intro d
  let s : Triple (Basis n) := ((a,c),d)
  have h := congrArg (fun t => t*F a c d) (insertions half unit x y b s)
  unfold directAdjointEntry at h
  simp only [sumOverMulRight] at h
  simpa only [s,col1,Semiring.mul_assoc] using h

private theorem minusSum {I C : Type} [CommRing C] (L : List I) (f : I→C) :
    sumOver L (fun i => -f i)= -sumOver L f := by
  induction L with | nil => change 0= -0; grind only | cons a L ih => change -f a+sumOver L _= -(f a+sumOver L _); rw [ih]; grind only
private theorem starNeg (z : ComplexScalar R) : star (-z)= -star z := by apply ComplexScalar.ext <;> simp <;> grind only

private theorem doubleCutSkew {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (b : Basis n × Basis n) :
    doubleCut half x y p b= -doubleCut half y x p b := by
  have flip (c d : Basis n) : wedgeSquareColumn (R:=R) half p (b,(d,c))= -wedgeSquareColumn half p (b,(c,d)) := by
    let perm : ExteriorPauliBase.Permutation := ((0,1),(3,2))
    have raw := AlternatingTrace.alternatingRow (PhysicalMixedFrame.doubledWord (R:=R) p) perm (by decide) (b,(c,d))
    change WedgeSquareIntertwiner.alternatingWord p (b,(d,c))=
      Int.cast (R:=ComplexScalar R) (-1)*WedgeSquareIntertwiner.alternatingWord p (b,(c,d)) at raw
    unfold wedgeSquareColumn; rw [raw]; grind only
  unfold doubleCut columnCut oneHole; simp only [extend,sumOverMulLeft]
  rw [sumOverSwap,←minusSum]; apply sumOverCongr; intro c; rw [←minusSum]; apply sumOverCongr; intro d
  rw [flip c d]; grind only

private theorem swapG {n : Nat} (half : R) (x y r : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (b : Basis n × Basis n) :
    gAfterC half x y r F b= -gAfterC half y x r F b := by
  let L := qubitIndices n
  have raised (z : Basis n) (p : Word n) (a c d : Basis n) :
      raise3 (coord z) (col2 half x y p) a c d= -raise3 (coord z) (col2 half y x p) a c d := by
    unfold raise3 col2
    rw [doubleCutSkew half x y p (c,d),doubleCutSkew half x y p (a,d),doubleCutSkew half x y p (a,c)]; grind only
  have gram (z : Basis n) (p : Word n) :
      gram3 L (raise3 (coord z) (col2 half x y p)) F= -gram3 L (raise3 (coord z) (col2 half y x p)) F := by
    simp only [gram3,sum3,raised,starNeg,Ring.neg_mul,minusSum]
  unfold gAfterC
  change (sumOver L (fun z => sumOver _ (fun p => _*gram3 L (raise3 (coord z) (col2 half x y p)) F)))=_
  simp only [gram,Ring.mul_neg,minusSum]; rfl

private theorem swapL {n : Nat} (half : R) (x y : Basis n→ComplexScalar R)
    (Z : Word n→Basis n→Basis n→Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R) (b : Basis n × Basis n) :
    linkAfterSingle half x y Z F b= -linkAfterSingle half y x Z F b := by
  unfold linkAfterSingle
  simp only [doubleCutSkew half (fun a => star (x a)) (fun a => star (y a)),Ring.neg_mul,minusSum]

private theorem readoutResidual {n : Nat} (half : R) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (alt : Alt3 F)
    (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (p : Word n) :
    gram3 (qubitIndices n) (singleCol half x y p) F=gram3 (qubitIndices n) (col1 half x p) F := by
  unfold singleCol
  rw [PhysicalTwoHoleOccupancy.subtractLeft,PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt,PhysicalTwoHoleOccupancy.zeroGramRight _ yn]
  grind only

/-- Lemma 13 on the physical odd-Pauli coefficient family, for an
arbitrary alternating triple in the common x,y complement. The free
precursor sum is in the full computational basis. -/
theorem physicalAdjointIntertwinings {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (alt : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0)
    (b : Basis n × Basis n) :
    gAfterC half x y x F b=linkAfterSingle half x y (singleCol half x y) F b ∧
    gAfterC half x y y F b=linkAfterSingle half x y (singleCol half y x) F b := by
  have xh := rawGramTransport half unit x y F b
  have yh := rawGramTransport half unit y x F b
  constructor
  · simpa only [linkAfterSingle,readoutResidual half x y F alt yn] using xh
  · rw [swapG half x y y,swapL half x y,yh]
    simp only [linkAfterSingle,readoutResidual half y x F alt xn]

end RankSeven.PhysicalTwoHoleAdjointTransport
#print axioms RankSeven.PhysicalTwoHoleAdjointTransport.physicalAdjointIntertwinings
#print axioms RankSeven.PhysicalTwoHoleAdjointTransport.physicalAdjointTransportEntry
