import Rank7PhysicalC2Canonical
import Rank7PhysicalTwoHoleAdjointTransport
import Rank7PhysicalOmittedPair

/-! Testing the two-hole upper bound on a decomposable triple formed
by the last three of the five physical columns. -/
namespace RankSeven.FiveFaceTest
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel
open PhysicalCutCapacities (Triple triples columnCoef)
open PhysicalTwoHoleOccupancy (modeGram gram3 gram2 raise3 lower3 Alt3 Alt2 sum3 sum2)
open PhysicalTwoHoleAdjointTransport (col1 col2 singleCol coord)
variable {R I : Type} [CommRing R]
def pair (u v : I→ComplexScalar R) (a b : I) := u a*v b-u b*v a
def dual (u : I→ComplexScalar R) (a : I) := star (u a)
def triple (u v w : I→ComplexScalar R) := raise3 (dual u) (pair v w)
def form (A : I→Fin 7→ComplexScalar R) (i : Fin 7) := fun a => A a i
theorem tripleAlternating (u v w : I→ComplexScalar R) : Alt3 (triple u v w) := by
  constructor <;> intro a b c <;> simp only [triple,raise3,dual,star_star,pair] <;> grind only
private theorem starSub (a b : ComplexScalar R) : star (a-b)=star a-star b := by apply ComplexScalar.ext <;> simp <;> grind only
private theorem negativeSum {B : Type} (xs : List B) (F : B→ComplexScalar R) : sumOver xs (fun i => -F i)= -sumOver xs F := by
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem realSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun t => (f t).re) := by
  induction xs with
  | nil => rfl
  | cons a as ih => change (f a+sumOver as f).re=(f a).re+_; rw [re_add,ih]; rfl

theorem lowerVolume (L : List I) (t u v w : I→ComplexScalar R) (a b : I) :
    lower3 L (dual t) (triple u v w) a b=
    modeGram L t u*pair v w a b-modeGram L t v*pair u w a b+modeGram L t w*pair u v a b := by
  unfold lower3
  have row (c : I) : dual t c*triple u v w a b c=
      (star (t c)*u c)*pair v w a b-(star (t c)*v c)*pair u w a b+(star (t c)*w c)*pair u v a b := by
    simp only [triple,dual,raise3,star_star,pair]; grind only
  rw [sumOverCongr L row]; simp only [sumOverAdd,Compression.sumOverSub,←sumOverMulRight,modeGram]

private theorem pairTest (L : List I) (u v : I→ComplexScalar R) (F : I→I→ComplexScalar R) (skew : Alt2 F) :
    gram2 L (pair u v) F=2*sum2 L (fun a b => star (u a)*star (v b)*F a b) := by
  unfold gram2 sum2
  have row (a b) : star (pair u v a b)*F a b=star (u a)*star (v b)*F a b-star (u b)*star (v a)*F a b := by
    unfold pair; rw [starSub,star_mul,star_mul]; grind only
  simp only [row,Compression.sumOverSub]
  have s : sumOver L (fun a => sumOver L (fun b => star (u b)*star (v a)*F a b))=
      -sumOver L (fun a => sumOver L (fun b => star (u a)*star (v b)*F a b)) := by
    rw [sumOverSwap,←negativeSum]; apply sumOverCongr; intro a; rw [←negativeSum]; apply sumOverCongr; intro b
    rw [skew a b,Ring.mul_neg]
  rw [s]; grind only
theorem pairGram (L : List I) (u v w z : I→ComplexScalar R) :
    gram2 L (pair u v) (pair w z)=2*(modeGram L u w*modeGram L v z-modeGram L u z*modeGram L v w) := by
  have h (a b) : pair w z b a= -pair w z a b := by unfold pair; grind only
  rw [pairTest L u v _ h]; unfold sum2
  have row (a b) : star (u a)*star (v b)*pair w z a b=
    (star (u a)*w a)*(star (v b)*z b)-(star (u a)*z a)*(star (v b)*w b) := by unfold pair; grind only
  simp only [row,Compression.sumOverSub,←sumOverMulLeft,←sumOverMulRight,modeGram]
theorem gramSwap3 (L : List I) (u v : I→I→I→ComplexScalar R) : star (gram3 L u v)=gram3 L v u := by
  simp only [gram3,sum3,ComplexExterior.starSumOver,star_mul,star_star]; apply sumOverCongr; intro a
  apply sumOverCongr; intro b; apply sumOverCongr; intro c; grind only
theorem gramSwap2 (L : List I) (u v : I→I→ComplexScalar R) : star (gram2 L u v)=gram2 L v u := by
  simp only [gram2,sum2,ComplexExterior.starSumOver,star_mul,star_star]; apply sumOverCongr; intro a
  apply sumOverCongr; intro b; grind only
private theorem productSum {C U V : Type} [CommRing C] (xs : List U) (ys : List V) (F : U × V → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def volume (A : I→Fin 7→ComplexScalar R) := triple (form A 2) (form A 3) (form A 4)
theorem volumeLower {n} (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) (i : Fin 7) (a b : Basis n) :
    lower3 (qubitIndices n) (dual (form A i)) (volume A) a b=
    (if i=2 then 1 else 0)*pair (form A 3) (form A 4) a b-
    (if i=3 then 1 else 0)*pair (form A 2) (form A 4) a b+
    (if i=4 then 1 else 0)*pair (form A 2) (form A 3) a b := by
  change lower3 _ _ (triple _ _ _) _ _=_; rw [lowerVolume]; simp only [modeGram,form]; rw [orth,orth,orth]
theorem volumeEnergy {n} (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    sumOver (triples (qubitIndices n)) (fun u => normSq (volume A u.1.1 u.1.2 u.2))=6 := by
  let L := qubitIndices n
  let F := volume A
  have lower : lower3 L (dual (form A 2)) F=pair (form A 3) (form A 4) := by
    funext a b; rw [volumeLower _ orth]; simp only [Fin.reduceEq,ite_false,ite_true]; grind only
  have norm : gram3 L F F=6 := by
    change gram3 L (raise3 _ _) F=6
    have alt : Alt3 F := tripleAlternating _ _ _
    rw [PhysicalTwoHoleOccupancy.creationAdjointLeft L _ F _ alt,lower,pairGram]
    simp only [modeGram,form,L]; rw [orth,orth,orth,orth]; simp only [Fin.reduceEq,ite_false,ite_true]; grind only
  have qr := congrArg ComplexScalar.re norm
  change (gram3 L F F).re=(ofReal (6:R)).re at qr
  simp only [gram3,sum3,realSum,re_star_mul_self,re_ofReal] at qr
  simpa only [triples,productSum,F,L] using qr

private theorem gPerm {n} (half : R) (p : Word n) (u : Four (Basis n)) (q : ExteriorPauliBase.Permutation)
    (hq : q∈ExteriorPauliBase.permutations) (sign : ExteriorPauliBase.oddPermutation q=true) :
    WedgeSquareIntertwiner.wedgeSquareColumn half p (reorder u q)= -WedgeSquareIntertwiner.wedgeSquareColumn half p u := by
  unfold WedgeSquareIntertwiner.wedgeSquareColumn WedgeSquareIntertwiner.alternatingWord
  simp only [AlternatingTrace.alternatingRow _ q hq,FourCopySectors.coefficient,sign,ite_true,Ring.intCast_neg,Ring.intCast_one]; grind only
theorem oneSkew {n} (half : R) (x : Basis n→ComplexScalar R) (p : Word n) : Alt3 (col1 half x p) := by
  have s (a b c t : Basis n) : WedgeSquareIntertwiner.wedgeSquareColumn half p ((b,a),(c,t))= -WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),(c,t)) :=
    gPerm half p ((a,b),(c,t)) ((1,0),(2,3)) (by decide) (by decide)
  have t (a b c d : Basis n) : WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,c),(b,d))= -WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),(c,d)) :=
    gPerm half p ((a,b),(c,d)) ((0,2),(1,3)) (by decide) (by decide)
  constructor
  · intro a b c; unfold col1 PhysicalTwoHoleAdjointTransport.columnCut PhysicalUniformOccupation.oneHole PhysicalCutCapacities.extend
    rw [sumOverCongr _ (g:=fun d => -(x d*WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),(c,d)))) (by intro d; rw [s]; exact Ring.mul_neg _ _),negativeSum]
  · intro a b c; unfold col1 PhysicalTwoHoleAdjointTransport.columnCut PhysicalUniformOccupation.oneHole PhysicalCutCapacities.extend
    rw [sumOverCongr _ (g:=fun d => -(x d*WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),(c,d)))) (by intro d; rw [t]; exact Ring.mul_neg _ _),negativeSum]
theorem twoSkew {n} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) : Alt2 (col2 half x y p) := by
  intro a b; change sumOver _ (fun t => y t* col1 half x p b a t)=_
  change sumOver _ (fun t => y t*col1 half x p b a t)= -sumOver _ (fun t => y t*col1 half x p a b t)
  rw [←negativeSum]; apply sumOverCongr; intro t; rw [(oneSkew half x p).1 a b t,Ring.mul_neg]

/-- The pairing of a physical two-occupied Pauli column with an
orthonormal two-volume is twice its complex four-mode coefficient. -/
theorem twoExtract {n} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (a b c d : Fin 7) (p : Word n) :
    gram2 (qubitIndices n) (pair (form A a) (form A b)) (col2 half (dual (form A d)) (dual (form A c)) p)=
    2*columnCoef half A ((a,b),(c,d)) p := by
  rw [pairTest _ _ _ _ (twoSkew _ _ _ _)]; apply congrArg (fun z : ComplexScalar R => 2*z)
  change sum2 _ (fun i j => star (A i a)*star (A j b)*(sumOver (qubitIndices n) (fun k => star (A k c)*sumOver _ (fun l => star (A l d)*WedgeSquareIntertwiner.wedgeSquareColumn half p ((i,j),(k,l))))))=
    sumOver (fourIndices (qubitIndices n)) (fun u => star (tensorFour A u ((a,b),(c,d)))*WedgeSquareIntertwiner.wedgeSquareColumn half p u)
  unfold sum2 fourIndices; simp only [productSum,sumOverMulLeft]
  apply sumOverCongr; intro i; apply sumOverCongr; intro j; apply sumOverCongr; intro k; apply sumOverCongr; intro l
  unfold tensorFour tensor; simp only [star_mul]; grind only
theorem oneExtract {n} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (a b c d : Fin 7) (p : Word n) :
    gram3 (qubitIndices n) (triple (form A c) (form A a) (form A b)) (col1 half (dual (form A d)) p)=
    6*columnCoef half A ((a,b),(c,d)) p := by
  change gram3 _ (raise3 _ _) _=_
  rw [PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ (oneSkew _ _ _)]
  change 3*gram2 _ _ (col2 half (dual (form A d)) (dual (form A c)) p)=_
  rw [twoExtract]; grind only

end RankSeven.FiveFaceTest
#print axioms RankSeven.FiveFaceTest.volumeEnergy
#print axioms RankSeven.FiveFaceTest.oneExtract
