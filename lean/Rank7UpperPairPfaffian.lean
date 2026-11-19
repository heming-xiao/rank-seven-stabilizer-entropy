import Rank7PauliPairContraction
import Rank7OddSkewContraction
import Rank7UpperFrameReplay

namespace RankSeven.UpperPairPfaffian
open Lean.Grind Pauli ComplexScalar ExteriorPauliBase GenericExteriorKernel FourCopySectors
open PhysicalCutCapacities JointProbePayment
open PauliPairContraction (image normSum)
variable {R : Type} [CommRing R]
attribute [local instance] Ring.intCast
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

theorem wordSkew {n : Nat} (p : Word n) (hp : p ∈ MixedDefect.oddWords n) (x y : Basis n) :
    wordEntry (imaginaryUnit (R:=R)) p y x = -wordEntry imaginaryUnit p x y := by
  have s : (wordSign p : ComplexScalar R) = -1 := by
    rw [MixedDefect.oddWordTransposeSign,(List.mem_filter.mp hp).2]; rfl
  rw [wordEntryTranspose imaginaryUnit p y x,s]; grind only

private theorem signedMatching {C α : Type} [CommRing C] (M : α → α → C)
    (sk : ∀ i j, M j i = -M i j) (a b c d : α) :
    act (coefficient .antisymmetric) (fun t => M t.1.1 t.1.2*M t.2.1 t.2.2) ((a,b),c,d) =
      8*(M a b*M c d-M a c*M b d+M a d*M b c) := by
  let plus : C := Int.cast (1:Int)
  let minus : C := Int.cast (-1:Int)
  have op : plus = 1 := Ring.intCast_one
  have om : minus = -1 := by change Int.cast (R:=C) (-(1:Int)) = -1; rw [Ring.intCast_neg,Ring.intCast_one]
  change plus*(M a b*M c d)+(minus*(M a b*M d c)+(minus*(M a c*M b d)+(plus*(M a c*M d b)+(plus*(M a d*M b c)+(minus*(M a d*M c b)+(minus*(M b a*M c d)+(plus*(M b a*M d c)+(plus*(M b c*M a d)+(minus*(M b c*M d a)+(minus*(M b d*M a c)+(plus*(M b d*M c a)+(plus*(M c a*M b d)+(minus*(M c a*M d b)+(minus*(M c b*M a d)+(plus*(M c b*M d a)+(plus*(M c d*M a b)+(minus*(M c d*M b a)+(minus*(M d a*M b c)+(plus*(M d a*M c b)+(plus*(M d b*M a c)+(minus*(M d b*M c a)+(minus*(M d c*M a b)+(plus*(M d c*M b a)+(0)))))))))))))))))))))))) = _
  rw [op,om,sk a b,sk a c,sk a d,sk b c,sk b d,sk c d]
  grind only

private theorem ofReal_mul (a b : R) : ofReal (a*b)=ofReal a*ofReal b := by apply ComplexScalar.ext <;> simp <;> grind only

theorem physicalColumnPfaffian {n : Nat} (half : R) (unit : 2*half=1)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) (a b c d : Basis n) :
    let M := wordEntry (imaginaryUnit (R:=R)) p
    WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),c,d) =
      ofReal (2*half^n)*(M a b*M c d-M a c*M b d+M a d*M b c) := by
  let h := ofReal half
  have two : (2:ComplexScalar R)*h=1 := by
    change ofReal (2:R)*ofReal half=ofReal (1:R); rw [←ofReal_mul,unit]
  have coef : h^(n+2)*8=ofReal (2*half^n) := by
    rw [Semiring.pow_add,ofReal_mul,PhysicalPairedReduction.realEmbeddingPow]
    change h^n*h^2*8=2*h^n
    have sq := congrArg (fun z : ComplexScalar R => z*z) two
    change 2*h*(2*h)=1*1 at sq
    grind only
  change h^(n+2)*(act (coefficient .antisymmetric) (fun t =>
    wordEntry imaginaryUnit p t.1.1 t.1.2*wordEntry imaginaryUnit p t.2.1 t.2.2) ((a,b),c,d))=_
  rw [signedMatching _ (wordSkew p hp),←coef]; grind only

private theorem pairSum {C α β : Type} [CommRing C] (xs : List α) (ys : List β) (f : α×β→C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def pauliLeg {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (t : Basis n) (i : Fin 7) :=
  sumOver (qubitIndices n) (fun a => star (A a i)*wordEntry imaginaryUnit p a t)
def pair {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (i j : Fin 7) :=
  star (pairAmplitude A p i j)

theorem pairFromLeg {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (i j : Fin 7) :
    sumOver (qubitIndices n) (fun t => star (A t j)*pauliLeg A p t i)=pair A p i j := by
  unfold pair pairAmplitude PhysicalMixedFrame.pairs pauliLeg
  simp only [pairSum,ComplexExterior.starSumOver,star_mul,PhysicalMixedFrame.dual,ComplexPauliMoment.wordHermitian,sumOverMulLeft]
  rw [sumOverSwap]; apply sumOverCongr; intro a; apply sumOverCongr; intro b; grind only

private theorem threeSum {C α : Type} [CommRing C] (xs : List α) (f g h : α → C)
    (P : α → α → C) (t : α) :
    sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun c =>
      (f a*g b*h c)*(P a b*P c t-P a c*P b t+P a t*P b c)))) =
      (sumOver xs (fun a => f a*sumOver xs (fun b => g b*P a b)))*(sumOver xs (fun c => h c*P c t))-
      (sumOver xs (fun a => f a*sumOver xs (fun c => h c*P a c)))*(sumOver xs (fun b => g b*P b t))+
      (sumOver xs (fun b => g b*sumOver xs (fun c => h c*P b c)))*(sumOver xs (fun a => f a*P a t)) := by
  let A a b c := (f a*g b*h c)*(P a b*P c t)
  let B a b c := (f a*g b*h c)*(P a c*P b t)
  let D a b c := (f a*g b*h c)*(P a t*P b c)
  have re (a b c : α) : (f a*g b*h c)*(P a b*P c t-P a c*P b t+P a t*P b c)=A a b c-B a b c+D a b c := by dsimp [A,B,D]; grind only
  simp only [re,sumOverAdd,Compression.sumOverSub]
  congr 1
  · congr 1
    · conv => lhs; arg 2; intro a; rw [sumOverSwap]
      conv => lhs; rw [sumOverSwap]
      simp only [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro c; apply sumOverCongr; intro a; apply sumOverCongr; intro b; dsimp [A]; grind only
    · conv => lhs; rw [sumOverSwap]
      simp only [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro b; apply sumOverCongr; intro a; apply sumOverCongr; intro c; dsimp [B]; grind only
  · simp only [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro c; dsimp [D]; grind only

theorem anchoredLeg {n : Nat} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) (i j l : Fin 7) (t : Basis n) :
    leg half A ((i,j),l) t p = ofReal (2*half^n)*
      (pair A p i j*pauliLeg A p t l-pair A p i l*pauliLeg A p t j+pair A p j l*pauliLeg A p t i) := by
  let L := qubitIndices n
  let P := wordEntry (imaginaryUnit (R:=R)) p
  let f (i : Fin 7) (a : Basis n) := star (A a i)
  have pairs (r s : Fin 7) : pair A p r s=sumOver L (fun a => f r a*sumOver L (fun b => f s b*P a b)) := by
    rw [←pairFromLeg]; unfold pauliLeg; rw [sumOverCongr L (g:=fun t => sumOver L (fun a => f r a*(f s t*P a t))) (fun t => by
      rw [sumOverMulLeft]; apply sumOverCongr; intro a; dsimp [f,P]; grind only),sumOverSwap]
    simp only [sumOverMulLeft]
  change sumOver (triples L) (fun z => star (tensorThree A z ((i,j),l))*WedgeSquareIntertwiner.wedgeSquareColumn half p (extend z t))=_
  unfold triples
  simp only [pairSum,tensorThree,extend,star_mul,physicalColumnPfaffian half unit p hp]
  have re (a b c : Basis n) : (f i a*f j b*f l c)*(ofReal (2*half^n)*(P a b*P c t-P a c*P b t+P a t*P b c)) =
    ofReal (2*half^n)*((f i a*f j b*f l c)*(P a b*P c t-P a c*P b t+P a t*P b c)) := by grind only
  change sumOver L (fun a => sumOver L (fun b => sumOver L (fun c => (f i a*f j b*f l c)*(ofReal (2*half^n)*(P a b*P c t-P a c*P b t+P a t*P b c)))))=_
  simp only [re,←sumOverMulLeft,threeSum,pairs,pauliLeg]
  rfl

private theorem negStar (u : ComplexScalar R) : star (-u) = -star u := by apply ComplexScalar.ext <;> simp
theorem pairSkew {n} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (hp : p∈MixedDefect.oddWords n) (i j : Fin 7) :
    pair A p j i= -pair A p i j := by unfold pair; rw [PauliPairContraction.amplitudeSkew A p hp i j,negStar]

theorem anchoredColumn {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) (i j l m : Fin 7) :
    columnCoef half A ((i,j),l,m) p = ofReal (2*half^n)*
      (pair A p i j*pair A p l m-pair A p i l*pair A p j m+pair A p j l*pair A p i m) := by
  change columnCoef half A (extend ((i,j),l) m) p = _
  rw [coefficientFromLeg half A ((i,j),l) m p]
  simp only [anchoredLeg half unit A p hp]
  have f (t : Basis n) : star (A t m)*(ofReal (2*half^n)*(pair A p i j*pauliLeg A p t l-pair A p i l*pauliLeg A p t j+pair A p j l*pauliLeg A p t i)) =
      ofReal (2*half^n)*(pair A p i j*(star (A t m)*pauliLeg A p t l)-pair A p i l*(star (A t m)*pauliLeg A p t j)+pair A p j l*(star (A t m)*pauliLeg A p t i)) := by grind only
  simp only [f,←sumOverMulLeft,sumOverAdd,Compression.sumOverSub,pairFromLeg]

theorem anchoredSkew {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) (i j : Fin 7) :
    columnCoef half A ((0,1),i,j) p = -columnCoef half A ((0,1),j,i) p := by
  rw [anchoredColumn half unit A p hp,anchoredColumn half unit A p hp,pairSkew A p hp j i]
  grind only

end RankSeven.UpperPairPfaffian
#print axioms RankSeven.UpperPairPfaffian.physicalColumnPfaffian
#print axioms RankSeven.UpperPairPfaffian.anchoredLeg
#print axioms RankSeven.UpperPairPfaffian.anchoredColumn
#print axioms RankSeven.UpperPairPfaffian.anchoredSkew
