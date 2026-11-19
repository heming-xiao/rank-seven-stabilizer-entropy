import Rank7TwoHoleEigenInputs
import Rank7PhysicalProjectedTransport

/-! On each genuine single-occupied Pauli column the full two-hole
Gram operator has eigenvalue 36/d in full ordered coordinates. -/
namespace RankSeven.PhysicalTwoHoleEigen
open Lean.Grind Pauli ComplexScalar TwoHoleEigenInputs
open PhysicalTwoHoleOccupancy (gram3 gram2 modeGram lower3 Alt3 raise3)
open PhysicalTwoHoleAdjointTransport (singleCol col2 doubleCut linkAfterSingle)
open PhysicalProjectedTransport (projectedG)
open PhysicalC2Projected (free)
open WedgeSquareIntertwiner (wedgeSquareColumn)
open PhysicalWaveReproduction (gramFour)
variable {R I J : Type} [CommRing R]
noncomputable local instance {n} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

noncomputable def freeCol {n} (half : R) (x y : Basis n→ComplexScalar R) (i : Basis n) (p : Word n) :=
  raise3 (free x y i) (col2 half x y p)
def readProduct (L : List I) (U H F : I→I→I→ComplexScalar R) := gram3 L U H*gram3 L H F
noncomputable def totalGram {n} (half : R) (x y : Basis n→ComplexScalar R) (U F : Basis n→Basis n→Basis n→ComplexScalar R) :=
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  sumOver P (fun p => readProduct L U (singleCol half x y p) F)+
  sumOver P (fun p => readProduct L U (singleCol half y x p) F)+
  sumOver L (fun i => sumOver P (fun p => readProduct L U (freeCol half x y i p) F))

private theorem throughGram (L : List I) (js : List J) (E : I→I→ComplexScalar R) (H : J→I→I→ComplexScalar R) (z : J→ComplexScalar R) :
    sumOver js (fun j => gram2 L E (H j)*z j)=gram2 L E (fun a b => sumOver js (fun j => H j a b*z j)) := by
  unfold gram2 PhysicalTwoHoleOccupancy.sum2; simp only [sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap]; apply sumOverCongr; intro a; rw [sumOverSwap]; apply sumOverCongr; intro b
  apply sumOverCongr; intro j; grind only
private theorem throughTwice {K : Type} (L : List I) (js : List J) (ks : List K) (E : I→I→ComplexScalar R)
    (H : J→K→I→I→ComplexScalar R) (z : J→K→ComplexScalar R) :
    sumOver js (fun j => sumOver ks (fun k => 3*gram2 L E (H j k)*z j k))=
    3*gram2 L E (fun a b => sumOver js (fun j => sumOver ks (fun k => H j k a b*z j k))) := by
  have inner (j) : sumOver ks (fun k => 3*gram2 L E (H j k)*z j k)=
      3*gram2 L E (fun a b => sumOver ks (fun k => H j k a b*z j k)) := by
    rw [sumOverCongr ks (g:=fun k => 3*(gram2 L E (H j k)*z j k)) (fun _ => Semiring.mul_assoc _ _ _),←sumOverMulLeft,throughGram]
  rw [sumOverCongr js inner,←sumOverMulLeft]
  apply congrArg (fun u : ComplexScalar R => 3*u)
  simpa only [Semiring.mul_one] using
    throughGram L js E (fun j a b => sumOver ks (fun k => H j k a b*z j k)) (fun _ => (1:ComplexScalar R))
private theorem sumMember (xs : List I) (f g : I→ComplexScalar R) (h : ∀i∈xs,f i=g i) : sumOver xs f=sumOver xs g := by
  exact congrArg List.sum (List.map_congr_left h)
private theorem zeroSum (xs : List I) : sumOver xs (fun _ => (0:ComplexScalar R))=0 := by
  induction xs with | nil => rfl | cons a as ih => change 0+sumOver as _=0; rw [ih]; grind only

private theorem freePayment {n} (half : R) (x y g h : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (p : Word n) (hp : p∈MixedDefect.oddWords n)
    (direct : ∀i q,q∈MixedDefect.oddWords n →
      gram3 (qubitIndices n) (singleCol half g h p) (freeCol half x y i q)=
      3*gram2 (qubitIndices n) (col2 half (fun a => star (x a)) (fun a => star (y a)) p)
        (col2 half (fun a => star (g a)) (fun a => star (free x y i a)) q))
    (adj : ∀b,projectedG half x y g F b=linkAfterSingle half x y (singleCol half g h) F b) :
    sumOver (qubitIndices n) (fun i => sumOver (MixedDefect.oddWords n) (fun q =>
      readProduct (qubitIndices n) (singleCol half g h p) (freeCol half x y i q) F))=
    3*sumOver (MixedDefect.oddWords n) (fun q => gram2 (qubitIndices n) (col2 half x y p) (col2 half x y q)*
      gram3 (qubitIndices n) (singleCol half g h q) F) := by
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  let Z (i : Basis n) (q : Word n) := gram3 L (freeCol half x y i q) F
  let E (q : Word n) := col2 half (fun t => star (x t)) (fun t => star (y t)) q
  let H (i : Basis n) (q : Word n) := col2 half (fun t => star (g t)) (fun t => star (free x y i t)) q
  let Single (q : Word n) := gram3 L (singleCol half g h q) F
  have sumRow (i : Basis n) : sumOver P (fun q => readProduct L (singleCol half g h p) (freeCol half x y i q) F)=
      sumOver P (fun q => 3*gram2 L (E p) (H i q)*Z i q) := by
    apply sumMember; intro q hq; unfold readProduct; rw [direct i q hq]
  rw [sumOverCongr L sumRow,throughTwice]
  have transposed : (fun a b => sumOver L (fun i => sumOver P (fun q => H i q a b*Z i q)))=
       (fun a b => sumOver P (fun q => E q a b*Single q)) := by funext a b; exact adj (a,b)
  rw [transposed,←throughGram]; apply congrArg (fun u : ComplexScalar R => 3*u)
  apply sumMember; intro q hq; apply congrArg (fun t : ComplexScalar R => t*Single q)
  exact conjugateLinkGram half x y p q hp hq

private theorem measured (js : List J) (h : ComplexScalar R) (D Q z : J→ComplexScalar R) :
    sumOver js (fun j => (h*D j-3*Q j)*z j)+3*sumOver js (fun j => Q j*z j)=h*sumOver js (fun j => D j*z j) := by
  have eq (j) : (h*D j-3*Q j)*z j=h*(D j*z j)-3*(Q j*z j) := by grind only
  rw [sumOverCongr js eq,Compression.sumOverSub,←sumOverMulLeft,←sumOverMulLeft]; grind only

private theorem singlePayment {n} (half : R) (unit : 2*half=1) (x y g h : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F) (hn : ∀a b,lower3 (qubitIndices n) h F a b=0)
    (p : Word n)
    (single : ∀q,q∈MixedDefect.oddWords n → gram3 (qubitIndices n) (singleCol half g h p) (singleCol half g h q)=
      (ofReal half)^n*gramFour (wedgeSquareColumn half p) (wedgeSquareColumn half q)-3*gram2 (qubitIndices n) (col2 half x y p) (col2 half x y q)) :
    sumOver (MixedDefect.oddWords n) (fun q => readProduct (qubitIndices n) (singleCol half g h p) (singleCol half g h q) F)+
    3*sumOver (MixedDefect.oddWords n) (fun q => gram2 (qubitIndices n) (col2 half x y p) (col2 half x y q)*gram3 (qubitIndices n) (singleCol half g h q) F)=
    ofReal (36*half^n)*gram3 (qubitIndices n) (singleCol half g h p) F := by
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  let D (q) := gramFour (wedgeSquareColumn half p) (wedgeSquareColumn half q)
  let Q (q) := gram2 L (col2 half x y p) (col2 half x y q)
  let z (q) := gram3 L (singleCol half g h q) F
  have eq : sumOver P (fun q => readProduct L (singleCol half g h p) (singleCol half g h q) F)=
      sumOver P (fun q => ((ofReal half)^n*D q-3*Q q)*z q) := by
    apply sumMember; intro q hq; unfold readProduct; rw [single q hq]
  rw [eq,measured]; have rep : sumOver P (fun q => D q*z q)=36*z p := reproduceReadout half unit g h F af hn p
  have emb (a b : R) : ofReal (a*b)= ofReal a*ofReal b := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [rep,emb,PhysicalPairedReduction.realEmbeddingPow]
  change (ofReal half)^n*(36*z p)=((36:ComplexScalar R)*(ofReal half)^n)*z p; grind only
private theorem crossedZero {n} (U F : Basis n→Basis n→Basis n→ComplexScalar R)
    (V : Word n→Basis n→Basis n→Basis n→ComplexScalar R) (zero : ∀q,q∈MixedDefect.oddWords n → gram3 (qubitIndices n) U (V q)=0) :
    sumOver (MixedDefect.oddWords n) (fun q => readProduct (qubitIndices n) U (V q) F)=0 := by
  rw [←zeroSum (R:=R) (MixedDefect.oddWords n)]; apply sumMember; intro q hq; unfold readProduct; rw [zero q hq,Semiring.zero_mul]

/-- Equation (210) on the first physical single-occupied column. -/
theorem physicalEigenX {n} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1) (xy : modeGram (qubitIndices n) x y=0)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    totalGram half x y (singleCol half x y p) F=ofReal (36*half^n)*gram3 (qubitIndices n) (singleCol half x y p) F := by
  let s := atomic209 half unit x y xx yy xy p
  let d := atomic204 half unit x y xx yy xy
  have pr (b) := (PhysicalProjectedTransport.physicalProjectedIntertwinings half unit x y F af xn yn b).1
  dsimp only [totalGram]; rw [crossedZero _ F _ (fun q hq => (s q hp hq).2.2.1),Semiring.add_zero,
    freePayment half x y x y F p hp (fun i q hq => (d i p q hp hq).1) pr]
  exact singlePayment half unit x y x y F af yn p (fun q hq => (s q hp hq).1)

/-- Equation (210) on the other physical single-occupied column. -/
theorem physicalEigenY {n} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1) (xy : modeGram (qubitIndices n) x y=0)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (xn : ∀a b,lower3 (qubitIndices n) x F a b=0) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0)
    (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    totalGram half x y (singleCol half y x p) F=ofReal (36*half^n)*gram3 (qubitIndices n) (singleCol half y x p) F := by
  let s := atomic209 half unit x y xx yy xy p
  let d := atomic204 half unit x y xx yy xy
  have pr (b) := (PhysicalProjectedTransport.physicalProjectedIntertwinings half unit x y F af xn yn b).2
  dsimp only [totalGram]; rw [crossedZero _ F _ (fun q hq => (s q hp hq).2.2.2),show ∀z : ComplexScalar R,0+z=z from fun _ => by grind only,
    freePayment half x y y x F p hp (fun i q hq => (d i p q hp hq).2) pr]
  exact singlePayment half unit x y y x F af xn p (fun q hq => (s q hp hq).2.1)
end RankSeven.PhysicalTwoHoleEigen
#print axioms RankSeven.PhysicalTwoHoleEigen.physicalEigenX
#print axioms RankSeven.PhysicalTwoHoleEigen.physicalEigenY
