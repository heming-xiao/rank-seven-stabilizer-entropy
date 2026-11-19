import Rank7FiveFaceTest
import Rank7TwoHolePhysicalExchange
import Rank7PhysicalWaveReproduction

/-! Physical column identities for the two occupied channels of the
two-hole bound, in ordered coordinates and odd-Pauli frame units. -/
namespace RankSeven.TwoHoleEigenInputs
open Lean.Grind Pauli ComplexScalar
open PhysicalTwoHoleOccupancy (gram3 gram2 raise3 lower3 modeGram Alt3 oneOccupied twoOccupied)
open PhysicalTwoHoleAdjointTransport (singleCol col1 col2)
open WedgeSquareIntertwiner (wedgeSquareColumn)
open PhysicalWaveReproduction (gramFour)
open PhysicalC2Projected (free)
variable {R I : Type} [CommRing R]
noncomputable local instance {n} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
noncomputable local instance {n} : DecidableEq (Word n) := Classical.typeDecidableEq _
def unitAt [DecidableEq I] (i j : I) : ComplexScalar R := if i=j then 1 else 0
theorem atomicWave {n} (half : R) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    PhysicalUniformOccupation.wave half (unitAt p)=wedgeSquareColumn half p := by
  funext u; unfold PhysicalUniformOccupation.wave
  refine (sumOverCongr _ (g:=fun j => if p=j then wedgeSquareColumn half j u else 0) (fun j => ?_)).trans
    (ExteriorPauliBase.sumOnIndex _ p _ (MixedDefect.oddWordsNodup n) hp)
  by_cases h : p=j <;> simp [unitAt,h,Semiring.one_mul,Semiring.zero_mul]
theorem atomicOne {n} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    oneOccupied half x y (unitAt p)=singleCol half x y p := by
  unfold oneOccupied PhysicalTwoHoleOccupancy.anchored; rw [atomicWave half p hp]; rfl
theorem atomicTwo {n} (half : R) (x y : Basis n→ComplexScalar R) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    twoOccupied half x y (unitAt p)=col2 half x y p := by
  unfold twoOccupied PhysicalTwoHoleOccupancy.anchored; rw [atomicWave half p hp]; rfl
theorem gramWaveSwap {n} (f g : Four (Basis n)→ComplexScalar R) :
    star (gramFour f g)=gramFour g f := by
  unfold gramFour; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro u; simp only [star_mul,star_star]; grind only
theorem covectorFlip (L : List I) (x y : I→ComplexScalar R) (xy : modeGram L x y=0) : modeGram L y x=0 := by
  have eq : star (modeGram L x y)=modeGram L y x := by
    simp only [modeGram,ComplexExterior.starSumOver,star_mul,star_star]; apply sumOverCongr; intro a; grind only
  rw [←eq,xy]; exact star_ofReal _
theorem projectedOrth {n} (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (i : Basis n) :
    modeGram (qubitIndices n) (free x y i) x=0 ∧ modeGram (qubitIndices n) (free x y i) y=0 := by
  let L := qubitIndices n
  have one (u v : Basis n→ComplexScalar R) (vv : modeGram L v v=1) (uv : modeGram L u v=0) :
      modeGram L (free u v i) v=0 := by
    have e := PhysicalC2Projected.freeOrthogonal L (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) u v uv vv i
    unfold modeGram; rw [←e]; apply sumOverCongr; intro t; exact CommSemiring.mul_comm _ _
  have flip : free x y i=free y x i := by funext t; unfold free; grind only
  exact ⟨flip ▸ one y x xx (covectorFlip L x y xy),one x y yy xy⟩

theorem atomic209 {n} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0)
    (p q : Word n) (hp : p∈MixedDefect.oddWords n) (hq : q∈MixedDefect.oddWords n) :
    let L := qubitIndices n
    let target := (ofReal half)^n*gramFour (wedgeSquareColumn half p) (wedgeSquareColumn half q)-
      3*gram2 L (col2 half x y p) (col2 half x y q)
    gram3 L (singleCol half x y p) (singleCol half x y q)=target ∧
    gram3 L (singleCol half y x p) (singleCol half y x q)=target ∧
    gram3 L (singleCol half x y p) (singleCol half y x q)=0 ∧
    gram3 L (singleCol half y x p) (singleCol half x y q)=0 := by
  have a := PhysicalTwoHoleOccupancy.physicalOccupation209 half unit x y xx yy xy (unitAt p) (unitAt q)
  have b := PhysicalTwoHoleOccupancy.physicalOccupation209 half unit y x yy xx (covectorFlip _ _ _ xy) (unitAt p) (unitAt q)
  simp only [PhysicalTwoHoleOccupancy.waveGram,atomicWave _ _ hp,atomicWave _ _ hq,atomicOne _ _ _ _ hp,atomicOne _ _ _ _ hq,atomicTwo _ _ _ _ hp,atomicTwo _ _ _ _ hq] at a b
  exact ⟨a.1,a.2.1,a.2.2,b.2.2⟩
private theorem conjIs (x : I→ComplexScalar R) : PhysicalTwoHoleExchange.conjugate x=(fun i => star (x i)) := rfl
theorem atomic204 {n} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (i : Basis n)
    (p q : Word n) (hp : p∈MixedDefect.oddWords n) (hq : q∈MixedDefect.oddWords n) :
    let L := qubitIndices n
    let r := free x y i
    let C2 := raise3 r (col2 half x y q)
    let link := col2 half (fun t => star (x t)) (fun t => star (y t)) p
    gram3 L (singleCol half x y p) C2=3*gram2 L link (col2 half (fun t => star (x t)) (fun t => star (r t)) q) ∧
    gram3 L (singleCol half y x p) C2=3*gram2 L link (col2 half (fun t => star (y t)) (fun t => star (r t)) q) := by
  obtain ⟨rx,ry⟩ := projectedOrth x y xx yy xy i
  have h := PhysicalTwoHoleExchange.physicalIntertwinings204 half unit x y _ rx ry (unitAt p) (unitAt q)
  simpa only [atomicOne _ _ _ _ hp,atomicTwo _ _ _ _ hp,atomicTwo _ _ _ _ hq,conjIs] using h

theorem conjugateLinkGram {n} (half : R) (x y : Basis n→ComplexScalar R)
    (p q : Word n) (hp : p∈MixedDefect.oddWords n) (hq : q∈MixedDefect.oddWords n) :
    gram2 (qubitIndices n) (col2 half (fun t => star (x t)) (fun t => star (y t)) p)
      (col2 half (fun t => star (x t)) (fun t => star (y t)) q)=gram2 (qubitIndices n) (col2 half x y p) (col2 half x y q) := by
  have h := PhysicalTwoHoleExchange.doubleGramConjugate half x y (unitAt p) (unitAt q)
  simpa only [atomicTwo _ _ _ _ hp,atomicTwo _ _ _ _ hq,conjIs] using h

theorem residualReadout {n} (half : R) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F)
    (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (p : Word n) :
    gram3 (qubitIndices n) (singleCol half x y p) F=gram3 (qubitIndices n) (col1 half x p) F := by
  unfold singleCol; rw [PhysicalTwoHoleOccupancy.subtractLeft,
    PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ af,PhysicalTwoHoleOccupancy.zeroGramRight _ yn]; grind only
private theorem reproduceOne {n} (half : R) (unit : 2*half=1) (x : Basis n→ComplexScalar R) (p : Word n) (a b c : Basis n) :
    sumOver (MixedDefect.oddWords n) (fun q => gramFour (wedgeSquareColumn half q) (wedgeSquareColumn half p)*col1 half x q a b c)=36*col1 half x p a b c := by
  unfold col1 PhysicalTwoHoleAdjointTransport.columnCut PhysicalUniformOccupation.oneHole
  simp only [sumOverMulLeft]; rw [sumOverSwap]; apply sumOverCongr; intro t
  let w (q : Word n) := wedgeSquareColumn half q ((a,b),(c,t))
  let k (q : Word n) := gramFour (wedgeSquareColumn half q) (wedgeSquareColumn half p)
  have row (q) : k q*(x t*w q)=x t*(w q*k q) := by grind only
  change sumOver _ (fun q => k q*(x t*w q))=36*(x t*w p)
  rw [sumOverCongr _ row,←sumOverMulLeft]; have e := PhysicalWaveReproduction.columnReproduction half unit p ((a,b),(c,t))
  change sumOver _ (fun q => w q*k q)=36*w p at e; rw [e]; grind only

theorem reproduceReadout {n} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (af : Alt3 F) (yn : ∀a b,lower3 (qubitIndices n) y F a b=0) (p : Word n) :
    sumOver (MixedDefect.oddWords n) (fun q => gramFour (wedgeSquareColumn half p) (wedgeSquareColumn half q)*
      gram3 (qubitIndices n) (singleCol half x y q) F)=36*gram3 (qubitIndices n) (singleCol half x y p) F := by
  simp only [residualReadout half x y F af yn]; unfold gram3 PhysicalTwoHoleOccupancy.sum3
  simp only [sumOverMulLeft]; rw [sumOverSwap]; apply sumOverCongr; intro a; rw [sumOverSwap]; apply sumOverCongr; intro b; rw [sumOverSwap]; apply sumOverCongr; intro c
  let k (q : Word n) := gramFour (wedgeSquareColumn half q) (wedgeSquareColumn half p)
  let one (q : Word n) := col1 half x q a b c
  have eq (q) : gramFour (wedgeSquareColumn half p) (wedgeSquareColumn half q)*(star (one q)*F a b c)=
      star (k q*one q)*F a b c := by simp only [k,star_mul,gramWaveSwap]; grind only
  rw [sumOverCongr _ eq,←sumOverMulRight,←ComplexExterior.starSumOver]
  change star (sumOver _ (fun q => k q*one q))*F a b c=36*(star (one p)*F a b c)
  have e : sumOver _ (fun q => k q*one q)=36*one p := reproduceOne half unit x p a b c
  rw [e,star_mul,show star (36:ComplexScalar R)=36 from star_ofReal (36:R)]; grind only
end RankSeven.TwoHoleEigenInputs
#print axioms RankSeven.TwoHoleEigenInputs.atomic204
#print axioms RankSeven.TwoHoleEigenInputs.reproduceReadout
