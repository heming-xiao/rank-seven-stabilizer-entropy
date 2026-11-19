import Rank7AnchorSteiner
import Rank7AntiPairIncidence

namespace RankSeven.AnchorCharacterSupport
open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open PhysicalAntiQuartic StabilizerCharacterBasis CharacterFourOrbits StabilizerCosetTransform AnchorSteiner
variable {R : Type} [CommRing R]
local notation "C" => ComplexScalar R

theorem parityCriterion {n} {G : MaximalFamily n} {T : Transversal G} (a r b c : Line T) :
    plane a r b c ↔ ∀g∈G.labels,(((anti a.val g ^^ anti r.val g) ^^ anti b.val g) ^^ anti c.val g)=false := by
  unfold plane; rw [G.criterion]; simp only [antiAddLeft]

private theorem chiFour {n} (a r b c g : Word n) :
    chi a g*chi r g*chi b g*chi c g =
      (phase (((anti a g ^^ anti r g) ^^ anti b g) ^^ anti c g):C) := by
  unfold chi; cases anti a g <;> cases anti r g <;> cases anti b g <;> cases anti c g <;>
    simp [phase] <;> grind only

private theorem cocycleFourth {n} (p q : Word n) : (cocycle (imaginaryUnit (R:=R)) p q)^4=1 := by
  rw [cocyclePhaseBits _ imaginaryUnit_sq]
  have sq:=imaginaryUnit_fourth (R:=R)
  cases negativeProduct p q <;> cases anti p q <;> simp [phase] <;> grind only

/-- A raw character-projector column, in the original computational coordinate basis. -/
def column {n} {G : MaximalFamily n} (F : Lift G) (a : Word n) (j i : Basis n) : C := raw F a i j

private theorem charAct {n} {G : MaximalFamily n} (F : Lift G) (a g : Word n) (hg : g∈G.labels) (j i : Basis n) :
    act g (column (R:=R) F a j) i = (phase (F.sign g)*chi a g)*column F a j i := by
  have e:=rawEigen (R:=R) F a g hg i j
  have eq : phase (F.sign g)*act g (column (R:=R) F a j) i =
       matMul (qubitIndices n) (lifted F g) (raw F a) i j := by
    unfold act column matMul lifted; rw [sumOverMulLeft]; apply sumOverCongr; intro k; grind only
  rw [←eq] at e
  cases s:F.sign g <;> simp only [column,s,phase,Bool.false_eq_true,ite_false,ite_true] at e ⊢ <;> grind only

/-- Actual Pauli word p acting on one character-projector column is intertwined
with translation p↦p+g by that column's signed physical g eigencharacter. -/
theorem coefficientShift {n} {G : MaximalFamily n} (F : Lift G) (a g p : Word n) (hg : g∈G.labels)
    (j i : Basis n) :
    cocycle imaginaryUnit p g * act (wordAdd p g) (column (R:=R) F a j) i =
    (phase (F.sign g)*chi a g)*act p (column F a j) i := by
  rw [←actProduct]
  have e : act g (column (R:=R) F a j)=fun k=>(phase (F.sign g)*chi a g)*column F a j k :=
    funext (charAct F a g hg j)
  rw [e,actScale]

def fourAct {n} {G : MaximalFamily n} {T : Transversal G} (F : Lift G) (a r b c : Line T)
    (j i : Four (Basis n)) (p : Word n) : C :=
    act p (column F a.val j.1.1) i.1.1 * act p (column F r.val j.1.2) i.1.2 *
    act p (column F b.val j.2.1) i.2.1 * act p (column F c.val j.2.2) i.2.2

theorem fourActShift {n} {G : MaximalFamily n} {T : Transversal G} (F : Lift G) (a r b c : Line T)
    (j i : Four (Basis n)) (g p : Word n) (hg : g∈G.labels) :
    fourAct (R:=R) F a r b c j i (wordAdd p g) =
      phase (((anti a.val g ^^ anti r.val g) ^^ anti b.val g) ^^ anti c.val g)*fourAct F a r b c j i p := by
  let u:=cocycle (imaginaryUnit (R:=R)) p g
  let s:=(phase (F.sign g):C)
  let cp (v:Word n) (j i:Basis n) (p:Word n):=act p (column (R:=R) F v j) i
  have h (v : Word n) (j i:Basis n) : u*cp v j i (wordAdd p g)=(s*chi v g)*cp v j i p :=
    coefficientShift F v g p hg j i
  have group (w : Word n) : fourAct (R:=R) F a r b c j i w=
     cp a.val j.1.1 i.1.1 w*cp r.val j.1.2 i.1.2 w*cp b.val j.2.1 i.2.1 w*cp c.val j.2.2 i.2.2 w := rfl
  have u4 : u^4=1 := cocycleFourth p g
  have s4 : s^4=1 := by unfold s; cases F.sign g <;> simp [phase] <;> grind only
  have main :
      (u*cp a.val j.1.1 i.1.1 (wordAdd p g))*(u*cp r.val j.1.2 i.1.2 (wordAdd p g))*
      (u*cp b.val j.2.1 i.2.1 (wordAdd p g))*(u*cp c.val j.2.2 i.2.2 (wordAdd p g))=
      s^4*(chi a.val g*chi r.val g*chi b.val g*chi c.val g)*fourAct (R:=R) F a r b c j i p := by
    simp only [h,group]; grind only
  rw [chiFour,s4,Semiring.one_mul] at main
  rw [←main,group,←Semiring.one_mul (cp a.val j.1.1 i.1.1 _*_*_*_),←u4]; grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The actual (unscaled) fourth Pauli tensor average vanishes identically on
every off-plane product of four physical stabilizer character-projector columns. -/
theorem physicalFourSelection {n} {G : MaximalFamily n} {T : Transversal G} (F : Lift G)
    (a r b c : Line T) (mismatch : ¬plane a r b c) (j i : Four (Basis n)) :
    sumOver (words n) (fourAct (R:=R) F a r b c j i)=0 := by
  have gex : ∃g∈G.labels,(((anti a.val g ^^ anti r.val g) ^^ anti b.val g) ^^ anti c.val g)=true := by
    apply Classical.byContradiction; intro z; apply mismatch; apply (parityCriterion ..).mpr
    intro g hg; cases e : (((anti a.val g ^^ anti r.val g) ^^ anti b.val g) ^^ anti c.val g)
    · rfl
    · exact False.elim (z ⟨g,hg,e⟩)
  obtain ⟨g,hg,sg⟩:=gex
  let f:=fourAct (R:=R) F a r b c j i
  have row (p : Word n) : f (wordAdd p g)=(-1)*f p := by dsimp [f]; rw [fourActShift F a r b c j i g p hg,sg]; rfl
  have ss:=AntiPairIncidence.sumShift g f
  rw [sumOverCongr (words n) row,←sumOverMulLeft] at ss
  have rr:=congrArg ComplexScalar.re ss
  have ii:=congrArg ComplexScalar.im ss
  apply ComplexScalar.ext
  · simp at rr ⊢; grind only
  · simp at ii ⊢; grind only

end RankSeven.AnchorCharacterSupport
#print axioms RankSeven.AnchorCharacterSupport.physicalFourSelection
