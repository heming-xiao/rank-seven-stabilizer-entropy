import Rank7HighestCharacterChart
import Rank7AnchorOrbitBound

namespace RankSeven.HighestChartAction

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCharacterBasis StabilizerCosetTransform CharacterFourOrbits StabilizerPairedCharacters
open HighestCodeLocalization HighestExteriorOccupation HighestCharacterChart PhysicalAntiQuartic
open PauliPairContraction (normSum image)
variable {R : Type} [CommRing R]
local notation "C" => ComplexScalar R

private theorem adjoint {n} (p : Word n) (x z : Basis n→C) :
    innerProduct (qubitIndices n) (act p x) z=innerProduct (qubitIndices n) x (act p z) := by
  unfold innerProduct act
  simp only [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft,star_mul]
  rw [sumOverSwap]; apply sumOverCongr; intro j; apply sumOverCongr; intro i
  rw [ComplexPauliMoment.wordHermitian]; grind only

def vector {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (b : Line T) :=
  act (wordAdd c b.val) (fun j=>block half F c j i)

theorem analysisVector {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (b : Line T) (x : Basis n→C) :
    analysis half F T c i x b=innerProduct (qubitIndices n) (vector half F T c i b) x := by
  unfold vector; rw [adjoint]; apply sumOverCongr; intro j
  have h:=congrFun (congrFun (blockHerm (R:=R) half F c) i) j
  change star (block half F c j i)=block half F c i j at h; rw [h]

private theorem cocycleNorm {n : Nat} (p q : Word n) : normSq (cocycle (imaginaryUnit (R:=R)) p q)=1 := by
  induction p with
  | empty => cases q; change normSq (1:C)=1; unfold normSq; rw [re_one,im_one]; grind only
  | cons a p ih => cases q with | cons b q =>
        rw [cocycle,normSq_mul,ih]; cases a <;> cases b <;> simp only [axisCocycle,normSq,imaginaryUnit,re_one,im_one,re_neg,im_neg] <;> grind only

private theorem cancelLeft {n} (p q r : Word n) : wordAdd (wordAdd p q) (wordAdd p r)=wordAdd q r := by
  rw [wordAddComm p q,wordAddAssoc,←wordAddAssoc p p r,wordAddSelf,wordAddComm (unitWord n),wordAddZero]

noncomputable def step {n} {G : MaximalFamily n} (F : Lift G) (T : Transversal G) (c p : Word n) (b : Line T) : C :=
  let u:=wordAdd c b.val
  let t:=wordAdd c (shift T p b).val
  let g:=wordAdd (wordAdd p u) t
  cocycle imaginaryUnit p u*star (cocycle imaginaryUnit t g)*(phase (F.sign g)*chi c g)

theorem stepUnit {n} {G : MaximalFamily n} (F : Lift G) (T : Transversal G) (c p : Word n) (b : Line T) :
    normSq (step (R:=R) F T c p b)=1 := by
  unfold step; dsimp only
  simp only [normSq_mul,normSq_star,cocycleNorm]
  unfold chi; generalize F.sign _=s; generalize anti c _=e
  cases s <;> cases e <;> simp only [phase,Bool.false_eq_true,ite_false,ite_true,normSq,re_neg,im_neg,re_one,im_one] <;> grind only

theorem vectorAction {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c p : Word n) (i : Basis n) (b : Line T) :
    act p (vector half F T c i b)=fun j=>step F T c p b*vector half F T c i (shift T p b) j := by
  let u:=wordAdd c b.val
  let l:=shift T p b
  let t:=wordAdd c l.val
  let g:=wordAdd (wordAdd p u) t
  have eq : wordAdd p u=wordAdd c (wordAdd b.val p) := by unfold u; rw [wordAddComm p,wordAddAssoc]
  have mem : g∈G.labels := by
    change wordAdd (wordAdd p u) (wordAdd c l.val)∈G.labels
    rw [eq,cancelLeft]; exact (represents T (wordAdd b.val p)).2
  have rg : wordAdd t g=wordAdd p u := by unfold g; rw [wordAddComm t,wordAddCancel]
  let h:=(ofReal half)^n
  let S j:=AnchorCharacterSupport.column (R:=R) F c i j
  let Z:=cocycle (imaginaryUnit (R:=R)) t g
  let η : C:=phase (F.sign g)*chi c g
  have one : star Z*Z=1:=by rw [star_mul_self,cocycleNorm]; rfl
  funext j
  have shiftEq:=AnchorCharacterSupport.coefficientShift (R:=R) F c g t mem i j
  rw [rg] at shiftEq
  change Z*act (wordAdd p u) S j=η*act t S j at shiftEq
  change act p (act u (fun j=>h*S j)) j=(cocycle imaginaryUnit p u*star Z*η)*act t (fun j=>h*S j) j
  rw [actProduct,actScale,actScale]
  have eq':=congrArg (fun z=>star Z*z) shiftEq
  change star Z*(Z*act (wordAdd p u) S j)=star Z*(η*act t S j) at eq'
  grind only

theorem analysisAction {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c p : Word n) (i : Basis n) (b : Line T) (x : Basis n→C) :
    analysis half F T c i (act p x) b=star (step F T c p b)*analysis half F T c i x (shift T p b) := by
  rw [analysisVector,←adjoint,vectorAction,analysisVector]; unfold innerProduct
  rw [sumOverMulLeft]; apply sumOverCongr; intro j; rw [star_mul]; grind only

noncomputable def anchor {n} {G : MaximalFamily n} (T : Transversal G) (c : Word n) : Line T :=
  ⟨representative T c,(represents T c).1⟩

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem anchorOff {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (b : Line T) (off : b≠anchor T c) :
    analysis half F T c i (fun j=>block half F c j i) b=0 := by
  let u:=wordAdd c b.val
  let B:=block half F
  let X:=qubitIndices n
  let W:=wordEntry (imaginaryUnit (R:=R)) u
  have classNe : wordAdd b.val c∉G.labels := by
    intro eq; apply off; apply Subtype.ext
    exact (StabilizerSmallCodes.repClass T c b.val b.property (StabilizerCosetTransform.symm eq)).symm
  have m:=StabilizerOddSector.wordBlock half F u b.val
  have e : wordAdd b.val u=c := by unfold u; rw [wordAddComm b.val,wordAddCancel]
  rw [e] at m
  change matMul X W (B b.val)=matMul X (B c) W at m
  have z : matMul X (B b.val) (B c)=(fun _ _=>0) := by
    rw [blockProduct half h2]; simp only [classNe,ite_false]
  change matMul X (B c) (matMul X W (B c)) i i=0
  rw [←matMulAssoc,←m,matMulAssoc,z]
  change sumOver X (fun j=>W i j*0)=0
  simp only [Semiring.mul_zero]
  induction X with
  | nil => rfl
  | cons j X ih => change 0+sumOver X _=0; rw [ih]; grind only

theorem anchorNorm {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) :
    normSq (analysis half F T c i (fun j=>block half F c j i) (anchor T c))=(block half F c i i).re^2 := by
  classical
  let s j:=block half F c j i
  let ψ:=analysis half F T c i s
  let a:=anchor T c
  have norm:=chartNorm half h2 F T c i s
  have col:=congrFun (congrFun (blockIsometry (R:=R) half h2 F c) i) i
  change innerProduct (qubitIndices n) s s=block half F c i i at col
  have rn:=congrArg ComplexScalar.re col
  rw [selfProduct,re_ofReal] at rn
  have val (j : Line T) : normSq (ψ j)=if a=j then normSq (ψ j) else 0 := by
    by_cases eq:a=j
    · simp [eq]
    · simp only [eq,ite_false]; have zz : ψ j=0:=anchorOff half h2 F T c i j (Ne.symm eq)
      rw [zz]; simp only [normSq,re_zero,im_zero]; grind only
  change sumOver T.reps.attach (fun j=>normSq (ψ j))=_ at norm
  rw [sumOverCongr _ val,ExteriorPauliBase.sumOnIndex T.reps.attach a _ (linesNodup T) (List.mem_attach _ _),rn] at norm
  change normSq (ψ a)=_; grind only

end RankSeven.HighestChartAction

#print axioms RankSeven.HighestChartAction.analysisVector
#print axioms RankSeven.HighestChartAction.stepUnit
#print axioms RankSeven.HighestChartAction.vectorAction
#print axioms RankSeven.HighestChartAction.analysisAction
#print axioms RankSeven.HighestChartAction.anchorOff
#print axioms RankSeven.HighestChartAction.anchorNorm

