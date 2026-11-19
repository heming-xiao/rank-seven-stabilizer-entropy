import Rank7StabilizerSmallCodes

namespace RankSeven.StabilizerOddSector

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPopulationRounding StabilizerPairedCharacters StabilizerSmallCodes
open MixedDefect (oddWord oddWords)
variable {R C : Type} [CommRing R] [CommRing C]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem oddAdd {n : Nat} (p q : Word n) : oddWord (wordAdd p q)=((oddWord p ^^ oddWord q) ^^ anti p q) := by
  induction p with
  | empty => cases q; rfl
  | cons a p ih => cases q with
    | cons b q => simp only [wordAdd,oddWord,anti,ih]
                  cases a <;> cases b <;> cases oddWord p <;> cases oddWord q <;> cases anti p q <;> rfl

theorem oddId (n : Nat) : oddWord (unitWord n)=false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [unitWord,oddWord,ih]; rfl

theorem signAdd {n : Nat} (p q : Word n) : (wordSign (wordAdd p q):C)=wordSign p*wordSign q*chi p q := by
  simp only [MixedDefect.oddWordTransposeSign,oddAdd,chi]
  cases oddWord p <;> cases oddWord q <;> cases anti p q <;> simp [phase] <;> grind only

theorem charAddLeft {n : Nat} (a b g : Word n) : (chi (wordAdd a b) g:C)=chi a g*chi b g := by
  rw [chiSymm (wordAdd a b) g,characterAddRight,chiSymm g a,chiSymm g b]

structure TransposeOffset (G : MaximalFamily n) where
  offset : Word n
  agrees : ∀g∈G.labels,oddWord g=anti offset g

theorem offsetExists [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G) : Nonempty (TransposeOffset G) := by
  let F a := transform half G (fun g => (wordSign g:R)) a
  have tot : sumOver T.reps F=1 := by
    have e := transformSum half h2 T (fun g => (wordSign g:R))
    change sumOver T.reps F=_ at e; rw [e,MixedDefect.oddWordTransposeSign,oddId]; rfl
  have somePos : ∃a∈T.reps,F a≠0 := by
    apply Classical.byContradiction; intro no
    have zero (a : Word n) (ha : a∈T.reps) : F a=0 := Classical.byContradiction (fun ne => no ⟨a,ha,ne⟩)
    have absent (xs : List (Word n)) : sumOver xs (fun _ => (0:R))=0 := by
      induction xs with
      | nil => rfl
      | cons i xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
    rw [AnticommutingDefect.sumCongrMem T.reps F (fun _ => (0:R)) zero,absent] at tot; grind only
  obtain ⟨z,_,hz⟩ := somePos
  refine ⟨⟨z,?_⟩⟩; intro q hq
  have shift := groupSumShift G q hq (fun v => (chi z v:R)*wordSign v)
  have eq (v : Word n) (hv : v∈G.labels) :
      (chi z (wordAdd v q):R)*wordSign (wordAdd v q)=(chi z q*wordSign q)*(chi z v*wordSign v) := by
    rw [characterAddRight,signAdd]; have h := (G.criterion v).mp hv q hq
    unfold chi; rw [h]; simp only [phase,Bool.false_eq_true,ite_false]; grind only
  rw [AnticommutingDefect.sumCongrMem G.labels _ _ eq,←sumOverMulLeft] at shift
  have eqF : (chi z q*wordSign q)*F z=F z := by
    change (chi z q*wordSign q)*(half^n*sumOver G.labels (fun v => chi z v*wordSign v))=_
    dsimp only [F,transform]; have m := congrArg (fun u : R => half^n*u) shift; grind only
  rw [MixedDefect.oddWordTransposeSign] at eqF; unfold chi phase at eqF
  cases h : oddWord q <;> cases e : anti z q <;> first | rfl | (simp only [h,e,Bool.false_eq_true,ite_true,ite_false] at eqF; exact False.elim (hz (by grind only)))

theorem conjugateBlock {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (z : TransposeOffset G) (a : Word n) :
    transpose (block half L a)=block half L (wordAdd a z.offset) := by
  funext i j; unfold transpose block raw; congr 1; apply AnticommutingDefect.sumCongrMem; intro g hg
  unfold lifted; rw [wordEntryTranspose (imaginaryUnit (R:=R)) g i j,MixedDefect.oddWordTransposeSign,z.agrees g hg,charAddLeft]
  unfold chi; grind only

theorem wordBlock {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (p a : Word n) :
    matMul (qubitIndices n) (wordEntry imaginaryUnit p) (block half L a)=
      matMul (qubitIndices n) (block half L (wordAdd a p)) (wordEntry imaginaryUnit p) := by
  funext i j
  let h := (ofReal half)^n
  let W (v : Word n) := wordEntry (imaginaryUnit (R:=R)) v
  let c (a g : Word n) : ComplexScalar R := chi a g*phase (L.sign g)
  have right (a : Word n) : matMul (qubitIndices n) (W p) (block half L a) i j=
      sumOver G.labels (fun g => h*c a g*matMul (qubitIndices n) (W p) (W g) i j) := by
    unfold matMul block raw lifted; simp only [sumOverMulLeft,Semiring.mul_assoc]; rw [sumOverSwap]
    apply sumOverCongr; intro g; apply sumOverCongr; intro k; unfold h c W; grind only
  have left (b : Word n) : matMul (qubitIndices n) (block half L b) (W p) i j=
      sumOver G.labels (fun g => h*c b g*matMul (qubitIndices n) (W g) (W p) i j) := by
    unfold matMul block raw lifted; simp only [sumOverMulRight,sumOverMulLeft,Semiring.mul_assoc]; rw [sumOverSwap]
    apply sumOverCongr; intro g; apply sumOverCongr; intro k; unfold h c W; grind only
  change matMul _ (W p) (block half L a) i j=matMul _ (block half L _) (W p) i j
  rw [right,left]; apply sumOverCongr; intro g; unfold c W; rw [PhysicalAntiQuartic.wordCommutation imaginaryUnit imaginaryUnit_sq p g i j,charAddLeft]; grind only

private theorem cosetSum {n : Nat} (G : MaximalFamily n) (c : Word n) (f : Word n→C) :
    sumOver (words n) (fun p => if wordAdd p c∈G.labels then f p else 0)=sumOver G.labels (fun g => f (wordAdd g c)) := by
  let F p := if wordAdd p c∈G.labels then f p else 0
  change sumOver (words n) F=_
  rw [←AntiPairIncidence.sumShift c F]; simp only [F,wordAddCancel]; exact sumMembership G _

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

attribute [local instance] Semiring.natCast

theorem cosetOddCount {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (z : TransposeOffset G) (c : Word n)
    (different : wordAdd z.offset c∉G.labels) :
    JointProbeGram.oddAverage half (fun p => if wordAdd p c∈G.labels then (1:R) else 0)=1 := by
  have filter (xs : List (Word n)) (f : Word n→R) : sumOver (xs.filter oddWord) f=
      sumOver xs (fun p => if oddWord p then f p else 0) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => rw [List.filter_cons]; cases e : oddWord a <;> simp [e,sumOver] at ih ⊢ <;> grind only
  let count (p : Word n) : R := if oddWord p then 1 else 0
  have swap (p : Word n) : (if oddWord p then if wordAdd p c∈G.labels then (1:R) else 0 else 0)=
      (if wordAdd p c∈G.labels then count p else 0) := by cases o : oddWord p <;> by_cases h : wordAdd p c∈G.labels <;> simp [count,h,o]
  have s := HeavyPauliGroup.characterSum (R:=R) G (wordAdd z.offset c); rw [ite_eq_right different] at s
  have eq (g : Word n) (hg : g∈G.labels) : (wordSign (wordAdd g c):R)=wordSign c*chi (wordAdd z.offset c) g := by
    rw [signAdd,charAddLeft,chiSymm g c,MixedDefect.oddWordTransposeSign g,z.agrees g hg]; unfold chi; grind only
  have eta : sumOver G.labels (fun g => (wordSign (wordAdd g c):R))=0 := by
    rw [AnticommutingDefect.sumCongrMem G.labels _ _ eq,←sumOverMulLeft,s]; grind only
  have ce (g : Word n) : 2*count (wordAdd g c)=1-(wordSign (wordAdd g c):R) := by
    rw [MixedDefect.oddWordTransposeSign]; unfold count; cases oddWord (wordAdd g c) <;> simp [phase] <;> grind only
  have twice := sumOverCongr G.labels ce
  have ones (xs : List (Word n)) : sumOver xs (fun _ => (1:R))=Nat.cast xs.length := by
    induction xs with
    | nil => change 0=Nat.cast 0; rw [Semiring.natCast_zero]
    | cons a xs ih => change 1+sumOver xs _=Nat.cast (xs.length+1); rw [ih,Semiring.natCast_succ]; grind only
  rw [←sumOverMulLeft,Compression.sumOverSub,ones,cardinalCast,eta] at twice
  unfold JointProbeGram.oddAverage oddWords; rw [filter,sumOverCongr _ swap,cosetSum]
  have inv := SectorDefectAccounting.dimensionInverse half h2 n
  have m := congrArg (fun u : R => half^n*u) twice; grind only

private theorem cancelLeft {n : Nat} (z a : Word n) : wordAdd z (wordAdd z a)=a := by rw [wordAddComm z (wordAdd z a),wordAddComm z a,wordAddCancel]

private theorem cancelPair {n : Nat} (c a b : Word n) : wordAdd (wordAdd c a) (wordAdd c b)=wordAdd a b := by
  rw [wordAddComm c a,←wordAddAssoc,wordAddCancel]

def center {n : Nat} {G : MaximalFamily n} (z : TransposeOffset G) (c a : Word n) := wordAdd z.offset (wordAdd c a)

noncomputable def member {n : Nat} {G : MaximalFamily n} (z : TransposeOffset G) (c a b p : Word n) : Bool :=
  decide (wordAdd p (center z c a)∈G.labels) || decide (wordAdd p (center z c b)∈G.labels)

theorem selectorMass {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G) (z : TransposeOffset G)
    (c a b : Word n) (hc : c∈T.reps) (ha : a∈T.reps) (hb : b∈T.reps) (ca : c≠a) (cb : c≠b) (ab : a≠b) :
    JointProbeGram.oddAverage half (fun p => if member z c a b p then (1:R) else 0)=2 := by
  let v := center z c a
  let w := center z c b
  have d1 : wordAdd z.offset v∉G.labels := by unfold v center; rw [cancelLeft]; exact fun h => ca (T.separated c hc a ha h)
  have d2 : wordAdd z.offset w∉G.labels := by unfold w center; rw [cancelLeft]; exact fun h => cb (T.separated c hc b hb h)
  have dis : ¬equiv G v w := by
    change wordAdd (wordAdd z.offset (wordAdd c a)) (wordAdd z.offset (wordAdd c b))∉G.labels
    rw [cancelPair,cancelPair]; exact fun h => ab (T.separated a ha b hb h)
  have e (p : Word n) : (if member z c a b p then (1:R) else 0)=
      (if wordAdd p v∈G.labels then 1 else 0)+(if wordAdd p w∈G.labels then 1 else 0) := by
    change (if decide (wordAdd p v∈G.labels) || decide (wordAdd p w∈G.labels) then (1:R) else 0)=_
    by_cases h : wordAdd p v∈G.labels <;> by_cases j : wordAdd p w∈G.labels
    · exact False.elim (dis (StabilizerCosetTransform.trans (StabilizerCosetTransform.symm h) j))
    all_goals simp [h,j] <;> grind only
  have one := cosetOddCount half h2 z v d1; have two := cosetOddCount half h2 z w d2
  unfold JointProbeGram.oddAverage at one two ⊢; rw [sumOverCongr _ e,sumOverAdd]; grind only

private theorem equivCenter {n : Nat} {G : MaximalFamily n} (z : TransposeOffset G) (x p a : Word n) :
    equiv G (wordAdd (wordAdd x z.offset) p) a ↔ equiv G p (center z x a) := by
  unfold equiv center
  rw [wordAddComm (wordAdd x z.offset) p,wordAddAssoc,wordAddComm x z.offset,wordAddAssoc]

theorem selectorAction {n : Nat} {G : MaximalFamily n} (z : TransposeOffset G) (c a b p : Word n) :
    member z c a b p=true ↔ equiv G (wordAdd (wordAdd c z.offset) p) a ∨ equiv G (wordAdd (wordAdd c z.offset) p) b := by
  rw [equivCenter,equivCenter]; unfold member equiv; simp

end Order

end RankSeven.StabilizerOddSector

#print axioms RankSeven.StabilizerOddSector.offsetExists
#print axioms RankSeven.StabilizerOddSector.conjugateBlock
#print axioms RankSeven.StabilizerOddSector.wordBlock
#print axioms RankSeven.StabilizerOddSector.selectorAction
#print axioms RankSeven.StabilizerOddSector.selectorMass

