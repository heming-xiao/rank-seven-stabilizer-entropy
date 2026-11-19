import Rank7HighestCosetFourier

namespace RankSeven.HighestPhysicalConcentration

open Lean.Grind Pauli ComplexScalar PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerPopulationRounding SymmetricDefect HighestCodeParseval
open StabilizerOddSector HighestCodeLocalization HighestAnchorMoments HighestCodeTransport HighestCosetFourier
open JointProbeGram (oddAverage pairWeightAverage)
open JointProbePayment (pairWeight)
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
open MixedDefect (oddWords oddWord)
variable {R α : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem constSum (xs : List α) (v : R) : sumOver xs (fun _ => v)=v*sumOver xs (fun _ => (1:R)) := by
  rw [sumOverMulLeft]; apply sumOverCongr; intro i; rw [Semiring.mul_one]

theorem centeredVariance (xs : List α) (h : R) (unit : h*sumOver xs (fun _ => (1:R))=1)
    (f : α→ComplexScalar R) (a : ComplexScalar R) (mean : ofReal h*sumOver xs f=a) :
    sumOver xs (fun i => (star a*(f i-a)).re)=0 ∧
    h*sumOver xs (fun i => normSq (f i-a))=h*sumOver xs (fun i => normSq (f i))-normSq a := by
  let N := sumOver xs (fun _ => (1:R))
  let U := sumOver xs (fun i => (f i).re)
  let V := sumOver xs (fun i => (f i).im)
  have re := congrArg ComplexScalar.re mean
  have im := congrArg ComplexScalar.im mean
  simp only [re_mul,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,(realSum _ _).1,(realSum _ _).2] at re im
  change h*U-0=a.re at re; change h*V+0=a.im at im
  change h*N=1 at unit
  have rmu : U=N*a.re := by grind only
  have imu : V=N*a.im := by grind only
  let w i := (star a*(f i-a)).re
  have lin (i : α) : w i=a.re*(f i).re+a.im*(f i).im-normSq a := by
    unfold w; simp only [re_mul,re_star,im_star,re_sub,im_sub,normSq]; grind only
  have center : sumOver xs w=0 := by
    rw [sumOverCongr _ lin,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,constSum]
    change a.re*U+a.im*V-normSq a*N=0
    rw [rmu,imu]; unfold normSq; grind only
  have pt (i : α) : normSq (f i-a)=normSq (f i)-normSq a-2*w i := by
    rw [lin]; simp only [normSq,re_sub,im_sub]; grind only
  refine ⟨center,?_⟩
  rw [sumOverCongr _ pt,Compression.sumOverSub,Compression.sumOverSub,constSum,←sumOverMulLeft,center]
  change h*(sumOver xs (fun i => normSq (f i))-normSq a*N-2*0)=_
  grind only

theorem cosetAverage {n : Nat} (half : R) {G : MaximalFamily n} (z : TransposeOffset G)
    (p : Word n) (hp : oddWord p=true) (f : Word n→R) :
    oddAverage half (fun q => if wordAdd p q∈G.labels then f q else 0)=
    2*half^n*sumOver G.labels (fun g => if anti (wordAdd z.offset p) g then 0 else f (wordAdd g p)) := by
  classical
  let h q := if oddWord q then f q else 0
  let F q := if wordAdd q p∈G.labels then h q else 0
  let W := words n
  have swap (q : Word n) : (if oddWord q then if wordAdd p q∈G.labels then f q else 0 else 0)=F q := by
    unfold F h; rw [wordAddComm q p]; cases oddWord q <;> by_cases g : wordAdd p q∈G.labels <;> simp [g]
  have filter (xs : List (Word n)) (v : Word n→R) : sumOver (xs.filter oddWord) v=
      sumOver xs (fun i => if oddWord i then v i else 0) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => rw [List.filter_cons]; cases e : oddWord a <;> simp [e,sumOver] at ih ⊢ <;> grind only
  unfold oddAverage oddWords; rw [filter,sumOverCongr _ swap]
  apply congrArg (fun y => (2*half^n)*y)
  rw [←AntiPairIncidence.sumShift p F]
  simp only [F,wordAddCancel,sumMembership]
  apply AnticommutingDefect.sumCongrMem; intro g hg
  have parity := HighestAnchorOddCoset.oddKernel z p g hp hg
  unfold h; cases a : oddWord (wordAdd g p) <;> cases b : anti (wordAdd z.offset p) g <;> simp [a,b] at parity ⊢


variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem scaleNonnegative (half : R) (h2 : 2*half=1) (n : Nat) : 0≤2*half^n := by
  have one := OrderedRing.zero_lt_one (R:=R)
  have p (r : Nat) : 0≤half^r := by
    induction r with
    | zero => rw [Semiring.pow_zero]; grind only
    | succ r ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have := p n; grind only

theorem insideFourth {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (p a : Word n) (op : oddWord p=true) (ha : a∈T.reps) (dif : wordAdd z.offset p∉G.labels)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (bn : 0≤codePopulation half L T z p A a)
    (bu : codePopulation half L T z p A a≤1) :
    let b := codePopulation half L T z p A a
    let C := normSq (codeAmplitude half L T z p A a)
    let rho := oddAverage half (fun q => if wordAdd p q∈G.labels then pairWeight A q 0 1 else 0)
    0≤rho-C ∧ oddAverage half (fun q => if wordAdd p q∈G.labels then (pairWeight A q 0 1)^2 else 0)≤
      C^2+(6*C+4*b*(1-b)+(1-b)^2)*(rho-C) := by
  let b := codePopulation half L T z p A a
  let c := codeAmplitude half L T z p A a
  let xs := halfGroupList G (wordAdd z.offset p)
  let h := 2*half^n
  let f := dephased L p A a
  let rho := oddAverage half (fun q => if wordAdd p q∈G.labels then pairWeight A q 0 1 else 0)
  let r (i : Word n) := f i-c
  have av (v : Word n→R) : oddAverage half (fun q => if wordAdd p q∈G.labels then v q else 0)=h*sumOver xs (fun i => v (wordAdd i p)) := by
    rw [cosetAverage half z p op,halfGroupSum]
  have unit : h*sumOver xs (fun _ => (1:R))=1 := by
    rw [halfGroupSum]; exact halfGroup half h2 _ dif
  have mean := centeredMean half L T z p A a
  have hc : ofReal h=2*(ofReal half)^n := by
    have two : (2:ComplexScalar R)=1+1 := by grind only
    rw [two,←PhysicalPairedReduction.realEmbeddingPow]; apply ComplexScalar.ext <;>
      simp only [re_mul,im_mul,re_ofReal,im_ofReal,re_add,im_add,re_one,im_one] <;> grind only
  have mom := centeredVariance xs h unit f c (by rw [hc]; exact mean)
  have center : sumOver xs (fun i => (star c*r i).re)=0 := mom.1
  have norm : h*sumOver xs (fun i => normSq (f i))=rho := by
    unfold rho; rw [av]; apply congrArg (fun x => h*x); apply sumOverCongr; intro i; exact dephasedNorm L p A a i
  have resid : h*sumOver xs (fun i => normSq (r i))=rho-normSq c := by rw [←norm]; exact mom.2
  have hn := scaleNonnegative half h2 n
  have nn := OrderedRing.mul_nonneg hn (Compression.sumOverNonnegative xs (fun i => normSq (r i)) (fun i _ => normSq_nonnegative _))
  rw [resid] at nn
  refine ⟨nn,?_⟩
  have bd := averagedFourth xs h hn unit c r b (1-b) bn (by change b≤1 at bu; grind only) (codeBound half h2 L T z p dif A a ha)
    (fun i hi => insideDeviation half h2 L T z p a i ha dif hi A orth) center
  rw [resid] at bd
  have pt (i : Word n) : normSq (c+r i)^2=(pairWeight A (wordAdd i p) 0 1)^2 := by
    have e : c+r i=f i := by unfold r; grind only
    rw [e,dephasedNorm]
  rw [sumOverCongr xs pt] at bd
  rw [av]; exact bd

private theorem avgLE {n : Nat} (half : R) (h2 : 2*half=1) (f g : Word n→R) (le : ∀q∈oddWords n,f q≤g q) :
    oddAverage half f≤oddAverage half g := by
  have s := Compression.sumOverNonnegative (oddWords n) (fun i => g i-f i) (fun i hi => by have := le i hi; grind only)
  rw [Compression.sumOverSub] at s
  exact OrderedRing.mul_le_mul_of_nonneg_left (by grind only) (scaleNonnegative half h2 n)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgAdd {n : Nat} (half : R) (f g : Word n→R) :
    oddAverage half (fun p => f p+g p)=oddAverage half f+oddAverage half g := by unfold oddAverage; rw [sumOverAdd]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgSub {n : Nat} (half : R) (f g : Word n→R) :
    oddAverage half (fun p => f p-g p)=oddAverage half f-oddAverage half g := by unfold oddAverage; rw [Compression.sumOverSub]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgMul {n : Nat} (half c : R) (f : Word n→R) :
    oddAverage half (fun p => c*f p)=c*oddAverage half f := by unfold oddAverage; rw [←sumOverMulLeft]; grind only

theorem physicalFourthDeficit (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (mu : Fin 7→R) (orth : OrthonormalFrame A) {G : MaximalFamily (k+3)} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (p a : Word (k+3)) (op : oddWord p=true) (ha : a∈T.reps) (dif : wordAdd z.offset p∉G.labels)
    (bLarge : 3≤4*codePopulation half L T z p A a) (bUnit : codePopulation half L T z p A a≤1)
    (cLarge : 9≤16*normSq (codeAmplitude half L T z p A a))
    (tail : sumOver T.reps (fun i => normSq (codeAmplitude half L T z p A i))-2*normSq (codeAmplitude half L T z p A a)≤
      2*(1-codePopulation half L T z p A a)^2) :
    let b := codePopulation half L T z p A a
    4*b^2*(1-b)*(3*b-2)≤(physicalPayment half h2 k A mu).kappaOne := by
  classical
  let n := k+3
  let f (q : Word n) := pairWeight A q 0 1
  let cut (q : Word n) := wordAdd p q∈G.labels
  let on (v : Word n→R) (q : Word n) := if cut q then v q else 0
  let off (v : Word n→R) (q : Word n) := if cut q then 0 else v q
  let b := codePopulation half L T z p A a
  let C := normSq (codeAmplitude half L T z p A a)
  let rho := oddAverage half (on f)
  let K := (physicalPayment half h2 k A mu).kappaOne
  let sq (q : Word n) := (f q)^2
  have bb : 3≤4*b := bLarge
  have cc : 9≤16*C := cLarge
  have cb : C≤b^2 := codeBound half h2 L T z p dif A a ha
  have e := physicalCodeParseval half h2 L T z p op A
  change sumOver T.reps (fun i => normSq (codeAmplitude half L T z p A i))=2*rho at e
  rw [e] at tail
  change 2*rho-2*C≤2*(1-b)^2 at tail
  have inside := insideFourth half h2 L T z p a op ha dif A orth (by change 0≤b; grind only) bUnit
  change 0≤rho-C ∧ oddAverage half (on sq)≤C^2+(6*C+4*b*(1-b)+(1-b)^2)*(rho-C) at inside
  have outside := avgLE half h2 (off sq) (fun q => 4*b*(1-b)*off f q) (by
    intro q hq
    by_cases inf : cut q
    · unfold off; simp only [inf,ite_true,Semiring.mul_zero]; exact Std.le_refl _
    · have cap := outsidePoint half h2 L T z p q (List.mem_filter.mp hq).2 dif inf a ha A orth (by change 1≤2*b; grind only)
      have nn : 0≤f q := normSq_nonnegative _
      change f q≤4*b*(1-b) at cap
      have ss := OrderedRing.mul_le_mul_of_nonneg_right cap nn
      unfold off sq; simp only [inf,ite_false]; grind only)
  rw [avgMul] at outside
  have decomp (v : Word n→R) : oddAverage half v=oddAverage half (on v)+oddAverage half (off v) := by
    rw [←avgAdd]; apply congrArg (oddAverage half); funext q; unfold on off; split <;> grind only
  have av : oddAverage half f=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have mass := decomp f
  change oddAverage half f=rho+oddAverage half (off f) at mass
  have sqSplit := decomp sq
  have ksq : K=1-oddAverage half sq := by
    change oddAverage half (fun q => f q*(1-f q))=_
    have equal : (fun q => f q*(1-f q))=fun q => f q-sq q := by funext q; unfold sq; grind only
    rw [equal,avgSub,av]
  have away : oddAverage half (off f)=1-rho := by grind only
  rw [away] at outside
  exact fourthMomentDeficit b C rho K bb bUnit cc cb (by grind only) inside.1 (by have := inside.2; grind only)

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem physicalStrongPeak (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    ∃p∈oddWords (k+3),∃G : MaximalFamily (k+3),∃T : Transversal G,∃L : Lift G,∃z : TransposeOffset G,
      wordAdd z.offset p∉G.labels ∧ ∃a∈T.reps,
      let b := codePopulation half L T z p A a
      let K := (physicalPayment half h2 k A mu).kappaOne
      b≤1 ∧ 19<20*b ∧ 6137*(1-b)≤2000*K ∧ 4*b^2*(1-b)*(3*b-2)≤K := by
  obtain ⟨p,op,G,T,L,z,dif,a,ha,bl,cl,bu,tail⟩ := physicalPeak half h2 k A mu orth small
  let b := codePopulation half L T z p A a
  let K := (physicalPayment half h2 k A mu).kappaOne
  have bb : 3≤4*b := Std.le_of_lt bl
  have f := physicalFourthDeficit half h2 k A mu orth L T z p a (List.mem_filter.mp op).2 ha dif bb bu (Std.le_of_lt cl) tail
  have result := smallDeficit b K bb bu small f
  exact ⟨p,op,G,T,L,z,dif,a,ha,bu,result.1,result.2,f⟩

theorem physicalStabilizerPlane (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    ∃G : MaximalFamily (k+3),∃L : Lift G,∃c d : Word (k+3), ¬equiv G c d ∧
      let Q := PhysicalProjectionAngles.code half L c d
      let E := SlaterUnionBound.energy (qubitIndices (k+3)) Q (fun i => A i 0)+
        SlaterUnionBound.energy (qubitIndices (k+3)) Q (fun i => A i 1)
      E≤2 ∧ 19<10*E ∧ 6137*(2-E)≤4000*(physicalPayment half h2 k A mu).kappaOne := by
  obtain ⟨p,_,G,T,L,z,dif,a,_,bu,near,est,_⟩ := physicalStrongPeak half h2 k A mu orth small
  let c := wordAdd a p
  let d := wordAdd a z.offset
  have apart : ¬equiv G c d := by
    have can : wordAdd c d=wordAdd z.offset p := by
      unfold c d; rw [wordAddComm a p,wordAddAssoc,←wordAddAssoc a a z.offset,wordAddSelf,wordAddComm (unitWord _) z.offset,wordAddZero,wordAddComm]
    intro e; apply dif; change wordAdd c d∈G.labels at e; rwa [can] at e
  refine ⟨G,L,c,d,apart,?_⟩
  let b := codePopulation half L T z p A a
  let E := SlaterUnionBound.energy (qubitIndices (k+3)) (PhysicalProjectionAngles.code half L c d) (fun i => A i 0)+
        SlaterUnionBound.energy (qubitIndices (k+3)) (PhysicalProjectionAngles.code half L c d) (fun i => A i 1)
  have id : 2*b=E := physicalCodePopulation half h2 L T z p A a
  change b≤1 at bu; change 19<20*b at near; change 6137*(1-b)≤_ at est
  change E≤2 ∧ 19<10*E ∧ 6137*(2-E)≤_; grind only

end Field

end RankSeven.HighestPhysicalConcentration

#print axioms RankSeven.HighestPhysicalConcentration.insideFourth
#print axioms RankSeven.HighestPhysicalConcentration.physicalFourthDeficit
#print axioms RankSeven.HighestPhysicalConcentration.physicalStrongPeak
#print axioms RankSeven.HighestPhysicalConcentration.physicalStabilizerPlane

