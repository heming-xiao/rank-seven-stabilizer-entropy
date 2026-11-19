import Rank7HighestAnchorOddCoset

namespace RankSeven.HighestCodeParseval

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCosetTransform StabilizerOddSector StabilizerPairedCharacters StabilizerCharacterBasis
open UpperPairPfaffian (pair pauliLeg)
open JointProbePayment (pairWeight)
open JointProbeGram (oddAverage)
open MixedDefect (oddWords oddWord)
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
variable {R α : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def amplitudeBlock {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (p : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) : ComplexScalar R :=
  let xs := qubitIndices n
  let x j := A j 0
  sumOver xs (fun i => A i 1*sumOver xs (fun j => block half L a i j*act p x j))

def source {n : Nat} {G : MaximalFamily n} (L : Lift G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (g : Word n) :=
  (phase (L.sign g):ComplexScalar R)*sumOver (qubitIndices n) (fun i => A i 1*act g (act p (fun j => A j 0)) i)

theorem blockTransform {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (p : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :
    amplitudeBlock half L p A a=transform ((ofReal half):ComplexScalar R) G (source L p A) a := by
  let xs := qubitIndices n
  let v := act p (fun j => A j 0)
  let sf (g : Word n) : ComplexScalar R := phase (L.sign g)
  let χ (g : Word n) : ComplexScalar R := chi a g
  let h := (ofReal half)^n
  let e (g : Word n) := sumOver xs (fun i => A i 1*act g v i)
  have eq (i : Basis n) : sumOver xs (fun j => block half L a i j*v j)=h*sumOver G.labels (fun g => (χ g*sf g)*act g v i) := by
    unfold block raw lifted; simp only [h,Semiring.mul_assoc,sumOverMulRight,sumOverMulLeft]
    rw [sumOverSwap]; apply sumOverCongr; intro g; unfold χ sf act; simp only [sumOverMulLeft]; apply sumOverCongr; intro j; grind only
  change sumOver xs (fun i => A i 1*sumOver xs (fun j => block half L a i j*v j))=h*sumOver G.labels (fun g => χ g*(sf g*e g))
  simp only [eq,e,sumOverMulLeft,Semiring.mul_assoc]; rw [sumOverSwap]
  apply sumOverCongr; intro g; apply sumOverCongr; intro i; grind only

private theorem unitNorm {n : Nat} (p q : Word n) : normSq (PhysicalAntiQuartic.cocycle (imaginaryUnit (R:=R)) p q)=1 := by
  induction p with
  | empty => cases q; change normSq (1:ComplexScalar R)=1; unfold normSq; rw [re_one,im_one]; grind only
  | cons a p ih =>
    cases q with
    | cons b q =>
      rw [PhysicalAntiQuartic.cocycle,normSq_mul,ih]; cases a <;> cases b <;>
        simp only [PhysicalAntiQuartic.axisCocycle,normSq,imaginaryUnit,re_one,im_one,re_neg,im_neg] <;> grind only

theorem sourceNorm {n : Nat} {G : MaximalFamily n} (L : Lift G) (p : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) (g : Word n) : normSq (source L p A g)=pairWeight A (wordAdd g p) 0 1 := by
  let xs := qubitIndices n
  let x i := A i 0
  let q := wordAdd g p
  let c := PhysicalAntiQuartic.cocycle (imaginaryUnit (R:=R)) g p
  have same : sumOver xs (fun j => A j 1*act q x j)=star (pair A q 0 1) := by
    rw [←UpperPairPfaffian.pairFromLeg,ComplexExterior.starSumOver]
    apply sumOverCongr; intro j; rw [star_mul,star_star]
    apply congrArg (fun y => A j 1*y)
    unfold pauliLeg act; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro i
    rw [star_mul,star_star,ComplexPauliMoment.wordHermitian]; unfold x; grind only
  have eq : source L p A g=(phase (L.sign g):ComplexScalar R)*c*star (pair A q 0 1) := by
    unfold source; rw [←same,Semiring.mul_assoc]
    rw [sumOverMulLeft xs _ c]
    apply congrArg (fun y => (phase (L.sign g):ComplexScalar R)*y); apply sumOverCongr; intro j
    rw [actProduct]; unfold q c x; grind only
  rw [eq,normSq_mul,normSq_mul,unitNorm,normSq_star]
  unfold pair; rw [normSq_star]; cases h : L.sign g <;> simp [phase,normSq,re_one,im_one,pairWeight] <;> grind only

private theorem realSum (xs : List α) (f : α→ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) ∧ (sumOver xs f).im=sumOver xs (fun i => (f i).im) := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    change (f x+sumOver xs f).re=(f x).re+sumOver xs _ ∧ (f x+sumOver xs f).im=(f x).im+sumOver xs _
    rw [re_add,im_add,ih.1,ih.2]; exact ⟨rfl,rfl⟩

private theorem transformParts {n : Nat} (half : R) (G : MaximalFamily n) (f : Word n→ComplexScalar R) (a : Word n) :
    (transform (ofReal half) G f a).re=transform half G (fun g => (f g).re) a ∧
    (transform (ofReal half) G f a).im=transform half G (fun g => (f g).im) a := by
  have sign (g : Word n) : (chi a g:ComplexScalar R)=ofReal (chi a g:R) := by unfold chi phase; cases anti a g <;> apply ComplexScalar.ext <;> simp <;> grind only
  unfold transform; simp only [←PhysicalPairedReduction.realEmbeddingPow,re_mul,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,
    (realSum _ _).1,(realSum _ _).2,sign]
  constructor <;> congr 1 <;> grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem pairedIdentity {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f : Word n → R) (t : Word n) :
    let m a := representative T (wordAdd a t)
    let F := transform half G f
    sumOver T.reps (fun a => (F a+F (m a))^2)=4*half^n*sumOver G.labels (fun g => if anti t g then 0 else (f g)^2) := by
  let m a := representative T (wordAdd a t)
  let F := transform half G f
  let keep (g : Word n) := if anti t g then 0 else f g
  have eq (a : Word n) : F a+F (m a)=2*transform half G keep a := by
    change transform half G f a+transform half G f (representative T (wordAdd a t))=_
    rw [shifted]; unfold transform; rw [sumOverMulLeft,sumOverMulLeft,sumOverMulLeft,←sumOverAdd,sumOverMulLeft]
    apply sumOverCongr; intro g; unfold keep chi phase; cases e : anti t g <;> simp [e] <;> grind only
  have pt (a : Word n) : (F a+F (m a))^2=4*(transform half G keep a)^2 := by rw [eq]; grind only
  have val :=  sumOverCongr T.reps pt
  rw [←sumOverMulLeft] at val
  have norm := parseval half h2 T keep
  change sumOver T.reps (fun a => (transform half G keep a)^2)=half^n*sumOver G.labels (fun g => (keep g)^2) at norm
  have ks (g : Word n) : (keep g)^2=(if anti t g then 0 else (f g)^2) := by unfold keep; split <;> grind only
  rw [norm,sumOverCongr _ ks] at val
  change sumOver T.reps (fun a => (F a+F (m a))^2)=_; grind only

noncomputable def codeAmplitude {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :=
  amplitudeBlock half L p A a+amplitudeBlock half L p A (representative T (wordAdd a (wordAdd z.offset p)))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem cosetAvg {n : Nat} (half : R) {G : MaximalFamily n} (z : TransposeOffset G)
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

/-- The normalized odd-coset mass is exactly the sum over unordered two-character codes
of squared physical transition amplitudes. The transversal enumerates each code twice. -/
theorem physicalCodeParseval {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p : Word n) (op : oddWord p=true)
    (A : Basis n→Fin 7→ComplexScalar R) :
    sumOver T.reps (fun a => normSq (codeAmplitude half L T z p A a))=
      2*oddAverage half (fun q => if wordAdd p q∈G.labels then pairWeight A q 0 1 else 0) := by
  let V := source L p A
  let t := wordAdd z.offset p
  let m a := representative T (wordAdd a t)
  let U := amplitudeBlock half L p A
  let f (g : Word n) := (V g).re
  let j (g : Word n) := (V g).im
  let J := transform half G j
  let F := transform half G f
  have parts (a : Word n) : (U a).re=F a ∧ (U a).im=J a := by
    unfold U; rw [blockTransform]; exact transformParts half G V a
  have point (a : Word n) : normSq (codeAmplitude half L T z p A a)=(F a+F (m a))^2+(J a+J (m a))^2 := by
    change normSq (U a+U (m a))=_; unfold normSq
    rw [re_add,im_add,(parts a).1,(parts (m a)).1,(parts a).2,(parts (m a)).2]
  have rr := pairedIdentity half h2 T f t
  have ii := pairedIdentity half h2 T j t
  change sumOver T.reps (fun a => (F a+F (m a))^2)=_ at rr
  change sumOver T.reps (fun a => (J a+J (m a))^2)=_ at ii
  rw [sumOverCongr _ point,sumOverAdd,rr,ii,cosetAvg half z p op]
  let v (g : Word n) := if anti t g then 0 else (f g)^2
  let w (g : Word n) := if anti t g then 0 else (j g)^2
  have pt (g : Word n) : (if anti t g then (0:R) else pairWeight A (wordAdd g p) 0 1)=v g+w g := by
    unfold v w; cases anti t g <;> simp only [Bool.false_eq_true,ite_true,ite_false,Semiring.add_zero]
    rw [←sourceNorm L p A g]; rfl
  change 4*half^n*sumOver G.labels v+4*half^n*sumOver G.labels w=2*(2*half^n*sumOver G.labels _)
  rw [sumOverCongr _ pt,sumOverAdd]; grind only

end Order

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem physicalHeavyCodes (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    ∃p∈oddWords (k+3),∃G : MaximalFamily (k+3),∃T : Transversal G,∃L : Lift G,∃z : TransposeOffset G,
      wordAdd z.offset p∉G.labels ∧ 5<4*sumOver T.reps (fun a => normSq (codeAmplitude half L T z p A a)) := by
  classical
  obtain ⟨p,hp,G,z,diff,_,_,mass⟩ := HighestAnchorOddCoset.physicalOddCoset half h2 k A mu orth small
  obtain ⟨T⟩ := transversalExists G
  obtain ⟨L⟩ := liftExists G
  refine ⟨p,hp,G,T,L,z,diff,?_⟩
  rw [physicalCodeParseval half h2 L T z p (List.mem_filter.mp hp).2 A]
  grind only

end Field

end RankSeven.HighestCodeParseval

#print axioms RankSeven.HighestCodeParseval.blockTransform
#print axioms RankSeven.HighestCodeParseval.sourceNorm
#print axioms RankSeven.HighestCodeParseval.physicalCodeParseval
#print axioms RankSeven.HighestCodeParseval.physicalHeavyCodes

