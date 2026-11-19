import Rank7HighestCodeTransport

namespace RankSeven.HighestCosetFourier

open Lean.Grind Pauli ComplexScalar PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerPopulationRounding SymmetricDefect HighestCodeParseval
open StabilizerOddSector HighestCodeLocalization FiniteProjectionAngles SlaterUnionBound HighestCodeTransport
open PauliPairContraction (normSum image)
open PhysicalCompressionEffect (OrthonormalFrame)
open JointProbeGram (oddAverage)
open MixedDefect (oddWords oddWord)
variable {R α : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem realSum (xs : List α) (f : α→ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) ∧ (sumOver xs f).im=sumOver xs (fun i => (f i).im) := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    change (f x+sumOver xs f).re=(f x).re+sumOver xs _ ∧ (f x+sumOver xs f).im=(f x).im+sumOver xs _
    rw [re_add,im_add,ih.1,ih.2]; exact ⟨rfl,rfl⟩

private theorem chiReal {n : Nat} (a g : Word n) : (chi a g:ComplexScalar R)=ofReal (chi a g:R) := by
  unfold chi phase; cases anti a g <;> apply ComplexScalar.ext <;> simp <;> grind only

private theorem transformParts {n : Nat} (half : R) (G : MaximalFamily n) (f : Word n→ComplexScalar R) (a : Word n) :
    (transform (ofReal half) G f a).re=transform half G (fun g => (f g).re) a ∧
    (transform (ofReal half) G f a).im=transform half G (fun g => (f g).im) a := by
  unfold transform; simp only [←PhysicalPairedReduction.realEmbeddingPow,re_mul,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,
    (realSum _ _).1,(realSum _ _).2,chiReal]
  constructor <;> congr 1 <;> grind only

omit [CommRing R] in
def halfGroupList {n : Nat} (G : MaximalFamily n) (t : Word n) := G.labels.filter (fun g => !anti t g)

theorem halfGroupSum {n : Nat} (G : MaximalFamily n) (t : Word n) (v : Word n→R) :
    sumOver (halfGroupList G t) v=sumOver G.labels (fun g => if anti t g then 0 else v g) := by
  let xs := G.labels
  change sumOver (xs.filter _) v=sumOver xs _
  induction xs with
  | nil => rfl
  | cons g gs ih => rw [List.filter_cons]; cases e : anti t g <;> simp [e,sumOver] at ih ⊢ <;> grind only

def dephased {n : Nat} {G : MaximalFamily n} (L : Lift G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R)
    (a g : Word n) := (chi a g:ComplexScalar R)*source L p A g

theorem centeredMean {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (z : TransposeOffset G)
    (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :
    (2*(ofReal half)^n)*sumOver (halfGroupList G (wordAdd z.offset p)) (dephased L p A a)=codeAmplitude half L T z p A a := by
  let t := wordAdd z.offset p
  let U := source L p A
  change _=amplitudeBlock half L p A a+amplitudeBlock half L p A (representative T (wordAdd a t))
  rw [blockTransform,blockTransform,shifted]
  unfold transform
  rw [halfGroupSum,sumOverMulLeft,sumOverMulLeft,sumOverMulLeft,←sumOverAdd]
  apply sumOverCongr; intro g
  unfold dephased; cases e : anti t g <;> simp only [t] at e <;>
    simp only [t,chi,phase,e,Bool.false_eq_true,ite_true,ite_false] <;> grind only

theorem dephasedNorm {n : Nat} {G : MaximalFamily n} (L : Lift G) (p : Word n)
    (A : Basis n→Fin 7→ComplexScalar R) (a g : Word n) :
    normSq (dephased L p A a g)=JointProbePayment.pairWeight A (wordAdd g p) 0 1 := by
  unfold dephased; rw [normSq_mul,sourceNorm]
  cases e : anti a g <;> simp only [chi,phase,e,Bool.false_eq_true,ite_true,ite_false,normSq,re_neg,im_neg,re_one,im_one] <;> grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem inversionC {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f : Word n→ComplexScalar R) (g : Word n) (hg : g∈G.labels) :
    sumOver T.reps (fun a => chi a g*transform (ofReal half) G f a)=f g := by
  have re := inversion half h2 T (fun g => (f g).re) g hg
  have im := inversion half h2 T (fun g => (f g).im) g hg
  have z0 (x : R) : x-0=x := by grind only
  apply ComplexScalar.ext
  · rw [(realSum _ _).1]; simpa only [chiReal,re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,z0,
      (transformParts _ _ _ _).1] using re
  · rw [(realSum _ _).2]; simpa only [chiReal,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,Semiring.add_zero,
      (transformParts _ _ _ _).2] using im

private theorem absAdd (x y : ComplexScalar R) (u v : R) (un : 0≤u) (vn : 0≤v)
    (a : normSq x≤u^2) (b : normSq y≤v^2) : normSq (x+y)≤(u+v)^2 := by
  let s := (star x*y).re
  have n := normSq_mul (star x) y
  rw [normSq_star] at n
  change s^2+(star x*y).im^2=normSq x*normSq y at n
  have e := squareNonnegative (star x*y).im
  have h := Std.le_trans (OrderedRing.mul_le_mul_of_nonneg_right a (normSq_nonnegative y))
    (OrderedRing.mul_le_mul_of_nonneg_left b (squareNonnegative u))
  have cap : s≤u*v := by
    by_cases ok : s≤u*v
    · exact ok
    · have uv := OrderedRing.mul_nonneg un vn
      have neg := OrderedRing.mul_pos (show 0<s-u*v by grind only) (show 0<s+u*v by grind only)
      grind only
  have id : normSq (x+y)=normSq x+normSq y+2*s := by unfold normSq s; simp only [re_add,im_add,re_mul,re_star,im_star]; grind only
  rw [id]; grind only

theorem sumBound (xs : List α) (f : α→ComplexScalar R) (b : α→R) (bn : ∀i∈xs,0≤b i) (bound : ∀i∈xs,normSq (f i)≤(b i)^2) :
    normSq (sumOver xs f)≤(sumOver xs b)^2 := by
  induction xs with
  | nil => change normSq (0:ComplexScalar R)≤(0:R)^2; unfold normSq; rw [re_zero,im_zero]; grind only
  | cons i is ih =>
    have pos (j : α) (hj : j∈is) := bn j (List.mem_cons_of_mem _ hj)
    exact absAdd (f i) (sumOver is f) (b i) (sumOver is b) (bn i List.mem_cons_self)
      (Compression.sumOverNonnegative is b pos) (bound i List.mem_cons_self) (ih pos (fun j hj => bound j (List.mem_cons_of_mem _ hj)))

def linePopulation {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G)
    (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :=
  half*(pop half L a (act p fun i => A i 0)+pop half L a (fun i => star (A i 1)))

theorem lineBound {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :
    normSq (amplitudeBlock half L p A a)≤(linePopulation half L p A a)^2 := by
  let xs := qubitIndices n
  let B := block half L a
  let x := act p (fun i => A i 0)
  let y i := star (A i 1)
  have cv : innerProduct xs y (image xs B x)=amplitudeBlock half L p A a := by
    unfold innerProduct image amplitudeBlock y; simp only [star_star]; rfl
  have h := projectedBound xs B (PhysicalProjectionAngles.lineProjection half h2 L a) y x
  rw [cv] at h
  let u := pop half L a y
  let v := pop half L a x
  change normSq (amplitudeBlock half L p A a)≤u*v at h
  change normSq (amplitudeBlock half L p A a)≤(half*(v+u))^2
  have scalar (s t : R) : s*t≤(half*(t+s))^2 := by
    have eq := congrArg (fun z : R => z*z) h2
    change (2*half)*(2*half)=1*1 at eq
    have sq := squareNonnegative (s-t)
    have id : 4*(half*(t+s))^2=(t+s)^2 := by grind only
    simp only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] at sq id ⊢
    grind only
  exact Std.le_trans h (scalar _ _)

private theorem cutSum {S : Type} [CommRing S] [DecidableEq α] (xs : List α) (nd : xs.Nodup) (a b : α)
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) (f : α→S) :
    sumOver xs (fun i => if i=a ∨ i=b then 0 else f i)=sumOver xs f-f a-f b := by
  let aa i := if a=i then f i else 0
  let bb i := if b=i then f i else 0
  let rr i := if i=a ∨ i=b then 0 else f i
  have eq (i : α) : aa i+bb i+rr i=f i := by unfold aa bb rr; grind only
  have e := sumOverCongr xs eq
  rw [sumOverAdd,sumOverAdd] at e
  have aeq : sumOver xs aa=f a := ExteriorPauliBase.sumOnIndex xs a f nd ha
  have beq : sumOver xs bb=f b := ExteriorPauliBase.sumOnIndex xs b f nd hb
  change sumOver xs rr=_; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem signUnit {n : Nat} (a g : Word n) : (chi a g:ComplexScalar R)*(chi a g)=1 ∧ normSq (chi a g:ComplexScalar R)=1 := by
  cases e : anti a g <;> simp only [chi,phase,e,Bool.false_eq_true,ite_true,ite_false,normSq,re_neg,im_neg,re_one,im_one] <;> constructor <;> grind only

theorem insideDeviation {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p a g : Word n) (ha : a∈T.reps) (diff : wordAdd z.offset p∉G.labels)
    (hg : g∈halfGroupList G (wordAdd z.offset p)) (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    normSq (dephased L p A a g-codeAmplitude half L T z p A a)≤(1-codePopulation half L T z p A a)^2 := by
  let t := wordAdd z.offset p
  let m := mate T z p a
  let f := linePopulation half L p A
  let U := amplitudeBlock half L p A
  let χ i := (chi i g:ComplexScalar R)
  let v i := χ a*(χ i*U i)
  have gg : g∈G.labels := (List.mem_filter.mp hg).1
  have az : anti t g=false := by simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hg).2
  have cz : (chi t g:ComplexScalar R)=1 := by simp [chi,phase,az]
  have eq : χ m=χ a := by
    change (chi (representative T (wordAdd a t)) g:ComplexScalar R)=chi a g
    rw [←charConstant (represents T (wordAdd a t)).2 g gg,charAddLeft,cz,Semiring.mul_one]
  have main : v a+v m=codeAmplitude half L T z p A a := by
    change χ a*(χ a*U a)+χ a*(χ m*U m)=U a+U m
    rw [eq,←Semiring.mul_assoc,←Semiring.mul_assoc,(show χ a*χ a=1 from (signUnit a g).1)]; grind only
  have full : sumOver T.reps v=dephased L p A a g := by
    unfold v; rw [←sumOverMulLeft]
    apply congrArg (fun z => χ a*z)
    unfold U; simp only [blockTransform]; exact inversionC half h2 T _ g gg
  have count : sumOver T.reps f=1 := by
    have move : sumOver T.reps (fun i => f (mate T z p i))=sumOver T.reps f := by
      rw [←CharacterFourOrbits.lineSum T,←CharacterFourOrbits.lineSum T f]
      exact CharacterFourOrbits.translationSum T _ (fun i => f i.val)
    have tot := populationTotal half h2 L T z p A orth
    change sumOver T.reps (fun i => f i+f (mate T z p i))=2 at tot
    rw [sumOverAdd,move] at tot; grind only
  let cut (i : Word n) := i=a ∨ i=m
  let restV i := if cut i then 0 else v i
  let restB i := if cut i then 0 else f i
  have vn (i : Word n) : normSq (v i)≤(f i)^2 := by
    unfold v χ; rw [normSq_mul,normSq_mul,(signUnit a g).2,(signUnit i g).2,Semiring.one_mul,Semiring.one_mul]
    exact lineBound half h2 L p A i
  have nn (i : Word n) : 0≤f i := by
    have hn : 0≤half := by have := OrderedRing.zero_lt_one (R:=R); grind only
    have w := popNonnegative half h2 L i (act p fun j => A j 0)
    have y := popNonnegative half h2 L i (fun j => star (A j 1))
    exact OrderedRing.mul_nonneg hn (by grind only)
  have snd := sumBound T.reps restV restB (fun i _ => by unfold restB; split; exact Std.le_refl _; exact nn i)
    (fun i _ => by unfold restV restB; split; unfold normSq; rw [re_zero,im_zero]; grind only; exact vn i)
  have val := cutSum T.reps T.nodup a m ha (represents T _).1 (mateDifferent T t diff a) v
  have un := cutSum T.reps T.nodup a m ha (represents T _).1 (mateDifferent T t diff a) f
  change sumOver T.reps restV=_ at val; change sumOver T.reps restB=_ at un
  rw [full] at val; rw [count] at un
  have rv : sumOver T.reps restV=dephased L p A a g-codeAmplitude half L T z p A a := by grind only
  have rf : sumOver T.reps restB=1-codePopulation half L T z p A a := by change _=1-(f a+f m); grind only
  rwa [rv,rf] at snd

end RankSeven.HighestCosetFourier

#print axioms RankSeven.HighestCosetFourier.centeredMean
#print axioms RankSeven.HighestCosetFourier.dephasedNorm
#print axioms RankSeven.HighestCosetFourier.inversionC
#print axioms RankSeven.HighestCosetFourier.insideDeviation

