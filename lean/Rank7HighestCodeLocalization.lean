import Rank7HighestCodeParseval

namespace RankSeven.HighestCodeLocalization

open Lean.Grind Pauli ComplexScalar PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerPopulationRounding SymmetricDefect HighestCodeParseval
open StabilizerOddSector (TransposeOffset)
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
open PhysicalCompressionEffect (OrthonormalFrame)
variable {R α : Type} [CommRing R]
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def innerProduct (xs : List α) (x y : α→ComplexScalar R) :=
  sumOver xs (fun j => star (x j)*y j)

private theorem mixedSquare (xs : List α) (x y : α→ComplexScalar R) (u v : ComplexScalar R) :
    0≤normSq u*normSum xs y+normSq v*normSum xs x-2*(star (star u*v)*innerProduct xs x y).re := by
  induction xs with
  | nil =>
    change 0≤normSq u*0+normSq v*0-2*(star (star u*v)*0).re
    simp only [Semiring.mul_zero,re_zero]; grind only
  | cons i is ih =>
    change 0≤normSq u*(normSq (y i)+normSum is y)+normSq v*(normSq (x i)+normSum is x)-
      2*(star (star u*v)*(star (x i)*y i+innerProduct is x y)).re
    have pos := normSq_nonnegative (u*y i-v*x i)
    simp only [normSq,re_mul,im_mul,re_sub,im_sub,re_star,im_star,re_add,im_add] at ih pos ⊢
    grind only

theorem innerBound (xs : List α) (x y : α→ComplexScalar R) :
    normSq (innerProduct xs x y)≤normSum xs x*normSum xs y := by
  induction xs with
  | nil => change normSq (0:ComplexScalar R)≤0*0; simp [normSq,re_zero,im_zero]; grind only
  | cons i is ih =>
    have e := mixedSquare is x y (x i) (y i)
    change normSq (star (x i)*y i+innerProduct is x y)≤(normSq (x i)+normSum is x)*(normSq (y i)+normSum is y)
    simp only [normSq,re_add,im_add,re_star,im_star,re_mul,im_mul] at ih e ⊢
    grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem projectedInner (xs : List α) (Q : Mx α R) (q : Projection xs Q) (x y : α→ComplexScalar R) :
    innerProduct xs (image xs Q x) (image xs Q y)=innerProduct xs x (image xs Q y) := by
  let X (i : α) (_ : Unit) := x i
  let Y (i : α) (_ : Unit) := y i
  change matMul xs (dagger (matMul xs Q X)) (matMul xs Q Y) () ()=matMul xs (dagger X) (matMul xs Q Y) () ()
  rw [PhysicalPairedReduction.daggerProduct,q.herm,matMulAssoc,←matMulAssoc xs xs Q Q Y,q.square]

theorem projectedBound (xs : List α) (Q : Mx α R) (q : Projection xs Q) (x y : α→ComplexScalar R) :
    normSq (innerProduct xs x (image xs Q y))≤energy xs Q x*energy xs Q y := by
  rw [←projectedInner xs Q q,energyNorm xs Q q,energyNorm xs Q q]
  exact innerBound _ _ _

private theorem chooseMaximum (xs : List α) (f : α→R) (ne : xs≠[]) : ∃a∈xs,∀i∈xs,f i≤f a := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    by_cases empty : xs=[]
    · subst xs; exact ⟨a,by simp,fun i hi => (List.mem_singleton.mp hi) ▸ Std.le_refl _⟩
    · obtain ⟨b,hb,ub⟩ := ih empty
      by_cases ok : f a≤f b
      · refine ⟨b,List.mem_cons_of_mem _ hb,?_⟩
        intro i hi; rcases List.mem_cons.mp hi with rfl|hi; exact ok; exact ub i hi
      · refine ⟨a,List.mem_cons_self,?_⟩
        intro i hi; rcases List.mem_cons.mp hi with rfl|hi; exact Std.le_refl _
        have e := ub i hi; grind only

private theorem sumLE (xs : List α) (f g : α→R) (h : ∀i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have s := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at s; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem twoAtoms [DecidableEq α] (xs : List α) (nd : xs.Nodup) (a b : α)
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) (f : α→R) :
    sumOver xs (fun i => if i=a ∨ i=b then f i else 0)=f a+f b := by
  have pt (i : α) : (if i=a ∨ i=b then f i else 0)=(if a=i then f i else 0)+(if b=i then f i else 0) := by
    grind only
  rw [sumOverCongr _ pt,sumOverAdd,ExteriorPauliBase.sumOnIndex xs a f nd ha,ExteriorPauliBase.sumOnIndex xs b f nd hb]

theorem pairedPeak (xs : List α) (nd : xs.Nodup) (m : α→α)
    (member : ∀i∈xs,m i∈xs) (inv : ∀i∈xs,m (m i)=i) (apart : ∀i∈xs,i≠m i)
    (b C : α→R) (stable : ∀i∈xs,b (m i)=b i ∧ C (m i)=C i)
    (nn : ∀i∈xs,0≤b i) (bound : ∀i∈xs,C i≤(b i)^2)
    (total : sumOver xs b=2) (heavy : 5<4*sumOver xs C) :
    ∃a∈xs,3<4*b a ∧ 9<16*C a ∧ b a≤1 ∧
    sumOver xs C-2*C a≤2*(1-b a)^2 := by
  classical
  obtain ⟨a,ha,top⟩ := chooseMaximum xs b (by intro e; rw [e] at total; change (0:R)=2 at total; grind only)
  let cut (i : α) := i=a ∨ i=m a
  let rest (f : α→R) (i : α) := if cut i then 0 else f i
  have restTotal (f : α→R) : sumOver xs (rest f)=sumOver xs f-f a-f (m a) := by
    let part i := if cut i then f i else 0
    have eq (i : α) : f i=part i+rest f i := by unfold part rest; split <;> grind only
    have s : sumOver xs f=sumOver xs part+sumOver xs (rest f) := by rw [←sumOverAdd]; exact sumOverCongr _ eq
    have atom := twoAtoms xs nd a (m a) ha (member a ha) (apart a ha) f
    change sumOver xs part=_ at atom; grind only
  have bs := restTotal b
  have cs := restTotal C
  rw [total,(stable a ha).1] at bs
  rw [(stable a ha).2] at cs
  have r0 (i : α) (hi : i∈xs) : 0≤rest b i := by unfold rest; split; exact Std.le_refl _; exact nn i hi
  have all0 := Compression.sumOverNonnegative xs _ r0
  have restStable (i : α) (hi : i∈xs) : rest b (m i)=rest b i := by
    have cutEq : cut (m i) ↔ cut i := by
      change m i=a ∨ m i=m a ↔ i=a ∨ i=m a
      constructor
      · rintro (e|e)
        · exact Or.inr ((inv i hi) ▸ congrArg m e)
        · exact Or.inl (by simpa only [inv i hi,inv a ha] using congrArg m e)
      · rintro (e|e)
        · exact Or.inr (congrArg m e)
        · exact Or.inl (by rw [e,inv a ha])
    by_cases e : cut i
    · simp only [rest,e,cutEq.mpr e,ite_true]
    · have ncut : ¬cut (m i) := fun h => e (cutEq.mp h)
      simp only [rest,e,ncut,ite_false,(stable i hi).1]
  have r1 (i : α) (hi : i∈xs) : rest b i≤1-b a := by
    have k := twoAtoms xs nd i (m i) hi (member i hi) (apart i hi) (rest b)
    have l := sumLE xs (fun j => if j=i ∨ j=m i then rest b j else 0) (rest b) (fun j hj => by split; exact Std.le_refl _; exact r0 j hj)
    rw [k,restStable i hi] at l; grind only
  have cap := sumLE xs (rest C) (fun i => (1-b a)*rest b i) (by
    intro i hi
    have mul := OrderedRing.mul_le_mul_of_nonneg_right (r1 i hi) (r0 i hi)
    have bb := bound i hi
    unfold rest at mul ⊢; split <;> grind only)
  rw [←sumOverMulLeft,cs,bs] at cap
  have mx := sumLE xs C (fun i => b a*b i) (by
    intro i hi; have e := OrderedRing.mul_le_mul_of_nonneg_right (top i hi) (nn i hi); have := bound i hi; grind only)
  rw [←sumOverMulLeft,total] at mx
  have base := bound a ha
  have pos : 3<4*b a := by
    by_cases h : 3<4*b a
    · exact h
    · have p := OrderedRing.mul_nonneg (show 0≤3-4*b a by grind only) (show 0≤4*b a-1 by grind only)
      grind only
  have p := OrderedRing.mul_nonneg (show 0≤4*b a-3 by grind only) (show 0≤5-4*b a by grind only)
  exact ⟨a,ha,pos,by grind only,by grind only,by grind only⟩

noncomputable def mate {n : Nat} {G : MaximalFamily n} (T : Transversal G) (z : TransposeOffset G) (p a : Word n) :=
  representative T (wordAdd a (wordAdd z.offset p))

noncomputable def codePopulation {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :=
  let v := act p (fun i => A i 0)
  let y i := star (A i 1)
  let f i := half*(pop half L i v+pop half L i y)
  f a+f (mate T z p a)

theorem codeBound {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p : Word n) (diff : wordAdd z.offset p∉G.labels)
    (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) (ha : a∈T.reps) :
    normSq (codeAmplitude half L T z p A a)≤(codePopulation half L T z p A a)^2 := by
  let b := mate T z p a
  let xs := qubitIndices n
  let v := act p (fun i => A i 0)
  let y i := star (A i 1)
  let Q := PhysicalProjectionAngles.code half L a b
  have apart : ¬equiv G a b := fun e => mateDifferent T _ diff a (T.separated a ha b (represents T _).1 e)
  have q := PhysicalProjectionAngles.codeProjection (R:=R) half h2 L a b apart
  have cv : codeAmplitude half L T z p A a=innerProduct xs y (image xs Q v) := by
    change amplitudeBlock half L p A a+amplitudeBlock half L p A b=_
    unfold amplitudeBlock innerProduct image Q PhysicalProjectionAngles.code addM y
    simp only [star_star,Semiring.right_distrib,sumOverAdd,Semiring.left_distrib]
    rfl
  have bound := projectedBound xs Q q y v
  rw [←cv] at bound
  let Y := pop half L a y+pop half L b y
  let V := pop half L a v+pop half L b v
  have eqY : energy xs Q y=Y := energyAdd _ _ _ _
  have eqV : energy xs Q v=V := energyAdd _ _ _ _
  have point : 2*codePopulation half L T z p A a=V+Y := by
    unfold codePopulation V Y; change 2*(half*(_+_)+half*(_+_))=_; grind only
  rw [eqY,eqV] at bound
  have scalar (u v c : R) (hc : 2*c=u+v) : v*u≤c^2 := by
    have sq := squareNonnegative (u-v)
    have eq := congrArg (fun x : R => x^2) hc
    change (2*c)^2=(u+v)^2 at eq
    simp only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] at sq eq ⊢
    grind only
  exact Std.le_trans bound (scalar V Y _ point)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem columnUnit {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (i : Fin 7) :
    normSum (qubitIndices n) (fun j => A j i)=1 := by
  have eq := congrArg ComplexScalar.re (orth i i)
  have reSum {β : Type} (ys : List β) (f : β→ComplexScalar R) : (sumOver ys f).re=sumOver ys (fun j => (f j).re) := by
    induction ys with | nil => rfl | cons j ys ih => change (f j+sumOver ys f).re=_; rw [re_add,ih]; rfl
  unfold normSum; simpa only [reSum,ite_true,re_one,re_star_mul_self] using eq

theorem populationTotal {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    sumOver T.reps (codePopulation half L T z p A)=2 := by
  let v := act p (fun i => A i 0)
  let y i := star (A i 1)
  let f i := half*(pop half L i v+pop half L i y)
  have move : sumOver T.reps (fun a => f (mate T z p a))=sumOver T.reps f := by
    rw [←CharacterFourOrbits.lineSum T,←CharacterFourOrbits.lineSum T f]
    exact CharacterFourOrbits.translationSum T _ (fun i => f i.val)
  have vnorm : normSum (qubitIndices n) v=1 := (PauliPairContraction.wordIsometry p _).trans (columnUnit A orth 0)
  have ynorm : normSum (qubitIndices n) y=1 := by
    unfold normSum y; simp only [normSq_star]; exact columnUnit A orth 1
  have total : sumOver T.reps f=1 := by
    unfold f; rw [←sumOverMulLeft,sumOverAdd,popTotal half h2 L T,popTotal half h2 L T,vnorm,ynorm]; grind only
  change sumOver T.reps (fun a => f a+f (mate T z p a))=2
  rw [sumOverAdd,move,total]; grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem physicalPeak (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A) (small : 15*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne≤2) :
    ∃p∈MixedDefect.oddWords (k+3),∃G : MaximalFamily (k+3),∃T : Transversal G,∃L : Lift G,∃z : TransposeOffset G,
      wordAdd z.offset p∉G.labels ∧ ∃a∈T.reps,
      let b := codePopulation half L T z p A a
      let C i := normSq (codeAmplitude half L T z p A i)
      3<4*b ∧ 9<16*C a ∧ b≤1 ∧ sumOver T.reps C-2*C a≤2*(1-b)^2 := by
  obtain ⟨p,hp,G,T,L,z,diff,mass⟩ := physicalHeavyCodes half h2 k A mu orth small
  refine ⟨p,hp,G,T,L,z,diff,?_⟩
  let t := wordAdd z.offset p
  let m := mate T z p
  have inv (i : Word (k+3)) (hi : i∈T.reps) : m (m i)=i := StabilizerSmallCodes.mateInvol T t i hi
  apply pairedPeak T.reps T.nodup m (fun i _ => (represents T _).1) inv (fun i _ => mateDifferent T t diff i)
  · intro i hi
    have e := inv i hi
    constructor
    · unfold codePopulation; change _+(_*(_+_))=_+(_*(_+_))
      change half*(_+_)+half*(pop half L (m (m i)) _+pop half L (m (m i)) _)=_; rw [e]; grind only
    · unfold codeAmplitude
      change normSq (amplitudeBlock half L p A (m i)+amplitudeBlock half L p A (m (m i)))=_
      rw [e,AddCommMonoid.add_comm]; rfl
  · intro i _
    have h0 : 0≤half := by have one : (0:F)<1 := OrderedRing.zero_lt_one; grind only
    let term (j : Word (k+3)) := half*(pop half L j (act p fun x => A x 0)+pop half L j (fun x => star (A x 1)))
    have nn (j : Word (k+3)) : 0≤term j := by
      have u := popNonnegative half h2 L j (act p fun x => A x 0)
      have v := popNonnegative half h2 L j (fun x => star (A x 1))
      exact OrderedRing.mul_nonneg h0 (by grind only)
    change 0≤term i+term (m i)
    have := nn i; have := nn (m i); grind only
  · exact codeBound half h2 L T z p diff A
  · exact populationTotal half h2 L T z p A orth
  · exact mass

end Field

end RankSeven.HighestCodeLocalization

#print axioms RankSeven.HighestCodeLocalization.innerBound
#print axioms RankSeven.HighestCodeLocalization.pairedPeak
#print axioms RankSeven.HighestCodeLocalization.codeBound
#print axioms RankSeven.HighestCodeLocalization.populationTotal
#print axioms RankSeven.HighestCodeLocalization.physicalPeak

