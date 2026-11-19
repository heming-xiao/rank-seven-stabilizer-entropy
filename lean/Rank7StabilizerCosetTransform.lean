import Rank7StabilizerCharacterBasis

namespace RankSeven.StabilizerCosetTransform

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis
variable {C R : Type} [CommRing C] [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def equiv (G : MaximalFamily n) (a b : Word n) : Prop := wordAdd a b∈G.labels

theorem refl (G : MaximalFamily n) (a : Word n) : equiv G a a := by
  unfold equiv; rw [wordAddSelf]; exact zeroMem G

theorem symm {G : MaximalFamily n} {a b : Word n} (h : equiv G a b) : equiv G b a := by
  unfold equiv at *; rwa [wordAddComm b a]

theorem trans {G : MaximalFamily n} {a b c : Word n} (h : equiv G a b) (j : equiv G b c) : equiv G a c := by
  have x := addMem G _ _ h j
  have t : wordAdd (wordAdd a b) (wordAdd b c)=wordAdd a c := by rw [←wordAddAssoc,wordAddCancel]
  rwa [t] at x

structure Transversal (G : MaximalFamily n) where
  reps : List (Word n)
  nodup : reps.Nodup
  separated : ∀ a∈reps,∀ b∈reps,equiv G a b → a=b
  cover : ∀ p,∃ a∈reps,equiv G p a

theorem transversalExists (G : MaximalFamily n) : Nonempty (Transversal G) := by
  classical
  have f (xs : List (Word n)) : ∃ ys : List (Word n), ys.Nodup ∧ (∀ a∈ys,∀ b∈ys,equiv G a b → a=b) ∧
      ∀p∈xs,∃a∈ys,equiv G p a := by
    induction xs with
    | nil => exact ⟨[],by simp,by simp,by simp⟩
    | cons p xs ih =>
      obtain ⟨ys,nd,sep,cov⟩ := ih
      by_cases haveP : ∃a∈ys,equiv G p a
      · exact ⟨ys,nd,sep,fun q h => (List.mem_cons.mp h).elim (fun e => e ▸ haveP) (cov q)⟩
      · have absent : p∉ys := fun hp => haveP ⟨p,hp,refl G p⟩
        refine ⟨p::ys,List.nodup_cons.mpr ⟨absent,nd⟩,?_,?_⟩
        · intro a ha b hb h
          rcases List.mem_cons.mp ha with ea|ma <;> rcases List.mem_cons.mp hb with eb|mb
          · exact ea.trans eb.symm
          · subst a; exact False.elim (haveP ⟨b,mb,h⟩)
          · subst b; exact False.elim (haveP ⟨a,ma,symm h⟩)
          · exact sep a ma b mb h
        · intro a ha; cases List.mem_cons.mp ha with
          | inl e => subst a; exact ⟨p,List.mem_cons_self,refl G p⟩
          | inr h => obtain ⟨b,mb,h⟩ := cov a h; exact ⟨b,List.mem_cons_of_mem p mb,h⟩
  obtain ⟨ys,nd,sep,cover⟩ := f (words n)
  exact ⟨⟨ys,nd,sep,fun p => cover p (AntiPairIncidence.wordsComplete p)⟩⟩

theorem enumerate {n : Nat} {G : MaximalFamily n} (T : Transversal G) (f : Word n → C) :
    sumOver (words n) f=sumOver T.reps (fun a => sumOver G.labels (fun g => f (wordAdd g a))) := by
  classical
  have count (p : Word n) : f p=sumOver T.reps (fun a => if equiv G p a then f p else 0) := by
    obtain ⟨r,hr,hpr⟩ := T.cover p
    conv => lhs; rw [←ExteriorPauliBase.sumOnIndex T.reps r (fun _ => f p) T.nodup hr]
    apply AnticommutingDefect.sumCongrMem; intro a ha
    have e : equiv G p a ↔ r=a := ⟨fun h => T.separated r hr a ha (trans (symm hpr) h),fun h => h ▸ hpr⟩
    by_cases h : r=a <;> simp [e,h]
  rw [sumOverCongr (words n) count,sumOverSwap]
  apply sumOverCongr; intro a
  let F p := if equiv G p a then f p else 0
  change sumOver (words n) F=_
  rw [←AntiPairIncidence.sumShift a F]
  simp only [F,equiv,wordAddCancel]
  rw [←sumMembership G (fun p => f (wordAdd p a))]

attribute [local instance] Semiring.natCast
private theorem sumConst {α : Type} (xs : List α) (c : C) : sumOver xs (fun _ => c)=Nat.cast xs.length*c := by
  induction xs with
  | nil => change 0=Nat.cast 0*c; rw [Semiring.natCast_zero,Semiring.zero_mul]
  | cons a xs ih => change c+sumOver xs _=Nat.cast (xs.length+1)*c; rw [ih,Semiring.natCast_succ]; grind only

theorem classFunction {n : Nat} {G : MaximalFamily n} (T : Transversal G) (f : Word n → C)
    (invariant : ∀p,∀g∈G.labels,f (wordAdd g p)=f p) :
    sumOver (words n) f=(Nat.cast G.labels.length:C)*sumOver T.reps f := by
  rw [enumerate T, sumOverMulLeft]; apply sumOverCongr; intro p
  rw [←sumConst]; apply AnticommutingDefect.sumCongrMem; intro g hg; exact invariant p g hg

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem dimensionSq (m : Nat) : (4:R)^m=((2:R)^m)^2 := by
  induction m with
  | zero => simp only [Semiring.pow_zero]; grind only
  | succ m ih => simp only [Semiring.pow_succ,ih]; grind only

theorem quotientSum {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (g : Word n) (hg : g∈G.labels) :
    sumOver T.reps (fun a => (chi a g:R))=if g=unitWord n then (2:R)^n else 0 := by
  have unit (a : Word n) : (chi a (unitWord n):R)=1 := by simp only [chi,antiZero,phase,Bool.false_eq_true,ite_false]
  have e := characterOrthogonality (C:=R) g (unitWord n)
  simp only [unit,Semiring.mul_one] at e
  have same (p h : Word n) (hh : h∈G.labels) : (chi (wordAdd h p) g:R)=chi p g := by
    have c := (G.criterion h).mp hh g hg
    simp only [chi,antiAddLeft,c,Bool.false_bne]
  rw [classFunction T _ same,cardinalCast (R:=R),dimensionSq] at e
  have inv := SectorDefectAccounting.dimensionInverse half h2 n
  have m := congrArg (fun u : R => half^n*u) e
  by_cases h : g=unitWord n <;> simp only [h,ite_true,ite_false] at e m ⊢ <;> grind only

/-- Parseval on a transversal of the ambient symplectic characters,
restricted to the given maximal commuting Pauli group. -/
theorem parseval {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f : Word n→R) :
    sumOver T.reps (fun a => (half^n*sumOver G.labels (fun g => chi a g*f g))^2)=
      half^n*sumOver G.labels (fun g => (f g)^2) := by
  let χ (a g : Word n) : R := chi a g
  let F (a g : Word n) := χ a g*f g
  have sq (a : Word n) : (half^n*sumOver G.labels (F a))^2=
      (half^n)^2*sumOver G.labels (fun p => sumOver G.labels (fun q => (χ a p*χ a q)*(f p*f q))) := by
    have expand : sumOver G.labels (F a)*sumOver G.labels (F a)=
        sumOver G.labels (fun p => sumOver G.labels (fun q => (χ a p*χ a q)*(f p*f q))) := by
      rw [sumOverMulRight]; apply sumOverCongr; intro p; rw [sumOverMulLeft]; apply sumOverCongr; intro q; unfold F; grind only
    grind only
  change sumOver T.reps (fun a => (half^n*sumOver G.labels (F a))^2)=_
  rw [sumOverCongr _ sq,←sumOverMulLeft,sumOverSwap T.reps G.labels]
  have inside (p : Word n) (hp : p∈G.labels) :
      sumOver T.reps (fun a => sumOver G.labels (fun q => (χ a p*χ a q)*(f p*f q)))=(2:R)^n*(f p)^2 := by
    rw [sumOverSwap]
    have inner (q : Word n) (hq : q∈G.labels) :
        sumOver T.reps (fun a => (χ a p*χ a q)*(f p*f q))=if p=q then (2:R)^n*(f p)^2 else 0 := by
      rw [←sumOverMulRight]
      have pr (a : Word n) : χ a p*χ a q=chi a (wordAdd p q) := (characterAddRight _ _ _).symm
      rw [sumOverCongr _ pr,quotientSum half h2 T _ (addMem G _ _ hp hq)]
      simp only [wordAddEqZero]
      by_cases h : p=q <;> simp only [h,ite_true,ite_false] <;> grind only
    rw [AnticommutingDefect.sumCongrMem _ _ _ inner]
    exact ExteriorPauliBase.sumOnIndex G.labels p (fun _ => (2:R)^n*(f p)^2) G.nodup hp
  rw [AnticommutingDefect.sumCongrMem _ _ _ inside,←sumOverMulLeft]
  have inv := SectorDefectAccounting.dimensionInverse half h2 n; grind only

theorem transformSum {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f : Word n→R) :
    sumOver T.reps (fun a => half^n*sumOver G.labels (fun g => chi a g*f g))=f (unitWord n) := by
  rw [←sumOverMulLeft,sumOverSwap]
  have e (g : Word n) (hg : g∈G.labels) : sumOver T.reps (fun a => chi a g*f g)=
      if unitWord n=g then (2:R)^n*f g else 0 := by
    rw [←sumOverMulRight,quotientSum half h2 T _ hg]
    by_cases h : g=unitWord n <;> simp [h,Eq.comm,Semiring.zero_mul]
  rw [AnticommutingDefect.sumCongrMem _ _ _ e,ExteriorPauliBase.sumOnIndex _ _ _ G.nodup (zeroMem G)]
  have inv := SectorDefectAccounting.dimensionInverse half h2 n; grind only

end Order

end RankSeven.StabilizerCosetTransform

#print axioms RankSeven.StabilizerCosetTransform.transversalExists
#print axioms RankSeven.StabilizerCosetTransform.enumerate
#print axioms RankSeven.StabilizerCosetTransform.quotientSum
#print axioms RankSeven.StabilizerCosetTransform.transformSum
#print axioms RankSeven.StabilizerCosetTransform.parseval

