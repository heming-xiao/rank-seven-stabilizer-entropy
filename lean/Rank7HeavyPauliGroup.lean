import Rank7PhysicalFourierDefect

/-! Maximal commuting Pauli labels containing the physically large
first-column coefficients. -/
namespace RankSeven.HeavyPauliGroup
open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeadPauliFourier ThreeLegFourier PhysicalFourierDefect
open PhysicalCompressionEffect (OrthonormalFrame)
variable {R α : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

structure MaximalFamily (n : Nat) where
  labels : List (Word n)
  nodup : labels.Nodup
  criterion : ∀ p : Word n, p∈labels ↔ ∀ q∈labels,anti p q=false

private def Commutes (xs : List (Word n)) := ∀ p∈xs,∀ q∈xs,anti p q=false

private theorem extend (candidates seed : List (Word n)) (nd : seed.Nodup) (comm : Commutes seed) :
    ∃ xs : List (Word n),xs.Nodup ∧ Commutes xs ∧ seed⊆xs ∧
      ∀ p∈candidates,(∀ q∈xs,anti p q=false) → p∈xs := by
  classical
  induction candidates generalizing seed with
  | nil => exact ⟨seed,nd,comm,fun _ h => h,by simp⟩
  | cons a cs ih =>
    by_cases existing : a∈seed
    · obtain ⟨xs,n,c,sub,full⟩ := ih seed nd comm
      refine ⟨xs,n,c,sub,?_⟩; intro p hp h
      exact (List.mem_cons.mp hp).elim (fun eq => eq ▸ sub existing) (fun inCs => full p inCs h)
    · by_cases ok : ∀ q∈seed,anti a q=false
      · have pair : Commutes (a::seed) := by
          intro p hp q hq
          cases List.mem_cons.mp hp with
          | inl e =>
            subst p; cases List.mem_cons.mp hq with
            | inl e => subst q; exact antiSelf a
            | inr h => exact ok q h
          | inr h =>
            cases List.mem_cons.mp hq with
            | inl e => subst q; rw [antiSymm]; exact ok p h
            | inr j => exact comm p h q j
        obtain ⟨xs,n,c,sub,full⟩ := ih (a::seed) (List.nodup_cons.mpr ⟨existing,nd⟩) pair
        refine ⟨xs,n,c,fun _ h => sub (List.mem_cons_of_mem _ h),?_⟩; intro p hp h
        exact (List.mem_cons.mp hp).elim (fun eq => eq ▸ sub List.mem_cons_self) (fun inCs => full p inCs h)
      · obtain ⟨xs,n,c,sub,full⟩ := ih seed nd comm
        refine ⟨xs,n,c,sub,?_⟩; intro p hp h
        cases List.mem_cons.mp hp with
        | inl eq => subst p; exact False.elim (ok fun q hq => h q (sub hq))
        | inr j => exact full p j h

theorem maximalExtension (seed : List (Word n)) (nd : seed.Nodup)
    (commute : ∀ p∈seed,∀ q∈seed,anti p q=false) :
    ∃ G : MaximalFamily n, seed⊆G.labels := by
  obtain ⟨xs,nodup,cs,subs,full⟩ := extend (words n) seed nd commute
  exact ⟨⟨xs,nodup,fun p => ⟨cs p,full p (AntiPairIncidence.wordsComplete p)⟩⟩,subs⟩

theorem zeroMem (G : MaximalFamily n) : unitWord n∈G.labels :=
  (G.criterion _).mpr (fun p _ => by rw [antiSymm,antiZero])

theorem addMem (G : MaximalFamily n) (a b : Word n) (ha : a∈G.labels) (hb : b∈G.labels) :
    wordAdd a b∈G.labels := by
  apply (G.criterion _).mpr; intro q hq; rw [antiAddLeft,(G.criterion a).mp ha q hq,(G.criterion b).mp hb q hq]; rfl

theorem shiftPerm (G : MaximalFamily n) (a : Word n) (ha : a∈G.labels) :
    (G.labels.map (fun v => wordAdd v a)).Perm G.labels := by
  let f v := wordAdd v a
  have inj (v w : Word n) (h : f v=f w) : v=w := by
    have e := congrArg (fun u => wordAdd u a) h
    simpa only [f,wordAddCancel] using e
  have nd : (G.labels.map f).Nodup := List.Pairwise.map f (fun v w (ne : v≠w) e => ne (inj v w e)) G.nodup
  have equiv (v : Word n) : v∈G.labels.map f ↔ v∈G.labels := by
    refine ⟨?_,?_⟩
    · intro h; obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h; exact addMem G w a hw ha
    · intro h; exact List.mem_map.mpr ⟨f v,addMem G v a h ha,wordAddCancel v a⟩
  change (G.labels.map f).Perm G.labels
  apply List.perm_iff_count.mpr; intro v; rw [nd.count,G.nodup.count]; simp only [equiv]

private theorem sumPerm {xs ys : List α} (p : xs.Perm ys) (f : α → R) : sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (fun z => f a+z) ih
  | swap a b xs => change f b+(f a+_)=f a+(f b+_); grind only
  | trans _ _ ih jh => exact ih.trans jh

theorem groupSumShift (G : MaximalFamily n) (a : Word n) (ha : a∈G.labels) (f : Word n → R) :
    sumOver G.labels (fun v => f (wordAdd v a))=sumOver G.labels f := by
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (shiftPerm G a ha) f

attribute [local instance] Semiring.natCast
private theorem ones (xs : List α) : sumOver xs (fun _ => (1:R))=Nat.cast xs.length := by
  induction xs with
  | nil => change 0=Nat.cast 0; rw [Semiring.natCast_zero]
  | cons a xs ih => change 1+sumOver xs _=Nat.cast (xs.length+1); rw [ih,Semiring.natCast_succ]; grind only

theorem characterSum [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (G : MaximalFamily n) (p : Word n) :
    sumOver G.labels (fun q => (chi p q:R))=if p∈G.labels then Nat.cast G.labels.length else 0 := by
  by_cases h : p∈G.labels
  · rw [ite_eq_left h,←ones]
    unfold sumOver; congr 1; apply List.map_congr_left; intro q hq
    have a := (G.criterion p).mp h q hq; simp only [chi,a,phase,Bool.false_eq_true,ite_false]
  · rw [ite_eq_right h]
    have witness : ∃q∈G.labels,anti p q=true := by
      apply Classical.byContradiction; intro no; apply h; apply (G.criterion p).mpr; intro q hq
      cases c : anti p q with
      | false => rfl
      | true => exact False.elim (no ⟨q,hq,c⟩)
    obtain ⟨q,hq,eq⟩ := witness
    have moved := groupSumShift G q hq (fun v => (chi p v:R))
    have s (v : Word n) : chi p (wordAdd v q)=(-1:R)*chi p v := by
      simp only [chi,antiAddRight,eq]; cases anti p v <;> simp [phase] <;> grind only
    rw [sumOverCongr _ s,←sumOverMulLeft] at moved; grind only

private theorem filterSum {δ : Type} (xs : List δ) (f : δ → R) (pred : δ → Bool) :
    sumOver (xs.filter pred) f=sumOver xs (fun a => if pred a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.filter_cons]; cases e : pred a <;> simp [e,sumOver] at ih ⊢ <;> grind only

theorem sumMembership (G : MaximalFamily n) (f : Word n → R) :
    sumOver (words n) (fun p => if p∈G.labels then f p else 0)=sumOver G.labels f := by
  let pred (p : Word n) := decide (p∈G.labels)
  have perm : ((words n).filter pred).Perm G.labels := by
    have nd : ((words n).filter pred).Nodup := (MixedDefect.allWordsNodup n).filter pred
    apply List.perm_iff_count.mpr; intro v
    rw [nd.count,G.nodup.count]
    simp [pred,AntiPairIncidence.wordsComplete]
  rw [←sumPerm perm f,filterSum]; simp [pred]

theorem cardinalSquared [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (G : MaximalFamily n) : (Nat.cast G.labels.length:R)^2=(4:R)^n := by
  let J := unitWord n
  have freq (q : Word n) : sumOver (words n) (fun p => (chi p q:R))=if q=J then (4:R)^n else 0 := by
    have e := characterOrthogonality (C:=R) q J
    have zero (p : Word n) : (chi p J:R)=1 := by simp only [J,chi,antiZero,phase,Bool.false_eq_true,ite_false]
    simpa only [zero,Semiring.mul_one] using e
  have swap := sumOverSwap (words n) G.labels (fun p q => (chi p q:R))
  simp only [freq,characterSum] at swap
  rw [sumMembership G (fun _ => Nat.cast G.labels.length)] at swap
  have constant (xs : List (Word n)) (c : R) : sumOver xs (fun _ => c)=Nat.cast xs.length*c := by
    have e := sumOverMulRight xs (fun _ => (1:R)) c; rw [ones] at e; simpa only [Semiring.one_mul] using e.symm
  rw [constant] at swap
  have sel := ExteriorPauliBase.sumOnIndex G.labels J (fun _ => (4:R)^n) G.nodup (zeroMem G)
  have eq (p : Word n) : (if p=J then (4:R)^n else 0)=(if J=p then (4:R)^n else 0) := by by_cases h : p=J <;> simp [h,Eq.comm]
  rw [sumOverCongr _ eq,sel] at swap; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem cardinalCast (G : MaximalFamily n) : (Nat.cast G.labels.length:R)=(2:R)^n := by
  have power (m : Nat) : (4:R)^m=((2:R)^m)^2 := by
    induction m with
    | zero => simp only [Semiring.pow_zero]; grind only
    | succ n ih => simp only [Semiring.pow_succ,ih]; grind only
  have p := power n
  have eq := cardinalSquared (R:=R) G
  have positive (m : Nat) : 0<(2:R)^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)
  have pos := positive n
  have nonneg : 0≤(Nat.cast G.labels.length:R) := by
    rw [←ones]; exact Compression.sumOverNonnegative _ _ (fun _ _ => OrderedRing.zero_le_one)
  have f : (Nat.cast G.labels.length-(2:R)^n)*(Nat.cast G.labels.length+(2:R)^n)=0 := by grind only
  by_cases h : Nat.cast G.labels.length=(2:R)^n
  · exact h
  · have signs : Nat.cast G.labels.length<(2:R)^n ∨ (2:R)^n<Nat.cast G.labels.length := by grind only
    rcases signs with h'|h'
    · have u := OrderedRing.mul_pos (show 0<(2:R)^n-Nat.cast G.labels.length by grind only)
          (show 0<Nat.cast G.labels.length+(2:R)^n by grind only)
      grind only
    · have u := OrderedRing.mul_pos (show 0<Nat.cast G.labels.length-(2:R)^n by grind only)
          (show 0<Nat.cast G.labels.length+(2:R)^n by grind only)
      grind only

variable [DecidableRel ((·≤·) : R→R→Prop)]

theorem physicalFamily (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    ∃ G : MaximalFamily (k+3),
      (∀ p,1<2*(head (localH A p))^2 → p∈G.labels) ∧
      7*(half^(k+3)*sumOver (words (k+3)) (fun p => if p∈G.labels then 0 else (middle (localH A p))^2))≤
        60*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa := by
  classical
  let n := k+3
  let seed := (words n).filter (fun p => decide (1<2*(head (localH A p))^2))
  have mem (p : Word n) : p∈seed ↔ 1<2*(head (localH A p))^2 := by
    simp [seed,AntiPairIncidence.wordsComplete]
  have nd : seed.Nodup := (MixedDefect.allWordsNodup n).filter _
  obtain ⟨G,inc⟩ := maximalExtension seed nd (fun p hp q hq => heavyCommute A orth p q ((mem p).mp hp) ((mem q).mp hq))
  have inside (p : Word n) (h : 1<2*(head (localH A p))^2) : p∈G.labels := inc ((mem p).mpr h)
  refine ⟨G,inside,?_⟩
  let f p := if p∈G.labels then 0 else (middle (localH A p))^2
  let g p := if 2*(head (localH A p))^2≤1 then (middle (localH A p))^2 else 0
  have bound (p : Word n) : f p≤g p := by
    have sq := squareNonnegative (middle (localH A p))
    by_cases hp : p∈G.labels
    · unfold f g; simp only [hp,ite_true]; split <;> grind only
    · have small : 2*(head (localH A p))^2≤1 := by apply Classical.byContradiction; intro no; exact hp (inside p (by grind only))
      simp [f,g,hp,small]
  have le := Compression.sumOverNonnegative (words n) (fun i => g i-f i) (fun i _ => by have := bound i; grind only)
  rw [Compression.sumOverSub] at le
  have pos (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have up := OrderedRing.mul_le_mul_of_nonneg_left (show sumOver (words n) f≤sumOver (words n) g by grind only) (pos n)
  have hm := (weakMassLocalization half h2 k A mu orth).2.2
  change 7*(half^n*sumOver (words n) g)≤_ at hm
  change 7*(half^n*sumOver (words n) f)≤_
  grind only

end Order

end RankSeven.HeavyPauliGroup

#print axioms RankSeven.HeavyPauliGroup.maximalExtension
#print axioms RankSeven.HeavyPauliGroup.cardinalCast
#print axioms RankSeven.HeavyPauliGroup.characterSum
#print axioms RankSeven.HeavyPauliGroup.physicalFamily

