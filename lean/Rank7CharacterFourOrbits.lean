import Rank7StabilizerExteriorTrace

namespace RankSeven.CharacterFourOrbits

open Lean.Grind Pauli
variable {α R : Type} [CommRing R]

structure Action (α : Type) where
  x : α→α
  y : α→α
  xx : ∀i,x (x i)=i
  yy : ∀i,y (y i)=i
  commute : ∀i,y (x i)=x (y i)
  xFree : ∀i,i≠x i
  yFree : ∀i,i≠y i
  different : ∀i,x i≠y i

def orbit (H : Action α) (i : α) := [i,H.x i,H.y i,H.x (H.y i)]

private def act (H : Action α) (i : α) (x y : Bool) :=
  if x then (if y then H.x (H.y i) else H.x i) else if y then H.y i else i

private theorem actionLaw (H : Action α) (i : α) (a b c d : Bool) :
    act H (act H i a b) c d=act H i (a^^c) (b^^d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [act,H.commute,H.xx,H.yy]

private theorem inOrbit (H : Action α) (i j : α) : j∈orbit H i ↔ ∃x y,j=act H i x y := by
  constructor
  · intro h; simp only [orbit,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h
    · exact ⟨false,false,h⟩
    · exact ⟨true,false,h⟩
    · exact ⟨false,true,h⟩
    · exact ⟨true,true,h⟩
  · rintro ⟨x,y,rfl⟩; cases x <;> cases y <;> simp [act,orbit]

private theorem orbitSymm (H : Action α) {i j : α} (h : i∈orbit H j) : j∈orbit H i := by
  obtain ⟨a,b,eq⟩ := (inOrbit H j i).mp h
  apply (inOrbit H i j).mpr; refine ⟨a,b,?_⟩; rw [eq,actionLaw]; cases a <;> cases b <;> rfl

private theorem orbitTrans (H : Action α) {i j k : α} (h : i∈orbit H j) (t : j∈orbit H k) : i∈orbit H k := by
  obtain ⟨a,b,e⟩ := (inOrbit H j i).mp h; obtain ⟨c,d,f⟩ := (inOrbit H k j).mp t
  exact (inOrbit H k i).mpr ⟨c^^a,d^^b,by rw [e,f,actionLaw]⟩

theorem orbitNodup (H : Action α) (i : α) : (orbit H i).Nodup := by
  have first : i≠H.x (H.y i) := by intro h; have m := congrArg H.x h; rw [H.xx] at m; exact H.different i m
  have both : H.x i≠H.x (H.y i) := by intro h; have m := congrArg H.x h; rw [H.xx,H.xx] at m; exact H.yFree i m
  simp [orbit,H.xFree,H.yFree,H.different,first,both]

structure Partition (H : Action α) where
  centers : List α
  nodup : centers.Nodup
  separated : ∀a∈centers,∀b∈centers,a∈orbit H b → a=b
  cover : ∀p,∃a∈centers,p∈orbit H a

theorem partitionExists (H : Action α) (xs : List α) (all : ∀i,i∈xs) : Nonempty (Partition H) := by
  classical
  have f (ys : List α) : ∃ cs : List α,cs.Nodup ∧ (∀a∈cs,∀b∈cs,a∈orbit H b → a=b) ∧
      ∀p∈ys,∃a∈cs,p∈orbit H a := by
    induction ys with
    | nil => exact ⟨[],by simp,by simp,by simp⟩
    | cons p ys ih =>
      obtain ⟨cs,nd,sep,cov⟩ := ih
      by_cases inside : ∃a∈cs,p∈orbit H a
      · exact ⟨cs,nd,sep,fun q h => (List.mem_cons.mp h).elim (fun e => e ▸ inside) (cov q)⟩
      · have own : p∈orbit H p := List.mem_cons_self
        have out : p∉cs := fun hp => inside ⟨p,hp,own⟩
        refine ⟨p::cs,List.nodup_cons.mpr ⟨out,nd⟩,?_,?_⟩
        · intro a ha b hb h
          rcases List.mem_cons.mp ha with ea|ma <;> rcases List.mem_cons.mp hb with eb|mb
          · exact ea.trans eb.symm
          · subst a; exact False.elim (inside ⟨b,mb,h⟩)
          · subst b; exact False.elim (inside ⟨a,ma,orbitSymm H h⟩)
          · exact sep _ ma _ mb h
        · intro a ha; cases List.mem_cons.mp ha with
          | inl e => subst a; exact ⟨p,List.mem_cons_self,own⟩
          | inr h => obtain ⟨b,mb,h⟩ := cov a h; exact ⟨b,List.mem_cons_of_mem p mb,h⟩
  obtain ⟨cs,nd,sep,cov⟩ := f xs
  exact ⟨⟨cs,nd,sep,fun p => cov p (all p)⟩⟩

private theorem sumPerm {xs ys : List α} (p : xs.Perm ys) (f : α→R) : sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (fun v => f a+v) ih
  | swap a b xs => change f b+(f a+_)=f a+(f b+_); grind only
  | trans _ _ ih jh => exact ih.trans jh

private theorem restrict (xs ys : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (yd : ys.Nodup) (f : α→R)
    [DecidableEq α] : sumOver xs (fun i => if i∈ys then f i else 0)=sumOver ys f := by
  let P (i : α) := decide (i∈ys)
  have filtered (us : List α) : sumOver (us.filter P) f=sumOver us (fun i => if i∈ys then f i else 0) := by
    induction us with
    | nil => rfl
    | cons i us ih => rw [List.filter_cons]; by_cases h : i∈ys <;> simp [P,h,sumOver] at ih ⊢ <;> grind only
  rw [←filtered]
  apply sumPerm; have fd : (xs.filter P).Nodup := nd.filter P
  apply List.perm_iff_count.mpr; intro i; rw [fd.count,yd.count]; simp [P,full]

theorem orbitSum (H : Action α) (P : Partition H) (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (f : α→R) :
    sumOver xs f=sumOver P.centers (fun c => sumOver (orbit H c) f) := by
  classical
  have count (i : α) : f i=sumOver P.centers (fun c => if i∈orbit H c then f i else 0) := by
    obtain ⟨r,hr,hit⟩ := P.cover i
    conv => lhs; rw [←ExteriorPauliBase.sumOnIndex P.centers r (fun _ => f i) P.nodup hr]
    apply AnticommutingDefect.sumCongrMem; intro c hc
    have e : i∈orbit H c ↔ r=c := ⟨fun h => P.separated _ hr _ hc (orbitTrans H (orbitSymm H hit) h),fun h => h ▸ hit⟩
    by_cases eq : r=c <;> simp [e,eq]
  rw [sumOverCongr _ count,sumOverSwap]
  apply sumOverCongr; intro c; exact restrict xs (orbit H c) nd full (orbitNodup H c) f

theorem matchingPrice [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (H : Action α) (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (m : α→R)
    (bounds : ∀i,0≤m i ∧ m i≤1) (total : sumOver xs m≤6) :
    sumOver xs (fun i => m i*(m (H.x i)+m (H.y i)))≤10 := by
  obtain ⟨P⟩ := partitionExists H xs full
  let left c := m c+m (H.x (H.y c))
  let right c := m (H.x c)+m (H.y c)
  have grouping (c : α) : sumOver (orbit H c) m=left c+right c := by
    change m c+(m (H.x c)+(m (H.y c)+(m (H.x (H.y c))+0)))=_
    unfold left right; grind only
  rw [orbitSum H P xs nd full m,sumOverCongr _ grouping] at total
  have b (c : α) : 0≤left c+right c ∧ left c+right c≤4 := by
    have i := bounds c; have j := bounds (H.x c); have k := bounds (H.y c); have l := bounds (H.x (H.y c))
    unfold left right; grind only
  have price := SixPointRounding.sectorFive P.centers left right (fun c => left c*right c) (fun c _ => b c) total (fun _ _ => Std.le_refl _)
  have per (c : α) : sumOver (orbit H c) (fun i => m i*(m (H.x i)+m (H.y i)))=2*(left c*right c) := by
    simp only [orbit,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,H.commute,H.xx,H.yy,left,right]; grind only
  rw [orbitSum H P xs nd full,sumOverCongr _ per,←sumOverMulLeft]; grind only

open PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform StabilizerPairedCharacters
open StabilizerSmallCodes StabilizerOddSector StabilizerExteriorTrace

abbrev Line {n : Nat} {G : MaximalFamily n} (T : Transversal G) := {p : Word n // p∈T.reps}

noncomputable def shift {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n) (i : Line T) : Line T :=
  ⟨representative T (wordAdd i.val w),(represents T _).1⟩

private theorem cancelRight {n : Nat} (x y w : Word n) : wordAdd (wordAdd x w) (wordAdd y w)=wordAdd x y := by
  rw [wordAddComm y w,←wordAddAssoc,wordAddCancel]

private theorem cancelLeft {n : Nat} (w x y : Word n) : wordAdd (wordAdd w x) (wordAdd w y)=wordAdd x y := by
  rw [wordAddComm w x,wordAddComm w y,cancelRight]

theorem repCongr {n : Nat} {G : MaximalFamily n} (T : Transversal G) {x y : Word n} (h : equiv G x y) :
    representative T x=representative T y := repClass T _ _ (represents T y).1 (StabilizerCosetTransform.trans h (represents T y).2)

theorem shiftSum {n : Nat} {G : MaximalFamily n} (T : Transversal G) (v w : Word n) (i : Line T) :
    shift T w (shift T v i)=shift T (wordAdd v w) i := by
  apply Subtype.ext; apply repCongr
  change wordAdd (wordAdd (representative T (wordAdd i.val v)) w) (wordAdd i.val (wordAdd v w))∈G.labels
  rw [←wordAddAssoc i.val v w,cancelRight]; exact StabilizerCosetTransform.symm (represents T _).2

theorem shiftTwice {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n) (i : Line T) : shift T w (shift T w i)=i :=
  Subtype.ext (mateInvol T w i.val i.property)

theorem shiftFree {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n) (hw : w∉G.labels) (i : Line T) : i≠shift T w i :=
  fun e => mateDifferent T w hw i.val (congrArg Subtype.val e)

theorem shiftDifferent {n : Nat} {G : MaximalFamily n} (T : Transversal G) (v w : Word n) (h : wordAdd v w∉G.labels) (i : Line T) :
    shift T v i≠shift T w i := by
  intro e; apply h
  have f := (represents T (wordAdd i.val v)).2
  have j := (represents T (wordAdd i.val w)).2
  have k := congrArg Subtype.val e
  change representative T (wordAdd i.val v)=representative T (wordAdd i.val w) at k
  rw [k] at f
  have m := StabilizerCosetTransform.trans f (StabilizerCosetTransform.symm j)
  change wordAdd (wordAdd i.val v) (wordAdd i.val w)∈G.labels at m; rwa [cancelLeft] at m

noncomputable def characterAction {n : Nat} {G : MaximalFamily n} (T : Transversal G) (v w : Word n)
    (hv : v∉G.labels) (hw : w∉G.labels) (hvw : wordAdd v w∉G.labels) : Action (Line T) :=
  ⟨shift T v,shift T w,shiftTwice T v,shiftTwice T w,fun i => by rw [shiftSum,shiftSum,wordAddComm v w],
    shiftFree T v hv,shiftFree T w hw,shiftDifferent T v w hvw⟩

theorem linesNodup {n : Nat} {G : MaximalFamily n} (T : Transversal G) : T.reps.attach.Nodup := by
  have nd : (T.reps.attach.map Subtype.val).Nodup := by rw [List.attach_map_subtype_val]; exact T.nodup
  exact List.Pairwise.of_map Subtype.val (fun _ _ h e => h (congrArg Subtype.val e)) nd

theorem lineSum {n : Nat} {G : MaximalFamily n} (T : Transversal G) (f : Word n→R) :
    sumOver T.reps.attach (fun a => f a.val)=sumOver T.reps f := by
  conv => rhs; rw [←List.attach_map_subtype_val T.reps]
  simp only [sumOver,List.map_map,Function.comp_def]

theorem translationSum {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n) (f : Line T→R) :
    sumOver T.reps.attach (fun a => f (shift T w a))=sumOver T.reps.attach f := by
  classical
  let xs := T.reps.attach
  have invol := shiftTwice T w
  have nd : (xs.map (shift T w)).Nodup := List.Pairwise.map _ (fun a b (ne : a≠b) eq =>
    ne (by have e := congrArg (shift T w) eq; simpa only [invol] using e)) (linesNodup T)
  have perm : (xs.map (shift T w)).Perm xs := by
    apply List.perm_iff_count.mpr; intro a; rw [nd.count,(linesNodup T).count]
    have moved : a∈xs.map (shift T w) := List.mem_map.mpr ⟨shift T w a,List.mem_attach _ _,invol a⟩
    simp only [moved,List.mem_attach,ite_true]
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm perm f

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem massCongr {n : Nat} {β : Type} (xs : List β) (half : R) {G : MaximalFamily n} (L : Lift G)
    (A : Basis n→β→ComplexScalar R) {p q : Word n} (h : equiv G p q) :
    mass xs half L A p=mass xs half L A q := by
  have e : block half L p=block half L q := by funext i j; unfold block; rw [sameCoset (R:=R) L p q h]
  unfold mass StabilizerPopulationRounding.pop; rw [e]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem rowOnLines {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w z : Word n) (m : Word n→R)
    (respect : ∀p q,equiv G p q → m p=m q) :
    sumOver T.reps (fun a => m (wordAdd a w)*m (wordAdd a z))=
    sumOver T.reps.attach (fun i => m i.val*m (shift T (wordAdd w z) i).val) := by
  let M (i : Line T) := m i.val
  have e (v : Word n) (i : Line T) : m (wordAdd i.val v)=M (shift T v i) :=
    respect _ _ (represents T _).2
  have d : wordAdd z (wordAdd w z)=w := by rw [wordAddComm z (wordAdd w z),wordAddCancel]
  let F (i : Line T) := M i*M (shift T (wordAdd w z) i)
  have eq (i : Line T) : m (wordAdd i.val w)*m (wordAdd i.val z)=F (shift T z i) := by
    rw [e,e]; unfold F; rw [shiftSum,d,CommSemiring.mul_comm]
  rw [←lineSum T (fun a => m (wordAdd a w)*m (wordAdd a z)),sumOverCongr _ eq,translationSum]

theorem sixMassBounds {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let xs := (List.finRange 7).filter (fun i => i.val<6)
    let m := mass xs half L A
    (∀p,0≤m p ∧ m p≤1) ∧ sumOver T.reps m=6 := by
  let xs := (List.finRange 7).filter (fun i => i.val<6)
  let v p (i : Fin 7) := StabilizerPopulationRounding.pop half L p (fun t => A t i)
  have six : xs=[0,1,2,3,4,5] := by decide
  have seven : List.finRange 7=[0,1,2,3,4,5,6] := by decide
  change (∀p,0≤sumOver xs (v p) ∧ sumOver xs (v p)≤1) ∧ sumOver T.reps (fun p => sumOver xs (v p))=6
  constructor
  · intro p; have pos (i : Fin 7) : 0≤v p i := StabilizerPopulationRounding.popNonnegative half h2 L p _
    have b := StabilizerPopulationRounding.populationBessel half h2 L p A orth
    change sumOver (List.finRange 7) (v p)≤1 at b
    refine ⟨Compression.sumOverNonnegative xs _ (fun i _ => pos i),?_⟩
    rw [seven] at b; rw [six]
    simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at b ⊢
    have z := pos 6; grind only
  · rw [sumOverSwap]
    have total (i : Fin 7) : sumOver T.reps (fun p => v p i)=1 := by
      unfold v; rw [StabilizerPopulationRounding.popTotal half h2 L T]
      have reSum {δ : Type} (ys : List δ) (w : δ→ComplexScalar R) : (sumOver ys w).re=sumOver ys (fun t => (w t).re) := by
        induction ys with | nil => rfl | cons j ys ih => change (w j+sumOver ys w).re=_; rw [ComplexScalar.re_add,ih]; rfl
      have o := congrArg ComplexScalar.re (orth i i)
      simpa only [PauliPairContraction.normSum,reSum,ite_true,ComplexScalar.re_one,ComplexScalar.re_star_mul_self] using o
    rw [sumOverCongr _ total,six]; simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; grind only

theorem selectorTrace {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (c a b : Word n) (hc : c∈T.reps) (ha : a∈T.reps) (hb : b∈T.reps)
    (ca : c≠a) (cb : c≠b) (ab : a≠b) (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    JointProbeGram.oddAverage half (fun p => if member z c a b p then JointProbeGram.sixVertexMass A p else 0)≤5 := by
  classical
  let xs := (List.finRange 7).filter (fun i => i.val<6)
  let m := mass xs half L A
  let M (i : Line T) := m i.val
  let v := wordAdd c a
  let w := wordAdd c b
  let V := center z c a
  let W := center z c b
  have ev : wordAdd V z.offset=v := by change wordAdd (wordAdd z.offset v) z.offset=v; rw [wordAddComm z.offset v,wordAddCancel]
  have ew : wordAdd W z.offset=w := by change wordAdd (wordAdd z.offset w) z.offset=w; rw [wordAddComm z.offset w,wordAddCancel]
  have h1 : v∉G.labels := fun h => ca (T.separated c hc a ha h)
  have h2' : w∉G.labels := fun h => cb (T.separated c hc b hb h)
  have h3 : wordAdd v w∉G.labels := by unfold v w; rw [cancelLeft]; exact fun h => ab (T.separated a ha b hb h)
  let H := characterAction T v w h1 h2' h3
  have bounds := sixMassBounds half h2 L T A orth
  change (∀p,0≤m p ∧ m p≤1) ∧ sumOver T.reps m=6 at bounds
  have tot : sumOver T.reps.attach M≤6 := by rw [show sumOver T.reps.attach M=sumOver T.reps m from lineSum T m,bounds.2]; exact Std.le_refl _
  have price := matchingPrice H T.reps.attach (linesNodup T) (List.mem_attach T.reps) M (fun i => bounds.1 i.val) tot
  have respect (p q : Word n) (e : equiv G p q) : m p=m q := massCongr xs half L A e
  have coset (u : Word n) :
      2*JointProbeGram.oddAverage half (fun p => if wordAdd p u∈G.labels then wedgePrice xs A p else 0)≤
      sumOver T.reps.attach (fun i => M i*M (shift T (wordAdd u z.offset) i)) := by
    have s := cosetWedgePrice xs half h2 L T z u A
    change _≤sumOver T.reps (fun a => m (wordAdd a u)*m (wordAdd a z.offset)) at s
    rw [rowOnLines T u z.offset m respect] at s; exact s
  have one := coset V; have two := coset W; rw [ev] at one; rw [ew] at two
  change sumOver T.reps.attach (fun i => M i*(M (shift T v i)+M (shift T w i)))≤10 at price
  simp only [Semiring.left_distrib,sumOverAdd] at price
  have mv (p : Word n) : JointProbeGram.sixVertexMass A p=wedgePrice xs A p := by
    unfold JointProbeGram.sixVertexMass wedgePrice JointProbePayment.pairWeight
    apply sumOverCongr; intro e; rw [frameAmplitude]
  have evv : ¬equiv G V W := by change wordAdd (wordAdd z.offset v) (wordAdd z.offset w)∉G.labels; rw [cancelLeft]; exact h3
  have comb (p : Word n) : (if member z c a b p then JointProbeGram.sixVertexMass A p else 0)=
      (if wordAdd p V∈G.labels then wedgePrice xs A p else 0)+(if wordAdd p W∈G.labels then wedgePrice xs A p else 0) := by
    rw [mv]; change (if decide (wordAdd p V∈G.labels) || decide (wordAdd p W∈G.labels) then wedgePrice xs A p else 0)=_
    by_cases h : wordAdd p V∈G.labels <;> by_cases j : wordAdd p W∈G.labels
    · exact False.elim (evv (StabilizerCosetTransform.trans (StabilizerCosetTransform.symm h) j))
    all_goals simp [h,j] <;> grind only
  unfold JointProbeGram.oddAverage at one two ⊢
  rw [sumOverCongr _ comb,sumOverAdd]; grind only

end RankSeven.CharacterFourOrbits

#print axioms RankSeven.CharacterFourOrbits.orbitSum
#print axioms RankSeven.CharacterFourOrbits.matchingPrice
#print axioms RankSeven.CharacterFourOrbits.sixMassBounds
#print axioms RankSeven.CharacterFourOrbits.selectorTrace

