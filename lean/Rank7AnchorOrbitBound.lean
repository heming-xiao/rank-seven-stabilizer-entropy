import Rank7AnchorCharacterSupport
import Rank7AnchorExteriorFive

namespace RankSeven.AnchorOrbitBound
open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open CharacterFourOrbits StabilizerCosetTransform AnchorSteiner AnchorSteinerTest
variable {R J : Type} [CommRing R]
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance : NatCast R := Semiring.natCast
local notation "C" => ComplexScalar R

theorem orbitCount {n} {G : MaximalFamily n} (T : Transversal G) (a : Line T) (f : Line T→R) :
    sumOver (words n) (fun p=>f (shift T p a)) = (2:R)^n*sumOver T.reps.attach f := by
  let F:=fun p=>f (shift T p a)
  have fixed (g : Word n) (hg : g∈G.labels) : shift T g a=a := by
    apply Subtype.ext; apply StabilizerSmallCodes.repClass _ _ _ a.property
    change wordAdd (wordAdd a.val g) a.val∈G.labels
    rwa [wordAddComm a.val g,wordAddCancel]
  have invariant (p g : Word n) (hg:g∈G.labels) : F (wordAdd g p)=F p := by
    dsimp [F]; rw [←shiftSum,fixed g hg]
  rw [classFunction T F invariant,cardinalCast (R:=R) G,←lineSum T F]
  have flip (z : Line T) : F z.val=f (shift T a.val z) := by
    change f ⟨_,_⟩=f ⟨_,_⟩; congr 1; apply Subtype.ext
    change StabilizerPairedCharacters.representative T (wordAdd a.val z.val)=StabilizerPairedCharacters.representative T (wordAdd z.val a.val)
    rw [wordAddComm a.val z.val]
  rw [sumOverCongr T.reps.attach flip,translationSum T a.val f]

private theorem sumLe (B : List J) {f g : J→R} (h : ∀i∈B,f i≤g i) :
    sumOver B f≤sumOver B g := by
  induction B with
  | nil => exact Std.le_refl _
  | cons j B ih =>
    have x:=h j List.mem_cons_self; have z:=ih (fun i hi=>h i (List.mem_cons_of_mem _ hi))
    change f j+sumOver B f≤g j+sumOver B g; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem permSum {B B' : List J} (h : B.Perm B') (f : J→R) : sumOver B f=sumOver B' f := by
  induction h with
  | nil => rfl
  | cons j _ ih => exact congrArg (fun z=>f j+z) ih
  | swap x y B => change f y+(f x+sumOver B f)=f x+(f y+sumOver B f); grind only
  | trans _ _ ih jh => exact ih.trans jh

private theorem localPrice (x y t : C) (unit : normSq t=1) :
    2*(star x*(t*y)).re ≤ normSq x+normSq y := by
  have e : normSq (x-(t*y))=normSq x+normSq (t*y)-2*(star x*(t*y)).re := by
    generalize t*y=z; unfold normSq; simp; grind only
  have nn:=normSq_nonnegative (x-(t*y)); rw [e,normSq_mul,unit,Semiring.one_mul] at nn; grind only

noncomputable def gate {n} {G : MaximalFamily n} {T : Transversal G}
    (b : Line T) (occ : J→List (Line T)) (v : J→C) (j : J) : C :=
    @ite C (b∈occ j) (Classical.propDecidable _) (v j) 0

/-- The real Pauli expectation on a state with the anchor occupied is bounded
by the occupation of its translate. This uses only its induced involutive
monomial action and unit phase, with no sign or square-root convention. -/
theorem occupationPrice {n} {G : MaximalFamily n} (T : Transversal G) (a : Line T) (p : Word n)
    (B : List J) (occ : J→List (Line T)) (move : J→J) (v phase : J→C)
    (perm : (B.map move).Perm B) (inv : ∀j,move (move j)=j)
    (cov : ∀j,a∈occ (move j)↔shift T p a∈occ j)
    (anch : ∀j,a∉occ j→v j=0) (unit : ∀j,normSq (phase j)=1) :
    sumOver B (fun j=>(star (v j)*(phase j*v (move j))).re)
      ≤ mass B (gate (shift T p a) occ v) := by
  classical
  let r:=shift T p a
  let V:=gate r occ v
  have same (j : J) : (star (v j)*(phase j*v (move j))).re=(star (V j)*(phase j*V (move j))).re := by
    by_cases hj : r∈occ j
    · by_cases hk : r∈occ (move j)
      · simp only [V,gate,hj,hk,ite_true]
      · have z:=anch j (fun ha=>hk ((cov (move j)).mp (by rwa [inv])))
        simp only [V,gate,hj,hk,ite_true,ite_false,z]; simp; grind only
    · have z:=anch (move j) (fun ha=>hj ((cov j).mp ha))
      by_cases hk : r∈occ (move j) <;> simp only [V,gate,hj,hk,ite_true,ite_false,z] <;> simp <;> grind only
  have reindexed : sumOver B (fun j=>normSq (V (move j)))=sumOver B (fun j=>normSq (V j)) := by
    simpa only [sumOver,List.map_map,Function.comp_def] using permSum perm (fun j=>normSq (V j))
  rw [sumOverCongr B same]
  have price:=sumLe B (fun j _=>localPrice (V j) (V (move j)) (phase j) (unit j))
  rw [←sumOverMulLeft,sumOverAdd,reindexed] at price
  change _ ≤ sumOver B (fun j=>normSq (V j))
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem countMembers {A : Type} [DecidableEq A] (all : List A) (nd : all.Nodup) (full : ∀x,x∈all)
    (S : List A) (sn : S.Nodup) (z : R) :
    sumOver all (fun a=>if a∈S then z else 0)=(S.length:R)*z := by
  induction S with
  | nil =>
    have zero (L : List A) : sumOver L (fun _=>(0:R))=0 := by
      induction L with
      | nil => rfl
      | cons a L ih => change 0+sumOver L _=0; rw [ih]; grind only
    simp only [List.not_mem_nil,ite_false,List.length_nil]; rw [zero]; grind
  | cons a S ih =>
    obtain ⟨out,sn⟩:=List.nodup_cons.mp sn
    have each (b : A) : (if b∈a::S then z else 0) =
        (if a=b then z else 0)+(if b∈S then z else 0) := by
      by_cases eq : a=b
      · subst b; simp [out]; grind only
      · have ne:=Ne.symm eq; simp [eq,ne]; grind only
    rw [sumOverCongr all each,sumOverAdd,ExteriorPauliBase.sumOnIndex all a (fun _=>z) nd (full a),ih sn]
    simp only [List.length_cons]; grind

/-- All d² physical words are reindexed over stabilizer lines. The normalized
four-copy actuator has price (4/d), independent of the number of available
sites, and independent of all wedge-reordering phases. -/
theorem occupiedFourAverage {n} {G : MaximalFamily n} (T : Transversal G) (a : Line T)
    (B : List J) (occ : J→List (Line T)) (move : Word n→J→J) (v : J→C) (phase : Word n→J→C)
    (perm : ∀p,(B.map (move p)).Perm B) (inv : ∀p j,move p (move p j)=j)
    (cov : ∀p j,a∈occ (move p j)↔shift T p a∈occ j)
    (anch : ∀j,a∉occ j→v j=0) (unit : ∀p j,normSq (phase p j)=1)
    (nd : ∀j,(occ j).Nodup) (four : ∀j,(occ j).length=4) :
    sumOver (words n) (fun p=>sumOver B (fun j=>(star (v j)*(phase p j*v (move p j))).re)) ≤
      (2:R)^n * (4*mass B v) := by
  classical
  let f:=fun r=>mass B (gate r occ v)
  have cap:=sumLe (words n) (fun p _=>occupationPrice T a p B occ (move p) v (phase p)
      (perm p) (inv p) (cov p) anch (unit p))
  change _≤sumOver (words n) (fun p=>f (shift T p a)) at cap
  rw [orbitCount T a f] at cap
  have total : sumOver T.reps.attach f=4*mass B v := by
    change sumOver T.reps.attach (fun r=>sumOver B (fun j=>normSq (gate r occ v j)))=_
    rw [sumOverSwap]; unfold mass; rw [sumOverMulLeft]; apply sumOverCongr; intro j
    have e (r : Line T) : normSq (gate r occ v j)=(if r∈occ j then normSq (v j) else 0) := by
      by_cases hr : r∈occ j <;> simp [gate,hr]
    rw [sumOverCongr T.reps.attach e]
    have hc:=countMembers T.reps.attach (linesNodup T) (fun r=>List.mem_attach _ _) (occ j) (nd j) (normSq (v j))
    rw [four] at hc
    have hc4 : (Nat.cast (4:Nat):R)=4 := by grind only
    rw [hc4] at hc; rw [←hc]; apply sumOverCongr; intro r
    by_cases hr : r∈occ j <;> simp [hr]
  rw [total] at cap; exact cap

end RankSeven.AnchorOrbitBound
#print axioms RankSeven.AnchorOrbitBound.orbitCount
#print axioms RankSeven.AnchorOrbitBound.occupationPrice
#print axioms RankSeven.AnchorOrbitBound.occupiedFourAverage
