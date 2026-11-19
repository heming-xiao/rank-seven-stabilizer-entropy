import Rank7AnchorScoreEnumeration

namespace RankSeven.AnchorVacantScore
open Lean.Grind Pauli ComplexScalar HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits
open AnchorSteiner AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive AnchorExteriorHomogeneous
open AnchorMixedCAR AnchorTripleEnergy AnchorOccupation AnchorScoreEnumeration
variable {R I : Type} [CommRing R]
local instance : NatCast R := Semiring.natCast
local notation "C" => ComplexScalar R
abbrev energy {d : Nat} (v : Basis d→C) := mass (qubitIndices d) v

noncomputable def sites {n} {G : MaximalFamily n} {T : Transversal G} (a : Line T) (L : List (Line T)) :=
    (tripleList L).filter (fun t=>hit a t.1 t.2.1 t.2.2)

private theorem distinctPrice [DecidableEq I] (i j k : I) (ij : i≠j) (ik : i≠k) (jk : j≠k) (S : List I) :
    mark i (mark j (mark k (fun _=>(1:R)))) S =
      if i∈S ∧ j∈S ∧ k∈S then 1 else 0 := by
  simp only [mark,List.mem_erase_of_ne (Ne.symm ij),List.mem_erase_of_ne (Ne.symm jk),List.mem_erase_of_ne (Ne.symm ik)]
  by_cases x : i∈S <;> by_cases y : j∈S <;> by_cases z : k∈S <;> simp [x,y,z]

private theorem component [DecidableEq I] (L : List I) (nd : L.Nodup) (t : I×I×I) (mem : t∈tripleList L)
    (v : Basis L.length→C) :
    energy (three L (mode t.1) (mode t.2.1) (mode t.2.2) v)=
      sumOver (qubitIndices L.length) (fun z=>if t.1∈occupied L z ∧ t.2.1∈occupied L z ∧ t.2.2∈occupied L z then normSq (v z) else 0) := by
  obtain ⟨i,j,k⟩:=t
  obtain ⟨ij,ik,jk⟩:=tripleDistinct L nd mem
  unfold energy; rw [←weightedOne L _]; unfold three
  rw [single L nd,single L nd,single L nd]; apply sumOverCongr; intro z
  rw [distinctPrice i j k ij ik jk]; split <;> grind only

private theorem sumFilter {A : Type} (L : List A) (p : A→Bool) (f : A→R) :
    sumOver (L.filter p) f=sumOver L (fun i=>if p i then f i else 0) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change sumOver ((i::L).filter p) f=(if p i then f i else 0)+sumOver L (fun i=>if p i then f i else 0)
    cases e:p i
    · simp only [List.filter_cons,e,Bool.false_eq_true,ite_false,ih]; grind only
    · simp only [List.filter_cons,e,ite_true]; exact congrArg (fun a=>f i+a) ih
private theorem sumCongrAt {A : Type} (L : List A) {f g:A→R} (h : ∀i∈L,f i=g i) : sumOver L f=sumOver L g := by
  unfold sumOver; rw [List.map_congr_left (fun i hi=>h i hi)]

/-- The diagonal triple occupation observable equals the actual squared norm
sum of coordinate triple annihilations, for every Fock amplitude. -/
theorem tripleScore {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)]
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (v : Basis L.length→C) :
    sumOver (sites a L) (fun t=>energy (three L (mode t.1) (mode t.2.1) (mode t.2.2) v))=
    total (qubitIndices L.length) (fun z=>score a (occupied L z)) v := by
  let B:=qubitIndices L.length
  let contains (t : Line T×Line T×Line T) (z : Basis L.length):=
    t.1∈occupied L z ∧ t.2.1∈occupied L z ∧ t.2.2∈occupied L z
  let get (t : Line T×Line T×Line T) (z : Basis L.length):=if contains t z then normSq (v z) else 0
  have hd : sumOver (sites a L) (fun t=>energy (three L (mode t.1) (mode t.2.1) (mode t.2.2) v))=
      sumOver (sites a L) (fun t=>sumOver B (get t)) := by
    apply sumCongrAt; intro t ht; exact component L nd t (List.mem_filter.mp ht).1 v
  rw [hd,sumOverSwap]; unfold total; apply sumOverCongr; intro z
  unfold sites; rw [sumFilter]
  let k := fun (i:Line T)=>decide (i∈occupied L z)
  let p := fun i j l=>k i && (k j && (k l && hit a i j l))
  have same (t : Line T×Line T×Line T) :
      (if hit a t.1 t.2.1 t.2.2 then get t z else 0)=(if p t.1 t.2.1 t.2.2 then normSq (v z) else 0) := by
    by_cases b : t.1∈occupied L z <;> by_cases c : t.2.1∈occupied L z <;> by_cases d : t.2.2∈occupied L z <;>
      cases h : hit a t.1 t.2.1 t.2.2 <;> simp [p,k,get,contains,b,c,d,h]
  rw [sumOverCongr _ same,triplePrice]
  have cnt : triples p L=score a (occupied L z) := by
    change triples (fun i j l=>k i && (k j && (k l && hit a i j l))) L=_
    rw [←filterTriples]
    have ef : L.filter k=occupied L z := orderedFilter L nd z
    rw [ef]; rfl
  rw [cnt]

/-- The partner-vacant anchored physical-character score inequality in the
actual complex row tests D_{a_y e_T}. The output is homogeneous in y and v. -/
theorem vacantAnchored {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)]
    [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C) (v : Basis L.length→C)
    (cap : ∀S,v S≠0→(occupied L S).length≤5) (vac : lower y L v=fun _=>0) :
    sumOver (sites a L) (fun t=>energy (contracted L y (mode t.1) (mode t.2.1) (mode t.2.2) v))≤
      2*sumOver L (fun i=>normSq (y i))*energy v := by
  have each (t : Line T×Line T×Line T) := tripleEnergy L y (mode t.1) (mode t.2.1) (mode t.2.2) v vac
  have eq := sumOverCongr (sites a L) each
  rw [Compression.sumOverSub,←sumOverMulLeft] at eq
  rw [eq]
  change sumOver (sites a L) (fun t=>energy (three L (mode t.1) (mode t.2.1) (mode t.2.2) (raise y L v)))-
    sumOver L _*sumOver (sites a L) (fun t=>energy (three L (mode t.1) (mode t.2.1) (mode t.2.2) v))≤_
  rw [tripleScore a L nd,tripleScore a L nd]
  have h:=homogeneousCharacterFive a L nd y v cap
  dsimp only at h; unfold energy; grind only

end RankSeven.AnchorVacantScore
#print axioms RankSeven.AnchorVacantScore.tripleScore
#print axioms RankSeven.AnchorVacantScore.vacantAnchored
