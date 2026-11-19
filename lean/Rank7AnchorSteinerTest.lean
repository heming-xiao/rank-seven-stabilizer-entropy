import Rank7AnchorSteiner

namespace RankSeven.AnchorSteinerTest
open Lean.Grind Pauli ComplexScalar CharacterFourOrbits HeavyPauliGroup StabilizerCosetTransform AnchorSteiner
variable {R I J : Type} [CommRing R]
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance : NatCast R := Semiring.natCast
local notation "C" => ComplexScalar R

def mass (L : List I) (v : I → C) : R := sumOver L fun i => normSq (v i)
def mask (s : I → Nat) (k : Nat) (v : I → C) (i : I) : C := if k < s i then v i else 0
def action (L : List I) (K : J → I → C) (v : I → C) (j : J) : C := sumOver L fun i => K j i * v i
def total (L : List I) (s : I → Nat) (v : I → C) : R := sumOver L fun i => (s i:R) * normSq (v i)
def levels (L : List I) (s : I → Nat) (v : I → C) : Nat → R
  | 0 => 0
  | k+1 => levels L s v k + mass L (mask s k v)

private theorem sumLe (L : List I) {f g : I→R} (h : ∀i∈L, f i≤g i) :
    sumOver L f≤sumOver L g := by
  induction L with
  | nil => exact Std.le_refl _
  | cons i L ih =>
    have e:=h i List.mem_cons_self
    have t:=ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
    change f i+sumOver L f≤g i+sumOver L g; grind only

private theorem sumEq {V : Type} [CommRing V] (L : List I) {f g : I→V}
    (h : ∀i∈L, f i=g i) : sumOver L f=sumOver L g := by
  unfold sumOver; rw [List.map_congr_left (fun i hi=>h i hi)]

theorem maskMassLe (L : List I) (s : I→Nat) (k : Nat) (v : I→C) :
    mass L (mask s k v) ≤ mass L v := by
  apply sumLe; intro i _; unfold mask; split
  · exact Std.le_refl _
  · rw [normSq_zero]; exact normSq_nonnegative _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem layerEq (L : List I) (s : I→Nat) (v : I→C) (k : Nat) :
    levels L s v k = sumOver L (fun i=>(Nat.cast (min (s i) k):R) * normSq (v i)) := by
  induction k with
  | zero =>
    change 0=_
    rw [sumEq L (g:=fun _=>(0:R)) (fun _ _=>by simp; grind only)]
    induction L with
    | nil => rfl
    | cons i L h => change 0 = 0 + sumOver L _; rw [←h]; grind only
  | succ k ih =>
    change levels L s v k + mass L (mask s k v) = _
    rw [ih]; unfold mass; rw [←sumOverAdd]; apply sumOverCongr; intro i
    by_cases e : k<s i
    · have p : min (s i) k=k := Nat.min_eq_right (by omega)
      have q : min (s i) (k+1)=k+1 := Nat.min_eq_right (by omega)
      rw [p,q]; simp only [mask,e,ite_true]; grind
    · have p : min (s i) k=s i := Nat.min_eq_left (by omega)
      have q : min (s i) (k+1)=s i := Nat.min_eq_left (by omega)
      rw [p,q]; simp only [mask,e,ite_false,normSq_zero]; grind only

private def top (L : List I) (s : I→Nat) := (L.map s).foldr max 0
private theorem topBound (L : List I) (s : I→Nat) (i : I) (hi : i∈L) : s i≤top L s := by
  induction L with
  | nil => contradiction
  | cons a L h =>
    change s i≤max (s a) (top L s)
    rcases List.mem_cons.mp hi with e|e
    · subst i; omega
    · have := h e; omega

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem levelsFull (L : List I) (s : I→Nat) (v : I→C) {N : Nat} (enough : top L s≤N) :
    levels L s v N=total L s v := by
  rw [layerEq]; apply sumEq; intro i hi
  have h:=topBound L s i hi; rw [Nat.min_eq_left (Nat.le_trans h enough)]

/-- Localized level-set comparison: only the ordinary operator contraction and
the incidence support of its entries are needed; complex phases may be arbitrary. -/
theorem superlevel (L : List I) (M : List J) (s : I→Nat) (t : J→Nat) (h : Nat)
    (K : J→I→C) (con : ∀u, mass M (action L K u)≤mass L u)
    (support : ∀j∈M,∀i∈L, K j i≠0 → t j≤s i+h)
    (u : I→C) (level : Nat) :
    mass M (mask t (level+h) (action L K u)) ≤ mass L (mask s level u) := by
  have replace : mass M (mask t (level+h) (action L K u)) =
      mass M (mask t (level+h) (action L K (mask s level u))) := by
    apply sumEq; intro j hj
    by_cases high : level+h<t j
    · simp only [mask,high,ite_true]; congr 1; apply sumEq; intro i hi
      by_cases hi' : level<s i
      · simp [mask,hi']
      · have zero : K j i=0 := Classical.byContradiction (fun nz=>by have := support j hj i hi nz; omega)
        rw [zero]; grind only
    · simp only [mask,high,ite_false]
  rw [replace]
  exact Std.le_trans (maskMassLe ..) (con _)

theorem scoreTransport (L : List I) (M : List J) (s : I→Nat) (t : J→Nat)
    (K : J→I→C) (con : ∀u, mass M (action L K u)≤mass L u)
    (support : ∀j∈M,∀i∈L, K j i≠0 → t j≤s i+2) (u : I→C) :
    total M t (action L K u) ≤ total L s u+2*mass L u := by
  have layers (k : Nat) : levels M t (action L K u) (k+2) ≤ levels L s u k+2*mass L u := by
    induction k with
    | zero =>
      simp only [levels]; have x := maskMassLe M t 0 (action L K u)
      have y := maskMassLe M t 1 (action L K u); have z:=con u; grind only
    | succ k ih =>
      have step := superlevel L M s t 2 K con support u k
      change levels M t _ (k+2)+_ ≤ levels L s u k+_+_
      grind only
  let N:=max (top M t) (top L s)
  have main:=layers N
  rw [levelsFull M t _ (by dsimp [N];omega),levelsFull L s _ (by dsimp [N];omega)] at main
  exact main

/-- For a five-site (or four-site) input the anchored triple score of every
norm-contractive one-site creation matrix increases in expectation by at most two. -/
theorem characterFiveTail {n : Nat} {G : MaximalFamily n} {T : Transversal G}
    (a : Line T) (L M : List (List (Line T))) (K : List (Line T)→List (Line T)→C)
    (nodup : ∀S∈L,S.Nodup) (size : ∀S∈L,S.length≤5)
    (incidence : ∀U∈M,∀S∈L,K U S≠0→∃r:Line T,U.Perm (r::S))
    (contraction : ∀v, mass M (action L K v)≤mass L v) (v : List (Line T)→C) :
    total M (score a) (action L K v) ≤ total L (score a) v + 2*mass L v := by
  apply scoreTransport L M _ _ K contraction
  intro U hU S hS nz
  obtain ⟨r,add⟩:=incidence U hU S hS nz
  have h:=insertion a r add (nodup S hS)
  have lens:=size S hS; omega

end RankSeven.AnchorSteinerTest
#print axioms RankSeven.AnchorSteinerTest.characterFiveTail
