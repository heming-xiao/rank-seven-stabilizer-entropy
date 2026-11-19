import Rank7AnchorExteriorFive

namespace RankSeven.AnchorExteriorHomogeneous
open Lean.Grind Pauli ComplexScalar CharacterFourOrbits HeavyPauliGroup StabilizerCosetTransform
open AnchorSteiner AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive
variable {R I : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local notation "C" => ComplexScalar R

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem realSum {A : Type} (L : List A) (f : A→C) : (sumOver L f).re=sumOver L (fun i=>(f i).re) := by
  induction L with
  | nil => rfl
  | cons i L ih => change (f i+sumOver L f).re=(f i).re+sumOver L (fun i=>(f i).re); rw [re_add,ih]
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem diag {d : Nat} (v : Basis d→C) : (gram v v).re=mass (qubitIndices d) v := by
  unfold gram mass; rw [realSum]; simp only [re_star_mul_self]

theorem raiseHomogeneous (y : I→C) (L : List I) (v : Basis L.length→C) :
    mass (qubitIndices L.length) (raise y L v) ≤ sumOver L (fun i=>normSq (y i))*mass (qubitIndices L.length) v := by
  have sq:=congrArg ComplexScalar.re (carGram y L v v)
  simp only [re_add,diag,re_mul,im_ofReal,re_ofReal] at sq
  have pos : 0 ≤ mass (qubitIndices L.length) (lower y L v) :=
    Compression.sumOverNonnegative _ _ (fun _ _=>normSq_nonnegative _)
  grind only

/-- Exact anchored creation-score bound on arbitrary complex Fock amplitudes with at most
five occupied modes. The enumerated modes are actual stabilizer character lines. -/
theorem homogeneousCharacterFive {n : Nat} {G : MaximalFamily n} {T : Transversal G}
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C)
    (v : Basis L.length→C)
    (cap : ∀S, v S≠0 → (occupied L S).length≤5) :
    let sc := fun U=>score a (occupied L U)
    let B := qubitIndices L.length
    total B sc (raise y L v) ≤ sumOver L (fun i=>normSq (y i))*(total B sc v + 2*mass B v) := by
  let sc:=fun U=>score a (occupied L U)
  let B:=qubitIndices L.length
  change total B sc (raise y L v) ≤ sumOver L (fun i=>normSq (y i))*(total B sc v + 2*mass B v)
  let e:=sumOver L (fun i=>normSq (y i))
  have pos : 0≤e := Compression.sumOverNonnegative _ _ (fun _ _=>normSq_nonnegative _)
  have level (k : Nat) : mass B (mask sc (k+2) (raise y L v))≤e*mass B (mask sc k v) := by
    have replace : mass B (mask sc (k+2) (raise y L v))=
        mass B (mask sc (k+2) (raise y L (mask sc k v))) := by
      apply sumOverCongr; intro U
      by_cases high : k+2 < sc U
      · simp only [mask,high,ite_true]; congr 1; apply raiseLocal; intro r S add
        by_cases sk : k<sc S
        · simp [mask,sk]
        · have van : v S=0 := Classical.byContradiction (fun nz=>by
            have len:=cap S nz
            have ins:=insertion a r add (occNodup L nd S)
            change k+2<score a (occupied L U) at high
            change ¬k<score a (occupied L S) at sk
            omega)
          simp [mask,sk,van]
      · simp only [mask,high,ite_false]
    rw [replace]
    exact Std.le_trans (maskMassLe ..) (raiseHomogeneous y L _)
  have layers (k : Nat) : levels B sc (raise y L v) (k+2)≤e*(levels B sc v k + 2*mass B v) := by
    induction k with
    | zero =>
      simp only [levels]; have p:=maskMassLe B sc 0 (raise y L v)
      have q:=maskMassLe B sc 1 (raise y L v); have l:=raiseHomogeneous y L v
      change mass B _≤e*mass B v at l; grind only
    | succ k ih =>
      have p:=level k
      change levels B sc _ (k+2)+_≤e*(levels B sc _ k+_+_)
      grind only
  let N:=(B.map sc).foldr max 0
  have bound:=layers N
  rw [levelsFull B sc _ (by change N≤N+2; omega),levelsFull B sc _ (by exact Nat.le_refl N)] at bound
  exact bound


end RankSeven.AnchorExteriorHomogeneous
#print axioms RankSeven.AnchorExteriorHomogeneous.homogeneousCharacterFive
