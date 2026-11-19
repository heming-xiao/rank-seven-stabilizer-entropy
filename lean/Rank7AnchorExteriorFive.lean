import Rank7AnchorExteriorCreation

namespace RankSeven.AnchorExteriorFive
open Lean.Grind Pauli ComplexScalar CharacterFourOrbits HeavyPauliGroup StabilizerCosetTransform
open AnchorSteiner AnchorSteinerTest AnchorExteriorCreation
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

def occupied : (L : List I) → Basis L.length → List I
  | [],_ => []
  | _::L,(false,z) => occupied L z
  | i::L,(true,z) => i::occupied L z

private theorem occSub (L : List I) (z : Basis L.length) : occupied L z ⊆ L := by
  induction L with
  | nil => exact List.Subset.refl _
  | cons i L ih =>
    rcases z with ⟨b,z⟩; cases b
    · exact fun _ h=>List.mem_cons_of_mem i (ih z h)
    · intro j hj; rcases List.mem_cons.mp hj with h|h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem i (ih z h)

theorem occNodup (L : List I) (nd : L.Nodup) (z : Basis L.length) : (occupied L z).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons i L ih =>
    obtain ⟨off,tail⟩:=List.nodup_cons.mp nd; rcases z with ⟨b,z⟩; cases b
    · exact ih tail z
    · exact List.nodup_cons.mpr ⟨fun h=>off (occSub L z h),ih tail z⟩

/-- Exterior multiplication reads only coefficients one deletion below the output. -/
theorem raiseLocal (y : I→C) (L : List I) (f g : Basis L.length→C) (U : Basis L.length)
    (h : ∀r : I,∀S : Basis L.length,(occupied L U).Perm (r::occupied L S) → f S=g S) :
    raise y L f U=raise y L g U := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rcases U with ⟨b,z⟩; cases b
    · exact ih _ _ z (fun r S hs=>h r (false,S) hs)
    · have same:=h i (false,z) (List.Perm.refl _)
      have rest:=ih (fun w=>f (true,w)) (fun w=>g (true,w)) z (fun r S hs=>h r (true,S)
        ((hs.cons i).trans (List.Perm.swap r i _)))
      change y i*f (false,z)-_ = y i*g (false,z)-_; rw [same,rest]

private theorem reSum {A : Type} (L : List A) (f : A→C) : (sumOver L f).re = sumOver L (fun i=>(f i).re) := by
  induction L with
  | nil => rfl
  | cons i L h => change (f i + sumOver L f).re=(f i).re+sumOver L (fun i=>(f i).re); rw [re_add,h]
private theorem gramMass {d : Nat} (v : Basis d→C) : (gram v v).re=mass (qubitIndices d) v := by
  unfold gram mass; rw [reSum]; simp only [re_star_mul_self]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem raiseContraction (y : I→C) (L : List I) (unit : sumOver L (fun i=>normSq (y i))=1)
    (f : Basis L.length→C) : mass (qubitIndices L.length) (raise y L f)≤mass (qubitIndices L.length) f := by
  have car:=carGram y L f f
  rw [unit] at car
  have one : ofReal (1:R)=(1:C) := rfl
  rw [one,Semiring.one_mul] at car
  have energy:=congrArg ComplexScalar.re car
  simp only [re_add,gramMass] at energy
  have pos : 0 ≤ mass (qubitIndices L.length) (lower y L f) :=
    Compression.sumOverNonnegative _ _ (fun i _=>normSq_nonnegative _)
  grind only

/-- Exact anchored creation-score bound on arbitrary complex Fock amplitudes with at most
five occupied modes. The enumerated modes are actual stabilizer character lines. -/
theorem arbitraryCharacterFive {n : Nat} {G : MaximalFamily n} {T : Transversal G}
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C)
    (unit : sumOver L (fun i=>normSq (y i))=1) (v : Basis L.length→C)
    (cap : ∀S, v S≠0 → (occupied L S).length≤5) :
    let sc := fun U=>score a (occupied L U)
    let B := qubitIndices L.length
    total B sc (raise y L v) ≤ total B sc v + 2*mass B v := by
  let sc:=fun U=>score a (occupied L U)
  let B:=qubitIndices L.length
  change total B sc (raise y L v) ≤ total B sc v + 2*mass B v
  have level (k : Nat) : mass B (mask sc (k+2) (raise y L v))≤mass B (mask sc k v) := by
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
    exact Std.le_trans (maskMassLe ..) (raiseContraction y L unit _)
  have layers (k : Nat) : levels B sc (raise y L v) (k+2)≤levels B sc v k + 2*mass B v := by
    induction k with
    | zero =>
      simp only [levels]; have p:=maskMassLe B sc 0 (raise y L v)
      have q:=maskMassLe B sc 1 (raise y L v); have l:=raiseContraction y L unit v
      change mass B _≤mass B v at l; grind only
    | succ k ih =>
      have p:=level k
      change levels B sc _ (k+2)+_≤levels B sc _ k+_+_
      grind only
  let N:=(B.map sc).foldr max 0
  have bound:=layers N
  rw [levelsFull B sc _ (by change N≤N+2; omega),levelsFull B sc _ (by exact Nat.le_refl N)] at bound
  exact bound

end RankSeven.AnchorExteriorFive
#print axioms RankSeven.AnchorExteriorFive.arbitraryCharacterFive
