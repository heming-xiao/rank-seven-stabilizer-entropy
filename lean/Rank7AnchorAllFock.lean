import Rank7AnchorVacantScore
import Rank7HighestTailReplacement

namespace RankSeven.AnchorAllFock
open Lean.Grind Pauli ComplexScalar HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits
open AnchorExteriorCreation AnchorExteriorFive AnchorMixedCAR AnchorOccupation AnchorVacantScore
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

private theorem zeroOnLower (L : List I) (y : I→C) (hy : ∀i∈L,y i=0) (v : Basis L.length→C) :
    lower y L v=fun _=>0 := by
  funext z; induction L with
  | nil => rfl
  | cons i L ih =>
    have hd:=hy i List.mem_cons_self
    have tail (j : I) (hj:j∈L):y j=0 := hy j (List.mem_cons_of_mem _ hj)
    have st : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
    rcases z with ⟨b,z⟩; cases b <;> simp only [lower,hd,st,ih tail] <;> grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem individual (L : List I) (y : I→C) (i : I) (hi : i∈L) :
    normSq (y i) ≤ sumOver L (fun j=>normSq (y j)) := by
  induction L with
  | nil => contradiction
  | cons j L ih =>
    have rest:=Compression.sumOverNonnegative L (fun j=>normSq (y j)) (fun j _=>normSq_nonnegative _)
    have hd:=normSq_nonnegative (y j)
    change _≤normSq (y j)+sumOver L _
    rcases List.mem_cons.mp hi with h|h
    · subst j; grind only
    · have h:=ih h; grind only

/-- Arbitrary partner, arbitrary at-most-five-particle state, arbitrary stabilizer
character anchor. No orthogonality, vacancy, decomposability or normalization hypotheses. -/
theorem anchoredPairContractions {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)]
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C) (v : Basis L.length→C)
    (cap : HighestTailReplacement.cap L 5 v) :
    sumOver (sites a L) (fun t=>energy (contracted L y (mode t.1) (mode t.2.1) (mode t.2.2) v)) ≤
      2*sumOver L (fun i=>normSq (y i))*energy v := by
  by_cases hp : 0<HighestTailReplacement.modeMass L y
  · exact HighestTailReplacement.vacantSuffices L y (sites a L) (fun t=>mode t.1) (fun t=>mode t.2.1)
      (fun t=>mode t.2.2) v cap hp (fun f hf hv=>vacantAnchored a L nd y f hf hv)
  · have hy (i : Line T) (hi : i∈L) : y i=0 := by
      have h:=individual L y i hi; have pos:=normSq_nonnegative (y i)
      apply (normSq_eq_zero_iff _).mp
      change ¬0<sumOver L (fun j=>normSq (y j)) at hp
      grind only
    exact vacantAnchored a L nd y v cap (zeroOnLower L y hy v)

end RankSeven.AnchorAllFock
#print axioms RankSeven.AnchorAllFock.anchoredPairContractions
