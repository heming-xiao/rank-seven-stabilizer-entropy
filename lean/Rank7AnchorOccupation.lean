import Rank7AnchorTripleEnergy

namespace RankSeven.AnchorOccupation
open Lean.Grind Pauli ComplexScalar AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive AnchorMixedCAR
variable {R I : Type} [CommRing R] [DecidableEq I]
local notation "C" => ComplexScalar R

def mode (i j : I) : C := if i=j then 1 else 0

def weighted (L : List I) (Q : List I→R) (f : Basis L.length→C) :=
    sumOver (qubitIndices L.length) fun z=>Q (occupied L z)*normSq (f z)

def mark (i : I) (Q : List I→R) (S : List I) : R := if i∈S then Q (S.erase i) else 0

omit [DecidableEq I] in
theorem weightedOne (L : List I) (f : Basis L.length→C) :
    weighted L (fun _=>(1:R)) f=mass (qubitIndices L.length) f := by
  unfold weighted mass; simp only [Semiring.one_mul]

private theorem bits {V : Type} [CommRing V] {d : Nat} (f : Basis (d+1)→V) :
    sumOver (qubitIndices (d+1)) f = sumOver (qubitIndices d) (fun z=>f (false,z))+
      sumOver (qubitIndices d) (fun z=>f (true,z)) := by
  change Bool × Basis d → V at f
  change sumOver (productIndices [false,true] (qubitIndices d)) f=_
  have app (xs ys : List V) : (xs++ys).sum=xs.sum+ys.sum := by
    induction xs with
    | nil => change ys.sum=0+ys.sum; grind only
    | cons v xs ih => change v+(xs++ys).sum=v+xs.sum+ys.sum; rw [ih]; grind only
  simp [sumOver,productIndices,List.map_append,app,List.map_map,Function.comp_def]

omit [DecidableEq I] in
theorem weightedSplit (h : I) (L : List I) (Q : List I→R) (f : Basis (h::L).length→C) :
    weighted (h::L) Q f = weighted L Q (fun z=>f (false,z)) +
      weighted L (fun S=>Q (h::S)) (fun z=>f (true,z)) := bits _

omit [DecidableEq I] in
private theorem subOcc (L : List I) (z : Basis L.length) : occupied L z ⊆ L := by
  induction L with
  | nil => exact List.Subset.refl _
  | cons h L ih =>
    rcases z with ⟨b,z⟩; cases b
    · exact fun _ hz=>List.mem_cons_of_mem h (ih z hz)
    · intro x hx; rcases List.mem_cons.mp hx with h|h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (ih z h)

private theorem zeroStar : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
private theorem oneStar : star (1:C)=1 := by apply ComplexScalar.ext <;> simp <;> grind only

theorem absent (L : List I) (i : I) (off : i∉L) (f : Basis L.length→C) (z : Basis L.length) :
    lower (mode i) L f z=0 := by
  induction L with
  | nil => rfl
  | cons h L ih =>
    have ne : i≠h := fun eq=>off (List.mem_cons.mpr (Or.inl eq))
    have absent : i∉L := fun hi=>off (List.mem_cons_of_mem _ hi)
    rcases z with ⟨b,z⟩; cases b <;> simp only [lower,mode,ne,ite_false,zeroStar,ih absent] <;> grind only

omit [DecidableEq I] in
private theorem qCongr (L : List I) {Q Z : List I→R} (f : Basis L.length→C) (e : ∀S,S⊆L→Q S=Z S) :
    weighted L Q f=weighted L Z f := by
  apply sumOverCongr; intro z; rw [e _ (subOcc L z)]

omit [DecidableEq I] in
private theorem wNeg (L : List I) (Q : List I→R) (f : Basis L.length→C) :
    weighted L Q (fun z=> -f z)=weighted L Q f := by
  apply sumOverCongr; intro z
  have n : normSq (-f z)=normSq (f z) := by unfold normSq; simp; grind only
  rw [n]

private theorem zeros {A : Type} (xs : List A) : sumOver xs (fun _=>(0:R))=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0+sumOver xs _=0; rw [ih]; grind only

/-- Remove one coordinate site with the correct exterior signs, for every diagonal
test weight. Distinct ambient sites are enough; i may be absent from the site list. -/
theorem single (L : List I) (nd : L.Nodup) (i : I) (Q : List I→R) (f : Basis L.length→C) :
    weighted L Q (lower (mode i) L f)=weighted L (mark i Q) f := by
  induction L generalizing Q with
  | nil => change Q []*normSq 0+0=0*normSq (f ())+0; rw [normSq_zero]; grind only
  | cons h L ih =>
    obtain ⟨off,tail⟩:=List.nodup_cons.mp nd
    rw [weightedSplit,weightedSplit]
    by_cases same : i=h
    · subst i
      have lo : (fun z=>lower (mode h) (h::L) f (false,z))=fun z=>f (true,z) := by
        funext z; simp only [lower,mode,ite_true,oneStar,absent L h off]; grind only
      have hi : (fun z=>lower (mode h) (h::L) f (true,z))=fun _=>0 := by
        funext z; simp only [lower,absent L h off]; grind only
      have orig : weighted L (mark h Q) (fun z=>f (false,z))=0 := by
        unfold weighted; rw [←zeros (qubitIndices L.length)]; apply sumOverCongr; intro z
        have no : h∉occupied L z := fun hx=>off ((subOcc L z) hx)
        simp only [mark,no,ite_false,Semiring.zero_mul]
      have wk : weighted L (fun S=>mark h Q (h::S)) (fun z=>f (true,z))=weighted L Q (fun z=>f (true,z)) := by
        apply qCongr; intro S _; simp [mark]
      have vzero : weighted L (fun S=>Q (h::S)) (fun _=>0)=0 := by
        unfold weighted; simp only [normSq_zero,Semiring.mul_zero,zeros]
      rw [lo,hi,orig,wk,vzero]; grind only
    · have lo : (fun z=>lower (mode i) (h::L) f (false,z))=lower (mode i) L (fun z=>f (false,z)) := by
        funext z; simp only [lower,mode,same,ite_false,zeroStar]; grind only
      have hi : (fun z=>lower (mode i) (h::L) f (true,z))=fun z=> -lower (mode i) L (fun z=>f (true,z)) z := rfl
      rw [lo,hi,wNeg,ih tail,ih tail]
      congr 1; apply qCongr; intro S _
      by_cases hs : i∈S <;> simp [mark,same,Ne.symm same,hs]

end RankSeven.AnchorOccupation
#print axioms RankSeven.AnchorOccupation.single
