import Rank7PhysicalHopping
import Rank7PhysicalUniformOccupation
import Rank7FiveFrameContractions

/-! One free creation mode acting on an alternating three-tensor:
the two-term normal-ordering identity used in Proposition 9. -/
namespace RankSeven.SingleCreationCAR
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
variable {R C α : Type} [CommRing R] [CommRing C]
def ident : Permutation := ((0,1),(2,3))
def swap : Permutation := ((1,0),(2,3))
def swaps (i : Fin 4) : Permutation := [((0,1),(2,3)),((1,0),(2,3)),((2,1),(0,3)),((3,1),(2,0))].getD i.val ident
def blocks : List Permutation := [((0,1),(2,3)),((0,1),(3,2)),((0,2),(1,3)),((0,2),(3,1)),((0,3),(1,2)),((0,3),(2,1))]
private def choose (i j : Fin 4) : Permutation :=
  let choices : List (List Nat) := [[0,0,2,3],[0,0,2,3],[2,0,0,3],[3,0,2,0]]
  blocks.getD ((choices.getD i.val []).getD j.val 0) ident
private def shift (i j : Fin 4) := reorder (choose i j) (swaps i)
private def rep (i j : Fin 4) := if i=j then ident else swap
private def rest (i j : Fin 4) := reorder (rep i j) (reorder (shift i j) (swaps j))
set_option synthInstance.maxSize 1000 in
private theorem table : ∀ i j : Fin 4, shift i j∈permutations ∧ choose i j∈blocks ∧ rest i j∈blocks ∧
    reorder (shift i j) (swaps i)=choose i j ∧ reorder (shift i j) (swaps j)=reorder (rep i j) (rest i j) ∧
    (((oddPermutation (swaps i) ^^ oddPermutation (swaps j)) ^^ oddPermutation (choose i j)) ^^ oddPermutation (rest i j))=decide (i≠j) := by decide
theorem compose {B : Type} (v : Four B) (p q : Permutation) : reorder (reorder v p) q=reorder v (reorder p q) := by
  change ((position (reorder v p) _,position (reorder v p) _),(position (reorder v p) _,position (reorder v p) _))=_
  simp only [position_reorder]; rfl

private theorem permSum {B : Type} {xs ys : List B} (p : xs.Perm ys) (f : B → C) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2

def AlternatingTail (Z : Four α → ComplexScalar R) := ∀ p∈blocks,∀ u,Z (reorder u p)=signed (oddPermutation p) (Z u)
def merged (Z : Four α → ComplexScalar R) (u : Four α) :=
  sumOver (List.finRange 4) (fun i => signed (oddPermutation (swaps i)) (Z (reorder u (swaps i))))
private def term (Z : Four α → ComplexScalar R) (u : Four α) (i : Fin 4) := signed (oddPermutation (swaps i)) (Z (reorder u (swaps i)))
private def corr (xs : List α) (Z : Four α → ComplexScalar R) (q : Permutation) :=
  sumOver (fourIndices xs) (fun u => (star (Z u)*Z (reorder u q)).re)
private theorem signs (a b c d : Bool) (z w : ComplexScalar R) :
    (star (signed a (signed c z))*signed b (signed d w)).re=signed (((a^^b)^^c)^^d) (star z*w).re := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [signed,re_mul] <;> grind only
private theorem minusSum {A : Type} (xs : List A) (F : A → C) : sumOver xs (fun i => -F i)= -sumOver xs F := by
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem paired [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (Z : Four α → ComplexScalar R) (hz : AlternatingTail Z) (i j : Fin 4) :
    sumOver (fourIndices xs) (fun u => (star (term Z u i)*term Z u j).re)=if i=j then corr xs Z ident else -corr xs Z swap := by
  let p := shift i j
  let F (u : Four α) := (star (term Z u i)*term Z u j).re
  obtain ⟨leg,hl,hr,comp1,comp2,sg⟩ := table i j
  have perm := FourCopySectors.fullPermuted xs nd full p leg
  have ee : sumOver (fourIndices xs) (fun u => F (reorder u p))=sumOver (fourIndices xs) F := by
    simpa only [sumOver,List.map_map,Function.comp_def] using permSum perm F
  change sumOver (fourIndices xs) F=_; rw [←ee]
  have e (u : Four α) : F (reorder u p)=signed (decide (i≠j)) (star (Z u)*Z (reorder u (rep i j))).re := by
    unfold F term; rw [compose,compose,comp1,comp2,←compose,hz _ hl,hz _ hr,signs,sg]
  rw [sumOverCongr _ e]; by_cases h : i=j <;> simp [h,signed,rep,corr,minusSum]

private theorem reSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

theorem singleCreationCAR [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (Z : Four α → ComplexScalar R) (hz : AlternatingTail Z) :
    sumOver (fourIndices xs) (fun u => normSq (merged Z u))=
    4*(sumOver (fourIndices xs) (fun u => normSq (Z u)) -
      3*sumOver (fourIndices xs) (fun u => (star (Z u)*Z (reorder u swap)).re)) := by
  have ex (u : Four α) : normSq (merged Z u)=sumOver (List.finRange 4) (fun i => sumOver (List.finRange 4) (fun j =>
      (star (term Z u i)*term Z u j).re)) := by
    change normSq (sumOver (List.finRange 4) (term Z u))=_
    rw [←re_star_mul_self,ComplexExterior.starSumOver,sumOverMulRight]; simp only [sumOverMulLeft,reSum]
  rw [sumOverCongr _ ex,sumOverSwap]
  conv => lhs; arg 2; intro i; rw [sumOverSwap]
  simp only [paired xs nd full Z hz]
  let x := corr xs Z ident
  let y := corr xs Z swap
  have four (A : Fin 4 → R) : sumOver (List.finRange 4) A=A 0+(A 1+(A 2+(A 3+0))) := by rfl
  have sum (a b : R) : sumOver (List.finRange 4) (fun i => sumOver (List.finRange 4) (fun j => if i=j then a else -b))=4*(a-3*b) := by
    simp only [four]; change a+(-b+(-b+(-b+0)))+((-b+(a+(-b+(-b+0))))+((-b+(-b+(a+(-b+0))))+((-b+(-b+(-b+(a+0))))+0)))=_; grind only
  rw [sum]; unfold corr
  have fixed (u : Four α) : reorder u ident=u := by rfl
  simp only [fixed,re_star_mul_self]

end RankSeven.SingleCreationCAR
#print axioms RankSeven.SingleCreationCAR.singleCreationCAR
