import Rank7SingleCreationCAR

/-! Physical one-free-mode occupation estimate in the odd Pauli synthesis
coordinates used for Proposition 9 of the five-plane proof. -/
namespace RankSeven.PhysicalOccupationBound
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
open PhysicalCutCapacities (Triple triples)
open PhysicalUniformOccupation (wave)
open SingleCreationCAR (AlternatingTail merged swap)
variable {C R α I : Type} [CommRing C] [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
def tail {α : Type} (u : Four α) : Triple α := ((u.1.2,u.2.1),u.2.2)
def insert {α : Type} (a : α) (u : Triple α) : Four α := ((a,u.1.1),u.1.2,u.2)
def slice {n} (half : R) (x : Basis n → ComplexScalar R) (c : Word n → ComplexScalar R) (u : Triple (Basis n)) :=
  sumOver (qubitIndices n) (fun t => x t * wave half c (insert t u))
def atom (A : α → I → ComplexScalar R) (i : I) (Y : Triple α → ComplexScalar R) (u : Four α) := A u.1.1 i*Y (tail u)
def source (ys : List I) (A : α → I → ComplexScalar R) (Y : I → Triple α → ComplexScalar R) (u : Four α) :=
  sumOver ys (fun i => atom A i (Y i) u)
def physicalSource {n} (half : R) (ys : List I) (A : Basis n → I → ComplexScalar R)
    (x : Basis n → ComplexScalar R) (c : I → Word n → ComplexScalar R) := source ys A (fun i => slice half x (c i))
private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
private theorem signSum {B : Type} (xs : List B) (b : Bool) (F : B → C) :
    sumOver xs (fun i => signed b (F i))=signed b (sumOver xs F) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true]
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem mulSign (b : Bool) (z w : C) : z*signed b w=signed b (z*w) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true,Ring.mul_neg]
private theorem reSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

theorem physicalAlternating {n} (half : R) (ys : List I) (A : Basis n → I → ComplexScalar R)
    (x : Basis n → ComplexScalar R) (c : I → Word n → ComplexScalar R) :
    AlternatingTail (physicalSource half ys A x c) := by
  intro p hp u
  have loc (a : Basis n) : insert a (tail (reorder u p))=reorder (insert a (tail u)) p ∧ (reorder u p).1.1=u.1.1 := by
    simp only [SingleCreationCAR.blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩
  have legal : p∈permutations := by
    simp only [SingleCreationCAR.blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  unfold physicalSource source atom slice
  simp only [(loc (HyperplaneIncidence.zero n)).2,(loc _).1,FiveFrameContractions.waveReorder half _ _ p legal,mulSign,signSum]

private theorem expandPair {E T : Type} (es : List E) (xs : List T) (F H : E → T → ComplexScalar R) :
    sumOver xs (fun t => star (sumOver es (fun i => F i t))*sumOver es (fun j => H j t))=
      sumOver es (fun i => sumOver es (fun j => sumOver xs (fun t => star (F i t)*H j t))) := by
  simp only [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft]
  conv => rhs; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro j; rw [sumOverSwap]

private theorem zeroEntry (xs : List α) (A : α → I → ComplexScalar R) (i j : I) (Y W : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => star (atom A i Y u)*atom A j W u)=
      sumOver xs (fun a => star (A a i)*A a j)*sumOver (triples xs) (fun r => star (Y r)*W r) := by
  unfold fourIndices triples; simp only [productSum,sumOverMulRight,sumOverMulLeft]
  conv => lhs; rw [sumOverSwap]; arg 2; intro b; rw [sumOverSwap]; arg 2; intro c; rw [sumOverSwap]
  apply sumOverCongr; intro b; apply sumOverCongr; intro c; apply sumOverCongr; intro d; apply sumOverCongr; intro a
  unfold atom tail; simp only [star_mul]; grind only

private theorem crossEntry (xs : List α) (A : α → I → ComplexScalar R) (i j : I) (Y W : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => star (atom A i Y u)*atom A j W (reorder u swap))=
      sumOver (productIndices xs xs) (fun r => star (FiveFrameContractions.cutOne xs A j Y r.1 r.2) * FiveFrameContractions.cutOne xs A i W r.1 r.2) := by
  unfold fourIndices FiveFrameContractions.cutOne; simp only [productSum,ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; rw [sumOverSwap]
  apply sumOverCongr; intro c; apply sumOverCongr; intro d; apply sumOverCongr; intro a; apply sumOverCongr; intro b
  change star (A a i*Y ((b,c),d))*(A b j*W ((a,c),d))=_
  simp only [star_mul]; grind only

private theorem cutSlice {n} (half : R) (A : Basis n → I → ComplexScalar R) (x : Basis n → ComplexScalar R) (i : I)
    (c : Word n → ComplexScalar R) (r : PhysicalPairExchange.Edge n) :
    FiveFrameContractions.cutOne (qubitIndices n) A i (slice half x c) r.1 r.2 =
      PhysicalHopping.contract (fun p => x p.1*star (A p.2 i)) (wave half c) r := by
  unfold FiveFrameContractions.cutOne slice PhysicalHopping.contract PhysicalHopping.edges
  rw [productSum]; simp only [sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; unfold insert; grind only

theorem hoppingLayer {n} (half : R) (ys : List I) (A : Basis n → I → ComplexScalar R)
    (x : Basis n → ComplexScalar R) (c : I → Word n → ComplexScalar R) :
    let Z := physicalSource half ys A x c
    sumOver (fourIndices (qubitIndices n)) (fun u => star (Z u)*Z (reorder u swap))=
      sumOver (PhysicalHopping.edges n) (fun r => ofReal (normSq (sumOver ys (fun i =>
        PhysicalHopping.contract (fun p => star (x p.1*star (A p.2 i))) (wave half (c i)) r)))) := by
  intro Z
  change sumOver _ (fun u => star (sumOver ys (fun a => atom A a (slice half x (c a)) u))*sumOver ys (fun b => atom A b (slice half x (c b)) (reorder u swap)))=_
  rw [expandPair]; simp only [crossEntry,cutSlice]; rw [sumOverSwap]
  exact PhysicalHopping.physicalHoppingSquare half ys (fun i p => x p.1*star (A p.2 i)) c

theorem sliceLast {n} (half : R) (x : Basis n → ComplexScalar R) (c : Word n → ComplexScalar R) (r : Triple (Basis n)) :
    slice half x c r= -PhysicalUniformOccupation.oneHole x (wave half c) r := by
  let p : ExteriorPauliBase.Permutation := ((3,0),(1,2))
  have hp : p∈permutations := by decide
  have sign : oddPermutation p=true := by decide
  have row (t) : x t*wave half c (insert t r)=signed true (x t*wave half c (PhysicalCutCapacities.extend r t)) := by
    have h := FiveFrameContractions.waveReorder half c (PhysicalCutCapacities.extend r t) p hp
    rw [sign] at h; change wave half c (insert t r)= -wave half c (PhysicalCutCapacities.extend r t) at h
    rw [h]; exact Ring.mul_neg _ _
  unfold slice PhysicalUniformOccupation.oneHole; rw [sumOverCongr _ row,signSum]; rfl

private theorem collapse {B : Type} [DecidableEq B] (xs : List B) (nd : xs.Nodup) (i : B) (hi : i∈xs) (F : B → ComplexScalar R) :
    sumOver xs (fun j => (if i=j then 1 else 0)*F j)=F i := by
  refine (sumOverCongr xs (g:=fun j => if i=j then F j else 0) (fun j => ?_)).trans
    (ExteriorPauliBase.sumOnIndex xs i F nd hi)
  by_cases h : i=j <;> simp [h,Semiring.one_mul,Semiring.zero_mul]

theorem sourceNorm [DecidableEq I] (xs : List α) (ys : List I) (nd : ys.Nodup)
    (A : α → I → ComplexScalar R) (orth : ∀i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (Y : I → Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => normSq (source ys A Y u))=
    sumOver ys (fun i => sumOver (triples xs) (fun u => normSq (Y i u))) := by
  have h : sumOver (fourIndices xs) (fun u => star (source ys A Y u)*source ys A Y u)=
    sumOver ys (fun i => sumOver (triples xs) (fun u => star (Y i u)*Y i u)) := by
    unfold source; rw [expandPair]; simp only [zeroEntry,orth]
    apply congrArg List.sum; apply List.map_congr_left; intro i hi
    exact collapse ys nd i hi (fun j => sumOver (triples xs) (fun u => star (Y i u)*Y j u))
  simpa only [reSum,re_star_mul_self] using congrArg ComplexScalar.re h

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
private theorem sumLe {E : Type} (xs : List E) (f g : E → R) (h : ∀i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i is ih =>
    have a := h i List.mem_cons_self
    have b := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    change f i+sumOver is f≤g i+sumOver is g; grind only

/-- The raw ordered-coordinate estimate for the one-free-mode physical
source. The coefficient 144/d is 4! times the exterior bound 3q/2 on
odd-Pauli coefficients. The list of free modes can have arbitrary length. -/
theorem physicalOccupation [DecidableEq I] {n} (half : R) (unit : 2*half=1)
    (ys : List I) (nd : ys.Nodup) (A : Basis n → I → ComplexScalar R)
    (orth : ∀i j,sumOver (qubitIndices n) (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (x : Basis n → ComplexScalar R) (hx : sumOver (qubitIndices n) (fun a => star (x a)*x a)=1)
    (c : I → Word n → ComplexScalar R) :
    sumOver (fourIndices (qubitIndices n)) (fun u => normSq (merged (physicalSource half ys A x c) u))≤
    144*half^n * sumOver ys (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq (c i p))) := by
  let xs := qubitIndices n
  let os := MixedDefect.oddWords n
  let Z := physicalSource half ys A x c
  have car := SingleCreationCAR.singleCreationCAR xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) Z (physicalAlternating half ys A x c)
  have occ := sourceNorm xs ys nd A orth (fun i => slice half x (c i))
  have hc : 0≤sumOver (fourIndices xs) (fun u => (star (Z u)*Z (reorder u swap)).re) := by
    have z := congrArg ComplexScalar.re (hoppingLayer half ys A x c); simp only [reSum,re_ofReal] at z
    rw [show sumOver (fourIndices xs) (fun u => (star (Z u)*Z (reorder u swap)).re)=_ from z]
    apply Compression.sumOverNonnegative; intro i _; apply normSq_nonnegative
  have li (i : I) : sumOver (triples xs) (fun u => normSq (slice half x (c i) u))≤36*half^n*sumOver os (fun p => normSq (c i p)) := by
    have neg (w : ComplexScalar R) : normSq (-w)=normSq w := by simp [normSq]; grind only
    simp only [sliceLast,neg]; exact PhysicalUniformOccupation.physicalOneHoleBound half unit x hx (c i)
  have total := sumLe ys _ _ (fun i _ => li i)
  rw [←sumOverMulLeft] at total; change sumOver (fourIndices xs) (fun u => normSq (Z u))=_ at occ
  rw [←occ] at total; change sumOver (fourIndices xs) (fun u => normSq (merged Z u))≤_
  rw [car]; grind only
end Order

end RankSeven.PhysicalOccupationBound
#print axioms RankSeven.PhysicalOccupationBound.physicalOccupation
