import Rank7PhysicalOccupationBound

/-! The second occupation measurement is contractive in exterior norm.
The 4-to-3 conversion is explicit in ordered tensor coordinates. -/
namespace RankSeven.PhysicalDoubleHoleNorm
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
open SingleCreationCAR (AlternatingTail merged swaps blocks swap)
open PhysicalOccupationBound (tail insert)
open PhysicalCutCapacities (Triple triples)
variable {R C α I : Type} [CommRing R] [CommRing C]
def Alternating (F : Four α → ComplexScalar R) := ∀ p∈permutations, ∀ u,F (reorder u p)=signed (oddPermutation p) (F u)
private def adjust (p : Permutation) (i : Fin 4) := reorder (swaps (position p i)) (reorder p (swaps i))
set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 20000 in
private theorem square : permutations.all (fun p => decide (
    ((List.finRange 4).map (position p)).Perm (List.finRange 4) ∧ ∀ i : Fin 4,
    adjust p i∈blocks ∧ reorder p (swaps i)=reorder (swaps (position p i)) (adjust p i) ∧
    (oddPermutation (swaps i) ^^ oddPermutation (adjust p i))=
      (oddPermutation p ^^ oddPermutation (swaps (position p i)))))=true := by decide

private theorem permSum {B : Type} {xs ys : List B} (p : xs.Perm ys) (f : B → C) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2
private theorem signSum {B : Type} (xs : List B) (b : Bool) (F : B → C) :
    sumOver xs (fun i => signed b (F i))=signed b (sumOver xs F) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true]
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem mulSign (b : Bool) (z w : C) : z*signed b w=signed b (z*w) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true,Ring.mul_neg]
private theorem signGroup (a b c d : Bool) (eq : (a^^b)=(c^^d)) (z : C) : signed a (signed b z)=signed c (signed d z) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [signed] <;> grind only

set_option synthInstance.maxSize 1000 in
theorem fullyAlternates (Z : Four α → ComplexScalar R) (hz : AlternatingTail Z) : Alternating (merged Z) := by
  intro p hp u
  obtain ⟨perm,tab⟩ := _root_.of_decide_eq_true (List.all_eq_true.mp square p hp)
  let term (i : Fin 4) := signed (oddPermutation (swaps i)) (Z (reorder u (swaps i)))
  have row (i : Fin 4) : signed (oddPermutation (swaps i)) (Z (reorder (reorder u p) (swaps i)))=
      signed (oddPermutation p) (term (position p i)) := by
    obtain ⟨nin,cp,sg⟩ := tab i
    rw [SingleCreationCAR.compose,cp,←SingleCreationCAR.compose,hz _ nin]
    exact signGroup _ _ _ _ sg _
  unfold merged; rw [sumOverCongr _ row,signSum]; apply congrArg (signed _)
  simpa only [sumOver,List.map_map,Function.comp_def] using permSum perm term

def contraction (xs : List α) (y : α → ComplexScalar R) (F : Four α → ComplexScalar R) (r : Triple α) :=
  sumOver xs (fun a => star (y a)*F (insert a r))
private def lifted (y : α → ComplexScalar R) (G : Triple α → ComplexScalar R) (u : Four α) :=
  y u.1.1 * G (tail u)
private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
private theorem reSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl
private theorem sliceFactor (xs : List α) (F : Four α → C) :
    sumOver (fourIndices xs) F=sumOver xs (fun a => sumOver (triples xs) (fun r => F (insert a r))) := by
  unfold fourIndices triples; simp only [productSum]; rfl

private theorem normLift (xs : List α) (y : α → ComplexScalar R) (unit : sumOver xs (fun t => star (y t)*y t)=1)
    (G : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => normSq (lifted y G u))=sumOver (triples xs) (fun r => normSq (G r)) := by
  have h := congrArg ComplexScalar.re unit
  change (sumOver xs (fun t => star (y t)*y t)).re=(1:ComplexScalar R).re at h; rw [reSum] at h
  simp only [re_star_mul_self,re_one] at h
  rw [sliceFactor]; unfold lifted; change sumOver xs (fun a => sumOver (triples xs) (fun r => normSq (y a*G r)))=_
  simp only [normSq_mul,←sumOverMulLeft,←sumOverMulRight,h,Semiring.one_mul]

private theorem adjoint (xs : List α) (y : α → ComplexScalar R) (F : Four α → ComplexScalar R) (G : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => star (F u)*lifted y G u)=
    sumOver (triples xs) (fun r => star (contraction xs y F r)*G r) := by
  rw [sliceFactor]; unfold contraction
  change sumOver xs (fun a => sumOver (triples xs) (fun r => star (F (insert a r))*(y a*G r)))=_
  rw [sumOverSwap]; simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight]
  apply sumOverCongr; intro r; apply sumOverCongr; intro a; grind only

private def innerCut (xs : List α) (y : α → ComplexScalar R) (G : Triple α → ComplexScalar R) (b c : α) :=
  sumOver xs (fun a => star (y a)*G ((a,b),c))
private theorem liftSwap (xs : List α) (y : α → ComplexScalar R) (G : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => (star (lifted y G u)*lifted y G (reorder u swap)).re)=
    sumOver xs (fun b => sumOver xs (fun c => normSq (innerCut xs y G b c))) := by
  have eq : sumOver (fourIndices xs) (fun u => star (lifted y G u)*lifted y G (reorder u swap))=
      sumOver xs (fun b => sumOver xs (fun c => star (innerCut xs y G b c)*innerCut xs y G b c)) := by
    unfold fourIndices innerCut; simp only [productSum,ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
    conv => lhs; arg 2; intro a; rw [sumOverSwap]
    conv => lhs; rw [sumOverSwap]
    conv => lhs; arg 2; intro c; arg 2; intro a; rw [sumOverSwap]
    conv => lhs; arg 2; intro c; rw [sumOverSwap]
    apply sumOverCongr; intro c; apply sumOverCongr; intro d; apply sumOverCongr; intro a; apply sumOverCongr; intro b
    change star (y a*G ((b,c),d))*(y b*G ((a,c),d))=_
    simp only [star_mul]; grind only
  simpa only [reSum,re_star_mul_self] using congrArg ComplexScalar.re eq

private theorem swapTable : ∀ i : Fin 4, swaps i∈permutations ∧ reorder (swaps i) (swaps i)=SingleCreationCAR.ident := by decide
private theorem reBased {C : Type} [CommRing C] [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (i : Fin 4) (F : Four α → C) :
    sumOver (fourIndices xs) (fun u => F (reorder u (swaps i)))=sumOver (fourIndices xs) F := by
  simpa only [sumOver,List.map_map,Function.comp_def] using permSum (FourCopySectors.fullPermuted xs nd full (swaps i) (swapTable i).1) F

private theorem adjointFour [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (y : α → ComplexScalar R) (F : Four α → ComplexScalar R) (hF : Alternating F) (G : Triple α → ComplexScalar R) :
    sumOver (fourIndices xs) (fun u => star (F u)*merged (lifted y G) u)=
      4*sumOver (triples xs) (fun r => star (contraction xs y F r)*G r) := by
  unfold merged; simp only [sumOverMulLeft]; rw [sumOverSwap]
  have row (i : Fin 4) :
      sumOver (fourIndices xs) (fun u => star (F u)*signed (oddPermutation (swaps i)) (lifted y G (reorder u (swaps i))))=
      sumOver (fourIndices xs) (fun u => star (F u)*lifted y G u) := by
    rw [←reBased xs nd full i (fun u => star (F u)*signed (oddPermutation (swaps i)) (lifted y G (reorder u (swaps i))))]
    simp only [SingleCreationCAR.compose,(swapTable i).2,show ∀u : Four α,reorder u SingleCreationCAR.ident=u from fun _ => rfl,hF _ (swapTable i).1]
    apply sumOverCongr; intro u; cases oddPermutation (swaps i) <;> simp [signed]
    have h (z : ComplexScalar R) : star (-z)= -star z := by apply ComplexScalar.ext <;> simp
    rw [h]; grind only
  rw [sumOverCongr _ row,adjoint]; conv => rhs; rw [←sumOverMulLeft]
  let z := sumOver (triples xs) (fun r => star (contraction xs y F r)*G r)
  change z+(z+(z+(z+0)))=4*z; grind only

private theorem liftAlternates (xs : List α) (y : α → ComplexScalar R) (F : Four α → ComplexScalar R) (hF : Alternating F) :
    AlternatingTail (lifted y (contraction xs y F)) := by
  intro p hp u
  have fixed (t : α) : insert t (tail (reorder u p))=reorder (insert t (tail u)) p ∧ (reorder u p).1.1=u.1.1 := by
    simp only [SingleCreationCAR.blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩
  have leg : p∈permutations := by
    simp only [SingleCreationCAR.blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  unfold lifted contraction
  simp only [(fixed u.1.1).2,(fixed _).1,hF _ leg,mulSign,signSum]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
/-- Unit contraction from an alternating four-tensor to a three-tensor.
Both norms sum over ordered coordinates, giving exactly the factor four. -/
theorem contractionNorm [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (y : α → ComplexScalar R) (unit : sumOver xs (fun a => star (y a)*y a)=1)
    (F : Four α → ComplexScalar R) (hF : Alternating F) :
    4*sumOver (triples xs) (fun r => normSq (contraction xs y F r))≤sumOver (fourIndices xs) (fun u => normSq (F u)) := by
  let G := contraction xs y F
  let T := lifted y G
  let M := merged T
  let xs4 := fourIndices xs
  let N := sumOver (triples xs) (fun r => normSq (G r))
  have car := SingleCreationCAR.singleCreationCAR xs nd full T (liftAlternates xs y F hF)
  have nn := normLift xs y unit G
  have swap := liftSwap xs y G
  have pos := Compression.sumOverNonnegative xs _ (fun b _ => Compression.sumOverNonnegative xs _ (fun c _ => normSq_nonnegative (innerCut xs y G b c)))
  have upper : sumOver xs4 (fun u => normSq (M u))≤4*N := by
    change sumOver xs4 (fun u => normSq (M u)) = 4*(sumOver xs4 (fun u => normSq (T u))-3*_) at car
    change sumOver xs4 (fun u => normSq (T u))=N at nn
    rw [car,nn,swap]; grind only
  have adj := congrArg ComplexScalar.re (adjointFour xs nd full y F hF G)
  change (sumOver xs4 (fun u => star (F u)*M u)).re=(ofReal (4:R)*sumOver (triples xs) (fun r => star (G r)*G r)).re at adj
  have factor (z : ComplexScalar R) : (ofReal (4:R)*z).re=4*z.re := by simp [re_mul,ofReal]; grind only
  simp only [factor,reSum,re_star_mul_self] at adj
  have dif (u) : normSq (F u-M u)=normSq (F u)+normSq (M u)-2*(star (F u)*M u).re := by
    simp only [normSq,re_sub,im_sub,re_mul,re_star,im_star]; grind only
  have nonnegative := Compression.sumOverNonnegative xs4 (fun u => normSq (F u-M u)) (fun _ _ => normSq_nonnegative _)
  rw [sumOverCongr _ dif,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,adj] at nonnegative
  change 4*N≤sumOver xs4 (fun u => normSq (F u)); grind only

theorem physicalSecondContraction [DecidableEq I] {n} (half : R) (unit : 2*half=1)
    (ys : List I) (nd : ys.Nodup) (A : Basis n → I → ComplexScalar R)
    (orth : ∀i j,sumOver (qubitIndices n) (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (x y : Basis n → ComplexScalar R) (hx : sumOver (qubitIndices n) (fun a => star (x a)*x a)=1)
    (hy : sumOver (qubitIndices n) (fun a => star (y a)*y a)=1) (c : I → Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun r => normSq (contraction (qubitIndices n) y
      (merged (PhysicalOccupationBound.physicalSource half ys A x c)) r))≤
    36*half^n * sumOver ys (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq (c i p))) := by
  letI : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
  have h := contractionNorm (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
    y hy _ (fullyAlternates _ (PhysicalOccupationBound.physicalAlternating half ys A x c))
  have g := Std.le_trans h (PhysicalOccupationBound.physicalOccupation half unit ys nd A orth x hx c)
  grind only

end Order
end RankSeven.PhysicalDoubleHoleNorm
#print axioms RankSeven.PhysicalDoubleHoleNorm.contractionNorm
#print axioms RankSeven.PhysicalDoubleHoleNorm.physicalSecondContraction
