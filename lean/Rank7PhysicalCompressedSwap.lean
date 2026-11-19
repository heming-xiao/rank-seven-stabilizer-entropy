import Rank7PhysicalCutCapacities

/-! Triple contraction isometry on arbitrary seven-column orthonormal frames
and the physical compressed-swap estimate from the two-link argument. -/
namespace RankSeven.PhysicalCompressedSwap
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase HyperplaneIncidence
open PhysicalCutCapacities (Triple triplePerms extend head permute tripleAlt triples tensorThree leg)
open FourCopySectors (Perm)
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem sumPairs {C α β : Type} [CommRing C] (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]
  apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem mapPermThree {α β C : Type} [CommRing C] (A : α → β → C)
    (x : Triple α) (v : Triple β) (p : Perm) (hp : p∈triplePerms) :
    tensorThree A (permute x p) v =
      tensorThree A x (permute v (FourCopySectors.inverse p)) := by
  simp [triplePerms] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [tensorThree,permute,head,extend,reorder,position,FourCopySectors.inverse] <;> grind only

private theorem tripleTensorGram {α β : Type} [DecidableEq β] (xs : List α)
    (A : α → β → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0) (u v : Triple β) :
    sumOver (triples xs) (fun x => star (tensorThree A x u)*tensorThree A x v) =
      if u=v then 1 else 0 := by
  let h (i j : β) (x : α) := star (A x i)*A x j
  have e := factorProductSum (productIndices xs xs) xs
    (fun p : α × α => h u.1.1 v.1.1 p.1*h u.1.2 v.1.2 p.2) (h u.2 v.2)
  rw [factorProductSum] at e
  refine (sumOverCongr (triples xs) (g:=fun x => (h _ _ x.1.1*h _ _ x.1.2)*h _ _ x.2) (fun x => ?_)).trans (e.trans ?_)
  · unfold h tensorThree; simp only [star_mul]; grind only
  · unfold h; simp only [orth]
    rcases u with ⟨⟨a,b⟩,c⟩; rcases v with ⟨⟨d,e'⟩,f'⟩
    by_cases ad : a=d <;> by_cases be : b=e' <;> by_cases cf : c=f' <;> simp [ad,be,cf] <;> grind only

private theorem triplesNodup {α : Type} (xs : List α) (nd : xs.Nodup) : (triples xs).Nodup :=
  HyperplaneInduction.pairsNodup _ _ (HyperplaneInduction.pairsNodup _ _ nd nd) nd
private theorem triplesFull {α : Type} (xs : List α) (full : ∀ a,a∈xs) (u : Triple α) : u∈triples xs := by
  change u∈(productIndices xs xs).flatMap (fun a => xs.map (fun b => (a,b)))
  exact List.mem_flatMap.mpr ⟨u.1,HyperplaneInduction.pairMember (full _) (full _),List.mem_map.mpr ⟨u.2,full _,rfl⟩⟩

private def bilinear {α : Type} (xs : List α) (z v : α → ComplexScalar R) (K : α → α → ComplexScalar R) :=
  sumOver xs (fun a => sumOver xs (fun b => star (z a)*K a b*v b))

private theorem threeGram {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (nd : xs.Nodup) (full : ∀ x,x∈xs)
    (A : α → β → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (u v : Triple β) :
    bilinear (triples xs) (fun x => tensorThree A x u) (fun x => tensorThree A x v) tripleAlt=
    sumOver triplePerms (fun p => (signed (oddPermutation p) 1 : ComplexScalar R) *
      (if permute u (FourCopySectors.inverse p)=v then 1 else 0)) := by
  let ts := triples xs
  let z (x : Triple α) := tensorThree A x u
  let w (x : Triple α) := tensorThree A x v
  let c (p : Perm) : ComplexScalar R := signed (oddPermutation p) 1
  let δ (a b : Triple α) (p : Perm) : ComplexScalar R := if a=permute b p then c p else 0
  change sumOver ts (fun a => sumOver ts (fun b => star (z a)*(sumOver triplePerms (δ a b))*w b))=_
  simp only [sumOverMulLeft,sumOverMulRight]
  rw [sumOverSwap ts ts]
  conv => lhs; arg 2; intro b; rw [sumOverSwap ts triplePerms]
  rw [sumOverSwap ts triplePerms]
  have select (p : Perm) (b : Triple α) :
      sumOver ts (fun a => star (z a)*δ a b p*w b)=c p*(star (z (permute b p))*w b) := by
    refine (sumOverCongr ts (g:=fun a => if permute b p=a then c p*(star (z a)*w b) else 0) (fun a => ?_)).trans
      (ExteriorPauliBase.sumOnIndex ts _ _ (triplesNodup xs nd) (triplesFull xs full _))
    by_cases eq : a=permute b p <;> simp [δ,eq,Ne.symm] <;> grind only
  simp only [select,←sumOverMulLeft]
  have rows (p : Perm) (hp : p∈triplePerms) :
      sumOver ts (fun b => star (z (permute b p))*w b)=(if permute u (FourCopySectors.inverse p)=v then 1 else 0) := by
    unfold z w; simp only [mapPermThree A _ u p hp]; exact tripleTensorGram xs A orth _ v
  refine (congrArg List.sum (List.map_congr_left (g:=fun p => c p*
    (if permute u (FourCopySectors.inverse p)=v then 1 else 0)) (fun p hp => congrArg (fun w => c p*w) (rows p hp))))
private def sourceProjection {α β : Type} (xs : List α) (z : α → ComplexScalar R) (F : α → β → ComplexScalar R) (p : β) :=
  sumOver xs (fun a => star (z a)*F a p)

private theorem pullGram {α β : Type} (xs : List α) (os : List β)
    (z v : α → ComplexScalar R) (F : α → β → ComplexScalar R) (K : α → α → ComplexScalar R)
    (rel : ∀ a b,2*sumOver os (fun p => F a p*star (F b p))=3*K a b) :
    2*sumOver os (fun p => sourceProjection xs z F p*star (sourceProjection xs v F p))=3*bilinear xs z v K := by
  unfold sourceProjection bilinear
  simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro p; rw [sumOverSwap xs xs]
  rw [sumOverSwap os xs]
  apply sumOverCongr; intro a
  rw [sumOverSwap os xs]; apply sumOverCongr; intro b
  have g := congrArg (fun w => star (z a)*w*v b) (rel a b)
  change star (z a)*(2*sumOver os _)*v b=_ at g
  rw [sumOverMulLeft,sumOverMulLeft,sumOverMulRight] at g
  refine (sumOverCongr os (g:=fun p => star (z a)*(2*(F a p*star (F b p)))*v b) (fun p => ?_)).trans ?_
  · grind only
  · rw [g]; grind only

def signedOverlap (u v : Triple (Fin 7)) : ComplexScalar R :=
  sumOver triplePerms (fun p => signed (oddPermutation p) 1 *
    (if permute u (FourCopySectors.inverse p)=v then 1 else 0))

/-- The full complex off-diagonal contracted Gram, with the exact physical normalization.
Its six-term overlap is the exterior determinant of the triple Kronecker matrix. -/
theorem physicalLegGram (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (u v : Triple (Fin 7)) :
    2*sumOver (MixedDefect.oddWords n) (fun p => sumOver (qubitIndices n) (fun t => leg half A u t p * star (leg half A v t p))) =
      (3*(4*ofReal half^n)) * signedOverlap u v := by
  let xs := qubitIndices n
  let ts := triples xs
  let os := MixedDefect.oddWords n
  let z (a : Triple (Basis n)) := tensorThree A a u
  let w (a : Triple (Basis n)) := tensorThree A a v
  let T := exteriorKernel (n:=n) (imaginaryUnit (R:=R)) (ofReal half)
  have h2 : 2*ofReal half=(1:ComplexScalar R) := by
    change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  have occ (t : Basis n) : 2*sumOver os (fun p => leg half A u t p * star (leg half A v t p)) =
      3*bilinear ts z w (fun a b => T (extend a t) (extend b t)) :=
    pullGram ts os z w _ _ (fun a b => WedgeSquareIntertwiner.physicalWedgeSquareGram half unit _ _)
  have total : sumOver xs (fun t => bilinear ts z w (fun a b => T (extend a t) (extend b t)))=
      (4*ofReal half^n)*signedOverlap u v := by
    unfold bilinear
    rw [sumOverSwap xs ts]
    conv => lhs; arg 2; intro a; rw [sumOverSwap xs ts]
    simp only [←sumOverMulRight,←sumOverMulLeft]
    have marginal (a b : Triple (Basis n)) : sumOver xs (fun t => T (extend a t) (extend b t))=
        4*ofReal half^n*tripleAlt a b := PhysicalCutCapacities.oneHoleResolution imaginaryUnit (ofReal half) imaginaryUnit_fourth h2 a b
    simp only [marginal]
    have factor (a b : Triple (Basis n)) :
        star (z a)*(4*ofReal half^n*tripleAlt a b)*w b=(4*ofReal half^n)*(star (z a)*tripleAlt a b*w b) := by grind only
    simp only [factor,←sumOverMulLeft]
    exact congrArg ((4*ofReal half^n)* ·) (threeGram xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) A orth u v)
  rw [sumOverSwap,sumOverMulLeft,sumOverCongr xs occ,←sumOverMulLeft,total]; grind only

def ascending (u : Triple (Fin 7)) := u.1.1<u.1.2 ∧ u.1.2<u.2

theorem sortedOverlap (u v : Triple (Fin 7)) (hu : ascending u) (hv : ascending v) :
    signedOverlap (R:=R) u v=if u=v then 1 else 0 := by
  rcases u with ⟨⟨a,b⟩,c⟩
  have elim (T : Triple (Fin 7)) (h : ¬ ascending T) : T≠v := fun eq => h (eq ▸ hv)
  obtain ⟨h1,h2⟩ := hu
  change a<b at h1; change b<c at h2
  have e1 := elim ((a,c),b) (by unfold ascending; dsimp only; omega)
  have e2 := elim ((b,a),c) (by unfold ascending; dsimp only; omega)
  have e3 := elim ((b,c),a) (by unfold ascending; dsimp only; omega)
  have e4 := elim ((c,a),b) (by unfold ascending; dsimp only; omega)
  have e5 := elim ((c,b),a) (by unfold ascending; dsimp only; omega)
  simp [signedOverlap,triplePerms,permute,FourCopySectors.inverse,extend,head,reorder,position,oddPermutation,signed,
    sumOver,e1,e2,e3,e4,e5]; split <;> grind only

def swapFiber {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (ts : List (Triple (Fin 7))) (c : Triple (Fin 7) → Word n → ComplexScalar R) (t : Basis n) (p q : Word n) :=
  sumOver ts (fun u => leg half A u t p*c u q)

private theorem sumPermute3 {C I J K : Type} [CommRing C] (xs : List I) (ys : List J) (zs : List K) (f : I → J → K → C) :
    sumOver xs (fun x => sumOver ys (fun y => sumOver zs (f x y))) =
    sumOver ys (fun y => sumOver zs (fun z => sumOver xs (fun x => f x y z))) := by
  rw [sumOverSwap]; apply sumOverCongr; intro y; rw [sumOverSwap]

private theorem reSum {I : Type} (xs : List I) (f : I → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

private theorem productSum {I J C : Type} [CommRing C] (xs : List I) (ys : List J) (f : I × J → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem scaledIsometry {I J : Type} [DecidableEq I] (xs : List I) (nd : xs.Nodup) (rs : List J)
    (M : J → I → ComplexScalar R) (k : R)
    (orth : ∀ i∈xs, ∀ j∈xs, 2 * sumOver rs (fun r => M r i * star (M r j)) =
      if i=j then ofReal k else 0) (y : I → ComplexScalar R) :
    2 * sumOver rs (fun r => normSq (sumOver xs (fun i => M r i*y i))) = k*sumOver xs (fun i => normSq (y i)) := by
  have pull :
    2*sumOver rs (fun r => (sumOver xs (fun i => M r i*y i))*star (sumOver xs (fun i => M r i*y i))) =
      ofReal k * sumOver xs (fun i => y i*star (y i)) := by
    simp only [ComplexExterior.starSumOver,star_mul,sumOverMulLeft,sumOverMulRight]
    rw [sumPermute3]
    apply congrArg List.sum; apply List.map_congr_left; intro j hj
    refine (sumOverCongr xs (g:=fun i => ((2:ComplexScalar R)*sumOver rs (fun r => M r i* star (M r j)))*(y i*star (y j))) (fun i => ?_)).trans ?_
    · simp only [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro r; grind only
    · refine (congrArg List.sum (List.map_congr_left (g:=fun i => if j=i then ofReal k*(y i*star (y i)) else 0) (fun i hi => ?_))).trans
        (ExteriorPauliBase.sumOnIndex xs j _ nd hj)
      rw [orth i hi j hj]; by_cases e : i=j <;> simp [e,Ne.symm] <;> grind only
  have eq := congrArg ComplexScalar.re pull
  have scale (v : ComplexScalar R) (a : R) : (ofReal a*v).re=a*v.re := by simp [re_mul,ofReal]; grind only
  change (ofReal (2:R)*_).re=(ofReal k*_).re at eq
  simp only [scale,reSum] at eq
  have self (z : ComplexScalar R) : (z*star z).re=normSq z := by rw [CommSemiring.mul_comm,re_star_mul_self]
  simpa only [self] using eq

theorem physicalSwapIsometry (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (ts : List (Triple (Fin 7))) (nd : ts.Nodup) (hs : ∀ u∈ts, ascending u)
    (c : Triple (Fin 7) → Word n → ComplexScalar R) (q : Word n) :
    2 * sumOver (MixedDefect.oddWords n) (fun p => sumOver (qubitIndices n) (fun t => normSq (swapFiber half A ts c t p q))) =
      (3*(4*half^n))*sumOver ts (fun u => normSq (c u q)) := by
  let os := MixedDefect.oddWords n
  let bs := qubitIndices n
  rw [←productSum os bs (fun r => normSq (swapFiber half A ts c r.2 r.1 q))]
  refine scaledIsometry ts nd (productIndices os bs) (fun r u => leg half A u r.2 r.1) (3*(4*half^n)) ?_ (fun u => c u q)
  intro u hu v hv; rw [productSum,physicalLegGram half unit A orth u v,sortedOverlap u v (hs u hu) (hs v hv)]
  by_cases e : u=v
  · simp only [ite_eq_left e,Semiring.mul_one,←PhysicalPairedReduction.realEmbeddingPow]
    change ofReal (3:R) * (ofReal (4:R)*ofReal (half^n))=ofReal _
    apply ComplexScalar.ext <;> simp [re_mul,im_mul,ofReal] <;> grind only
  · simp [e,Semiring.mul_zero]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumLe {I : Type} (xs : List I) (f g : I → R) (h : ∀ i∈xs, f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i is ih =>
    have a := h i List.mem_cons_self
    have b := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    change f i+sumOver is f ≤ g i+sumOver is g; grind only

private theorem swapEstimate {I : Type} (xs : List I) (S : I → I → ComplexScalar R) :
    sumOver xs (fun i => sumOver xs (fun j => (star (S i j)*S j i).re)) ≤
    sumOver xs (fun i => sumOver xs (fun j => normSq (S i j))) := by
  have pair (i j : I) : 2*(star (S i j)*S j i).re ≤ normSq (S i j)+normSq (S j i) := by
    have h := normSq_nonnegative (S i j - S j i)
    simp only [normSq,re_sub,im_sub,re_mul,re_star,im_star] at h ⊢; grind only
  have all := sumLe xs _ _ (fun i _ => sumLe xs _ _ (fun j _ => pair i j))
  simp only [←sumOverMulLeft,sumOverAdd] at all
  have symm := sumOverSwap xs xs (fun i j => normSq (S i j))
  grind only

/-- The physical three-hole cross-Gram is dominated by the positive identity
price for any collection of distinct increasing frame triples. This is the
upper bound on the two-contraction layer in (192), in Pauli-frame coordinates. -/
theorem physicalCompressedSwapBound (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (ts : List (Triple (Fin 7))) (nd : ts.Nodup) (hs : ∀ u∈ts, ascending u)
    (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    let os := MixedDefect.oddWords n
    let S := swapFiber half A ts c
    2*sumOver (qubitIndices n) (fun t => sumOver os (fun p => sumOver os (fun q => (star (S t p q) * S t q p).re))) ≤
      (3*(4*half^n))*sumOver os (fun q => sumOver ts (fun u => normSq (c u q))) := by
  intro os S
  have localbound := sumLe (qubitIndices n) _ _ (fun t _ => swapEstimate os (S t))
  have row (f : Basis n → Word n → Word n → R) :
      sumOver (qubitIndices n) (fun t => sumOver os (fun p => sumOver os (fun q => f t p q))) =
        sumOver os (fun q => sumOver os (fun p => sumOver (qubitIndices n) (fun t => f t p q))) := by
    rw [sumPermute3,sumOverSwap]
  have e := row (fun t p q => normSq (S t p q))
  have total : 2*sumOver (qubitIndices n) (fun t => sumOver os (fun p => sumOver os (fun q => normSq (S t p q)))) =
      (3*(4*half^n))*sumOver os (fun q => sumOver ts (fun u => normSq (c u q))) := by
    rw [e,sumOverMulLeft,sumOverMulLeft]
    exact sumOverCongr os (physicalSwapIsometry half unit A orth ts nd hs c)
  grind only
end Order

end RankSeven.PhysicalCompressedSwap
#print axioms RankSeven.PhysicalCompressedSwap.physicalCompressedSwapBound
#print axioms RankSeven.PhysicalCompressedSwap.physicalSwapIsometry
#print axioms RankSeven.PhysicalCompressedSwap.physicalLegGram
