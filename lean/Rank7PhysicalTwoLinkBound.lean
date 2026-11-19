import Rank7FiveFrameContractions

/-! Physical five-mode source specialized to one reference column and the
ten unordered edges on five other columns. -/
namespace RankSeven.PhysicalTwoLinkBound
open Lean.Grind Pauli ComplexScalar
open PhysicalCutCapacities (Triple leg triples extend tensorThree)
open FiveShuffleCAR (Five indices act ident firstSwap secondSwap merge)
open FiveFrameContractions (anchored source pairing)
variable {R C : Type} [CommRing R] [CommRing C]
attribute [local instance] Ring.intCast

abbrev Edge := Fin 7 × Fin 7
def modes : List (Fin 7) := [1,2,3,4,5]
def edges : List Edge := [(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def edgeTriple (e : Edge) : Triple (Fin 7) := ((0,e.1),e.2)
def frameTriples := edges.map edgeTriple
private theorem sorted : frameTriples.Nodup ∧ frameTriples.all (fun u => decide (u.1.1<u.1.2 ∧ u.1.2<u.2))=true := by decide
private theorem edgeOrder : edges.all (fun e => decide (e.1<e.2))=true := by decide
private theorem bothOrders : (productIndices modes modes).Perm ((modes.map (fun x => (x,x)))++edges++edges.map Prod.swap) := by decide

def extendEdges {B : Type} (c : Triple (Fin 7) → B → ComplexScalar R) (i j : Fin 7) (p : B) :=
  if i<j then c ((0,i),j) p else if j<i then -c ((0,j),i) p else 0
private theorem skew {B : Type} (c : Triple (Fin 7) → B → ComplexScalar R) (i j : Fin 7) (p : B) :
    extendEdges c j i p = -extendEdges c i j p := by
  unfold extendEdges; by_cases a : i<j <;> by_cases b : j<i <;> simp [a,b] <;> grind only
private theorem onDiag {B : Type} (c : Triple (Fin 7) → B → ComplexScalar R) (i : Fin 7) (p : B) :
    extendEdges c i i p=0 := by simp [extendEdges]
private theorem onEdges {B : Type} (c : Triple (Fin 7) → B → ComplexScalar R) (e : Edge) (he : e∈edges) (p : B) :
    extendEdges c e.1 e.2 p=c (edgeTriple e) p := by
  have h := _root_.of_decide_eq_true (List.all_eq_true.mp edgeOrder e he)
  simp only [extendEdges,ite_eq_left h,edgeTriple]

private theorem sumPerm {I : Type} {xs ys : List I} (h : xs.Perm ys) (f : I → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2
private theorem sumAppend {I : Type} (xs ys : List I) (f : I → C) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih => change f i+sumOver (xs++ys) f=(f i+sumOver xs f)+_; rw [ih]; grind only
private theorem sum0 {I : Type} (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs <;> simp_all [sumOver,List.map,AddCommMonoid.zero_add]
private theorem edgesTwice (f : Edge → C) (diag : ∀i, f (i,i)=0) (sw : ∀e∈edges, f e.swap=f e) :
    sumOver (productIndices modes modes) f = 2*sumOver edges f := by
  rw [sumPerm bothOrders,sumAppend,sumAppend]
  have mapped {A B : Type} (xs : List A) (F : B → C) (T : A → B) :
      sumOver (xs.map T) F=sumOver xs (fun i => F (T i)) := by simp [sumOver,List.map_map,Function.comp_def]
  rw [mapped,mapped,sumOverCongr _ diag,sum0]
  have e : sumOver edges (fun i => f i.swap)=sumOver edges f := congrArg List.sum (List.map_congr_left sw)
  rw [e]; grind only
private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem reSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

private theorem column12 {n} (half : R) (p : Word n) (a b c d : Basis n) :
    WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,c),b,d)= -WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),c,d) := by
  let s : ExteriorPauliBase.Permutation := ((0,2),(1,3))
  have hs : s∈ExteriorPauliBase.permutations := by decide
  have neg : FourCopySectors.coefficient .antisymmetric s=(-1:Int) := by decide
  have h := AlternatingTrace.alternatingRow (PhysicalMixedFrame.doubledWord (R:=R) p) s hs ((a,b),c,d)
  rw [neg] at h
  change (ofReal half)^(n+2)*WedgeSquareIntertwiner.alternatingWord p (GenericExteriorKernel.reorder ((a,b),c,d) s)=_
  change WedgeSquareIntertwiner.alternatingWord p (GenericExteriorKernel.reorder ((a,b),c,d) s)=
    Int.cast (R:=ComplexScalar R) (-1:Int) * WedgeSquareIntertwiner.alternatingWord p ((a,b),c,d) at h
  rw [h,Ring.intCast_neg,Ring.intCast_one]; unfold WedgeSquareIntertwiner.wedgeSquareColumn; grind only

theorem legFlip {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (i j : Fin 7) (t : Basis n) (p : Word n) :
    leg half A ((0,j),i) t p= -leg half A ((0,i),j) t p := by
  let xs := qubitIndices n
  let Z := fun u : Triple (Basis n) => WedgeSquareIntertwiner.wedgeSquareColumn half p (extend u t)
  change sumOver (triples xs) (fun u => star (tensorThree A u ((0,j),i))*Z u)=
    -sumOver (triples xs) (fun u => star (tensorThree A u ((0,i),j))*Z u)
  have minus {B : Type} (ys : List B) (f : B → ComplexScalar R) : -sumOver ys f=sumOver ys (fun k => -f k) := by
    have e := sumOverMulLeft ys f (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e
  unfold triples; simp only [productSum,minus]
  apply sumOverCongr; intro a; rw [sumOverSwap]; apply sumOverCongr; intro b; apply sumOverCongr; intro c
  unfold Z tensorThree extend; rw [column12]; simp only [star_mul]; grind only

private def contracted {B T O : Type} (es : List B) (L : B → T → O → ComplexScalar R) (c : B → O → ComplexScalar R) (t : T) (p q : O) :=
  sumOver es (fun e => L e t p * star (c e q))
private theorem reshape {B T O : Type} (es : List B) (xs : List T) (os : List O)
    (L : B → T → O → ComplexScalar R) (c : B → O → ComplexScalar R) :
    sumOver es (fun b => sumOver es (fun e => sumOver xs (fun t =>
      star (sumOver os (fun p => c b p*L e t p)) * sumOver os (fun q => c e q*L b t q)))) =
    sumOver xs (fun t => sumOver os (fun p => sumOver os (fun q =>
      star (contracted es L c t p q)*contracted es L c t q p))) := by
  unfold contracted; simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  conv => lhs; arg 2; intro t; arg 2; intro b; arg 2; intro e; rw [sumOverSwap]
  conv => lhs; arg 2; intro t; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro t; rw [sumOverSwap]
  conv => lhs; arg 2; intro t; arg 2; intro p; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro t; arg 2; intro p; rw [sumOverSwap]
  apply sumOverCongr; intro t; apply sumOverCongr; intro p; apply sumOverCongr; intro q; apply sumOverCongr; intro b; apply sumOverCongr; intro e
  grind only

private theorem contractedTwice {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (c : Triple (Fin 7) → Word n → ComplexScalar R) (t : Basis n) (p q : Word n) :
    contracted (productIndices modes modes) (fun e t p => leg half A (edgeTriple e) t p) (fun e => extendEdges c e.1 e.2) t p q=
      2*PhysicalCompressedSwap.swapFiber half A frameTriples (fun e p => star (c e p)) t p q := by
  let f (e : Edge) := leg half A (edgeTriple e) t p * star (extendEdges c e.1 e.2 q)
  have d (i : Fin 7) : f (i,i)=0 := by unfold f; rw [onDiag,show star (0:ComplexScalar R)=0 from star_ofReal 0,Semiring.mul_zero]
  have s (e : Edge) (_ : e∈edges) : f e.swap=f e := by
    rcases e with ⟨i,j⟩; unfold f; change leg half A ((0,j),i) t p*star (extendEdges c j i q)=_
    rw [legFlip,skew c i j q]
    have h (z : ComplexScalar R) : star (-z)= -star z := by apply ComplexScalar.ext <;> simp
    rw [h]; change _=leg half A ((0,i),j) t p*star (extendEdges c i j q); grind only
  change sumOver _ f=_
  rw [edgesTwice f d s]; apply congrArg (2*·)
  change sumOver edges f=sumOver (edges.map edgeTriple) _
  simp only [sumOver,List.map_map,Function.comp_def]; apply congrArg List.sum; apply List.map_congr_left
  intro e he; unfold f; rw [onEdges c e he]

def edgeMass {n} (c : Triple (Fin 7) → Word n → ComplexScalar R) :=
  sumOver (MixedDefect.oddWords n) (fun p => sumOver frameTriples (fun u => normSq (c u p)))
def physicalSource {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (c : Triple (Fin 7) → Word n → ComplexScalar R) : Five (Basis n) → ComplexScalar R :=
  source modes A (fun i j => anchored half A 0 (extendEdges c i j))

private theorem massTwice {n} (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    sumOver modes (fun i => sumOver modes (fun j => sumOver (MixedDefect.oddWords n) (fun p => normSq (extendEdges c i j p))))=2*edgeMass c := by
  let os := MixedDefect.oddWords n
  let f (e : Edge) := sumOver os (fun p => normSq (extendEdges c e.1 e.2 p))
  have d (i : Fin 7) : f (i,i)=0 := by unfold f; simp only [onDiag,normSq_zero,sum0]
  have s (e : Edge) (_ : e∈edges) : f e.swap=f e := by
    rcases e with ⟨i,j⟩
    apply sumOverCongr; intro p
    change normSq (extendEdges c j i p)=normSq (extendEdges c i j p); rw [skew c i j]; simp [normSq]; grind only
  rw [←productSum modes modes f,edgesTwice f d s]; apply congrArg (2*·)
  unfold edgeMass; rw [sumOverSwap]; apply sumOverCongr; intro p
  change sumOver edges _=sumOver (edges.map edgeTriple) _
  unfold sumOver; rw [List.map_map]; apply congrArg List.sum; apply List.map_congr_left; intro e he
  exact congrArg normSq (onEdges c e he p)

private theorem realFactor (a : R) (z : ComplexScalar R) : (ofReal a*z).re=a*z.re := by simp [re_mul,ofReal]; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
theorem secondLayer {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    let Z := physicalSource half A c
    2*sumOver (indices (qubitIndices n)) (fun u => (star (Z u)*Z (act secondSwap u)).re)≤
      12*(4*half^n)*edgeMass c := by
  intro Z
  let xs := qubitIndices n
  let os := MixedDefect.oddWords n
  let S := PhysicalCompressedSwap.swapFiber half A frameTriples (fun u p => star (c u p))
  have v := FiveFrameContractions.sourceTwo (qubitIndices n) modes A (fun i j => anchored half A 0 (extendEdges c i j))
  simp only [FiveFrameContractions.anchoredCutTwo] at v
  have x := reshape (productIndices modes modes) xs os (fun e t p => leg half A (edgeTriple e) t p) (fun e => extendEdges c e.1 e.2)
  have eq := congrArg ComplexScalar.re (v.trans x)
  unfold FiveFrameContractions.pairing at eq; simp only [reSum,contractedTwice] at eq
  have scale (f g : ComplexScalar R) : (star (2*f)*(2*g)).re=4*(star f*g).re := by
    have e : star (2:ComplexScalar R)=2 := star_ofReal (2:R)
    rw [star_mul,e]
    have b : (2:ComplexScalar R)*star f*(2*g)=ofReal (4:R)*(star f*g) := by change _=4*_; grind only
    rw [b,realFactor]
  simp only [scale,←sumOverMulLeft] at eq
  change sumOver (indices xs) (fun u => (star (Z u)*Z (act secondSwap u)).re)=
    4*sumOver xs (fun t => sumOver os (fun p => sumOver os (fun q => (star (S t p q)*S t q p).re))) at eq
  have cap := PhysicalCompressedSwap.physicalCompressedSwapBound half unit A orth frameTriples sorted.1
    (fun u hu => _root_.of_decide_eq_true (p:=u.1.1<u.1.2 ∧ u.1.2<u.2) (List.all_eq_true.mp sorted.2 u hu)) (fun u p => star (c u p))
  simp only [normSq_star] at cap
  change 2*sumOver xs (fun t => sumOver os (fun p => sumOver os (fun q => (star (S t p q)*S t q p).re)))≤(3*(4*half^n))*edgeMass c at cap
  rw [eq]; grind only

theorem zeroLayer {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    sumOver (indices (qubitIndices n)) (fun u => normSq (physicalSource half A c u))≤(72*half^n)*edgeMass c := by
  have h := FiveFrameContractions.physicalZeroExchange half unit A orth 0 modes (by decide) (extendEdges c)
  dsimp only at h; rw [massTwice] at h; change sumOver _ _≤_ at h
  exact Std.le_trans h (Std.le_of_eq (by grind only))

theorem firstLayer {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    let Z := physicalSource half A c
    0≤sumOver (indices (qubitIndices n)) (fun u => (star (Z u)*Z (act firstSwap u)).re) := by
  intro Z
  have h := congrArg ComplexScalar.re (FiveFrameContractions.physicalOneExchange half A orth 0 modes (by decide) (extendEdges c))
  unfold FiveFrameContractions.pairing at h; simp only [reSum,re_ofReal] at h
  change 0≤sumOver (indices (qubitIndices n)) (fun u => (star (Z u)*Z (act firstSwap u)).re)
  rw [show sumOver (indices (qubitIndices n)) (fun u => (star (Z u)*Z (act firstSwap u)).re)=_ from h]
  apply Compression.sumOverNonnegative; intro i _; apply Compression.sumOverNonnegative; intro r _; apply normSq_nonnegative
end Order

private theorem genAlternating {A : Type} (Z : Five A → ComplexScalar R)
    (h0 : ∀ a b c d e,Z ((b,a),(c,d),e)= -Z ((a,b),(c,d),e))
    (h1 : ∀ a b c d e,Z ((a,b),(d,c),e)= -Z ((a,b),(c,d),e))
    (h2 : ∀ a b c d e,Z ((a,b),(c,e),d)= -Z ((a,b),(c,d),e)) :
    FiveShuffleCAR.BlockAlternating Z := by
  intro p hp u; rcases u with ⟨⟨a,b⟩,⟨c,d⟩,e⟩
  simp only [FiveShuffleCAR.blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · change Z ((a,b),(c,e),d)=-Z ((a,b),(c,d),e); rw [h2 a b c d e]
  · change Z ((a,b),(d,c),e)=-Z ((a,b),(c,d),e); rw [h1 a b c d e]
  · change Z ((a,b),(d,e),c)=Z ((a,b),(c,d),e); rw [h2 a b d c e,h1 a b c d e]; grind only
  · change Z ((a,b),(e,c),d)=Z ((a,b),(c,d),e); rw [h1 a b c e d,h2 a b c d e]; grind only
  · change Z ((a,b),(e,d),c)=-Z ((a,b),(c,d),e); rw [h1 a b d e c,h2 a b d c e,h1 a b c d e]; grind only
  · change Z ((b,a),(c,d),e)=-Z ((a,b),(c,d),e); rw [h0 a b c d e]
  · change Z ((b,a),(c,e),d)=Z ((a,b),(c,d),e); rw [h2 b a c d e,h0 a b c d e]; grind only
  · change Z ((b,a),(d,c),e)=Z ((a,b),(c,d),e); rw [h1 b a c d e,h0 a b c d e]; grind only
  · change Z ((b,a),(d,e),c)=-Z ((a,b),(c,d),e); rw [h2 b a d c e,h1 b a c d e,h0 a b c d e]; grind only
  · change Z ((b,a),(e,c),d)=-Z ((a,b),(c,d),e); rw [h1 b a c e d,h2 b a c d e,h0 a b c d e]; grind only
  · change Z ((b,a),(e,d),c)=Z ((a,b),(c,d),e); rw [h1 b a d e c,h2 b a d c e,h1 b a c d e,h0 a b c d e]; grind only

private theorem minusSum {I : Type} (xs : List I) (v : I → C) : sumOver xs (fun i => -v i)= -sumOver xs v := by
  have e := sumOverMulLeft xs v (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm

private theorem waveSkew {n} (half : R) (c : Triple (Fin 7) → Word n → ComplexScalar R) (i j : Fin 7)
    (u : Four (Basis n)) :
    PhysicalUniformOccupation.wave half (extendEdges c j i) u= -PhysicalUniformOccupation.wave half (extendEdges c i j) u := by
  unfold PhysicalUniformOccupation.wave
  refine (sumOverCongr _ (fun p => ?_)).trans (minusSum _ _)
  rw [skew c i j p,Ring.neg_mul]

theorem sourceSkew {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    FiveShuffleCAR.BlockAlternating (physicalSource half A c) := by
  let Z := physicalSource half A c
  let Y := fun i j => anchored half A 0 (extendEdges c i j)
  have head (i j : Fin 7) (u : Triple (Basis n)) : Y j i u = -Y i j u := by
    unfold Y anchored; simp only [waveSkew half c i j,Ring.mul_neg,minusSum]
  have tail (i j : Fin 7) (a b d : Basis n) :
      Y i j ((b,a),d)= -Y i j ((a,b),d) ∧ Y i j ((a,d),b)= -Y i j ((a,b),d) := by
    let W := PhysicalUniformOccupation.wave half (extendEdges c i j)
    have e1 (t : Basis n) : W ((t,b),a,d)= -W ((t,a),b,d) := by
      exact FiveFrameContractions.waveReorder half (extendEdges c i j) ((t,a),b,d) ((0,2),(1,3)) (by decide)
    have e2 (t : Basis n) : W ((t,a),d,b)= -W ((t,a),b,d) := by
      exact FiveFrameContractions.waveReorder half (extendEdges c i j) ((t,a),b,d) ((0,1),(3,2)) (by decide)
    change (sumOver _ (fun t => star (A t 0)*W ((t,b),a,d))= -sumOver _ (fun t => star (A t 0)*W ((t,a),b,d))) ∧
      sumOver _ (fun t => star (A t 0)*W ((t,a),d,b))= -sumOver _ (fun t => star (A t 0)*W ((t,a),b,d))
    constructor
    · simp only [e1,Ring.mul_neg,minusSum]
    · simp only [e2,Ring.mul_neg,minusSum]
  have expand (a b d e f : Basis n) :
    Z ((a,b),(d,e),f) = sumOver modes (fun i => sumOver modes (fun j => (A a i*A b j)*Y i j ((d,e),f))) :=
    productSum modes modes (fun r => (A a r.1*A b r.2)*Y r.1 r.2 ((d,e),f))
  apply genAlternating Z
  · intro a b d e f; rw [expand,expand,sumOverSwap,←minusSum]; apply sumOverCongr; intro i
    rw [←minusSum]; apply sumOverCongr; intro j; rw [head i j]; grind only
  · intro a b d e f; rw [expand,expand,←minusSum]; apply sumOverCongr; intro i
    rw [←minusSum]; apply sumOverCongr; intro j; rw [(tail i j d e f).1,Ring.mul_neg]
  · intro a b d e f; rw [expand,expand,←minusSum]; apply sumOverCongr; intro i
    rw [←minusSum]; apply sumOverCongr; intro j; rw [(tail i j d e f).2,Ring.mul_neg]

section Norm
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

/-- Sharp physical two-link estimate on five free Schmidt modes. The factor
120=5! is the ratio between the ordered tensor and exterior squared norms;
the Pauli synthesis factor is 3/2. -/
theorem physicalTwoLinkBound {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (c : Triple (Fin 7) → Word n → ComplexScalar R) :
    sumOver (indices (qubitIndices n)) (fun u => normSq (merge (physicalSource half A c) u))≤
      1440*half^n * edgeMass c := by
  let Z := physicalSource half A c
  let xs := indices (qubitIndices n)
  let N := edgeMass c
  have car := FiveShuffleCAR.fiveShuffleCAR (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) Z (sourceSkew half A c)
  have z := zeroLayer half unit A orth c
  have one := firstLayer half A orth c
  have two := secondLayer half unit A orth c
  change sumOver xs (fun u => normSq (Z u))≤72*half^n*N at z
  change 0≤sumOver xs (fun u => (star (Z u)*Z (act firstSwap u)).re) at one
  change 2*sumOver xs (fun u => (star (Z u)*Z (act secondSwap u)).re)≤12*(4*half^n)*N at two
  change sumOver xs (fun u => normSq (merge Z u))≤1440*half^n*N
  rw [car]; grind only
end Norm

end RankSeven.PhysicalTwoLinkBound
#print axioms RankSeven.PhysicalTwoLinkBound.physicalTwoLinkBound
#print axioms RankSeven.PhysicalTwoLinkBound.secondLayer
