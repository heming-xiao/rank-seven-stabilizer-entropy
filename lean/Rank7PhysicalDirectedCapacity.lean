import Rank7FiveVolumeBessel
import Rank7PackingDual

/-! The physical directed packing row. -/
namespace RankSeven.PhysicalDirectedCapacity
open Lean.Grind Pauli ComplexScalar FiveShuffleCAR FiveVolumeBessel PhysicalTwoLinkBound
open PhysicalCutCapacities (Triple triples columnCoef rowMass)
open FiveFrameContractions (anchored source)
open GenericExteriorKernel (signed)
variable {R C α I : Type} [CommRing R] [CommRing C]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private def inverseShuffle (i : Fin 10) : Perm := [((0,1),(2,3),4),
  ((0,2),(1,3),4),
  ((0,2),(3,1),4),
  ((0,2),(3,4),1),
  ((2,0),(1,3),4),
  ((2,0),(3,1),4),
  ((2,0),(3,4),1),
  ((2,3),(0,1),4),
  ((2,3),(0,4),1),
  ((2,3),(4,0),1)].getD i.val ident
private theorem twoSided : ∀ i : Fin 10, act (shuffle i) (inverseShuffle i)=ident ∧ act (inverseShuffle i) (shuffle i)=ident := by decide
private theorem choiceCases (i : Fin 10) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by revert i; decide
private theorem productShuffle (A : α → I → ComplexScalar R) (v : Five I) (u : Five α) (s : Fin 10) :
    productColumn A (act (shuffle s) v) (act (shuffle s) u)=productColumn A v u := by
  rcases v with ⟨⟨i,j⟩,⟨k,l⟩,m⟩; rcases u with ⟨⟨a,b⟩,⟨c,d⟩,e⟩
  rcases choiceCases s with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change ((A a i*A b j)*(A c k*A d l))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A c k)*(A b j*A d l))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A d l)*(A b j*A c k))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A e m)*(A b j*A c k))*A d l=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A b j*A c k)*(A a i*A d l))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A b j*A d l)*(A a i*A c k))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A b j*A e m)*(A a i*A c k))*A d l=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A c k*A d l)*(A a i*A b j))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A c k*A e m)*(A a i*A b j))*A d l=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A d l*A e m)*(A a i*A b j))*A c k=((A a i*A b j)*(A c k*A d l))*A e m; grind only

private theorem shuffleMove [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀a,a∈xs)
    (A : α → I → ComplexScalar R) (v : Five I) (Z : Five α → ComplexScalar R) (s : Fin 10) :
    sumOver (indices xs) (fun u => star (productColumn A v u)*Z (act (shuffle s) u)) =
      sumOver (indices xs) (fun u => star (productColumn A (act (shuffle s) v) u)*Z u) := by
  rw [←changeVariables xs nd full (inverseShuffle s) (shuffle s) (twoSided s).1 (twoSided s).2
    (fun u => star (productColumn A v u)*Z (act (shuffle s) u))]
  apply sumOverCongr; intro u
  have h := productShuffle A v (act (inverseShuffle s) u) s
  rw [actCompose,(twoSided s).1,actIdent] at h ⊢; rw [h]

private theorem signSum {B : Type} (xs : List B) (b : Bool) (F : B → C) :
    sumOver xs (fun i => signed b (F i))=signed b (sumOver xs F) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true]
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem mulSign (b : Bool) (z w : C) : z*signed b w=signed b (z*w) := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true,Ring.mul_neg]

private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def physicalLabels (i : Fin 10) := act (shuffle i) orderedModes
def frameTriple (i : Fin 10) := edgeTriple (physicalLabels i).1
def complement (i : Fin 10) : Four (Fin 7) := ((0,(physicalLabels i).2.1.1),(physicalLabels i).2.1.2,(physicalLabels i).2.2)
def select (u : Triple (Fin 7)) := (choices.find? (fun i => decide (frameTriple i=u))).getD 0
def witness {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (u : Triple (Fin 7)) (p : Word n) :=
  signed (odd (shuffle (select u))) (star (columnCoef half A (complement (select u)) p))

private theorem labelFacts : ∀ i : Fin 10, (physicalLabels i).1.1∈modes ∧ (physicalLabels i).1.2∈modes ∧
    (physicalLabels i).1.1<(physicalLabels i).1.2 ∧ select (frameTriple i)=i := by decide
private theorem enumerates : frameTriples=choices.map frameTriple := by decide

def tailProduct (A : α → Fin 7 → ComplexScalar R) (v : Triple (Fin 7)) (u : Triple α) :=
  A u.1.1 v.1.1*A u.1.2 v.1.2*A u.2 v.2
private theorem evalPair (xs : List α) (A : α → Fin 7 → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (v : Five (Fin 7)) (i j : Fin 7) (Y : Triple α → ComplexScalar R) :
    sumOver (indices xs) (fun u => star (productColumn A v u)*FiveFrameContractions.slotPair A i j Y u) =
      (if v.1.1=i then (1:ComplexScalar R) else 0)*((if v.1.2=j then 1 else 0)*
        sumOver (triples xs) (fun t => star (tailProduct A v.2 t)*Y t)) := by
  let f (a : α) := star (A a v.1.1)*A a i
  let g (b : α) := star (A b v.1.2)*A b j
  let h (t : Triple α) := star (tailProduct A v.2 t)*Y t
  have value := factorProductSum (productIndices xs xs) (triples xs) (fun ab => f ab.1*g ab.2) h
  rw [factorProductSum] at value
  have eq := sumOverCongr (indices xs) (g:=fun u => (f u.1.1*g u.1.2)*h u.2)
    (fun u => show star (productColumn A v u)*FiveFrameContractions.slotPair A i j Y u=(f u.1.1*g u.1.2)*h u.2 by
      unfold productColumn FiveFrameContractions.slotPair f g h tailProduct; simp only [star_mul]; grind only)
  refine eq.trans (value.trans ?_)
  unfold f g h; rw [orth,orth]; grind only

private theorem collapse {B : Type} [DecidableEq B] (xs : List B) (nd : xs.Nodup) (i : B) (hi : i∈xs) (F : B → ComplexScalar R) :
    sumOver xs (fun j => (if i=j then 1 else 0)*F j)=F i := by
  refine (sumOverCongr xs (g:=fun j => if i=j then F j else 0) (fun j => ?_)).trans
    (ExteriorPauliBase.sumOnIndex xs i F nd hi)
  by_cases h : i=j <;> simp [h,Semiring.one_mul,Semiring.zero_mul]

private theorem productSource (xs : List α) (A : α → Fin 7 → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (v : Five (Fin 7)) (h1 : v.1.1∈modes) (h2 : v.1.2∈modes) (Y : Fin 7 → Fin 7 → Triple α → ComplexScalar R) :
    sumOver (indices xs) (fun u => star (productColumn A v u)*source modes A Y u)=
      sumOver (triples xs) (fun t => star (tailProduct A v.2 t)*Y v.1.1 v.1.2 t) := by
  unfold source; simp only [sumOverMulLeft]; rw [sumOverSwap]; simp only [evalPair xs A orth]
  rw [productSum]
  let H (i j : Fin 7) := sumOver (triples xs) (fun t => star (tailProduct A v.2 t)*Y i j t)
  have h (i) := collapse modes (by decide) v.1.2 h2 (H i)
  have k := collapse modes (by decide) v.1.1 h1 (fun i => H i v.1.2)
  change sumOver modes (fun i => sumOver modes (fun j => (if v.1.1=i then 1 else 0)*((if v.1.2=j then 1 else 0)*H i j)))=_
  have move (i : Fin 7) := (sumOverMulLeft modes (fun j => (if v.1.2=j then 1 else 0)*H i j)
    (if v.1.1=i then (1:ComplexScalar R) else 0)).symm
  rw [sumOverCongr modes move]; simp only [h]; exact k

private theorem tailEval {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (v : Triple (Fin 7)) (c : Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun t => star (tailProduct A v t)*anchored half A 0 c t) =
      sumOver (MixedDefect.oddWords n) (fun p => c p*columnCoef half A ((0,v.1.1),v.1.2,v.2) p) := by
  let xs := qubitIndices n
  let os := MixedDefect.oddWords n
  change sumOver (triples xs) (fun t => star (tailProduct A v t)*sumOver xs (fun a => star (A a 0)*
    sumOver os (fun p => c p*WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,t.1.1),t.1.2,t.2)))) =
    sumOver os (fun p => c p*sumOver (fourIndices xs) (fun t => star (tensorFour A t ((0,v.1.1),v.1.2,v.2))*
      WedgeSquareIntertwiner.wedgeSquareColumn half p t))
  unfold triples fourIndices; simp only [productSum,sumOverMulLeft]
  conv => lhs; arg 2; intro b; arg 2; intro c; arg 2; intro d; rw [sumOverSwap]
  conv => lhs; arg 2; intro b; arg 2; intro c; rw [sumOverSwap]
  conv => lhs; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  conv => lhs; arg 2; intro p; arg 2; intro b; arg 2; intro c; rw [sumOverSwap]
  conv => lhs; arg 2; intro p; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro p; rw [sumOverSwap]
  apply sumOverCongr; intro p; apply sumOverCongr; intro e; apply sumOverCongr; intro b; apply sumOverCongr; intro c; apply sumOverCongr; intro d
  unfold tailProduct tensorFour tensor; simp only [star_mul]; grind only

private theorem signNorm (b : Bool) (z : ComplexScalar R) : normSq (signed b (star z))=normSq z := by
  cases b <;> simp only [signed,Bool.false_eq_true,ite_true,ite_false,normSq_star]
  simp [normSq]; grind only

private theorem toRealSum {B : Type} (xs : List B) (f : B → R) :
    sumOver xs (fun i => ofReal (f i))=ofReal (sumOver xs f) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ofReal (f i)+sumOver xs _=ofReal (f i+sumOver xs f); rw [ih]; apply ComplexScalar.ext <;> simp <;> grind only

def targetMass {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :=
  sumOver choices (fun i => rowMass half A (complement i))

theorem witnessNorm {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :
    edgeMass (witness half A)=targetMass half A := by
  unfold edgeMass targetMass; rw [sumOverSwap,enumerates]
  simp only [sumOver,List.map_map,Function.comp_def]; apply congrArg List.sum; apply List.map_congr_left
  intro i _; unfold rowMass witness; rw [(labelFacts i).2.2.2]
  exact sumOverCongr (MixedDefect.oddWords n) (fun p => signNorm _ _)

theorem witnessAmplitude {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    productAmplitude (qubitIndices n) A orderedModes (physicalSource half A (witness half A))=ofReal (targetMass half A) := by
  let xs := qubitIndices n
  let Z := physicalSource half A (witness half A)
  unfold productAmplitude merge
  simp only [sumOverMulLeft,mulSign]; rw [sumOverSwap]; simp only [signSum]
  unfold targetMass; rw [←toRealSum]; apply sumOverCongr; intro i
  rw [shuffleMove (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)]
  let v := physicalLabels i
  change signed (odd (shuffle i)) (sumOver (indices xs) (fun u => star (productColumn A v u)*
    source modes A (fun a b => anchored half A 0 (extendEdges (witness half A) a b)) u))=_
  rw [productSource xs A orth v (labelFacts i).1 (labelFacts i).2.1,tailEval]
  have coeff (p : Word n) : extendEdges (witness half A) v.1.1 v.1.2 p=
      signed (odd (shuffle i)) (star (columnCoef half A (complement i) p)) := by
    unfold extendEdges; rw [ite_eq_left (labelFacts i).2.2.1]
    change signed (odd (shuffle (select (frameTriple i)))) (star (columnCoef half A (complement (select (frameTriple i))) p))=_
    rw [(labelFacts i).2.2.2]
  let f (p : Word n) := columnCoef half A (complement i) p
  change signed (odd (shuffle i)) (sumOver (MixedDefect.oddWords n) (fun p => extendEdges (witness half A) v.1.1 v.1.2 p*f p))=
    ofReal (sumOver (MixedDefect.oddWords n) (fun p => normSq (f p)))
  have row (p : Word n) :
      extendEdges (witness half A) v.1.1 v.1.2 p*f p = signed (odd (shuffle i)) (ofReal (normSq (f p))) := by
    rw [coeff,←star_mul_self]; change signed _ (star (f p))*f p=signed _ _
    cases odd (shuffle i) <;> simp only [signed,Bool.false_eq_true,ite_true,ite_false,Ring.neg_mul]
  rw [sumOverCongr _ row,signSum,toRealSum]; cases odd (shuffle i) <;> simp only [signed,Bool.false_eq_true,ite_true,ite_false] <;> grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Directed five-point link bound in odd Pauli-frame units. -/
theorem directedPauliMass {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) : targetMass half A≤12*half^n := by
  let c := witness half A
  let Z := physicalSource half A c
  let N := targetMass half A
  let xs := qubitIndices n
  have b := FiveVolumeBessel.volumeBessel xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) A orth Z
    (PhysicalTwoLinkBound.sourceSkew half A c)
  have upper := PhysicalTwoLinkBound.physicalTwoLinkBound half unit A orth c
  have mass := witnessNorm half A
  have amplitude := witnessAmplitude half A orth
  change productAmplitude xs A orderedModes Z=ofReal N at amplitude
  rw [amplitude,normSq_ofReal] at b; change edgeMass c=N at mass
  rw [mass] at upper
  have both := Std.le_trans b upper
  have hnon (m : Nat) : 0≤half^m := by
    induction m with
    | zero => simp only [Semiring.pow_zero]; grind only
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  by_cases h : N≤12*half^n
  · exact h
  · have positive : 0<N := by have hn := hnon n; grind only
    have strict := OrderedRing.mul_pos (show 0<N-12*half^n by grind only) positive
    grind only

def relabel (ignored fixed : Fin 7) (i : Fin 7) : Fin 7 :=
  ([fixed]++(List.finRange 7).filter (fun j => j != ignored && j != fixed)++[ignored]).getD i.val 0
private def unsorted (ignored fixed : Fin 7) (i : Fin 10) :=
  PhysicalWedges.mapFourSites (relabel ignored fixed) (complement i)
private def sortPerm (u : Four (Fin 7)) : ExteriorPauliBase.Permutation :=
  if u.1.1<u.1.2 then ((0,1),(2,3))
  else if u.1.1<u.2.1 then ((1,0),(2,3))
  else if u.1.1<u.2.2 then ((1,2),(0,3))
  else ((1,2),(3,0))
private theorem sortPermLegal (u : Four (Fin 7)) : sortPerm u∈ExteriorPauliBase.permutations := by
  unfold sortPerm; split
  · decide
  · split
    · decide
    · split <;> decide
private def sortedTuple (ignored fixed : Fin 7) (i : Fin 10) :=
  let u := unsorted ignored fixed i
  GenericExteriorKernel.reorder u (sortPerm u)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 4000000 in
private theorem enumeration : ∀ i j : Fin 7, i≠j →
    (choices.map (sortedTuple i j)).Perm ((ExteriorCuts.wedges.filter (PackingDual.Row.directed i j).covers).map FrameExteriorSector.sourceTuple) := by decide

set_option maxRecDepth 20000 in
private theorem relabelInjective : ∀ i j : Fin 7, i≠j → ∀ a b : Fin 7, relabel i j a=relabel i j b → a=b := by decide

private theorem sumPerm {B : Type} {xs ys : List B} (h : xs.Perm ys) (f : B → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2

private theorem filterSum {B : Type} (xs : List B) (keep : B → Bool) (f : B → C) :
    sumOver (xs.filter keep) f=sumOver xs (fun i => if keep i then f i else 0) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.filter_cons]; cases h : keep i
    · change sumOver (xs.filter keep) f = (if keep i then f i else 0)+_; rw [h,ih]; simp only [Bool.false_eq_true,ite_false,AddCommMonoid.zero_add]; rfl
    · change f i+sumOver (xs.filter keep) f=(if keep i then f i else 0)+_; rw [h,ih]; rfl

/-- Every legal directed rank-seven packing row for the actual normalized physical
wedge effect. The proof uses all ten choices of three out of five tail sites. -/
theorem physicalDirectedCapacity (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (ignored fixed : Fin 7) (ne : ignored≠fixed) :
    PackingDual.rowMass (fun w => (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w)
      (.directed ignored fixed)≤2 := by
  let p := relabel ignored fixed
  let B := fun t i => A t (p i)
  have orthB : PhysicalCompressionEffect.OrthonormalFrame B := by
    intro i j; change sumOver _ (fun t => star (A t (p i))*A t (p j))=_
    rw [orth]; by_cases eq : i=j
    · simp [eq]
    · have pe : p i≠p j := fun z => eq (relabelInjective ignored fixed ne i j z)
      simp [eq,pe]
  let f := fun w => (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w
  let ws := ExteriorCuts.wedges.filter (PackingDual.Row.directed ignored fixed).covers
  let q := 4*half^(k+3)
  let M := fun v => 2*rowMass half A v
  have eqS (i : Fin 10) : M (sortedTuple ignored fixed i)=2*rowMass half B (complement i) := by
    exact PhysicalCutCapacities.massReorder half unit A (unsorted ignored fixed i) _ (sortPermLegal _)
  have eqW (w : ExteriorCuts.Wedge7) : M (FrameExteriorSector.sourceTuple w)=(3*q)*f w :=
    PhysicalCutCapacities.coordinateMass half unit k A w
  have eq := sumPerm (enumeration ignored fixed ne) M
  have mapS {U V : Type} (xs : List U) (F : V → R) (map : U → V) :
      sumOver (xs.map map) F=sumOver xs (fun i => F (map i)) := by simp [sumOver,List.map_map,Function.comp_def]
  change sumOver (choices.map (sortedTuple ignored fixed)) M=sumOver (ws.map FrameExteriorSector.sourceTuple) M at eq
  rw [mapS,mapS,sumOverCongr choices eqS,sumOverCongr ws eqW,←sumOverMulLeft,←sumOverMulLeft] at eq
  change 2*targetMass half B=(3*q)*sumOver ws f at eq
  have cap := directedPauliMass half unit B orthB
  have hpos (m : Nat) : 0<half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)
  have pos : 0<3*q := OrderedRing.mul_pos (by grind only) (OrderedRing.mul_pos (by grind only) (hpos _))
  change sumOver ExteriorCuts.wedges (fun w => if (PackingDual.Row.directed ignored fixed).covers w then f w else 0)≤2
  rw [←filterSum]; change sumOver ws f≤2
  by_cases h : sumOver ws f≤2
  · exact h
  · have bad := OrderedRing.mul_pos pos (show 0<sumOver ws f-2 by grind only)
    change 2*targetMass half B=(3*(4*half^(k+3)))*sumOver ws f at eq
    change 0<(3*(4*half^(k+3)))*(sumOver ws f-2) at bad
    grind only

end Order

end RankSeven.PhysicalDirectedCapacity
#print axioms RankSeven.PhysicalDirectedCapacity.directedPauliMass
#print axioms RankSeven.PhysicalDirectedCapacity.physicalDirectedCapacity
