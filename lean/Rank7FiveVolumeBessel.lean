import Rank7PhysicalTwoLinkBound

/-! Bessel extraction at the unit volume of five orthonormal modes.
The 120 ordered products of the same five columns are orthonormal. -/
namespace RankSeven.FiveVolumeBessel
open Lean.Grind Pauli ComplexScalar FiveShuffleCAR
variable {R C α I : Type} [CommRing R] [CommRing C]
attribute [local instance] Ring.intCast

def adjacent (g : Fin 4) : Perm := [((1,0),(2,3),4),((0,2),(1,3),4),((0,1),(3,2),4),((0,1),(2,4),3)].getD g.val ident
private def inverseAt (p : Perm) (k : Fin 5) : Fin 5 :=
  if p.1.1=k then 0 else if p.1.2=k then 1 else if p.2.1.1=k then 2 else if p.2.1.2=k then 3 else 4
private def inverse (p : Perm) : Perm := ((inverseAt p 0,inverseAt p 1),(inverseAt p 2,inverseAt p 3),inverseAt p 4)
private def choiceChange (g : Fin 4) (i : Fin 10) : Fin 10 :=
  let changes : List (List (Fin 10)) := [[0,4,5,6,1,2,3,7,8,9],
    [1,0,2,3,4,7,8,5,6,9],
    [0,2,1,3,5,4,6,7,9,8],
    [0,1,3,2,4,6,5,8,7,9]]
  ((changes.getD g.val []).getD i.val 0)
private def innerBlock (g : Fin 4) (i : Fin 10) := act (act (shuffle i) (adjacent g)) (inverse (shuffle (choiceChange g i)))
private theorem signs : ∀ g : Fin 4, act (adjacent g) (adjacent g)=ident ∧ (choices.map (choiceChange g)).Perm choices := by decide
set_option synthInstance.maxSize 200 in
set_option maxRecDepth 40000 in
private theorem rowTable : ∀ g : Fin 4, ∀ i : Fin 10, innerBlock g i∈blocks ∧
    act (shuffle i) (adjacent g)=act (innerBlock g i) (shuffle (choiceChange g i)) ∧
    (odd (shuffle i) ^^ odd (innerBlock g i))= !odd (shuffle (choiceChange g i)) := by decide

private theorem sumPerm {A : Type} {xs ys : List A} (h : xs.Perm ys) (f : A → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2
private theorem minusSum {A : Type} (xs : List A) (F : A → C) : sumOver xs (fun i => -F i)= -sumOver xs F := by
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem signJoin (a b c : Bool) (h : (a^^b)= !c) (z : C) :
    GenericExteriorKernel.signed a (GenericExteriorKernel.signed b z)= -GenericExteriorKernel.signed c z := by
  cases a <;> cases b <;> cases c <;> simp_all [GenericExteriorKernel.signed] <;> grind only

theorem mergeAdjacent (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) (g : Fin 4) (u : Five α) :
    merge Z (act (adjacent g) u)= -merge Z u := by
  let term (i : Fin 10) := GenericExteriorKernel.signed (odd (shuffle i)) (Z (act (shuffle i) u))
  have row (i : Fin 10) : GenericExteriorKernel.signed (odd (shuffle i)) (Z (act (shuffle i) (act (adjacent g) u)))= -term (choiceChange g i) := by
    obtain ⟨hin,hc,hs⟩ := rowTable g i
    rw [actCompose,hc,←actCompose,hz _ hin]; exact signJoin _ _ _ hs _
  unfold merge; rw [sumOverCongr _ row,minusSum]; apply congrArg Neg.neg
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (signs g).2 term

/-- Radix 2,3,4,5 insertion of successive largest symbols; the selected
adjacent transpositions produce each permutation exactly once. -/
def steps (k : Fin 120) : List (Fin 4) :=
  let stage (last count : Nat) := (List.range count).map (fun j => Fin.ofNat 4 (last-j))
  stage 0 (k.val%2) ++ stage 1 ((k.val/2)%3) ++ stage 2 ((k.val/6)%4) ++ stage 3 ((k.val/24)%5)
def applySteps {α : Type} (w : List (Fin 4)) (u : Five α) := w.foldl (fun v g => act (adjacent g) v) u
def orderedModes : Five (Fin 7) := ((1,2),(3,4),5)
def labels (k : Fin 120) := applySteps (steps k) orderedModes
set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem labelsNodup : ((List.finRange 120).map labels).Nodup := by decide

private theorem labelInjective (k l : Fin 120) (h : labels k=labels l) : k=l := by
  have inject (xs : List (Fin 120)) (nd : (xs.map labels).Nodup) (hk : k∈xs) (hl : l∈xs) : k=l := by
    induction xs with
    | nil => simp at hk
    | cons a xs ih =>
      obtain ⟨absent,tail⟩ := List.nodup_cons.mp nd
      rcases List.mem_cons.mp hk with ka|kt <;> rcases List.mem_cons.mp hl with la|lt
      · exact ka.trans la.symm
      · exact False.elim (absent (List.mem_map.mpr ⟨l,lt,h.symm.trans (congrArg labels ka)⟩))
      · exact False.elim (absent (List.mem_map.mpr ⟨k,kt,h.trans (congrArg labels la)⟩))
      · exact ih tail kt lt
  exact inject _ labelsNodup (List.mem_finRange k) (List.mem_finRange l)

def productColumn (A : α → I → ComplexScalar R) (v : Five I) (u : Five α) :=
  ((A u.1.1 v.1.1*A u.1.2 v.1.2)*(A u.2.1.1 v.2.1.1*A u.2.1.2 v.2.1.2))*A u.2.2 v.2.2
private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem productGram [DecidableEq I] (xs : List α) (A : α → I → ComplexScalar R)
    (orth : ∀ i j, sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (u v : Five I) :
    sumOver (indices xs) (fun t => star (productColumn A u t)*productColumn A v t)=if u=v then 1 else 0 := by
  let h (i j : I) (a : α) := star (A a i)*A a j
  let es := productIndices xs xs
  let f (a : α × α) := h u.1.1 v.1.1 a.1*h u.1.2 v.1.2 a.2
  let g (a : α × α) := h u.2.1.1 v.2.1.1 a.1*h u.2.1.2 v.2.1.2 a.2
  let last := h u.2.2 v.2.2
  have eqGram := factorProductSum es (productIndices es xs) f (fun y => g y.1*last y.2)
  rw [factorProductSum,factorProductSum,factorProductSum] at eqGram
  refine (sumOverCongr (indices xs) (g:=fun a => f a.1*(g a.2.1*last a.2.2)) (fun a => ?_)).trans (eqGram.trans ?_)
  · unfold productColumn f g last h; simp only [star_mul]; grind only
  · unfold last h; simp only [orth]
    rcases u with ⟨⟨a,b⟩,⟨c,d⟩,e⟩; rcases v with ⟨⟨i,j⟩,⟨k,l⟩,m⟩
    by_cases a0 : a=i <;> by_cases b0 : b=j <;> by_cases c0 : c=k <;> by_cases d0 : d=l <;> by_cases e0 : e=m <;>
      simp [a0,b0,c0,d0,e0] <;> grind only

private theorem productAdjacent (A : α → I → ComplexScalar R) (v : Five I) (u : Five α) (g : Fin 4) :
    productColumn A (act (adjacent g) v) (act (adjacent g) u)=productColumn A v u := by
  have gg : g=0 ∨ g=1 ∨ g=2 ∨ g=3 := by revert g; decide
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩,e⟩; rcases v with ⟨⟨i,j⟩,⟨k,l⟩,m⟩
  rcases gg with rfl|rfl|rfl|rfl
  · change ((A b j*A a i)*(A c k*A d l))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A c k)*(A b j*A d l))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A b j)*(A d l*A c k))*A e m=((A a i*A b j)*(A c k*A d l))*A e m; grind only
  · change ((A a i*A b j)*(A c k*A e m))*A d l=((A a i*A b j)*(A c k*A d l))*A e m; grind only

def productAmplitude (xs : List α) (A : α → I → ComplexScalar R) (v : Five I) (Z : Five α → ComplexScalar R) :=
  sumOver (indices xs) (fun u => star (productColumn A v u)*merge Z u)

theorem amplitudeAdjacent [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ a,a∈xs)
    (A : α → I → ComplexScalar R) (v : Five I) (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) (g : Fin 4) :
    productAmplitude xs A (act (adjacent g) v) Z= -productAmplitude xs A v Z := by
  unfold productAmplitude
  rw [←changeVariables xs nd full _ _ (signs g).1 (signs g).1 (fun u => star (productColumn A (act (adjacent g) v) u)*merge Z u)]
  simp only [productAdjacent,mergeAdjacent Z hz,Ring.mul_neg,minusSum]

private theorem amplitudeNorm [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ a,a∈xs)
    (A : α → I → ComplexScalar R) (v : Five I) (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) (w : List (Fin 4)) :
    normSq (productAmplitude xs A (applySteps w v) Z)=normSq (productAmplitude xs A v Z) := by
  induction w generalizing v with
  | nil => rfl
  | cons g w ih =>
    change normSq (productAmplitude xs A (applySteps w (act (adjacent g) v)) Z)=_
    rw [ih,amplitudeAdjacent xs nd full A v Z hz g]; simp [normSq]; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

set_option maxRecDepth 20000 in
/-- All 120 orthogonal product columns carry the same squared amplitude
on the merged exterior tensor, yielding the exact five-volume Bessel factor. -/
theorem volumeBessel [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ a,a∈xs)
    (A : α → Fin 7 → ComplexScalar R)
    (orth : ∀ i j,sumOver xs (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (Z : Five α → ComplexScalar R) (hz : BlockAlternating Z) :
    120*normSq (productAmplitude xs A orderedModes Z)≤sumOver (indices xs) (fun u => normSq (merge Z u)) := by
  let ks := List.finRange 120
  have gram (i j : Fin 120) :
      sumOver (indices xs) (fun u => star (productColumn A (labels i) u)*productColumn A (labels j) u)=if i=j then 1 else 0 := by
    rw [productGram xs A orth]
    by_cases h : i=j
    · simp [h]
    · have ne : labels i≠labels j := fun e => h (labelInjective i j e)
      simp [h,ne]
  have b := PhysicalCutCapacities.frameBessel ks (indices xs) (List.nodup_finRange 120) List.mem_finRange
    (fun u i => productColumn A (labels i) u) gram (merge Z)
  change sumOver ks (fun i => normSq (productAmplitude xs A (labels i) Z))≤_ at b
  have h (i : Fin 120) : normSq (productAmplitude xs A (labels i) Z)=normSq (productAmplitude xs A orderedModes Z) :=
    amplitudeNorm xs nd full A orderedModes Z hz (steps i)
  rw [sumOverCongr ks h] at b
  have many (z : R) : sumOver ks (fun _ => z)=120*z := by
    have sumInt {B : Type} (is : List B) (f : B → Int) :
        Int.cast (R:=R) (sumOver is f)=sumOver is (fun i => Int.cast (R:=R) (f i)) := by
      induction is with
      | nil => exact Ring.intCast_zero
      | cons i is ih => change Int.cast (f i+sumOver is f)=_; rw [Ring.intCast_add,ih]; rfl
    have e : sumOver ks (fun _ => (1:Int))=120 := by decide
    have hc := congrArg (Int.cast (R:=R)) e
    rw [sumInt] at hc
    simp only [Ring.intCast_one,show Int.cast (R:=R) (120:Int)=(120:R) from Ring.intCast_ofNat 120] at hc
    rw [←hc,sumOverMulRight]; apply sumOverCongr; intro i; rw [Semiring.one_mul]
  rw [many] at b; exact b
end Order
end RankSeven.FiveVolumeBessel
#print axioms RankSeven.FiveVolumeBessel.volumeBessel
