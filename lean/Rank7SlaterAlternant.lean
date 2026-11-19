import Rank7OddTensorUncertainty

/-! The top alternating source tensor and the action of a one-particle
map on all its legs. No determinant normalization or division is used. -/
namespace RankSeven.SlaterAlternant
open Lean.Grind Pauli ComplexScalar OddTensorUncertainty
variable {C α β γ : Type} [CommRing C]

def Alternating (F : List α → C) : Prop :=
  ∀ (pre : List α) (a b : α) (post : List α), F (pre++a::b::post)= -F (pre++b::a::post)

theorem prefixAlt (F : List α → C) (alt : Alternating F) (a : α) :
    Alternating (fun xs => F (a::xs)) := fun pre u v post => alt (a::pre) u v post

theorem permZero (F : List α → C) (alt : Alternating F) {xs ys : List α} (p : xs.Perm ys) :
    ∀ pre : List α, F (pre++xs)=0 → F (pre++ys)=0 := by
  induction p with
  | nil => exact fun _ h => h
  | cons a p ih =>
    intro pre z
    have w := ih (pre++[a])
    simpa only [List.append_assoc,List.singleton_append] using w (by simpa only [List.append_assoc,List.singleton_append] using z)
  | swap a b xs =>
    intro pre z; have e := alt pre a b xs; rw [z] at e; grind only
  | trans p q ih ih' => exact fun pre z => ih' pre (ih pre z)

private theorem fill {xs ys : List α} [DecidableEq α] (nd : xs.Nodup) (length : xs.length=ys.length)
    (subset : xs⊆ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have z : ys=[] := List.length_eq_zero_iff.mp length.symm
    rw [z]
  | cons a xs ih =>
    have h := List.nodup_cons.mp nd
    have ays := subset (a:=a) List.mem_cons_self
    have p := List.perm_cons_erase ays
    have l := p.length_eq
    have sub : xs ⊆ ys.erase a := by
      intro b hb
      have raw := p.mem_iff.mp (subset (List.mem_cons_of_mem a hb))
      cases List.mem_cons.mp raw with
      | inl eq => exact False.elim (h.1 (eq ▸ hb))
      | inr yes => exact yes
    exact (List.Perm.cons a (ih h.2 (by simp only [List.length_cons] at l length; omega) sub)).trans p.symm

private theorem repeatedZero {F : List α → C} [DecidableEq α] (alt : Alternating F) (cancel : ∀ z : C,z= -z → z=0)
    (xs : List α) (repeated : ¬xs.Nodup) : ∀ pre, F (pre++xs)=0 := by
  induction xs with
  | nil => exact False.elim (repeated List.nodup_nil)
  | cons a xs ih =>
    intro pre
    by_cases h : a∈xs
    · have p := List.Perm.cons a (List.perm_cons_erase h)
      have e := alt pre a a (xs.erase a)
      exact permZero F alt p.symm pre (cancel _ e)
    · have j := ih (fun nd => repeated (List.nodup_cons.mpr ⟨h,nd⟩)) (pre++[a])
      simpa only [List.append_assoc,List.singleton_append] using j

/-- Every alternating tensor of top degree on a finite source is on the
same line. The cross-multiplied identity works over rings. -/
theorem topLine [DecidableEq α] (labels xs : List α) (length : xs.length=labels.length) (sub : xs⊆labels)
    (F G : List α → C) (f : Alternating F) (g : Alternating G) (cancel : ∀ z : C,z= -z → z=0) :
    F xs*G labels=G xs*F labels := by
  let H ys := F ys*G labels-G ys*F labels
  have alt : Alternating H := by
    intro pre a b post
    have u := f pre a b post; have v := g pre a b post; dsimp only [H]; rw [u,v]; grind only
  have zero : H xs=0 := by
    by_cases nd : xs.Nodup
    · have perm := fill nd length sub
      exact permZero H alt perm.symm [] (show H labels=0 by unfold H; grind only)
    · exact repeatedZero alt cancel xs nd []
  dsimp only [H] at zero; grind only

def tupleList {α : Type} : (m : Nat) → Sites α m → List α
  | 0,_ => []
  | m+1,x => x.1::tupleList m x.2

theorem tupleLength (m : Nat) (x : Sites α m) : (tupleList m x).length=m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg Nat.succ (ih x.2)

def tupleOfList {α : Type} : (xs : List α) → Sites α xs.length
  | [] => ()
  | a::xs => (a,tupleOfList xs)

theorem tupleOfList_spec (xs : List α) : tupleList xs.length (tupleOfList xs)=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (List.cons a) ih

def push (inputs : List β) (A : α → β → C) (F : List β → C) : List α → C
  | [] => F []
  | a::xs => sumOver inputs (fun b => A a b*push inputs A (fun ys => F (b::ys)) xs)

theorem pushCongr (inputs : List β) (A : α → β → C) (F G : List β → C)
    (q : ∀ y,F y=G y) (xs : List α) : push inputs A F xs=push inputs A G xs := by
  have e := funext q; rw [e]

theorem pushNeg (inputs : List β) (A : α → β → C) (F : List β → C) (xs : List α) :
    push inputs A (fun y => -F y) xs= -push inputs A F xs := by
  induction xs generalizing F with
  | nil => rfl
  | cons a xs ih =>
    simp only [push,ih,Ring.mul_neg]
    have s := sumOverMulLeft inputs (fun b => A a b*push inputs A (fun ys => F (b::ys)) xs) (-1)
    simpa only [Ring.neg_mul,Semiring.one_mul] using s.symm

theorem pushAlt (inputs : List β) (A : α → β → C) (F : List β → C) (alt : Alternating F) :
    Alternating (push inputs A F) := by
  intro pre
  induction pre generalizing F with
  | nil =>
    intro a b post
    simp only [List.nil_append,push,sumOverMulLeft]
    rw [sumOverSwap inputs inputs (fun u v => A b u*(A a v*push inputs A (fun ys => F (u::v::ys)) post))]
    have entry' (u v : β) : push inputs A (fun ys => F (u::v::ys)) post= -push inputs A (fun ys => F (v::u::ys)) post := by
      rw [←pushNeg]; apply pushCongr; exact fun ys => alt [] u v ys
    have neg (f : β → C) : -sumOver inputs f=sumOver inputs (fun w => -f w) := by
      have s := sumOverMulLeft inputs f (-1); simpa only [Ring.neg_mul,Semiring.one_mul] using s
    rw [neg]; apply sumOverCongr; intro u; rw [neg]; apply sumOverCongr; intro v
    rw [entry' u v]; grind only
  | cons k pre ih =>
    intro a b post
    simp only [List.cons_append,push]
    have e (u : β) := ih (fun ys => F (u::ys)) (prefixAlt F alt u) a b post
    have neg := sumOverMulLeft inputs (fun u => A k u*push inputs A (fun ys => F (u::ys)) (pre++b::a::post)) (-1)
    simp only [Ring.neg_mul,Semiring.one_mul] at neg; rw [neg]
    apply sumOverCongr; intro u; rw [e u]; grind only

theorem pushIsMatrix (inputs : List β) (A : α → β → C) (F : List β → C) (r : Nat) (x : Sites α r) :
    push inputs A F (tupleList r x)=sumOver (indices inputs r) (fun y => matrix A r x y*F (tupleList r y)) := by
  induction r generalizing F with
  | zero => change F []=1*F []+0; grind only
  | succ r ih =>
    change sumOver inputs (fun b => A x.1 b*push inputs A (fun ys => F (b::ys)) (tupleList r x.2))=_
    change _=sumOver (productIndices inputs (indices inputs r)) (fun y : β×Sites β r => (A x.1 y.1*matrix A r x.2 y.2)*F (y.1::tupleList r y.2))
    unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro u
    rw [ih,sumOverMulLeft]; simp only [sumOver,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left; intro y _
    change A x.1 u*(matrix A r x.2 y*F (u::tupleList r y))=(A x.1 u*matrix A r x.2 y)*F (u::tupleList r y)
    grind only

private def pairSign (a b : Fin m) : C := if a<b then 1 else if b<a then -1 else 0

private theorem signSwap (a b : Fin m) : pairSign (C:=C) a b= -pairSign b a := by
  unfold pairSign
  by_cases h : a<b <;> by_cases z : b<a <;> simp [h,z] <;> first | omega | grind only

private def signRow (a : Fin m) : List (Fin m) → C
  | [] => 1
  | b::xs => pairSign a b*signRow a xs

def orientation {C : Type} [CommRing C] {m : Nat} : List (Fin m) → C
  | [] => 1
  | a::xs => signRow a xs*orientation xs

private theorem rowSwap (h : Fin m) (pre : List (Fin m)) (a b : Fin m) (post : List (Fin m)) :
    signRow (C:=C) h (pre++a::b::post)=signRow h (pre++b::a::post) := by
  induction pre with
  | nil => simp only [List.nil_append,signRow]; grind only
  | cons y pre ih => simp only [List.cons_append,signRow,ih]

theorem orientationAlt (m : Nat) : Alternating (orientation (C:=C) (m:=m)) := by
  intro pre a b post
  induction pre with
  | nil =>
    simp only [List.nil_append,orientation,signRow]
    rw [signSwap a b]; grind only
  | cons h pre ih =>
    simp only [List.cons_append,orientation]
    rw [rowSwap,ih]; grind only

theorem orientationIncreasing (xs : List (Fin m)) (sorted : xs.Pairwise (·<·)) : orientation (C:=C) xs=1 := by
  have row (a : Fin m) (ys : List (Fin m)) (w : ∀ b∈ys,a<b) : signRow (C:=C) a ys=1 := by
    induction ys with
    | nil => rfl
    | cons b ys ih =>
      have first := w b List.mem_cons_self
      rw [signRow,ih (fun y hy => w y (List.mem_cons_of_mem b hy))]
      simp [pairSign,first,Semiring.one_mul]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨w,q⟩ := List.pairwise_cons.mp sorted
    rw [orientation,row a xs w,ih q,Semiring.one_mul]

def tupleFrom (xs : List α) (r : Nat) (length : xs.length=r) : Sites α r := length ▸ tupleOfList xs

theorem tupleFrom_spec (xs : List α) (r : Nat) (length : xs.length=r) : tupleList r (tupleFrom xs r length)=xs := by
  cases length; exact tupleOfList_spec xs

def canonical (m : Nat) : Sites (Fin m) m := tupleFrom (List.finRange m) m (List.length_finRange (n:=m))

def slater (m : Nat) (x : Sites (Fin m) m) : C := orientation (tupleList m x)

theorem canonicalValue (m : Nat) : slater (C:=C) m (canonical m)=1 := by
  unfold slater canonical; rw [tupleFrom_spec]; exact orientationIncreasing _ (List.pairwise_lt_finRange _)

def determinant (m : Nat) (A : Fin m → Fin m → C) :=
  push (List.finRange m) A orientation (List.finRange m)

section Complex
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem conjugateCancel (z : ComplexScalar R) (h : z= -z) : z=0 := by
  have re := congrArg ComplexScalar.re h; have im := congrArg ComplexScalar.im h
  simp only [re_neg,im_neg] at re im; apply ComplexScalar.ext <;> change _=0 <;> grind only

/-- The top Slater tensor is an exact eigenvector of each full tensor
power on the m-dimensional source, including all singular matrices. -/
theorem topEigenvector (m : Nat) (A : Fin m → Fin m → ComplexScalar R) (x : Sites (Fin m) m) :
    PauliPairContraction.image (indices (List.finRange m) m) (matrix A m) (slater m) x=
    slater m x*determinant m A := by
  let F := push (List.finRange m) A orientation
  let labels := List.finRange m
  have t := topLine labels (tupleList m x) (by rw [tupleLength]; exact (List.length_finRange (n:=m)).symm)
    (fun _ _ => List.mem_finRange _) F orientation (pushAlt _ A _ (orientationAlt m)) (orientationAlt m) conjugateCancel
  have c : orientation (C:=ComplexScalar R) labels=1 := orientationIncreasing _ (List.pairwise_lt_finRange _)
  rw [c,Semiring.mul_one] at t
  change F (tupleList m x)=slater m x*determinant m A at t
  exact (pushIsMatrix labels A orientation m x).symm.trans t

theorem slaterMassPositive (m : Nat) :
    0<PauliPairContraction.normSum (indices (List.finRange m) m) (slater (C:=ComplexScalar R) m) := by
  let xs := indices (List.finRange m) m
  let u := canonical m
  let f i := normSq (slater (C:=ComplexScalar R) m i)
  have e := ExteriorPauliBase.sumOnIndex xs u f (indicesNodup _ (List.nodup_finRange _) _) (indicesFull _ (fun j => List.mem_finRange j) _ u)
  have h := Compression.sumOverNonnegative xs (fun i => f i-(if u=i then f i else 0))
    (fun i _ => by split <;> have p : 0≤f i := normSq_nonnegative _ <;> grind only)
  rw [Compression.sumOverSub,e] at h
  have one : f u=1 := by unfold f u; rw [canonicalValue,normSq_one]
  change 0<sumOver xs f; grind only

end Complex

end RankSeven.SlaterAlternant

#print axioms RankSeven.SlaterAlternant.topLine
#print axioms RankSeven.SlaterAlternant.pushAlt
#print axioms RankSeven.SlaterAlternant.pushIsMatrix
#print axioms RankSeven.SlaterAlternant.orientationAlt
#print axioms RankSeven.SlaterAlternant.canonicalValue
#print axioms RankSeven.SlaterAlternant.topEigenvector
#print axioms RankSeven.SlaterAlternant.slaterMassPositive

