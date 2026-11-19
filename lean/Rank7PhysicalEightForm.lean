import Rank7PhysicalChartRestriction
import Rank7PhysicalExteriorSupport
import Rank7PhysicalExteriorPositivity

/-! Orientation of the complementary four-planes entering the physical
particle-hole map between grade five and grade three. -/
namespace RankSeven.PhysicalEightForm

open Pauli PlaneOrientation GenericExteriorKernel
open ExteriorPauliBase (Permutation permutations)

private def slots := List.finRange 4

/-- Number of inversions between the first four-site block and the second,
in the computational site's integer order. -/
def shuffleInversions {n : Nat} (u v : Four (Basis n)) : Nat :=
  (((slots.flatMap fun i => slots.map fun j => (i,j)).map
      fun p => inverted n (position u p.1) (position v p.2)).count true)

private theorem invertedPivot (n : Nat) (x y : Basis n) :
    inverted n x y = pivotFlip n (xorBasis n x y) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    cases a <;> cases b <;> simp [inverted,xorBasis,pivotFlip,ih]

private theorem pivotLinear (n : Nat) (t x y : Basis n) :
    pivotFlip n t (xorBasis n x y)=(pivotFlip n t x ^^ pivotFlip n t y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with ⟨b,t⟩; rcases x with ⟨e,x⟩; rcases y with ⟨f,y⟩
    cases b <;> simp [pivotFlip,xorBasis,ih]

private theorem zeroParity (a b c d : Bool) (h : (a^^b)=(c^^d)) :
    [a,b,c,d].count true % 2 = 0 := by revert a b c d; decide

private theorem fourPivotEven {n : Nat} (u : Four (Basis n)) (h : PlaneRelation u) (d : Basis n) :
    (slots.map (fun i => pivotFlip n d (position u i))).count true % 2=0 := by
  have p := congrArg (pivotFlip n d) h
  change pivotFlip n d (xorBasis n u.1.1 u.1.2)=pivotFlip n d (xorBasis n u.2.1 u.2.2) at p
  rw [pivotLinear,pivotLinear] at p
  exact zeroParity _ _ _ _ p

/-- Each common binary point difference occurs four times. On those four
pairs the parity of the most significant differing bit is even. -/
theorem parallelPlaneShuffleEven {n : Nat} (x y a b : Basis n) :
    shuffleInversions (affinePlaneFrame x a b) (affinePlaneFrame y a b) % 2=0 := by
  let L (i j : Fin 4) := inverted n (planePoint n x a b i) (planePoint n y a b j)
  let D (k : Fin 4) := planePoint n (xorBasis n x y) a b k
  have shift (k i : Fin 4) : L i (indexXor i k)=pivotFlip n (D k) (position (affinePlaneFrame x a b) i) := by
    have inv : ∀ (i k : Fin 4), indexXor i (indexXor i k)=k := by decide
    unfold L D
    rw [invertedPivot,planePoint_difference,inv,position_planeFrame]
  have idx : (slots.flatMap (fun i => slots.map fun j => (i,j))).Perm
      (slots.flatMap (fun k => slots.map fun i => (i,indexXor i k))) := by decide
  have perm := idx.map (fun p => L p.1 p.2)
  have counts := (List.perm_iff_count.mp perm) true
  have block (k : Fin 4) : (slots.map (fun i => L i (indexXor i k))).count true % 2=0 := by
    simp only [shift]; exact fourPivotEven _ (generatorPlaneRelation x a b) _
  unfold shuffleInversions
  simp only [position_planeFrame]
  change ((slots.flatMap (fun i => slots.map fun j => (i,j))).map (fun p => L p.1 p.2)).count true %2=0
  rw [counts]
  have blocks : (slots.flatMap (fun k => slots.map fun i => (i,indexXor i k))).map (fun p => L p.1 p.2) =
      (slots.map (fun i => L i (indexXor i 0))) ++ (slots.map (fun i => L i (indexXor i 1))) ++
      (slots.map (fun i => L i (indexXor i 2))) ++ (slots.map (fun i => L i (indexXor i 3))) := by rfl
  rw [blocks]; simp only [List.count_append]; have h0 := block 0; have h1 := block 1
  have h2 := block 2; have h3 := block 3; omega

private theorem positionReordered {α : Type} (u : Four α) (p : Permutation) (i : Fin 4) :
    position (reorder u p) i=position u (position p i) := by
  have cases4 : ∀ j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
  rcases cases4 i with rfl|rfl|rfl|rfl <;> rfl

private theorem shuffleReorder {n : Nat} (u v : Four (Basis n)) (p : Permutation) (hp : p∈permutations) :
    shuffleInversions u (reorder v p)=shuffleInversions u v := by
  let pairs := slots.flatMap fun (i : Fin 4) => slots.map fun j => (i,j)
  have stable : ∀ p : Permutation, p∈permutations →
      (pairs.map (fun ij => (ij.1,position p ij.2))).Perm pairs := by decide
  have perm := (stable _ hp).map (fun ij => inverted n (position u ij.1) (position v ij.2))
  simpa only [shuffleInversions,List.map_map,Function.comp_def,positionReordered,pairs] using (List.perm_iff_count.mp perm) true

/-- In the actual sorted Pauli kernel every supported unequal pair of
four-planes has positive wedge-shuffle sign in any number of qubits. -/
theorem supportedShuffleEven {n : Nat} (u v : PhysicalWedges.Coordinate n) (neq : u≠v)
    (h : supportedPair u.val v.val=true) : shuffleInversions u.val v.val % 2=0 := by
  obtain ⟨dat⟩ := PhysicalExteriorSupport.supported_offdiag u.val v.val u.property v.property
    (fun eq => neq (Subtype.ext eq)) h
  rw [←shuffleReorder u.val v.val dat.perm dat.perm_mem,dat.col]
  conv => lhs; arg 1; arg 1; rw [dat.row]
  apply parallelPlaneShuffleEven

open Lean.Grind
open HyperplaneIncidence (zero)

private def skip5 (j : Fin 5) (i : Fin 4) : Fin 5 := ⟨if i.val<j.val then i.val else i.val+1,by split <;> omega⟩

def face {α : Type} (s : Fin 5 → α) (j : Fin 5) : Four α :=
  ((s (skip5 j 0),s (skip5 j 1)),(s (skip5 j 2),s (skip5 j 3)))

def prepend {α : Type} (z : α) (t : Fin 3 → α) : Four α := ((z,t 0),(t 1,t 2))

def spectator {n : Nat} (t : Fin 3 → Basis n) : Basis n := xorBasis n (t 0) (xorBasis n (t 1) (t 2))

/-- Both contractions use the same coordinate mode. The five choices in
the first contraction carry the signs of their positions in the input wedge. -/
def particleHoleEntry {C : Type} [CommRing C] {n : Nat} (i half : C) (s : Fin 5 → Basis n)
    (t : Fin 3 → Basis n) : C :=
  sumOver (List.finRange 5) fun j => signed (j.val%2==1) (exteriorKernel i half (prepend (s j) t) (face s j))

private theorem fourZero {n : Nat} (z a b c : Basis n) :
    xorBasis n (xorBasis n z a) (xorBasis n b c)=zero n ↔ z=xorBasis n a (xorBasis n b c) := by
  induction n with
  | zero => rcases z with ⟨⟩; exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ n ih =>
    rcases z with ⟨z',z⟩; rcases a with ⟨a',a⟩; rcases b with ⟨b',b⟩; rcases c with ⟨c',c⟩
    change ((z'^^a')^^(b'^^c'),xorBasis n (xorBasis n z a) (xorBasis n b c))=(false,zero n) ↔
      (z',z)=(a'^^(b'^^c'),xorBasis n a (xorBasis n b c))
    simp only [Prod.mk.injEq,ih]
    have head : ∀ (z a b c : Bool), ((z^^a)^^(b^^c))=false ↔ z=(a^^(b^^c)) := by decide
    rw [head]

private theorem onlySpectator {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (s : Fin 5 → Basis n) (t : Fin 3 → Basis n) {j : Fin 5} (h : s j≠spectator t) :
    signed (j.val%2==1) (exteriorKernel i half (prepend (s j) t) (face s j))=0 := by
  rw [nonplane_exterior_kernel i half hi hh (prepend (s j) t) (face s j) (fun e => h ((fourZero _ _ _ _).mp e))]
  unfold signed; split <;> grind

theorem particleHoleAbsent {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (s : Fin 5 → Basis n) (t : Fin 3 → Basis n) (absent : ∀j,s j≠spectator t) :
    particleHoleEntry i half s t=0 := by
  simp only [particleHoleEntry,onlySpectator i half hi hh s t (absent _)]
  change 0+(0+(0+(0+(0+0))))=(0:C); grind

/-- The Pauli contraction sum has exactly one candidate. It is the XOR
of the three output sites, for every number of qubits. -/
theorem particleHoleUnique {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (s : Fin 5 → Basis n) (t : Fin 3 → Basis n) (inj : ∀j k,s j=s k → j=k)
    (j : Fin 5) (found : s j=spectator t) :
    particleHoleEntry i half s t=signed (j.val%2==1) (exteriorKernel i half (prepend (s j) t) (face s j)) := by
  let E (k : Fin 5) := signed (k.val%2==1) (exteriorKernel i half (prepend (s k) t) (face s k))
  change sumOver (List.finRange 5) E=E j
  rw [←ExteriorPauliBase.sumOnIndex (List.finRange 5) j E (List.nodup_finRange _) (List.mem_finRange _)]
  apply sumOverCongr; intro k; split
  next y => rfl
  next h => exact onlySpectator i half hi hh s t (fun e => h (inj j k (found.trans e.symm)))

def front4 (j : Fin 4) : Permutation :=
  match j.val with
  | 0 => ((0,1),(2,3))
  | 1 => ((1,0),(2,3))
  | 2 => ((2,0),(1,3))
  | _ => ((3,0),(1,2))

/-- With the two four-faces in sorted computational order, the surviving
entry is exactly q with the two contraction-position signs, or zero if
the faces fail the physical parallel-plane test. -/
theorem particleHoleOnSortedFaces {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (s : Fin 5 → Basis n) (t : Fin 3 → Basis n) (inj : ∀j k,s j=s k → j=k) (j : Fin 5) (found : s j=spectator t)
    (f g : PhysicalWedges.Coordinate n) (p : Fin 4)
    (left : prepend (s j) t=reorder f.val (front4 p)) (right : face s j=g.val) :
    particleHoleEntry i half s t=signed (j.val%2==1) (signed (p.val%2==1)
      (if supportedPair f.val g.val then 4*half^n else 0)) := by
  have front : ∀p,front4 p∈permutations ∧ ExteriorPauliBase.oddPermutation (front4 p)=(p.val%2==1) := by decide
  rw [particleHoleUnique i half hi hh s t inj j found,left,right,kernel_reorder_left i half hi hh _ _ _ (front p).1,
    (front p).2,sorted_kernel_entry i half hi hh f.val g.val f.property g.property]

private def cross {n : Nat} (xs ys : List (Basis n)) : Nat :=
  (xs.flatMap (fun x => ys.map (inverted n x))).count true

private theorem crossRow {n : Nat} (x : Basis n) (xs ys : List (Basis n)) :
    cross (x::xs) ys=(ys.map (inverted n x)).count true+cross xs ys := by
  simp only [cross,List.flatMap_cons,List.count_append]

private theorem crossCol {n : Nat} (y : Basis n) (xs ys : List (Basis n)) :
    cross xs (y::ys)=(xs.map fun x => inverted n x y).count true+cross xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [crossRow,crossRow,ih]; simp only [List.map_cons,List.count_cons]; omega

private theorem crossPermLeft {n : Nat} {xs zs : List (Basis n)} (p : xs.Perm zs) (ys : List (Basis n)) :
    cross xs ys=cross zs ys := (List.Perm.flatMap_right (fun x => ys.map (inverted n x)) p).count_eq true

private theorem crossPermRight {n : Nat} (xs : List (Basis n)) {ys zs : List (Basis n)} (p : ys.Perm zs) :
    cross xs ys=cross xs zs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [crossRow,crossRow,ih,(p.map (inverted n x)).count_eq true]

private def rows {k : Nat} {α : Type} (v : Fin k → α) := (List.finRange k).map v

/-- Computational wedge-shuffle sign of an increasing five-tuple and
increasing three-tuple, with the five-tuple placed first. -/
def fiveThreeParity {n : Nat} (s : Fin 5 → Basis n) (t : Fin 3 → Basis n) : Bool :=
  cross (rows s) (rows t)%2==1

private theorem pieces5 {α : Type} (s : Fin 5 → α) (j : Fin 5) :
    (rows s).Perm (s j::rows (position (face s j))) := by
  have split : ∀ j : Fin 5, (List.finRange 5).Perm (j::(slots.map (skip5 j))) := by decide
  have perm := (split j).map s
  apply perm.trans
  apply List.Perm.of_eq
  have cases5 : ∀i : Fin 5, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by decide
  rcases cases5 j with rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem pieces4 {α : Type} (v : Four α) (p : Fin 4) (z : α) (t : Fin 3 → α)
    (left : prepend z t=reorder v (front4 p)) :
    (rows (position v)).Perm (z::rows t) ∧ position v p=z := by
  have cover : ∀ p : Fin 4, slots.Perm (slots.map (position (front4 p))) ∧ position (front4 p) 0=p := by decide
  have perm := ((cover p).1.map (position v))
  have goal : rows (position (prepend z t))=z::rows t := rfl
  have lemma4 (g : Four α) (q : Permutation) : rows (position (reorder g q))=(slots.map (position q)).map (position g) := by
    simp only [rows,slots,List.map_map,Function.comp_def]; apply List.map_congr_left; intro j _; exact positionReordered _ _ _
  have h0 := congrArg (fun k => position k 0) left
  change z=position (reorder v (front4 p)) 0 at h0
  rw [positionReordered,(cover p).2] at h0
  rw [left,lemma4] at goal
  exact ⟨goal ▸ perm,h0.symm⟩

private theorem rankCmp {k n : Nat} (x : Fin k → Basis n)
    (inc : ∀i j,i<j → label n (x i)<label n (x j)) (i j : Fin k) :
    inverted n (x i) (x j)=decide (j<i) := by
  apply Bool.eq_iff_iff.mpr; rw [inverted_iff,decide_eq_true_iff]
  constructor
  · intro h; by_cases e : i=j
    · subst j; omega
    · by_cases l : i<j
      · have g := inc i j l; omega
      · omega
  · exact inc _ _

private theorem increasingCoordinate {n : Nat} (f : PhysicalWedges.Coordinate n) :
    ∀i j,i<j → label n (position f.val i)<label n (position f.val j) := by
  obtain ⟨h0,h1,h2⟩ := f.property
  have cases4 : ∀j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
  intro i j lt; rcases cases4 i with rfl|rfl|rfl|rfl <;> rcases cases4 j with rfl|rfl|rfl|rfl <;>
    first | exact h0 | exact h1 | exact h2 | exact Nat.lt_trans h0 h1 | exact Nat.lt_trans h1 h2 | exact Nat.lt_trans h0 (Nat.lt_trans h1 h2) | (simp at lt)

private theorem crossShuffle {n : Nat} (u v : Four (Basis n)) :
    cross (rows (position u)) (rows (position v))=shuffleInversions u v := by
  rfl

/-- The two coordinate-contraction signs in the nonzero particle-hole
entry equal the wedge-order sign on its concatenated five and three sites. -/
theorem particleHoleShuffleParity {n : Nat} (s : Fin 5 → Basis n) (t : Fin 3 → Basis n)
    (sorted : ∀i j,i<j → label n (s i)<label n (s j))
    (j : Fin 5) (f g : PhysicalWedges.Coordinate n) (p : Fin 4)
    (left : prepend (s j) t=reorder f.val (front4 p)) (right : face s j=g.val)
    (neq : g≠f) (supp : supportedPair g.val f.val=true) :
    fiveThreeParity s t=((j.val%2==1) ^^ (p.val%2==1)) := by
  let G := rows (position g.val)
  let T := rows t
  let F := rows (position f.val)
  have gperm : (rows s).Perm (s j::G) := by simpa only [G,right] using pieces5 s j
  obtain ⟨fperm,point⟩ := pieces4 f.val p (s j) t left
  have fil : (G.map (fun x => inverted n x (s j))).count true=4-j.val := by
    have e := (gperm.map (fun x => inverted n x (s j))).count_eq true
    simp only [rows,List.map_map,Function.comp_def,rankCmp s sorted,List.map_cons,List.count_cons] at e

    have num : ∀j : Fin 5, ((List.finRange 5).map (fun i => decide (j<i))).count true=4-j.val := by decide
    simp [num] at e; exact e.symm
  have til : (T.map (inverted n (s j))).count true=p.val := by
    have e := (fperm.map (inverted n (position f.val p))).count_eq true
    simp only [rows,List.map_map,Function.comp_def,rankCmp _ (increasingCoordinate f),List.map_cons,List.count_cons] at e
    rw [←point,rankCmp _ (increasingCoordinate f)] at e
    have num : ∀p : Fin 4, ((List.finRange 4).map (fun i => decide (i<p))).count true=p.val := by decide
    simp only [num] at e
    simpa [T,rows,point,Function.comp_def] using e.symm
  have even := supportedShuffleEven g f neq supp
  have even' : cross G F%2=0 := by simpa only [G,F,crossShuffle] using even
  rw [crossPermRight _ fperm,crossCol,fil] at even'
  unfold fiveThreeParity
  rw [crossPermLeft gperm,crossRow]
  change (((T.map (inverted n (s j))).count true + cross G T)%2==1) = _
  rw [til]
  have jBound := j.isLt
  change (4-j.val+cross G T)%2=0 at even'
  have xorTrue (a b : Bool) : (a^^b)=true ↔ (a=true ∧ b=false) ∨ (a=false ∧ b=true) := by cases a <;> cases b <;> decide
  apply Bool.eq_iff_iff.mpr; rw [xorTrue]; simp only [beq_iff_eq,Bool.eq_false_iff]
  have four : j.val≤4 := by omega
  have sum4 : 4-j.val+j.val=4 := by omega
  simp only [ne_eq,beq_iff_eq]; omega

/-- On a supported pair the actual sandwiched physical kernel is q
times the sign of the concatenated five and three sites. -/
theorem particleHoleSignedVolume {C : Type} [CommRing C] {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (s : Fin 5 → Basis n) (t : Fin 3 → Basis n)
    (sorted : ∀i j,i<j → label n (s i)<label n (s j))
    (j : Fin 5) (found : s j=spectator t) (f g : PhysicalWedges.Coordinate n) (p : Fin 4)
    (left : prepend (s j) t=reorder f.val (front4 p)) (right : face s j=g.val)
    (supported : supportedPair f.val g.val=true) :
    particleHoleEntry i half s t=signed (fiveThreeParity s t) (4*half^n) := by
  have inj (i k : Fin 5) (eq : s i=s k) : i=k := by
    have same := congrArg (label n) eq
    by_cases l : i<k
    · have lt := sorted _ _ l; omega
    · by_cases r : k<i
      · have lt := sorted _ _ r; omega
      · omega
  have neq : g≠f := by
    intro e; subst g
    have specPosition := (pieces4 f.val p _ t left).2
    rw [←right] at specPosition
    have facePosition : position (face s j) p = s (skip5 j p) := by
      have items : ∀p : Fin 4, p=0 ∨ p=1 ∨ p=2 ∨ p=3 := by decide
      rcases items p with rfl|rfl|rfl|rfl <;> rfl
    have bad := inj _ _ (facePosition.symm.trans specPosition)
    exact (show ∀ (i : Fin 4) (k : Fin 5), skip5 k i≠k by decide) p j bad
  rw [particleHoleShuffleParity s t sorted j f g p left right neq (PhysicalExteriorPositivity.supportedSymm supported),
    particleHoleOnSortedFaces i half hi hh s t inj j found f g p left right,ite_eq_left supported]
  cases (j.val%2==1) <;> cases (p.val%2==1) <;> simp [signed] <;> grind

end RankSeven.PhysicalEightForm

#print axioms RankSeven.PhysicalEightForm.particleHoleSignedVolume
