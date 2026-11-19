import Rank7ExteriorPauliBase

/-! Canonical orientation of binary affine planes. The first Bool of Basis (n+1)
is the most significant coordinate. No restriction on the number of qubits is used. -/
namespace RankSeven.PlaneOrientation

open RankSeven.Pauli

/-- The ordinary binary integer label, in computational-basis order. -/
def label : (n : Nat) → Basis n → Nat
  | 0, _ => 0
  | n+1, (b,v) => (if b then 2^n else 0) + label n v

theorem labelBound (n : Nat) (v : Basis n) : label n v < 2^n := by
  induction n with
  | zero => cases v; decide
  | succ n ih =>
    rcases v with ⟨b,v⟩
    have h := ih v
    cases b <;> simp [label,Nat.pow_succ] <;> omega

theorem labelInjective (n : Nat) (x y : Basis n) (eq : label n x = label n y) : x=y := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    have hx := labelBound n x
    have hy := labelBound n y
    cases b <;> cases c <;> simp [label] at eq
    all_goals first | exact congrArg (fun w => (_,w)) (ih x y eq) | omega

/-- Inversion predicate for two labels in lexicographic order. -/
def inverted : (n : Nat) → Basis n → Basis n → Bool
  | 0, _, _ => false
  | n+1, (a,x), (b,y) => if a=b then inverted n x y else a

theorem inverted_iff (n : Nat) (x y : Basis n) :
    inverted n x y = true ↔ label n y < label n x := by
  induction n with
  | zero => simp [label,inverted]
  | succ n ih =>
    rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    have hx := labelBound n x
    have hy := labelBound n y
    cases b <;> cases c <;> simp [label,inverted,ih] <;> omega

/-- Does t flip the highest bit at which two vertices differ? An identical pair
has no differing bit and returns false. -/
def pivotFlip : (n : Nat) → Basis n → Basis n → Bool
  | 0, _, _ => false
  | n+1, (d,rest), (b,t) => if d then b else pivotFlip n rest t

theorem translatedComparison (n : Nat) (t x y : Basis n) :
    inverted n (xorBasis n t x) (xorBasis n t y) =
      (inverted n x y ^^ pivotFlip n (xorBasis n x y) t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with ⟨a,t⟩; rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    cases a <;> cases b <;> cases c <;> simp [xorBasis,inverted,pivotFlip,ih]

def translate {n : Nat} (t : Basis n) (u : Four (Basis n)) : Four (Basis n) :=
  ((xorBasis n t u.1.1,xorBasis n t u.1.2),(xorBasis n t u.2.1,xorBasis n t u.2.2))

/-- This is the actual inversion count of the four integer labels, with their
six pairs taken in the usual order 01,02,03,12,13,23. -/
def inversionCount {n : Nat} (u : Four (Basis n)) : Nat :=
  let a := label n u.1.1
  let b := label n u.1.2
  let c := label n u.2.1
  let d := label n u.2.2
  [(decide (b<a)),(decide (c<a)),(decide (d<a)),
    (decide (c<b)),(decide (d<b)),(decide (d<c))].count true

def parity {n : Nat} (u : Four (Basis n)) : Bool := inversionCount u % 2 == 1

private def six (a b c d e f : Bool) := a ^^ b ^^ c ^^ d ^^ e ^^ f

private theorem sixParity (a b c d e f : Bool) :
    ([a,b,c,d,e,f].count true % 2 == 1) = six a b c d e f := by
  revert a b c d e f; decide

private theorem decInverted (n : Nat) (a b : Basis n) :
    decide (label n b < label n a) = inverted n a b := by
  have h := inverted_iff n a b
  cases h' : inverted n a b <;> simp_all

private theorem parityFormula {n : Nat} (a b c d : Basis n) :
    parity ((a,b),(c,d)) = six (inverted n a b) (inverted n a c) (inverted n a d)
      (inverted n b c) (inverted n b d) (inverted n c d) := by
  simp only [parity,inversionCount,decInverted,sixParity]

private theorem cancelPairs (a b c d e f p q r : Bool) :
    six (a^^p) (b^^q) (c^^r) (d^^r) (e^^q) (f^^p) = six a b c d e f := by
  revert a b c d e f p q r; decide

/-- Opposite differences agree in an affine binary plane in any vertex order. -/
def PlaneRelation {n : Nat} (u : Four (Basis n)) : Prop :=
  xorBasis n u.1.1 u.1.2 = xorBasis n u.2.1 u.2.2

private theorem opposite {n : Nat} (a b c d : Basis n)
    (h : xorBasis n a b = xorBasis n c d) :
    xorBasis n a c = xorBasis n b d ∧ xorBasis n a d = xorBasis n b c := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩; rcases c with ⟨c,z⟩; rcases d with ⟨d,w⟩
    have hd := congrArg Prod.fst h
    have tl := congrArg Prod.snd h
    change (a^^b)=(c^^d) at hd
    change xorBasis n x y = xorBasis n z w at tl
    obtain ⟨p,q⟩ := ih x y z w tl
    simp only [xorBasis,p,q]
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all <;> exact ⟨rfl,rfl⟩

/-- Translating any ordered affine-plane tuple preserves the parity of the
sorting permutation. It also holds for degenerate tuples satisfying the relation. -/
theorem translationPreservesParity {n : Nat} (t : Basis n) (u : Four (Basis n))
    (plane : PlaneRelation u) : parity (translate t u) = parity u := by
  rcases u with ⟨⟨a,b⟩,c,d⟩
  change xorBasis n a b = xorBasis n c d at plane
  obtain ⟨second,third⟩ := opposite a b c d plane
  change parity ((xorBasis n t a,xorBasis n t b),(xorBasis n t c,xorBasis n t d)) =
    parity ((a,b),(c,d))
  rw [parityFormula,parityFormula]
  simp only [translatedComparison,←plane,←second,←third,cancelPairs]

/-- Numeric modulo-two statement, rather than just preservation of an abstract
choice of orientation. -/
theorem translationPreservesInversions {n : Nat} (t : Basis n) (u : Four (Basis n))
    (plane : PlaneRelation u) : inversionCount (translate t u) % 2 = inversionCount u % 2 := by
  have hp := translationPreservesParity t u plane
  unfold parity at hp
  by_cases h : inversionCount u % 2 = 1
  · simp [h] at hp; omega
  · have h' : inversionCount u % 2 = 0 := by omega
    simp [h'] at hp; omega

private theorem xorAssoc (n : Nat) (a b c : Basis n) :
    xorBasis n (xorBasis n a b) c = xorBasis n a (xorBasis n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩; rcases c with ⟨c,z⟩
    simp only [xorBasis,Bool.xor_assoc,ih]; rfl

private theorem xorUntranslate (n : Nat) (p q : Basis n) : xorBasis n (xorBasis n q p) p = q := by
  induction n with
  | zero => cases q; rfl
  | succ n ih =>
    rcases p with ⟨a,x⟩; rcases q with ⟨b,y⟩
    simp only [xorBasis,ih]; cases a <;> cases b <;> rfl

private theorem frameDirectionBit (p a b : Bool) :
    (p ^^ (p ^^ a)) = ((p ^^ b) ^^ ((p ^^ a) ^^ b)) := by revert p a b; decide

theorem generatorPlaneRelation {n : Nat} (p a b : Basis n) :
    PlaneRelation (affinePlaneFrame p a b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨p,x⟩; rcases a with ⟨a,y⟩; rcases b with ⟨b,z⟩
    specialize ih x y z
    simp only [PlaneRelation,affinePlaneFrame,xorBasis] at ih ⊢
    rw [frameDirectionBit,ih]

theorem translateGeneratorFrame {n : Nat} (t p a b : Basis n) :
    translate t (affinePlaneFrame p a b) = affinePlaneFrame (xorBasis n t p) a b := by
  simp only [translate,affinePlaneFrame,xorAssoc]

/-- Common generators induce the same canonical sorting sign on every coset. -/
theorem parallelFrameParity {n : Nat} (p q a b : Basis n) :
    parity (affinePlaneFrame p a b) = parity (affinePlaneFrame q a b) := by
  have e := translationPreservesParity (xorBasis n q p) _ (generatorPlaneRelation p a b)
  rw [translateGeneratorFrame,xorUntranslate] at e
  exact e.symm

def orientationSign {n : Nat} (u : Four (Basis n)) : Int := if parity u then -1 else 1

theorem parallelFrameSignProduct {n : Nat} (p q a b : Basis n) :
    orientationSign (affinePlaneFrame p a b) * orientationSign (affinePlaneFrame q a b) = 1 := by
  simp only [orientationSign,parallelFrameParity p q a b]
  cases parity (affinePlaneFrame q a b) <;> decide

/-- Select the four entries of an enumeration in the order specified by p.
Taking f to be the coordinate lookup of a sorted wedge gives the convention
used in the finite determinant sum. -/
def selectLabels {α : Type} (f : Fin 4 → α) (p : ExteriorPauliBase.Permutation) : Four α :=
  ((f p.1.1,f p.1.2),(f p.2.1,f p.2.2))

private theorem orderReflection {n : Nat} (f : Fin 4 → Basis n)
    (increasing : ∀ i j, i<j → label n (f i) < label n (f j)) (i j : Fin 4) :
    label n (f i) < label n (f j) ↔ i<j := by
  constructor
  · intro h
    by_cases hij : i=j
    · subst j; omega
    · by_cases hji : j<i
      · have := increasing _ _ hji; omega
      · omega
  · exact increasing i j

/-- The sign convention agrees exactly with the existing four-axis determinant
permutation. Distinctness of p is not needed for this comparison identity. -/
theorem parityFromIncreasingLabels {n : Nat} (f : Fin 4 → Basis n)
    (increasing : ∀ i j, i<j → label n (f i) < label n (f j))
    (p : ExteriorPauliBase.Permutation) :
    parity (selectLabels f p) = ExteriorPauliBase.oddPermutation p := by
  simp only [parity,inversionCount,selectLabels,ExteriorPauliBase.oddPermutation,
    orderReflection f increasing]

/-- The two permutation signs that convert canonically sorted plane vertices
to the same generator order agree, so their determinant signs cancel. -/
theorem parallelSortingParities {n : Nat} (f g : Fin 4 → Basis n)
    (increasingF : ∀ i j, i<j → label n (f i) < label n (f j))
    (increasingG : ∀ i j, i<j → label n (g i) < label n (g j))
    (p q : ExteriorPauliBase.Permutation) (x y a b : Basis n)
    (fOrder : selectLabels f p = affinePlaneFrame x a b)
    (gOrder : selectLabels g q = affinePlaneFrame y a b) :
    ExteriorPauliBase.oddPermutation p = ExteriorPauliBase.oddPermutation q := by
  rw [←parityFromIncreasingLabels f increasingF,←parityFromIncreasingLabels g increasingG,
    fOrder,gOrder,parallelFrameParity x y]

def Increasing {n : Nat} (u : Four (Basis n)) : Prop :=
  label n u.1.1 < label n u.1.2 ∧ label n u.1.2 < label n u.2.1 ∧ label n u.2.1 < label n u.2.2

theorem sortedParity {n : Nat} (u : Four (Basis n)) (ord : Increasing u) : parity u = false := by
  obtain ⟨ab,bc,cd⟩ := ord
  let a := label n u.1.1
  let b := label n u.1.2
  let c := label n u.2.1
  let d := label n u.2.2
  change a<b at ab
  change b<c at bc
  change c<d at cd
  change ([decide (b<a),decide (c<a),decide (d<a),decide (c<b),decide (d<b),decide (d<c)].count true % 2 == 1) = false
  have hba : ¬b<a := by omega
  have hca : ¬c<a := by omega
  have hda : ¬d<a := by omega
  have hcb : ¬c<b := by omega
  have hdb : ¬d<b := by omega
  have hdc : ¬d<c := by omega
  simp [hba,hca,hda,hcb,hdb,hdc]

/-- Every permutation connecting two canonically ordered plane wedges by a
single common translation is even. This applies directly to each supported
summand of the physical Pauli determinant. -/
theorem translatedSortedPermutationEven {n : Nat} (u : Four (Basis n))
    (sortedU : Increasing u) (plane : PlaneRelation u)
    (f : Fin 4 → Basis n) (increasingF : ∀ i j, i<j → label n (f i) < label n (f j))
    (p : ExteriorPauliBase.Permutation) (t : Basis n)
    (aligned : selectLabels f p = translate t u) : ExteriorPauliBase.oddPermutation p = false := by
  rw [←parityFromIncreasingLabels f increasingF,aligned,translationPreservesParity t u plane,
    sortedParity u sortedU]

end RankSeven.PlaneOrientation
