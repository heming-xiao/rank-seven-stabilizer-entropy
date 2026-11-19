import Rank7PhysicalCompressionEffect
import Rank7RectangularPairedReduction

/-! The fourth exterior block of a Pauli twirl after compression by a complex frame. -/

namespace RankSeven.FrameExteriorSector

open Lean.Grind Pauli HyperplaneInduction ExteriorCuts ExteriorPauliBase PhysicalWedges
open GenericExteriorKernel (position reorder signed wordMinor exteriorKernel)
open ComplexScalar (star ofReal imaginaryUnit)
open PhysicalExteriorCompression (wedgeRows inverseWeight)
open PhysicalCompressionEffect (physicalEntries)

variable {C R α β : Type} [CommRing C] [CommRing R]

private abbrev Pair := Fin 4 × Fin 4

private def factors (p : Permutation) : List Pair := [(0,p.1.1),(1,p.1.2),(2,p.2.1),(3,p.2.2)]

private def insert (i : Pair) : List Pair → List Pair
  | [] => [i]
  | a :: as => if i.1 ≤ a.1 then i :: a :: as else a :: insert i as

private def ordered (xs : List Pair) : List Pair := xs.foldr insert []

private def monomial (M : Fin 4 → Fin 4 → C) : List Pair → C
  | [] => 1
  | (i,j) :: xs => M i j * monomial M xs

private theorem insertValue (M : Fin 4 → Fin 4 → C) (i : Pair) (xs : List Pair) :
    monomial M (insert i xs) = M i.1 i.2 * monomial M xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [insert]; split <;> simp only [monomial, ih] <;> grind

private theorem orderedValue (M : Fin 4 → Fin 4 → C) (xs : List Pair) :
    monomial M (ordered xs) = monomial M xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change monomial M (insert a (ordered xs)) = _
    rw [insertValue, ih]; rfl

private theorem transposeTable :
    (permutations.map (fun p => (oddPermutation p, ordered ((factors p).map Prod.swap)))).Perm
      (permutations.map (fun p => (oddPermutation p, factors p))) := by decide

private theorem sumPerm {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ a b => exact a.trans b

private def detFour (M : Fin 4 → Fin 4 → C) :=
  sumOver permutations fun p => signed (oddPermutation p) (monomial M (factors p))

private theorem detTranspose (M : Fin 4 → Fin 4 → C) :
    detFour (fun i j => M j i) = detFour M := by
  let eval (t : Bool × List Pair) := signed t.1 (monomial M t.2)
  have h := sumPerm transposeTable eval
  simpa only [detFour,sumOver,List.map_map,Function.comp_def,eval,orderedValue,
    factors,List.map_cons,List.map_nil,monomial,Prod.swap] using h

private theorem minorDet (A : α → Fin 7 → C) (r : Fin 4 → α) (v : Wedge7) :
    minor4 A r v = detFour (fun i j => A (r i) (sourceSite v j)) := by
  apply sumOverCongr
  intro p
  unfold signed
  simp only [monomial,factors]
  split <;> grind

private theorem wordDet {n : Nat} (i : C) (p : Word n) (r s : Four (Basis n)) :
    wordMinor i p r s = detFour (fun a b => wordEntry i p (position r a) (position s b)) := by
  apply sumOverCongr
  intro p'
  unfold signed
  simp only [monomial,factors,tensorFour,tensor,reorder, show position r 0=r.1.1 from rfl,
    show position r 1=r.1.2 from rfl, show position r 2=r.2.1 from rfl, show position r 3=r.2.2 from rfl]
  split <;> grind

private local instance {n : Nat} (r : Four (Basis n)) : Decidable (PlaneOrientation.Increasing r) := by
  unfold PlaneOrientation.Increasing
  infer_instance

private theorem physicalList (n : Nat) :
    (coords n).map Subtype.val = (fourIndices (qubitIndices n)).filter
      (ExteriorIsometry.increasing (PlaneOrientation.label n)) := by
  unfold coords
  rw [List.map_filterMap, ←List.filterMap_eq_filter]
  apply congrArg (fun f => (fourIndices (qubitIndices n)).filterMap f)
  funext r
  change Option.map Subtype.val (if h : PlaneOrientation.Increasing r then some ⟨r,h⟩ else none) =
    Option.guard (ExteriorIsometry.increasing (PlaneOrientation.label n)) r
  change _ = (if decide (PlaneOrientation.Increasing r) then some r else none)
  by_cases h : PlaneOrientation.Increasing r <;> simp [h]

section Ordered
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Fourth Cauchy–Binet on the physical increasing coordinate enumeration. -/
theorem physicalCauchyBinet {n : Nat} (A B : Basis n → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    minor4 (ExteriorIsometry.columnGram (qubitIndices n) (fun s j => star (A s j)) B) (sourceSite u) v =
      sumOver (coords n) (fun r => star (minor4 A (wedgeRows r) u) * minor4 B (wedgeRows r) v) := by
  classical
  have cb := ExteriorIsometry.cauchyBinet (qubitIndices n) qubitIndicesComplete
    (HyperplaneIncidence.normalsNodup n) (PlaneOrientation.label n)
    (PlaneOrientation.labelInjective n) A B u v
  rw [←physicalList] at cb
  simp only [sumOver,List.map_map,Function.comp_def] at cb
  exact cb.symm

private def firstFour : Wedge7 := ⟨0,1,2,3,by decide,by decide,by decide⟩
private def fourIndex (j : Fin 7) : Fin 4 := Fin.ofNat 4 j.val

private theorem firstFourIndex : ∀ j : Fin 4, fourIndex (sourceSite firstFour j) = j := by decide

/-- The minor of a Pauli image of the seven columns, expanded once on the
increasing intermediate physical wedges. -/
theorem minorWordImage {n : Nat} (p : Word n) (A : Basis n → Fin 7 → ComplexScalar R)
    (r : Coordinate n) (v : Wedge7) :
    minor4 (matMul (qubitIndices n) (wordEntry imaginaryUnit p) A) (wedgeRows r) v =
      sumOver (coords n) (fun s => wordMinor imaginaryUnit p r.val s.val *
        minor4 A (wedgeRows s) v) := by
  let P := wordEntry (imaginaryUnit (R := R)) p
  let B s j := star (P (wedgeRows r (fourIndex j)) s)
  have gram (j : Fin 4) (t : Fin 7) :
      ExteriorIsometry.columnGram (qubitIndices n) (fun s k => star (B s k)) A (sourceSite firstFour j) t =
        matMul (qubitIndices n) P A (wedgeRows r j) t := by
    simp only [ExteriorIsometry.columnGram,B,ComplexScalar.star_star,firstFourIndex,matMul]
  have left := physicalCauchyBinet B A firstFour v
  rw [minorDet] at left
  simp only [gram] at left
  rw [minorDet]
  refine left.trans (sumOverCongr _ (fun s => ?_))
  rw [ExteriorIsometry.starMinor, minorDet, wordDet]
  simp only [B,ComplexScalar.star_star,firstFourIndex,wedgeRows]
  rw [detTranspose]

/-- The single-copy matrix of a physical Pauli word in the supplied frame. -/
def framedWord {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    Fin 7 → Fin 7 → ComplexScalar R :=
  matMul (qubitIndices n) (transpose (fun s j => star (A s j)))
    (matMul (qubitIndices n) (wordEntry imaginaryUnit p) A)

/-- Two applications of Cauchy–Binet give the compressed single-word minor.
The seven columns may be arbitrary. -/
theorem framedWordMinor {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (u v : Wedge7) :
    minor4 (framedWord A p) (sourceSite u) v =
      sumOver (coords n) (fun r => sumOver (coords n) (fun s =>
        star (minor4 A (wedgeRows r) u) * wordMinor imaginaryUnit p r.val s.val *
        minor4 A (wedgeRows s) v)) := by
  change minor4 (ExteriorIsometry.columnGram (qubitIndices n) (fun s j => star (A s j))
    (matMul (qubitIndices n) (wordEntry imaginaryUnit p) A)) _ _ = _
  rw [physicalCauchyBinet]
  apply sumOverCongr
  intro r
  rw [minorWordImage, sumOverMulLeft]
  apply sumOverCongr
  intro s
  grind

/-- Sum of compressed Pauli minors, with the four-copy projector normalization. -/
theorem framedWordMinor_sum (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    (ofReal half)^(n+n) * sumOver (words n) (fun p => minor4 (framedWord A p) (sourceSite u) v) =
      sumOver (coords n) (fun r => sumOver (coords n) (fun s =>
        star (minor4 A (wedgeRows r) u) * exteriorKernel imaginaryUnit (ofReal half) r.val s.val *
        minor4 A (wedgeRows s) v)) := by
  simp only [framedWordMinor,exteriorKernel,sumOverMulLeft,sumOverMulRight]
  rw [sumOverSwap (words n) (coords n)]
  apply sumOverCongr
  intro r
  rw [sumOverSwap (words n) (coords n)]
  apply sumOverCongr
  intro s
  apply sumOverCongr
  intro p
  grind

/-- The normalized physical twirl conjugated by the fourth tensor power of
the frame, on all ordered four-tuples of source columns. -/
def frameTwirl (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (x y : Four (Fin 7)) : ComplexScalar R :=
  let Q := fourIndices (qubitIndices n)
  (ofReal half)^(n+n) * matMul Q (matMul Q (transpose (tensorFour (fun s j => star (A s j))))
    (unnormalizedTwirl imaginaryUnit)) (tensorFour A) x y

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem frameTwirl_words (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (x y : Four (Fin 7)) :
    frameTwirl half A x y =
      (ofReal half)^(n+n) * sumOver (words n) (fun p => tensorFour (framedWord A p) x y) := by
  let Q := fourIndices (qubitIndices n)
  let left := transpose (tensorFour (fun s j => star (A s j)))
  let right := tensorFour A
  have term (p : Word n) : tensorFour (framedWord A p) =
      matMul Q (matMul Q left (tensorFour (wordEntry imaginaryUnit p))) right := by
    unfold framedWord
    rw [fourMatMul, fourMatMul, fourTranspose, ←matMulAssoc]
  change _ * matMul Q (matMul Q left (unnormalizedTwirl imaginaryUnit)) right x y = _
  congr 1
  simp only [term, matMul,unnormalizedTwirl,sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap (words n) Q]
  apply sumOverCongr
  intro b
  rw [sumOverSwap (words n) Q]

def sourceTuple (w : Wedge7) : Four (Fin 7) := ((w.i,w.j),(w.k,w.m))

/-- Increasing-coordinate matrix entry on the antisymmetric fourth tensor power. -/
def exteriorSector (T : Four (Fin 7) → Four (Fin 7) → C) (u v : Wedge7) : C :=
  sumOver permutations (fun p => signed (oddPermutation p) (T (sourceTuple u) (reorder (sourceTuple v) p)))

theorem tensorExteriorSector (M : Fin 7 → Fin 7 → C) (u v : Wedge7) :
    exteriorSector (tensorFour M) u v = minor4 M (sourceSite u) v := by
  have one (p : Permutation) :
      tensorFour M (sourceTuple u) (reorder (sourceTuple v) p) =
        M (sourceSite u 0) (sourceSite v p.1.1) * M (sourceSite u 1) (sourceSite v p.1.2) *
        M (sourceSite u 2) (sourceSite v p.2.1) * M (sourceSite u 3) (sourceSite v p.2.2) := by
    unfold tensorFour tensor
    simp only [Semiring.mul_assoc]
    rfl
  apply sumOverCongr
  intro p
  rw [one]
  rfl

private theorem signSum (b : Bool) (xs : List α) (f : α → C) :
    signed b (sumOver xs f) = sumOver xs (fun i => signed b (f i)) := by
  induction xs with
  | nil => cases b <;> simp [signed,sumOver] <;> grind
  | cons a xs ih =>
    change signed b (f a + sumOver xs f) = signed b (f a) + sumOver xs (fun i => signed b (f i))
    rw [← ih]
    cases b <;> simp [signed] <;> grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem frameTwirl_exteriorSector (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (u v : Wedge7) :
    exteriorSector (frameTwirl half A) u v =
      (ofReal half)^(n+n) * sumOver (words n) (fun p => minor4 (framedWord A p) (sourceSite u) v) := by
  simp only [exteriorSector,frameTwirl_words,←tensorExteriorSector, sumOverMulLeft,exteriorSector,signSum]
  rw [sumOverSwap permutations (words n)]
  apply sumOverCongr
  intro p
  apply sumOverCongr
  intro perm
  cases oddPermutation perm <;> simp [signed] <;> grind

/-- Recover a complex entry from the two real coordinate fields. -/
def effectEntry (half : R) (halfUnit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (u v : Wedge7) : ComplexScalar R :=
  ⟨(physicalEntries half halfUnit k A).realPart u v, (physicalEntries half halfUnit k A).imagPart u v⟩

/-- Exact normalization relating the exterior block of the full frame twirl
and the matrix used by the rank-seven effect and crossed cut bounds. -/
theorem normalizedSector_eq_physicalEntry (half : R) (halfUnit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    ofReal (inverseWeight R k) * exteriorSector (frameTwirl half A) u v = effectEntry half halfUnit k A u v := by
  rw [frameTwirl_exteriorSector, framedWordMinor_sum]
  change _ = ExteriorCompressionEffect.normalizedMatrix _ _ _ _ u v
  rw [ExteriorCompressionEffect.normalizedMatrix_entry]
  congr 1
  apply sumOverCongr
  intro r
  apply sumOverCongr
  intro s
  rw [PhysicalExteriorCompression.physicalKernel_eq half halfUnit,
    PhysicalExteriorCompression.normalizedComplexEntry half halfUnit]

/-- The exterior block equals the physical effect multiplied by its exact
scale, equivalently four divided by the one-particle ambient dimension. -/
theorem sector_eq_weight_mul_physicalEntry (half : R) (halfUnit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    exteriorSector (frameTwirl half A) u v =
      ofReal (PhysicalChartRestriction.weight half (k+3)) * effectEntry half halfUnit k A u v := by
  rw [← normalizedSector_eq_physicalEntry, ← Semiring.mul_assoc]
  have unit := PhysicalExteriorCompression.inverseWeight_mul_weight half halfUnit k
  have product : ofReal (PhysicalChartRestriction.weight half (k+3)) * ofReal (inverseWeight R k) =
      (1 : ComplexScalar R) := by
    apply ComplexScalar.ext <;> simp <;> grind
  rw [product, Semiring.one_mul]

theorem exteriorSector_scale (c : C) (T : Four (Fin 7) → Four (Fin 7) → C) (u v : Wedge7) :
    exteriorSector (fun x y => c * T x y) u v = c * exteriorSector T u v := by
  unfold exteriorSector
  rw [sumOverMulLeft]
  apply sumOverCongr
  intro p
  cases oddPermutation p <;> simp [signed] <;> grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- The fourth-copy projector normalization contributes one more inverse
ambient dimension than the local factor in the rectangular purity trace. -/
theorem frameTwirl_eq_normalizedFrame (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) :
    frameTwirl half A = (fun x y => ofReal (half^n) * RectangularPairedReduction.normalizedFrame half A x y) := by
  funext x y
  change (ofReal half)^(n+n) * PhysicalPairedReduction.frameTwirl A x y =
    ofReal (half^n) * (ofReal (half^n) * PhysicalPairedReduction.frameTwirl A x y)
  rw [Semiring.pow_add,PhysicalPairedReduction.realEmbeddingPow,Semiring.mul_assoc]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem dimensionScale (half : R) (halfUnit : 2*half=1) (n : Nat) :
    ofReal ((2:R)^n) * ofReal (half^n) = (1 : ComplexScalar R) := by
  rw [PhysicalPairedReduction.realEmbeddingPow, PhysicalPairedReduction.realEmbeddingPow, ←CommSemiring.mul_pow]
  have pair : ofReal (2:R) * ofReal half = (1 : ComplexScalar R) := by
    apply ComplexScalar.ext <;> simp <;> grind
  rw [pair, Semiring.one_pow]

/-- With the rectangular purity-trace normalization the fourth exterior
block equals exactly four times the normalized physical compression. -/
theorem normalizedFrameSector_eq_four_effectEntry (half : R) (halfUnit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    exteriorSector (RectangularPairedReduction.normalizedFrame half A) u v =
      ofReal (4:R) * effectEntry half halfUnit k A u v := by
  have h := sector_eq_weight_mul_physicalEntry half halfUnit k A u v
  rw [frameTwirl_eq_normalizedFrame, exteriorSector_scale] at h
  have weight : ofReal (PhysicalChartRestriction.weight half (k+3)) =
      ofReal (half^(k+3)) * ofReal (4:R) := by
    apply ComplexScalar.ext <;> simp [PhysicalChartRestriction.weight] <;> grind
  rw [weight, Semiring.mul_assoc] at h
  have scaled := congrArg (fun t => ofReal ((2:R)^(k+3))*t) h
  simpa only [←Semiring.mul_assoc,dimensionScale half halfUnit,Semiring.one_mul] using scaled

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem realSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x + sumOver xs f).re = (f x).re + sumOver xs (fun a => (f a).re)
    rw [ComplexScalar.re_add, ih]

/-- The paired trace in the increasing exterior coordinates carries exactly
the factor sixteen multiplying the spectral quadratic trace. This applies
in particular to the diagonal of fourth Schmidt amplitudes. -/
theorem physicalWedgeTrace_eq_spectral (half : R) (halfUnit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (a : Wedge7 → R) :
    (pairedFrameTrace wedges (PhysicalPairedReduction.diagonal a)
      (exteriorSector (RectangularPairedReduction.normalizedFrame half A))
      (exteriorSector (RectangularPairedReduction.normalizedFrame half A))).re =
      16 * (physicalEntries half halfUnit k A).realQuadraticTrace wedges a := by
  rw [PhysicalPairedReduction.pairedTraceDiagonal wedges wedgesNodup memWedges]
  simp only [realSum,normalizedFrameSector_eq_four_effectEntry half halfUnit k A]
  unfold Compression.HermitianEntries.realQuadraticTrace
  simp only [sumOverMulLeft]
  apply sumOverCongr
  intro u
  apply sumOverCongr
  intro v
  simp only [ComplexScalar.re_mul,ComplexScalar.im_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal,
    effectEntry]
  grind

end Ordered
end RankSeven.FrameExteriorSector

#print axioms RankSeven.FrameExteriorSector.framedWordMinor
#print axioms RankSeven.FrameExteriorSector.normalizedSector_eq_physicalEntry
#print axioms RankSeven.FrameExteriorSector.sector_eq_weight_mul_physicalEntry
#print axioms RankSeven.FrameExteriorSector.normalizedFrameSector_eq_four_effectEntry
#print axioms RankSeven.FrameExteriorSector.physicalWedgeTrace_eq_spectral
