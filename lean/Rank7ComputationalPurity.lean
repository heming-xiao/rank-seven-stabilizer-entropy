import Rank7SectorDefectAccounting
import Rank7RectangularPairedReduction

/-! Direct evaluation of the computational stabilizer purity by the physical
three-qubit Pauli trace and its common-translation support. -/
namespace RankSeven.ComputationalPurity

open Lean.Grind Pauli PhysicalPairedReduction RectangularPairedReduction SectorDefectAccounting
open ComplexScalar (ofReal star imaginaryUnit)
open ExteriorCuts (Wedge7 wedges amplitude product4)
open GenericExteriorKernel (parity position)
open HyperplaneIncidence (zero)

variable {R C α : Type} [CommRing R] [CommRing C]

private abbrev Site := Basis 3
private abbrev Row := Four Site
private local instance : DecidableEq Site := HyperplaneInduction.cubeDecEq 3
private def sites := qubitIndices 3
private def rows := fourIndices sites
private def shift (t : Site) (u : Row) : Row := PhysicalWedges.mapFourSites (xorBasis 3 t) u
private def labels (u : Row) : List Nat :=
  [PlaneOrientation.label 3 u.1.1, PlaneOrientation.label 3 u.1.2,
    PlaneOrientation.label 3 u.2.1, PlaneOrientation.label 3 u.2.2]
private def present (u : Row) : Bool := (labels u).all (fun i => decide (i<7))
private def activeRow (u : Row) : Bool := decide (parity u = zero 3) && present u

private def insert (i : Nat) : List Nat → List Nat
  | [] => [i]
  | a :: as => if i ≤ a then i :: a :: as else a :: insert i as
private def sorted (xs : List Nat) := xs.foldr insert []

/-- Degree-eight monomials supplied by ordered zero-parity tuples and
their common shifts that stay within the seven computational sites. -/
private def physicalTerms : List (List Nat) :=
  (rows.filter activeRow).flatMap (fun u =>
    (sites.filter (fun t => present (shift t u))).map (fun t => sorted (labels u ++ labels (shift t u))))

private def indices := List.finRange 7
private def single (i : Fin 7) : List Nat := List.replicate 8 i.val
private def pair (ij : Fin 7 × Fin 7) : List Nat :=
  sorted (List.replicate 4 ij.1.val ++ List.replicate 4 ij.2.val)
private def plane (w : Wedge7) : List Nat := sorted [w.i.val,w.j.val,w.k.val,w.m.val,w.i.val,w.j.val,w.k.val,w.m.val]

private def countedTerms : List (List Nat) :=
  indices.map single ++ (wedgePairs indices).flatMap (fun ij => List.replicate 14 (pair ij)) ++
    (wedges.filter planeFlag).flatMap (fun w => List.replicate 168 (plane w))

/-- Group monomials by their support; permutation invariance holds for any list. -/
private def bucket : Nat → List (List Nat) → List (List Nat)
  | 0, xs => xs
  | n+1, xs => bucket n (xs.filter (fun m => m.contains n)) ++
      bucket n (xs.filter (fun m => !(m.contains n)))

private theorem bucketPerm (n : Nat) (xs : List (List Nat)) : (bucket n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    exact ((ih _).append (ih _)).trans (List.filter_append_perm (fun m => m.contains n) xs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem monomialTable : bucket 7 physicalTerms = bucket 7 countedTerms := by decide

private theorem monomialPerm : physicalTerms.Perm countedTerms := by
  apply (bucketPerm 7 physicalTerms).symm.trans
  rw [monomialTable]
  exact bucketPerm 7 countedTerms

private def extend (mu : Fin 7 → R) (i : Nat) : R := if h : i < 7 then mu ⟨i,h⟩ else 0
private def weight (mu : Fin 7 → R) (s : Site) := extend mu (PlaneOrientation.label 3 s)
private def value (mu : Fin 7 → R) : List Nat → R
  | [] => 1
  | x::xs => extend mu x * value mu xs

private theorem valueInsert (mu : Fin 7 → R) (i : Nat) (xs : List Nat) :
    value mu (insert i xs) = extend mu i * value mu xs := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [insert]; split <;> simp only [value,ih] <;> grind

private theorem valueSorted (mu : Fin 7 → R) (xs : List Nat) : value mu (sorted xs) = value mu xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change value mu (insert i (sorted xs)) = _
    rw [valueInsert,ih]; rfl

private theorem valueLabels (mu : Fin 7 → R) (u v : Row) :
    value mu (sorted (labels u ++ labels v)) = fourWeights (weight mu) u * fourWeights (weight mu) v := by
  rw [valueSorted]
  simp [labels,value,fourWeights,weight,Semiring.mul_one,Semiring.mul_assoc]

private theorem zeroOutside (mu : Fin 7 → R) (u : Row) (no : present u = false) : fourWeights (weight mu) u = 0 := by
  simp only [present, labels,List.all_cons,List.all_nil,Bool.and_true] at no
  unfold fourWeights weight extend
  split <;> split <;> split <;> split <;> simp_all <;> grind

private theorem sumMap (xs : List α) (g : α → β) (f : β → C) :
    sumOver (xs.map g) f = sumOver xs (fun x => f (g x)) := by
  simp only [sumOver,List.map_map,Function.comp_def]

private theorem sumFilter (xs : List α) (keep : α → Bool) (f : α → C) :
    sumOver (xs.filter keep) f = sumOver xs (fun x => if keep x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : keep x
    · simp only [List.filter_cons,h,ite_false,Bool.false_eq_true]
      change sumOver (xs.filter keep) f = _ + sumOver xs _
      rw [ih]; grind
    · simp only [List.filter_cons,h,ite_true]
      change f x + sumOver (xs.filter keep) f = _ + sumOver xs _
      rw [ih]; grind

private theorem sumZero (xs : List α) : sumOver xs (fun _ => (0:C)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change 0 + sumOver xs _ = 0; rw [ih]; grind

private theorem sumPerm {xs ys : List α} (p : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ a b => exact a.trans b

private theorem rowComplete (r : Row) : r ∈ rows :=
  HyperplaneInduction.pairMember
    (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
    (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))

private theorem rowNodup : rows.Nodup := by
  have nd := HyperplaneIncidence.normalsNodup 3
  have pairs := HyperplaneInduction.pairsNodup _ _ nd nd
  exact HyperplaneInduction.pairsNodup _ _ pairs pairs

private theorem xorComm (n : Nat) (a b : Basis n) : xorBasis n a b = xorBasis n b a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xorBasis,Bool.xor_comm a.1 b.1,ih a.2 b.2]; rfl

private theorem shiftInjective (u : Row) (s t : Site) (eq : shift s u = shift t u) : s=t := by
  have h := congrArg (fun v : Row => v.1.1) eq
  change xorBasis 3 s u.1.1 = xorBasis 3 t u.1.1 at h
  rw [xorComm 3 s, xorComm 3 t] at h
  have inv := congrArg (xorBasis 3 u.1.1) h
  simpa only [HyperplaneIncidence.xorCancelLeft] using inv

private theorem supportShift (u v : Row) :
    allowedTwirlEntry 3 u v = true ↔ parity u = zero 3 ∧ ∃ t : Site, shift t u = v := by
  rw [GenericExteriorKernel.allowed_iff_translation]
  apply and_congr_right; intro _
  constructor
  · rintro ⟨t,h⟩
    exact ⟨t,(Prod.ext (Prod.ext (h 0) (h 1)) (Prod.ext (h 2) (h 3))).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,PhysicalWedges.mapFourPosition _ u⟩

private theorem sumRow (u : Row) (f : Row → R) :
    sumOver rows (fun v => if allowedTwirlEntry 3 u v then f v else 0) =
      if parity u = zero 3 then sumOver sites (fun t => f (shift t u)) else 0 := by
  classical
  by_cases par : parity u = zero 3
  · rw [ite_eq_left par]
    have singleTerm (v : Row) : (if allowedTwirlEntry 3 u v then f v else 0) =
        sumOver sites (fun t => if shift t u = v then f v else 0) := by
      by_cases yes : ∃ t : Site, shift t u=v
      · obtain ⟨t,ht⟩ := yes
        have each (s : Site) : shift s u=v ↔ t=s := by
          rw [←ht]; exact ⟨fun e => (shiftInjective u s t e).symm,fun e => e ▸ rfl⟩
        simp only [each, (supportShift u v).mpr ⟨par,t,ht⟩, ite_true]
        exact (ExteriorPauliBase.sumOnIndex sites t (fun _ => f v) (HyperplaneIncidence.normalsNodup _) (qubitIndicesComplete _)).symm
      · have bad : allowedTwirlEntry 3 u v ≠ true := fun e => yes ((supportShift u v).mp e).2
        have none (t : Site) : shift t u≠v := fun e => yes ⟨t,e⟩
        simp [bad,none,sumZero]
    rw [sumOverCongr _ singleTerm,sumOverSwap rows sites]
    apply sumOverCongr; intro t
    exact ExteriorPauliBase.sumOnIndex rows _ f rowNodup (rowComplete _)
  · have none (v : Row) : allowedTwirlEntry 3 u v ≠ true := fun e => par ((supportShift u v).mp e).1
    simp [par,none,sumZero]

private theorem physicalValue (mu : Fin 7 → R) :
    sumOver rows (fun u => sumOver rows (fun v => if allowedTwirlEntry 3 u v then
      fourWeights (weight mu) u * fourWeights (weight mu) v else 0)) = sumOver physicalTerms (value mu) := by
  simp only [sumRow, physicalTerms, sumOverFlatMap, sumFilter, sumMap, valueLabels]
  apply sumOverCongr; intro u
  by_cases p : parity u = zero 3
  · cases h : present u
    · simp [activeRow,p,h,zeroOutside mu u h,Semiring.zero_mul,sumZero]
    · simp only [activeRow,p,h,decide_true,Bool.and_self,ite_true]
      apply sumOverCongr; intro t
      cases valid : present (shift t u)
      · simp [zeroOutside mu _ valid, Semiring.mul_zero]
      · rfl
  · simp [activeRow,p]

private theorem baseDiagonal (mu : Fin 7 → R) :
    computationalCoefficients 0 0 mu = diagonal (weight mu) := by
  funext a b
  unfold computationalCoefficients rankSevenCoefficients
  by_cases valid : PlaneOrientation.label 3 a < 7
  · let i : Fin 7 := ⟨_,valid⟩
    have pick (j : Fin 7) : PlaneOrientation.label 3 a = j.val ↔ i=j :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    have head (j : Fin 7) : ofReal (mu j) * computationalFrame 0 a j * computationalFrame 0 b j =
        if i=j then ofReal (mu j) * computationalFrame 0 b j else 0 := by
      change _ * (if PlaneOrientation.label 3 a = j.val then 1 else 0) * _ = _
      simp only [pick]
      by_cases eq : i=j <;> simp [eq,Semiring.mul_one,Semiring.mul_zero,Semiring.zero_mul]
    rw [sumOverCongr _ head,ExteriorPauliBase.sumOnIndex _ i _ (by decide) (List.mem_finRange _)]
    have both : PlaneOrientation.label 3 b = i.val ↔ a=b :=
      ⟨fun e => PlaneOrientation.labelInjective 3 _ _ e.symm,fun e => congrArg (PlaneOrientation.label 3) e.symm⟩
    change _ * (if PlaneOrientation.label 3 b = i.val then 1 else 0) = _
    by_cases eq : a=b
    · rw [ite_eq_left (both.mpr eq),Semiring.mul_one]
      simp only [diagonal,ite_eq_left eq,weight,extend,dite_eq_left valid]
      rfl
    · rw [ite_eq_right (fun e => eq (both.mp e)),Semiring.mul_zero]
      simp only [diagonal,ite_eq_right eq]
  · have no (j : Fin 7) : PlaneOrientation.label 3 a ≠ j.val := by intro h; exact valid (h ▸ j.isLt)
    simp only [computationalFrame, no, ite_false, Semiring.mul_zero, Semiring.zero_mul,sumZero]
    simp [diagonal,weight,extend,valid,show ofReal (0:R) = 0 from rfl]

private theorem realSum (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x + sumOver xs f).re = (f x).re + sumOver xs (fun a => (f a).re)
    rw [ComplexScalar.re_add, ih]

private theorem sumAppend (xs ys : List α) (f : α → C) :
    sumOver (xs ++ ys) f = sumOver xs f + sumOver ys f := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons x xs ih =>
    simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *
    grind

private theorem valueAppend (mu : Fin 7 → R) (xs ys : List Nat) :
    value mu (xs++ys) = value mu xs * value mu ys := by
  induction xs with
  | nil => simp [value,Semiring.one_mul]
  | cons i xs ih => simp only [List.cons_append,value,ih,Semiring.mul_assoc]

private theorem valueRepeat (mu : Fin 7 → R) (n : Nat) (i : Fin 7) :
    value mu (List.replicate n i.val) = (mu i)^n := by
  induction n with
  | zero => simp [value,Semiring.pow_zero]
  | succ n ih =>
    simp only [List.replicate_succ,value,extend,i.isLt,dite_true,ih,Semiring.pow_succ]
    grind

attribute [local instance] Semiring.natCast

private theorem sumRepeat (n : Nat) (x : α) (f : α → R) :
    sumOver (List.replicate n x) f = (n : R) * f x := by
  induction n with
  | zero => change 0 = _; grind
  | succ n ih =>
    rw [List.replicate_succ]
    change f x + sumOver (List.replicate n x) f = _
    rw [ih,Semiring.natCast_succ]; grind

private theorem countedValue (mu : Fin 7 → R) :
    sumOver countedTerms (value mu) = computationalValue indices mu (amplitude mu) := by
  have ex (i : Fin 7) : extend mu i.val = mu i := by simp [extend]
  have eachPlane (w : Wedge7) : value mu (plane w) = (amplitude mu w)^2 := by
    simp only [plane,valueSorted,value,ex,amplitude,product4]
    grind
  simp only [countedTerms,sumAppend,sumMap,sumOverFlatMap,sumRepeat,single,pair,valueSorted,valueAppend,
    valueRepeat,eachPlane,←sumOverMulLeft,sumFilter]
  unfold computationalValue spectralInvariant
  rw [cbOverlap]
  have counts := wedgePairTrace indices (fun i => (mu i)^4)
  have square (i : Fin 7) : ((mu i)^4)^2=(mu i)^8 := by grind
  simp only [square] at counts
  grind

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The actual squared Pauli trace on the computational diagonal selects
zero-parity tuples with a common translate, with unit weight on its support. -/
theorem basePurity_support (half : R) (unit : 2*half=1) (mu : Fin 7 → R) :
    purity half (computationalCoefficients 0 0 mu) =
      sumOver rows (fun u => sumOver rows (fun v => if allowedTwirlEntry 3 u v then
        fourWeights (weight mu) u * fourWeights (weight mu) v else 0)) := by
  rw [baseDiagonal]
  let h := weight mu
  let J : Row → Row → ComplexScalar R := unnormalizedTwirl imaginaryUnit
  have jt : transpose J = J := by funext a b; exact unnormalizedTwirlTranspose _ _ _
  have e := purityComplex half (diagonal h)
  rw [normalizedPauliMoment] at e
  rw [diagonalReal,pauliMomentEqTrace,tensorDiagonal,coefficientTraceMatMul,diagonalSymmetric,
    show transpose (unnormalizedTwirl (n:=3) (imaginaryUnit (R := R))) = J from jt] at e
  change ofReal _ = (ofReal half)^6 * pairedFrameTrace rows (diagonal (fourWeights h)) J J at e
  rw [pairedTraceDiagonal rows rowNodup rowComplete] at e
  simp only [sumOverMulLeft] at e
  have two : (2:ComplexScalar R) * ofReal half = 1 := by
    change ofReal (2:R) * ofReal half = ofReal (1:R)
    apply ComplexScalar.ext <;> simp <;> grind
  have norm : (ofReal half)^6 * ((2:ComplexScalar R)^3)^2=1 := by
    have h6 := congrArg (fun t : ComplexScalar R => t^6) two
    simp only [CommSemiring.mul_pow,Semiring.one_pow] at h6
    grind
  have entry (a b : Row) :
      (ofReal half)^6 * (ofReal (fourWeights h a) * J a b * ofReal (fourWeights h b) * J b a) =
        ofReal (if allowedTwirlEntry 3 a b then fourWeights h a * fourWeights h b else 0) := by
    change _ * (_ * unnormalizedTwirl imaginaryUnit a b * _ * unnormalizedTwirl imaginaryUnit b a) = _
    rw [unnormalizedTwirlTranspose imaginaryUnit a b,unnormalizedTwirlEntry _ ComplexScalar.imaginaryUnit_fourth]
    cases ha : allowedTwirlEntry 3 a b
    · simp [Semiring.mul_zero,Semiring.zero_mul]; rfl
    · simp only [ite_true]
      calc
        _ = ((ofReal half)^6 * ((2:ComplexScalar R)^3)^2) * (ofReal (fourWeights h a) * ofReal (fourWeights h b)) := by grind
        _ = _ := by rw [norm,Semiring.one_mul]; apply ComplexScalar.ext <;> simp <;> grind
  simp only [entry] at e
  have re := congrArg ComplexScalar.re e
  simpa only [realSum,ComplexScalar.re_ofReal,h] using re

/-- The actual stabilizer purity of the computational Schmidt state equals
the closed computational spectral value in every pair of admissible ambient
dimensions. The real amplitudes may have arbitrary signs. -/
theorem computationalPurity_eq_value (half : R) (unit : 2*half=1) (m n : Nat) (mu : Fin 7 → R) :
    purity half (computationalCoefficients m n mu) =
      computationalValue (List.finRange 7) mu (amplitude mu) := by
  rw [computationalPurityInvariant half (by grind) m n mu,basePurity_support half unit,physicalValue,
    sumPerm monomialPerm, countedValue] <;> rfl

/-- The nonzero monomials have multiplicity one for eight copies of a
single label, fourteen for two labels of multiplicity four, and 168 for an
affine plane with all four labels of multiplicity two. -/
theorem computationalPurity_polynomial (half : R) (unit : 2*half=1) (m n : Nat) (mu : Fin 7 → R) :
    purity half (computationalCoefficients m n mu) =
      sumOver (List.finRange 7) (fun i => (mu i)^8) +
        14 * sumOver (wedgePairs (List.finRange 7)) (fun ij => (mu ij.1)^4 * (mu ij.2)^4) +
        168 * sumOver wedges (fun w => if planeFlag w then (amplitude mu w)^2 else 0) := by
  rw [computationalPurity_eq_value half unit, computationalValue, spectralInvariant, cbOverlap]
  have count := wedgePairTrace (List.finRange 7) (fun i => (mu i)^4)
  have square (i : Fin 7) : ((mu i)^4)^2=(mu i)^8 := by grind
  simp only [square] at count
  grind

end Order
end RankSeven.ComputationalPurity

#print axioms RankSeven.ComputationalPurity.computationalPurity_eq_value
#print axioms RankSeven.ComputationalPurity.computationalPurity_polynomial
