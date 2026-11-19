import Rank7SectorDefectAccounting
import Rank7FourCopySectors
import Rank7FrameExteriorSector

/-! Ordered-pair Pauli Fourier square certificate for the symmetric
four-copy defect. All Pauli coefficients use physical word matrices. -/
namespace RankSeven.SymmetricDefect

open Lean.Grind Pauli
open ComplexScalar (ofReal star imaginaryUnit)

def axisAnti (p r : Axis) : Bool :=
  p != .identity && r != .identity && p != r

def anti : {n : Nat} → Word n → Word n → Bool
  | _, .empty, .empty => false
  | _, .cons p ps, .cons r rs => (axisAnti p r) ^^ (anti ps rs)

variable {C R : Type} [CommRing C] [CommRing R]

def phase (b : Bool) : C := if b then -1 else 1

def chi {n : Nat} (p r : Word n) : C := phase (anti p r)

private theorem phaseXor (a b : Bool) : phase (a^^b) = (phase a : C)*phase b := by
  cases a <;> cases b <;> simp [phase] <;> grind

theorem chiCons {n : Nat} (p r : Axis) (ps rs : Word n) :
    chi (.cons p ps) (.cons r rs) = (phase (axisAnti p r) : C)*chi ps rs := by
  exact phaseXor _ _

theorem chiSymm {n : Nat} (p r : Word n) : chi p r = (chi r p : C) := by
  have symm : ∀ p r : Axis, axisAnti p r = axisAnti r p := by intro a b; cases a <;> cases b <;> rfl
  induction p with
  | empty => cases r; rfl
  | cons a p ih => cases r with
    | cons b r => rw [chiCons,chiCons,symm a b,ih r]

private theorem factorWords {n : Nat} (f : Word (n+1) → C) (head : Axis → C) (tail : Word n → C)
    (step : ∀ a p, f (.cons a p)=head a*tail p) :
    sumOver (words (n+1)) f =
    (head .identity+head .x+head .y+head .z)*sumOver (words n) tail := by
  rw [words,sumOverFlatMap,sumOverMulLeft]
  apply sumOverCongr; intro p
  simp only [sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons,step]
  grind

set_option maxHeartbeats 1200000 in
private theorem axisResolution (i : C) (isq : i^2= -1) (p : Axis) (a b c d : Bool) :
    let g (r : Axis) := phase (axisAnti p r)*entry i r a b*entry i r c d
    g .identity+g .x+g .y+g .z = 2*entry i p a d*entry i p c b := by
  cases p <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [axisAnti,phase,entry] <;> grind

/-- The signed Pauli completeness kernel, before contraction against A twice. -/
theorem signedResolution {n : Nat} (i : C) (isq : i^2= -1) (p : Word n) (a b c d : Basis n) :
    sumOver (words n) (fun r => chi p r*wordEntry i r a b*wordEntry i r c d) =
      (2:C)^n*wordEntry i p a d*wordEntry i p c b := by
  induction p with
  | empty => simp [words,sumOver,wordEntry,chi,anti,phase]; grind
  | cons p ps ih =>
    obtain ⟨a₀,a⟩ := a; obtain ⟨b₀,b⟩ := b; obtain ⟨c₀,c⟩ := c; obtain ⟨d₀,d⟩ := d
    let g r := phase (axisAnti p r)*entry i r a₀ b₀*entry i r c₀ d₀
    let tail r := chi ps r*wordEntry i r a b*wordEntry i r c d
    rw [factorWords _ g tail (by intro r rs; simp [g,tail,wordEntry,chiCons]; grind)]
    have h := axisResolution i isq p a₀ b₀ c₀ d₀
    change g .identity+g .x+g .y+g .z=_ at h
    rw [h]
    unfold tail
    rw [ih,Semiring.pow_succ]
    simp only [wordEntry]; grind

private theorem axisOrth (p q : Axis) :
    let f r := (phase (axisAnti r p) : C) * phase (axisAnti r q)
    f .identity+f .x+f .y+f .z = if p=q then 4 else 0 := by
  cases p <;> cases q <;> simp [axisAnti,phase] <;> grind

noncomputable local instance {n} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem characterOrthogonality {n : Nat} (p q : Word n) :
    sumOver (words n) (fun r => (chi r p : C)*chi r q) = if p=q then (4:C)^n else 0 := by
  induction p with
  | empty => cases q; simp [sumOver,words,chi,anti,phase]; grind
  | cons p ps ih =>
    cases q with
    | cons q qs =>
      let g r := (phase (axisAnti r p) : C)*phase (axisAnti r q)
      let tail r := (chi r ps : C)*chi r qs
      rw [factorWords _ g tail (by intro r rs; simp [g,tail,chiCons]; grind)]
      change (g .identity+g .x+g .y+g .z)*sumOver _ _=_
      have h := axisOrth (C:=C) p q
      change g .identity+g .x+g .y+g .z=_ at h
      rw [h]
      unfold tail; rw [ih]
      by_cases e : p=q <;> by_cases eq : ps=qs <;> simp [e,eq,Semiring.pow_succ] <;> grind

private theorem sumSelect {n : Nat} (p : Word n) (f : Word n → C) :
    sumOver (words n) (fun r => if p=r then f r else 0)=f p := by
  induction p with
  | empty => simp [words,sumOver]; grind
  | cons a p ih =>
    rw [words,sumOverFlatMap]
    calc
      _ = sumOver _ (fun r => if p=r then f (.cons a r) else 0) := by
        apply sumOverCongr; intro r
        cases a <;> by_cases h : p=r <;> simp [sumOver,h] <;> grind
      _ = _ := ih _

private theorem squareSum {α : Type} (xs : List α) (f : α → C) :
    (sumOver xs f)^2 = sumOver xs (fun x => sumOver xs (fun y => f x*f y)) := by
  calc
    _ = sumOver xs f*sumOver xs f := by grind
    _ = _ := by rw [sumOverMulRight]; apply sumOverCongr; intro i; exact sumOverMulLeft _ _ _

private theorem cycleSums {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ) (f : α → β → γ → C) :
    sumOver xs (fun i => sumOver ys (fun j => sumOver zs (f i j))) =
    sumOver ys (fun j => sumOver zs (fun k => sumOver xs (fun i => f i j k))) := by
  rw [sumOverSwap xs ys]
  apply sumOverCongr; intro j; exact sumOverSwap xs zs _

/-- Polarized finite Pauli Fourier Parseval for the exact physical word list. -/
theorem fourierParseval {n : Nat} (f : Word n → C) :
    sumOver (words n) (fun p => (sumOver (words n) (fun r => chi p r*f r))^2) =
      (4:C)^n * sumOver (words n) (fun r => (f r)^2) := by
  simp only [squareSum]
  rw [cycleSums,sumOverMulLeft]
  apply sumOverCongr; intro r
  calc
    _ = sumOver (words n) (fun s => (sumOver (words n) (fun p => (chi p r : C)*chi p s))* (f r*f s)) := by
      apply sumOverCongr; intro s; rw [sumOverMulRight]; apply sumOverCongr; intro p; grind
    _ = sumOver (words n) (fun s => if r=s then (4:C)^n*(f s)^2 else 0) := by
      apply sumOverCongr; intro s; rw [characterOrthogonality]
      by_cases e : r=s <;> simp [e] <;> grind
    _ = _ := sumSelect _ _

def physicalMatrix {n : Nat} (p : Word n) : Basis n → Basis n → ComplexScalar R :=
  wordEntry imaginaryUnit p

def squeezed {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (q : Word n) :=
  matMul (qubitIndices n) (matMul (qubitIndices n) N (physicalMatrix q)) N

def physicalCoeff {n : Nat} (A : Basis n → Basis n → ComplexScalar R) (p : Word n) : R :=
  (trace (qubitIndices n) (matMul (qubitIndices n) (physicalMatrix p) A)).re

def coeff {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (q p : Word n) : R :=
  physicalCoeff (squeezed N q) p

def unsignedSum {n : Nat} (f : Word n → Word n → R) : R :=
  sumOver (words n) (fun q => (sumOver (words n) (fun p => (f q p)^2))^2)

def signedSum {n : Nat} (f : Word n → Word n → R) : R :=
  sumOver (words n) (fun q => sumOver (words n) (fun p => sumOver (words n)
    (fun r => chi p r*(f q p)^2*(f q r)^2)))

/-- Ordered anticommuting pairs; each nonzero summand is a square of a
product of physical trace coefficients. -/
def antiSquares {n : Nat} (f : Word n → Word n → R) : R :=
  sumOver (words n) (fun q => sumOver (words n) (fun p => sumOver (words n)
    (fun r => if anti p r then (f q p*f q r)^2 else 0)))

theorem coefficientGap {n : Nat} (f : Word n → Word n → R) :
    unsignedSum f - signedSum f = 2*antiSquares f := by
  unfold unsignedSum signedSum antiSquares
  rw [← Compression.sumOverSub,sumOverMulLeft]
  apply sumOverCongr; intro q
  rw [squareSum,←Compression.sumOverSub,sumOverMulLeft]
  apply sumOverCongr; intro p
  rw [← Compression.sumOverSub,sumOverMulLeft]
  apply sumOverCongr; intro r
  unfold chi
  cases e : anti p r <;> simp [phase] <;> grind

theorem symmetricDefect_eq_squares {n : Nat} (N : Basis n → Basis n → ComplexScalar R)
    (d di : R) (inverse : d*di=1) (s : SectorDefectAccounting.SectorTerms R)
    (fourth : unsignedSum (coeff N)=d^2*s.pauliFourth)
    (sectors : signedSum (coeff N)=d^5*(s.symmetric-s.alternating)) :
    SectorDefectAccounting.symmetricDefect di s=2*di^5*antiSquares (coeff N) := by
  have h := coefficientGap (coeff N)
  rw [fourth,sectors] at h
  unfold SectorDefectAccounting.symmetricDefect
  grind

theorem physicalSquaresNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (N : Basis n → Basis n → ComplexScalar R) :
    0 ≤ antiSquares (coeff N) := by
  apply Compression.sumOverNonnegative; intro q _
  apply Compression.sumOverNonnegative; intro p _
  apply Compression.sumOverNonnegative; intro r _
  split
  · exact squareNonnegative _
  · grind

private theorem sumPairs {α β : Type} (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f = sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro x
  simp [sumOver,List.map_map,Function.comp_def]

/-- The exact complex coefficient Tr(AP). The equality of Tr(AP) and
Tr(PA) connects this convention to physicalCoeff. -/
def traceWord {n : Nat} (i : C) (A : Basis n → Basis n → C) (p : Word n) :=
  trace (qubitIndices n) (matMul (qubitIndices n) A (wordEntry i p))

def traceWordSquare {n : Nat} (i : C) (A : Basis n → Basis n → C) (p : Word n) :=
  let ap := matMul (qubitIndices n) A (wordEntry i p)
  trace (qubitIndices n) (matMul (qubitIndices n) ap ap)

/-- Contract the entrywise completeness kernel twice against an arbitrary
matrix A. This is the full signed Pauli Fourier trace identity (132). -/
theorem fourierTrace {n : Nat} (i : C) (isq : i^2= -1) (A : Basis n → Basis n → C) (p : Word n) :
    sumOver (words n) (fun r => chi p r*(traceWord i A r)^2) = (2:C)^n*traceWordSquare i A p := by
  let xs := qubitIndices n
  let pairs := productIndices xs xs
  let term (r : Word n) (ij : Basis n × Basis n) := A ij.1 ij.2*wordEntry i r ij.2 ij.1
  let X := wordEntry i p
  have single (r : Word n) : traceWord i A r=sumOver pairs (term r) := (sumPairs xs xs (term r)).symm
  calc
    _ = sumOver (words n) (fun r => sumOver pairs (fun u => sumOver pairs (fun v =>
          chi p r*term r u*term r v))) := by
      apply sumOverCongr; intro r; rw [single,squareSum,sumOverMulLeft]
      apply sumOverCongr; intro u; rw [sumOverMulLeft]; apply sumOverCongr; intro v; grind
    _ = sumOver pairs (fun u => sumOver pairs (fun v =>
        (2:C)^n*(A u.1 u.2*A v.1 v.2*X u.2 v.1*X v.2 u.1))) := by
      rw [cycleSums]; apply sumOverCongr; intro u; apply sumOverCongr; intro v
      have e := congrArg (fun z => (A u.1 u.2*A v.1 v.2)*z)
        (signedResolution i isq p u.2 u.1 v.2 v.1)
      simp only [sumOverMulLeft] at e
      calc
        _ = sumOver (words n) (fun r => A u.1 u.2*A v.1 v.2*
          (chi p r*wordEntry i r u.2 u.1*wordEntry i r v.2 v.1)) := by
            apply sumOverCongr; intro r; unfold term; grind
        _ = _ := by rw [e]; unfold X; grind
    _ = _ := by
      unfold pairs; simp only [sumPairs]
      unfold traceWordSquare trace matMul
      change _ = (2:C)^n*sumOver xs (fun a => sumOver xs (fun c =>
        (sumOver xs (fun b => A a b*X b c))*(sumOver xs (fun d => A c d*X d a))))
      rw [sumOverMulLeft]; apply sumOverCongr; intro a
      rw [sumOverSwap xs xs,sumOverMulLeft]; apply sumOverCongr; intro c
      rw [sumOverMulRight,sumOverMulLeft]; apply sumOverCongr; intro b
      rw [sumOverMulLeft,sumOverMulLeft]; apply sumOverCongr; intro d; grind

private theorem powerFour (n : Nat) : ((2:C)^n)^2 = (4:C)^n := by
  induction n with
  | zero => grind
  | succ n ih => simp only [Semiring.pow_succ]; grind

/-- Pauli fourth moment trade (133) for an arbitrary matrix; characteristic
division is carried by the chosen inverse of the physical qubit dimension. -/
theorem fourthMomentTrade {n : Nat} (i : C) (isq : i^2= -1) (A : Basis n → Basis n → C)
    (di : C) (inverse : (2:C)^n*di=1) :
    sumOver (words n) (fun p => (traceWordSquare i A p)^2) =
      sumOver (words n) (fun p => (traceWord i A p)^4) := by
  let d := (2:C)^n
  let f (r : Word n) := (traceWord i A r)^2
  have h := fourierParseval f
  have t (p : Word n) : (sumOver (words n) (fun r => chi p r*f r))^2 =
      d^2*(traceWordSquare i A p)^2 := by
    unfold f; rw [fourierTrace i isq]; unfold d; grind
  rw [sumOverCongr _ t,←sumOverMulLeft,←powerFour n] at h
  have pow (p : Word n) : (f p)^2 = (traceWord i A p)^4 := by unfold f; grind
  rw [sumOverCongr _ pow] at h
  change d*di=1 at inverse
  change d^2*_=d^2*_ at h
  grind

def unitWord : (n : Nat) → Word n
  | 0 => .empty
  | n+1 => .cons .identity (unitWord n)

local instance {n} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem chiUnit {n : Nat} (r : Word n) : chi (unitWord n) r = (1:C) := by
  induction r with
  | empty => rfl
  | cons a w ih => rw [unitWord,chiCons,ih]; cases a <;> simp [phase,axisAnti] <;> grind

private theorem identityEntry (i : C) (n : Nat) (x y : Basis n) :
    wordEntry i (unitWord n) x y=if x=y then 1 else 0 := by
  induction n with
  | zero => cases x; cases y; simp [unitWord,wordEntry]; grind
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    have h := ih x y
    cases a <;> cases b <;> by_cases e : x=y <;> simp [unitWord,wordEntry,entry,h,e] <;> grind

private theorem identityRight {n : Nat} (i : C) (A : Basis n → Basis n → C) :
    matMul (qubitIndices n) A (wordEntry i (unitWord n))=A := by
  funext a b; unfold matMul
  calc
    _ = sumOver (qubitIndices n) (fun z => if b=z then A a z else 0) := by
      apply sumOverCongr; intro z; rw [identityEntry]; by_cases e : b=z
      · subst z; simp; grind
      · simp [e,Ne.symm e]; grind
    _ = _ := ExteriorPauliBase.sumOnIndex _ _ _ (HyperplaneIncidence.normalsNodup _) (qubitIndicesComplete b)

theorem pauliParseval {n : Nat} (i : C) (isq : i^2= -1) (A : Basis n → Basis n → C) :
    sumOver (words n) (fun r => (traceWord i A r)^2) =
      (2:C)^n*trace (qubitIndices n) (matMul (qubitIndices n) A A) := by
  simpa only [chiUnit,Semiring.one_mul,traceWordSquare,identityRight] using fourierTrace i isq A (unitWord n)

private theorem rotateSquare {α : Type} (xs : List α) (N Q : α → α → C) :
    let A := matMul xs (matMul xs N Q) N
    let B := matMul xs (matMul xs N N) Q
    trace xs (matMul xs A A) = trace xs (matMul xs B B) := by
  dsimp only
  simp only [matMulAssoc]
  rw [traceMatMulSwap xs xs N]
  simp only [matMulAssoc]
  rw [traceMatMulSwap xs xs Q]
  simp only [matMulAssoc]

/-- The unsigned fourth source is a spectral Pauli fourth moment, directly
from physical trace sums; no positivity or Fourier hypothesis is used. -/
theorem unsignedComplex {n : Nat} (i : C) (isq : i^2= -1) (N : Basis n → Basis n → C)
    (di : C) (inverse : (2:C)^n*di=1) :
    sumOver (words n) (fun q =>
      (sumOver (words n) (fun p => (traceWord i
        (matMul (qubitIndices n) (matMul (qubitIndices n) N (wordEntry i q)) N) p)^2))^2) =
      ((2:C)^n)^2 * sumOver (words n) (fun p =>
        (traceWord i (matMul (qubitIndices n) N N) p)^4) := by
  let xs := qubitIndices n
  let N2 := matMul xs N N
  rw [←fourthMomentTrade i isq N2 di inverse,sumOverMulLeft]
  apply sumOverCongr; intro q
  rw [pauliParseval i isq,rotateSquare]
  unfold traceWordSquare N2 xs; grind

private theorem embedMul (x y : R) : ofReal (x*y)=ofReal x * ofReal y := by
  apply ComplexScalar.ext <;> simp <;> grind

private theorem embedSum {α : Type} (xs : List α) (f : α → R) :
    ofReal (sumOver xs f)=sumOver xs (fun x => ofReal (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ofReal (f x+sumOver xs f)=ofReal (f x)+sumOver xs _
    rw [←ih]
    apply ComplexScalar.ext <;> simp <;> grind

private theorem daggerWord {n : Nat} (p : Word n) :
    PhysicalPairedReduction.dagger (physicalMatrix (R:=R) p)=physicalMatrix p := by
  funext u v; exact ComplexPauliMoment.wordHermitian p v u

private theorem daggerSqueezed {n : Nat} (N : Basis n → Basis n → ComplexScalar R)
    (herm : PhysicalPairedReduction.dagger N=N) (q : Word n) :
    PhysicalPairedReduction.dagger (squeezed N q)=squeezed N q := by
  unfold squeezed
  rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerProduct,herm,daggerWord,matMulAssoc]

private theorem traceDagger {α : Type} (xs : List α) (B : α → α → ComplexScalar R) :
    star (trace xs B)=trace xs (PhysicalPairedReduction.dagger B) :=
  ComplexExterior.starSumOver xs _

private theorem realTraceWord [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (A : Basis n → Basis n → ComplexScalar R) (herm : PhysicalPairedReduction.dagger A=A) (p : Word n) :
    ofReal (physicalCoeff A p)=traceWord imaginaryUnit A p := by
  let xs := qubitIndices n
  let P := physicalMatrix (R:=R) p
  let z := trace xs (matMul xs P A)
  have real : star z=z := by
    unfold z; rw [traceDagger,PhysicalPairedReduction.daggerProduct,herm,daggerWord,traceMatMulSwap xs xs A]
  have im := congrArg ComplexScalar.im real
  rw [ComplexScalar.im_star] at im
  have iz : z.im=0 := by grind
  change ofReal z.re=trace xs (matMul xs A P)
  rw [traceMatMulSwap xs xs A]
  exact ComplexScalar.ext rfl iz.symm

/-- Scalar equality for the actual real traces of Hermitian physical matrices.
It discharges the unsigned trace input of symmetricDefect_eq_squares. -/
theorem unsignedPhysical [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (half : R) (unit : 2*half=1) (N : Basis n → Basis n → ComplexScalar R)
    (herm : PhysicalPairedReduction.dagger N=N) :
    unsignedSum (coeff N)=((2:R)^n)^2 *
      sumOver (words n) (fun p => (physicalCoeff (matMul (qubitIndices n) N N) p)^4) := by
  let N2 := matMul (qubitIndices n) N N
  have hn2 : PhysicalPairedReduction.dagger N2=N2 := by unfold N2; rw [PhysicalPairedReduction.daggerProduct,herm]
  have hi : (2:ComplexScalar R)^n*ofReal (half^n)=1 := by
    have e := congrArg (ofReal (R:=R)) (SectorDefectAccounting.dimensionInverse half unit n)
    rw [embedMul,PhysicalPairedReduction.realEmbeddingPow] at e; exact e
  have src := unsignedComplex imaginaryUnit (ComplexScalar.imaginaryUnit_sq (R:=R)) N _ hi
  have allReal : ofReal (unsignedSum (coeff N))=ofReal (((2:R)^n)^2 * sumOver (words n)
        (fun p => (physicalCoeff N2 p)^4)) := by
    unfold unsignedSum
    simp only [embedMul,embedSum,PhysicalPairedReduction.realEmbeddingPow,coeff,realTraceWord N2 hn2,
      realTraceWord _ (daggerSqueezed N herm _)]
    exact src
  exact congrArg ComplexScalar.re allReal

open FourCopySectors
open ExteriorPauliBase (permutations oddPermutation)
open GenericExteriorKernel (reorder position position_reorder)

private theorem compose {α : Type} (u : Four α) (p q : Perm) :
    reorder (reorder u p) q=reorder u (reorder p q) := by
  change ((position (reorder u p) _,position (reorder u p) _),
    (position (reorder u p) _,position (reorder u p) _))=_
  simp only [position_reorder]; rfl

attribute [local instance] Ring.intCast

private theorem sumCast {α : Type} (xs : List α) (f : α → Int) :
    Int.cast (R:=C) (sumOver xs f)=sumOver xs (fun p => Int.cast (R:=C) (f p)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons a xs ih => change Int.cast (R:=C) (f a+sumOver xs f)=_ ; rw [Ring.intCast_add,ih]; rfl

/-- In the Klein-fixed, permutation-equivariant image all twelve odd
permutations have the same trace as the first transposition. -/
theorem oddTrace {α : Type} (xs : List (Four α)) (closed : PermutedList xs) (K : Four α → Four α → C)
    (equiv : Equivariant K) (fixed : KleinFixed K) (p : Perm) (hp : p∈permutations) (odd : oddPermutation p=true) :
    permTrace xs K p=permTrace xs K transposition := by
  have tab : permutations.all (fun p => !oddPermutation p || permutations.any (fun h =>
    permutations.any (fun k => klein k && (FourCopySectors.conjugate h p == reorder transposition k))))=true := by decide
  have found := List.all_eq_true.mp tab p hp
  simp only [odd,Bool.not_true,Bool.false_or] at found
  obtain ⟨h,hh,hk⟩ := List.any_eq_true.mp found
  obtain ⟨k,km,hk⟩ := List.any_eq_true.mp hk
  obtain ⟨kk,eq⟩ := Bool.and_eq_true_iff.mp hk
  rw [←permTraceClass xs closed K equiv h hh p hp,beq_iff_eq.mp eq]
  apply sumOverCongr; intro x
  rw [←compose]; exact fixed k km kk _ _

theorem sectorTraceDifference {α : Type} (xs : List (Four α)) (closed : PermutedList xs)
    (K : Four α → Four α → C) (equiv : Equivariant K) (fixed : KleinFixed K) :
    trace xs (rawBlock .symmetric K)-trace xs (rawBlock .antisymmetric K) =
      24*permTrace xs K transposition := by
  rw [rawBlockTrace,rawBlockTrace]
  unfold characterTrace
  rw [←Compression.sumOverSub]
  let f (p : Perm) : Int := if oddPermutation p then 2 else 0
  have total : sumOver permutations f=24 := by decide
  calc
    _ = sumOver permutations (fun p => Int.cast (R:=C) (f p)*permTrace xs K transposition) := by
      apply congrArg List.sum; apply List.map_congr_left; intro p hp
      by_cases odd : oddPermutation p=true
      · rw [oddTrace xs closed K equiv fixed p hp odd]
        simp [coefficient,odd,f,Ring.intCast_neg] <;> grind
      · simp [coefficient,odd,f] <;> grind
    _ = _ := by rw [←sumOverMulRight,←sumCast,total,Ring.intCast_ofNat]

theorem pairedTraceDifference {α : Type} (xs : List (Four α)) (closed : PermutedList xs)
    (H A B : Four α → Four α → C) (h : Equivariant H) (a : Equivariant A) (b : Equivariant B) (fixed : KleinFixed A) :
    pairedFrameTrace xs H (rawBlock .symmetric A) B - pairedFrameTrace xs H (rawBlock .antisymmetric A) B =
      24*permTrace xs (matMul xs (matMul xs (matMul xs H A) H) B) transposition := by
  rw [←traceBlockFrame xs closed .symmetric H A B h,←traceBlockFrame xs closed .antisymmetric H A B h]
  exact sectorTraceDifference xs closed _
    (mulEquivariant xs closed _ _ (mulEquivariant xs closed _ H (mulEquivariant xs closed H A h a) h) b)
    (mulFixedLeft xs _ B (mulFixedLeft xs _ H (mulFixedRight xs closed H A h fixed)))

theorem transpositionTensor {α : Type} (xs : List α) (X : α → α → C) :
    permTrace (fourIndices xs) (tensorFour X) transposition =
      trace xs (matMul xs X X)*(trace xs X)^2 := by
  change sumOver (productIndices (productIndices xs xs) (productIndices xs xs))
    (fun uv => (X uv.1.2 uv.1.1*X uv.1.1 uv.1.2)*(X uv.2.1 uv.2.1*X uv.2.2 uv.2.2))=_
  rw [factorProductSum (productIndices xs xs) (productIndices xs xs) (fun v : α × α => X v.2 v.1*X v.1 v.2) (fun v : α × α => X v.1 v.1*X v.2 v.2),
    factorProductSum xs xs (fun i => X i i) (fun i => X i i),sumPairs]
  unfold trace matMul; congr 1
  · apply sumOverCongr; intro i; apply sumOverCongr; intro j; grind
  · grind

private def matrixSum {α β γ : Type} (ls : List γ) (F : γ → α → β → C) : α → β → C :=
  fun a b => sumOver ls (fun k => F k a b)

private def smulM {α β : Type} (z : C) (A : α → β → C) : α → β → C := fun a b => z*A a b

private theorem matSumLeft {α β γ ι : Type} (xs : List β) (ls : List ι)
    (F : ι → α → β → C) (B : β → γ → C) :
    matMul xs (matrixSum ls F) B=matrixSum ls (fun i => matMul xs (F i) B) := by
  funext a b; simp only [matrixSum,matMul,sumOverMulRight]; rw [sumOverSwap]

private theorem matSumRight {α β γ ι : Type} (xs : List β) (ls : List ι)
    (A : α → β → C) (F : ι → β → γ → C) :
    matMul xs A (matrixSum ls F)=matrixSum ls (fun i => matMul xs A (F i)) := by
  funext a b; simp only [matrixSum,matMul,sumOverMulLeft]; rw [sumOverSwap]

private theorem matScaleLeft {α β γ : Type} (xs : List β) (z : C) (A : α → β → C) (B : β → γ → C) :
    matMul xs (smulM z A) B=smulM z (matMul xs A B) := by
  funext a b; simp only [smulM,matMul,sumOverMulLeft]; apply sumOverCongr; intro u; grind

private theorem matScaleRight {α β γ : Type} (xs : List β) (z : C) (A : α → β → C) (B : β → γ → C) :
    matMul xs A (smulM z B)=smulM z (matMul xs A B) := by
  funext a b; simp only [smulM,matMul,sumOverMulLeft]; apply sumOverCongr; intro u; grind

private theorem permMatSum {α ι : Type} (xs : List (Four α)) (ls : List ι) (F : ι → Four α → Four α → C) (p : Perm) :
    permTrace xs (matrixSum ls F) p=sumOver ls (fun i => permTrace xs (F i) p) := by
  unfold permTrace matrixSum; rw [sumOverSwap]

private theorem permMatScale {α : Type} (xs : List (Four α)) (z : C) (A : Four α → Four α → C) (p : Perm) :
    permTrace xs (smulM z A) p=z*permTrace xs A p := (sumOverMulLeft _ _ _).symm

private theorem normalizedWords {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :
    RectangularPairedReduction.normalizedFrame half A=smulM (ofReal (half^n)) (matrixSum (words n)
      (fun p => tensorFour (FrameExteriorSector.framedWord A p))) := by
  funext x y
  have e := FrameExteriorSector.frameTwirl_words (1:R) A x y
  have one : ofReal (1:R)=(1:ComplexScalar R) := rfl
  have opow (k : Nat) : (1:ComplexScalar R)^k=1 := by
    induction k with | zero => rfl | succ k ih => rw [Semiring.pow_succ,ih,Semiring.one_mul]
  simp only [FrameExteriorSector.frameTwirl,one,opow,Semiring.one_mul] at e
  exact congrArg (fun c => ofReal (half^n)*c) e

def sourceProduct {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (p q : Word n) :=
  let xs := List.finRange 7
  let D := PhysicalPairedReduction.diagonal mu
  matMul xs (matMul xs (matMul xs D (FrameExteriorSector.framedWord A p)) D) (FrameExteriorSector.framedWord A q)

/-- The real normalized-frame difference is reduced, before taking real
parts, to products of literal traces of the four physical source factors. -/
theorem physicalOddDifference {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let xs := List.finRange 7
    let ts := fourIndices xs
    let H := tensorFour (PhysicalPairedReduction.diagonal mu)
    let F := RectangularPairedReduction.normalizedFrame half A
    pairedFrameTrace ts H (rawBlock .symmetric F) F - pairedFrameTrace ts H (rawBlock .antisymmetric F) F =
      24*(ofReal (half^n))^2*sumOver (words n) (fun q => sumOver (words n) (fun p =>
        let X := sourceProduct A mu p q
        trace xs (matMul xs X X)*(trace xs X)^2)) := by
  dsimp only
  have closed := fullPermuted (List.finRange 7) (List.nodup_finRange 7) (fun i => List.mem_finRange i)
  have st := normalizedFrameStructure half A
  rw [pairedTraceDifference _ closed _ _ _ (tensorEquivariant _) st.1 st.1 st.2,normalizedWords]
  simp only [matScaleLeft,matScaleRight,matSumLeft,matSumRight,permMatScale,permMatSum,←fourMatMul,transpositionTensor]
  unfold sourceProduct
  rw [←sumOverMulLeft]
  grind

def orbitMatrix {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :=
  RectangularPairedReduction.rankSevenCoefficients A (ComplexPauliMoment.conjugate A) mu

private theorem twoTraces {α β : Type} (xs : List α) (ys : List β) (A : α → β → C) (L : β → α → C) :
    trace ys (matMul xs L A)=trace xs (matMul ys A L) ∧
    trace ys (matMul ys (matMul xs L A) (matMul xs L A)) =
      trace xs (matMul xs (matMul ys A L) (matMul ys A L)) := by
  constructor
  · exact traceMatMulSwap ys xs L A
  · rw [matMulAssoc,traceMatMulSwap ys xs L]; simp only [matMulAssoc]

theorem sourceWordTraces {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (p q : Word n) :
    let X := sourceProduct A mu p q
    let Y := squeezed (orbitMatrix A mu) p
    trace (List.finRange 7) X = traceWord imaginaryUnit Y q ∧
    trace (List.finRange 7) (matMul (List.finRange 7) X X) = traceWordSquare imaginaryUnit Y q := by
  let src := List.finRange 7
  let sites := qubitIndices n
  let D := PhysicalPairedReduction.diagonal mu
  let G := PhysicalPairedReduction.dagger A
  let P := physicalMatrix (R:=R) p
  let Q := physicalMatrix (R:=R) q
  let U := matMul src (matMul src A D) G
  let L := matMul src D (matMul sites G (matMul sites P (matMul sites U Q)))
  have srcId : sourceProduct A mu p q = matMul sites L A := by
    unfold sourceProduct FrameExteriorSector.framedWord L U
    simp only [matMulAssoc]; rfl
  have ambId : matMul sites (squeezed (orbitMatrix A mu) p) Q = matMul src A L := by
    unfold orbitMatrix; rw [← RectangularPairedReduction.rankSevenCoefficients_eq]
    unfold squeezed RectangularPairedReduction.coefficients L U
    simp only [matMulAssoc]; rfl
  dsimp only
  change trace src (sourceProduct A mu p q) = trace sites (matMul sites (squeezed (orbitMatrix A mu) p) Q) ∧
    trace src (matMul src (sourceProduct A mu p q) (sourceProduct A mu p q)) =
    trace sites (matMul sites (matMul sites (squeezed (orbitMatrix A mu) p) Q) (matMul sites (squeezed (orbitMatrix A mu) p) Q))
  rw [srcId,ambId]
  exact twoTraces _ _ A L

def oddMoment {n : Nat} (N : Basis n → Basis n → ComplexScalar R) : ComplexScalar R :=
  sumOver (words n) (fun q => sumOver (words n) (fun p =>
    traceWordSquare imaginaryUnit (squeezed N q) p*(traceWord imaginaryUnit (squeezed N q) p)^2))

theorem pairedOddMoment {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let ts := fourIndices (List.finRange 7)
    let H := tensorFour (PhysicalPairedReduction.diagonal mu)
    let F := RectangularPairedReduction.normalizedFrame half A
    pairedFrameTrace ts H (rawBlock .symmetric F) F - pairedFrameTrace ts H (rawBlock .antisymmetric F) F =
      24*(ofReal (half^n))^2*oddMoment (orbitMatrix A mu) := by
  dsimp only
  rw [physicalOddDifference half A mu]
  congr 1
  rw [sumOverSwap]
  apply sumOverCongr; intro p; apply sumOverCongr; intro q
  dsimp only
  rw [(sourceWordTraces A mu p q).1,(sourceWordTraces A mu p q).2]

private theorem embedChi {n : Nat} (p q : Word n) : ofReal (chi p q : R)=(chi p q : ComplexScalar R) := by
  unfold chi; cases anti p q <;> apply ComplexScalar.ext <;> simp [phase] <;> grind

theorem signedPhysical [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (herm : PhysicalPairedReduction.dagger N=N) :
    ofReal (signedSum (coeff N))=(2:ComplexScalar R)^n*oddMoment N := by
  unfold signedSum oddMoment coeff
  simp only [embedSum,embedMul,PhysicalPairedReduction.realEmbeddingPow,embedChi,realTraceWord _ (daggerSqueezed N herm _)]
  rw [sumOverMulLeft]; apply sumOverCongr; intro q; rw [sumOverMulLeft]; apply sumOverCongr; intro p
  let A := squeezed N q
  let a := (traceWord imaginaryUnit A p)^2
  calc
    _ = a*sumOver (words n) (fun r => chi p r*(traceWord imaginaryUnit A r)^2) := by
      rw [sumOverMulLeft]; apply sumOverCongr; intro r; unfold a A; grind
    _ = _ := by rw [fourierTrace _ ComplexScalar.imaginaryUnit_sq]; unfold a A; grind

/-- Real trace of the unaveraged S4 block for the physically normalized
paired source frame. -/
def rawSector {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (s : Sector) : R :=
  let H := tensorFour (PhysicalPairedReduction.diagonal mu)
  let F := RectangularPairedReduction.normalizedFrame half A
  (pairedFrameTrace (fourIndices (List.finRange 7)) H (rawBlock s F) F).re

private theorem orbitHermitian {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    PhysicalPairedReduction.dagger (orbitMatrix A mu)=orbitMatrix A mu := by
  funext a b
  unfold PhysicalPairedReduction.dagger transpose ComplexPauliMoment.conjugate orbitMatrix
    RectangularPairedReduction.rankSevenCoefficients
  rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro j
  simp only [ComplexPauliMoment.conjugate,ComplexScalar.star_mul,ComplexScalar.star_star,ComplexScalar.star_ofReal]
  grind

theorem rawDifferenceReal {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    rawSector half A mu .symmetric - rawSector half A mu .antisymmetric =
      24*(half^n)^2*(oddMoment (orbitMatrix A mu)).re := by
  have e := congrArg ComplexScalar.re (pairedOddMoment half A mu)
  have scalar : (24:ComplexScalar R)*(ofReal (half^n))^2=ofReal (24*(half^n)^2) := by
    rw [embedMul,PhysicalPairedReduction.realEmbeddingPow (half^n) 2]; rfl
  simp only [scalar,ComplexScalar.re_mul,ComplexScalar.re_sub,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal] at e
  change _ - _ = _ at e
  unfold rawSector; grind

private theorem signedRealScale [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    signedSum (coeff (orbitMatrix A mu))=(2:R)^n*(oddMoment (orbitMatrix A mu)).re := by
  have e := congrArg ComplexScalar.re (signedPhysical _ (orbitHermitian A mu))
  have scalar : (2:ComplexScalar R)^n=ofReal ((2:R)^n) := (PhysicalPairedReduction.realEmbeddingPow (2:R) n).symm
  simp only [scalar,ComplexScalar.re_mul,ComplexScalar.re_ofReal,ComplexScalar.im_ofReal] at e
  grind

/-- Sierant's symmetric defect is an ordered sum of real Pauli pair
squares for the actual paired rank-seven matrix and normalized raw sectors. -/
theorem physicalSymmetricCertificate [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (half invTwentyFour : R) (unit : 2*half=1) (unit24 : 24*invTwentyFour=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let di := half^n
    let N := orbitMatrix A mu
    let N2 := matMul (qubitIndices n) N N
    di^3*sumOver (words n) (fun p => (physicalCoeff N2 p)^4) -
      half^(n+n)*invTwentyFour*(rawSector half A mu .symmetric - rawSector half A mu .antisymmetric) =
      2*di^5*antiSquares (coeff N) := by
  dsimp only
  let N := orbitMatrix A mu
  let d := (2:R)^n
  let di := half^n
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half unit n
  have unsigned := unsignedPhysical half unit N (orbitHermitian A mu)
  have signed := signedRealScale A mu
  have gap := coefficientGap (coeff N)
  change signedSum (coeff N)=d*(oddMoment N).re at signed
  change unsignedSum (coeff N)=d^2*_ at unsigned
  rw [unsigned,signed] at gap
  rw [rawDifferenceReal,Semiring.pow_add]
  change di^3*_-di*di*invTwentyFour*(24*di^2*(oddMoment N).re)=2*di^5*antiSquares (coeff N)
  grind

theorem symmetricCertificateNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (half : R) (unit : 2*half=1) (N : Basis n → Basis n → ComplexScalar R) :
    0 ≤ 2*(half^n)^5*antiSquares (coeff N) := by
  have halfPos : 0 ≤ half := by grind
  have power {a : R} (ha : 0 ≤ a) (k : Nat) : 0 ≤ a^k := by
    induction k with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih ha
  exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (by grind : 0 ≤ (2:R)) (power (power halfPos n) 5))
    (physicalSquaresNonnegative _)

end RankSeven.SymmetricDefect

#print axioms RankSeven.SymmetricDefect.fourierTrace
#print axioms RankSeven.SymmetricDefect.pairedOddMoment
#print axioms RankSeven.SymmetricDefect.physicalSymmetricCertificate
#print axioms RankSeven.SymmetricDefect.symmetricCertificateNonnegative
