import Rank7SectorDefectAccounting
import Rank7PhysicalPairedReduction
import Rank7SymmetricDefect

/-! Sierant, Appendix B.3, equations (138)–(171). The Seidel signs may be any
symmetric ±1 labels. All matrix products and traces below are finite sums. -/
namespace RankSeven.MixedDefect

open Lean.Grind Pauli ComplexScalar
open SectorDefectAccounting (wedgePairs)
variable {R α : Type} [CommRing R]

abbrev Matrix (α R : Type) [CommRing R] := α → α → ComplexScalar R

def Hermitian (K : Matrix α R) := ∀ i j, K j i = star (K i j)

def square (xs : List α) (K : Matrix α R) := matMul xs K K
def hadamard (K : Matrix α R) : Matrix α R := fun i j => K i j * K i j
def realTrace (xs : List α) (M : Matrix α R) : R := (trace xs M).re

/-- True selects the positive Seidel sign and real part. False selects the
negative sign and imaginary part, including on commuting distinct Pauli labels. -/
def sign (b : Bool) : R := if b then 1 else -1
def rho (b : Bool) (z : ComplexScalar R) := if b then z.re else z.im

def seidel [DecidableEq α] (eps : α → α → Bool) : Matrix α R :=
  fun i j => if i=j then 0 else ofReal (sign (eps i j))

def seidelTrace [DecidableEq α] (xs : List α) (eps : α → α → Bool) (M : Matrix α R) :=
  realTrace xs (matMul xs (seidel eps) M)

theorem normSq_signedReal (b : Bool) (z : ComplexScalar R) :
    normSq z + sign b * (z * z).re = 2*(rho b z)^2 := by
  cases b <;> simp only [normSq,sign,rho,ComplexScalar.re_mul] <;> grind

private theorem reSum {T : Type} (xs : List T) (f : T → ComplexScalar R) :
    (sumOver xs f).re = sumOver xs (fun a => (f a).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a + sumOver xs f).re = (f a).re + _
    rw [re_add,ih]; rfl

private theorem realSum {T : Type} (xs : List T) (f : T → R) :
    sumOver xs (fun a => ofReal (f a)) = ofReal (sumOver xs f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ofReal (f a) + sumOver xs _ = ofReal (f a + sumOver xs f)
    rw [ih]; apply ComplexScalar.ext <;> simp <;> grind

private theorem sumMem {C T : Type} [CommRing C] (xs : List T) {f g : T → C}
    (h : ∀ x∈xs, f x = g x) : sumOver xs f = sumOver xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem sumAppend {C T : Type} [CommRing C] (xs ys : List T) (f : T → C) :
    sumOver (xs++ys) f = sumOver xs f + sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind
  | cons x xs ih => simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *; grind

/-- Split a double sum into its diagonal and the two orientations of each
unordered edge. This identity is purely positional even for repeated labels. -/
private theorem doubleSum (xs : List α) (f : α → α → R) :
    sumOver xs (fun i => sumOver xs (f i)) = sumOver xs (fun i => f i i) +
      sumOver (wedgePairs xs) (fun ij => f ij.1 ij.2 + f ij.2 ij.1) := by
  induction xs with
  | nil => simp [wedgePairs,sumOver]; grind
  | cons a xs ih =>
    rw [wedgePairs,sumAppend]
    have e : sumOver (xs.map (fun b => (a,b))) (fun ij => f ij.1 ij.2 + f ij.2 ij.1) =
        sumOver xs (fun b => f a b + f b a) := by
      simp only [sumOver,List.map_map,Function.comp_def]
    rw [e,sumOverAdd]
    change f a a + sumOver xs (f a) + sumOver xs (fun i => f i a + sumOver xs (f i)) =
      (f a a + sumOver xs (fun i => f i i)) + _
    rw [sumOverAdd,ih]; grind only

private theorem distinctPair (xs : List α) (nd : xs.Nodup) (e : α × α) (he : e∈wedgePairs xs) :
    e.1 ≠ e.2 := by
  induction xs with
  | nil => simp [wedgePairs] at he
  | cons a xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    rcases List.mem_append.mp he with h | h
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      change a ≠ b
      exact fun eq => fresh (eq ▸ hb)
    · exact ih rest h

private theorem zeroSum {C T : Type} [CommRing C] (xs : List T) :
    sumOver xs (fun _ => (0:C))=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0+sumOver xs _ = 0; rw [ih]; grind

theorem squareHermitian (xs : List α) (K : Matrix α R) (herm : Hermitian K) : Hermitian (square xs K) := by
  intro i j
  unfold square matMul
  rw [ComplexExterior.starSumOver]
  apply sumOverCongr; intro k
  rw [star_mul,←herm i k,←herm k j]
  grind only

theorem hadamardHermitian (K : Matrix α R) (herm : Hermitian K) : Hermitian (hadamard K) := by
  intro i j; unfold hadamard; rw [herm i j,star_mul]

theorem seidelTraceEdges [DecidableEq α] (xs : List α) (nd : xs.Nodup) (eps : α → α → Bool)
    (symm : ∀ i j, eps j i=eps i j) (M : Matrix α R) (herm : Hermitian M) :
    seidelTrace xs eps M = 2 * sumOver (wedgePairs xs) (fun ij => sign (eps ij.1 ij.2) * (M ij.1 ij.2).re) := by
  unfold seidelTrace realTrace trace matMul
  simp only [reSum]
  rw [doubleSum]
  have diag : sumOver xs (fun i => (seidel eps i i * M i i).re) = 0 := by
    simp only [seidel,ite_true,Semiring.zero_mul,ComplexScalar.re_zero,zeroSum]
  rw [diag,show ∀ z : R, 0+z=z by intro z; grind only,sumOverMulLeft]
  apply sumMem; intro ij he
  have ne := distinctPair xs nd ij he
  rcases ij with ⟨i,j⟩
  change i≠j at ne
  have er := congrArg ComplexScalar.re (herm i j)
  change (M j i).re = (M i j).re at er
  simp only [seidel,ite_eq_right ne,ite_eq_right (Ne.symm ne),re_mul,re_ofReal,im_ofReal,er,symm i j]
  grind only

private theorem squareDiag (xs : List α) (K : Matrix α R) (herm : Hermitian K) (c : α) :
    square xs K c c = ofReal (sumOver xs (fun a => normSq (K a c))) := by
  unfold square matMul
  rw [←realSum]
  apply sumOverCongr; intro a
  rw [herm a c,star_mul_self]

private theorem normSquareTrace (xs : List α) (K : Matrix α R) (herm : Hermitian K) :
    realTrace xs (square xs K) = sumOver xs (fun c => sumOver xs (fun a => normSq (K a c))) := by
  unfold realTrace trace
  simp only [reSum,squareDiag xs K herm,re_ofReal]

/-- S of (144). B is the entrywise square of K, C the entrywise square of K². -/
def curvature [DecidableEq α] (xs : List α) (eps : α → α → Bool) (K : Matrix α R) : R :=
  realTrace xs (hadamard (square xs K)) - realTrace xs (square xs (hadamard K)) +
    seidelTrace xs eps (square xs (hadamard K))

def edgeTriangle (xs : List α) (eps : α → α → Bool) (K : Matrix α R) : R :=
  sumOver (wedgePairs xs) (fun e => sumOver xs (fun c =>
    (rho (eps e.1 e.2) (K e.1 c * star (K e.2 c)))^2))

/-- The modulus part of (166) after cancellation of the diagonal fourth powers. -/
private theorem modulusEdges (xs : List α) (K : Matrix α R) (herm : Hermitian K) :
    realTrace xs (hadamard (square xs K)) - realTrace xs (square xs (hadamard K)) =
    2 * sumOver (wedgePairs xs) (fun e => sumOver xs (fun c => normSq (K e.1 c)*normSq (K e.2 c))) := by
  rw [normSquareTrace xs (hadamard K) (hadamardHermitian K herm)]
  unfold realTrace trace hadamard
  simp only [reSum,squareDiag xs K herm,re_mul,re_ofReal,im_ofReal,normSq_mul]
  rw [←Compression.sumOverSub, sumOverSwap (wedgePairs xs) xs, sumOverMulLeft]
  apply sumOverCongr; intro c
  have e := SectorDefectAccounting.wedgePairTrace xs (fun a => normSq (K a c))
  simp only [Semiring.pow_two] at e
  grind only

/-- Equation (167), compressed into an unordered edge and its third index.
The two endpoints give the edge terms. Each other index gives the triangle
term carrying the sign of its opposite edge. -/
theorem curvatureEqSOS [DecidableEq α] (xs : List α) (nd : xs.Nodup) (eps : α → α → Bool)
    (symm : ∀ i j, eps j i = eps i j) (K : Matrix α R) (herm : Hermitian K) :
    curvature xs eps K = 4 * edgeTriangle xs eps K := by
  unfold curvature
  rw [modulusEdges xs K herm,seidelTraceEdges xs nd eps symm _ (squareHermitian xs _ (hadamardHermitian K herm))]
  unfold edgeTriangle
  rw [sumOverMulLeft,sumOverMulLeft,←sumOverAdd,sumOverMulLeft]
  apply sumOverCongr; intro e
  unfold square matMul hadamard
  simp only [reSum]
  rw [sumOverMulLeft,←Semiring.mul_assoc,sumOverMulLeft,←sumOverAdd,sumOverMulLeft]
  apply sumOverCongr; intro c
  rw [herm e.2 c]
  let z := K e.1 c * star (K e.2 c)
  have norm : normSq z = normSq (K e.1 c) * normSq (K e.2 c) := by rw [normSq_mul,normSq_star]
  have eq := normSq_signedReal (eps e.1 e.2) z
  have sq : (K e.1 c * K e.1 c * (star (K e.2 c) * star (K e.2 c))).re = (z*z).re := by
    apply congrArg ComplexScalar.re
    dsimp [z]; grind only
  rw [sq,←norm]
  change 2*normSq z + 2*sign (eps e.1 e.2)*(z*z).re = 4*(rho (eps e.1 e.2) z)^2
  grind only

/-- R of (145), with K² computed before taking the required real component. -/
def linearResidual (xs : List α) (eps : α → α → Bool) (K : Matrix α R) :=
  sumOver (wedgePairs xs) (fun e => (rho (eps e.1 e.2) (square xs K e.1 e.2))^2)

theorem linearEqSOS [DecidableEq α] (xs : List α) (nd : xs.Nodup) (eps : α → α → Bool)
    (symm : ∀ i j, eps j i=eps i j) (L : Matrix α R) (herm : Hermitian L) :
    realTrace xs (square xs L) - realTrace xs (hadamard L) + seidelTrace xs eps (hadamard L) =
      4*sumOver (wedgePairs xs) (fun e => (rho (eps e.1 e.2) (L e.1 e.2))^2) := by
  have diagonal (i : α) : (L i i * L i i).re = normSq (L i i) := by
    calc
      _ = (star (L i i) * L i i).re := congrArg (fun z => (z * L i i).re) (herm i i)
      _ = _ := re_star_mul_self _
  have first : realTrace xs (square xs L) - realTrace xs (hadamard L) =
      2 * sumOver (wedgePairs xs) (fun e => normSq (L e.1 e.2)) := by
    rw [normSquareTrace xs L herm,doubleSum]
    simp only [realTrace,trace,hadamard,reSum,diagonal]
    have edge (e : α × α) : normSq (L e.2 e.1) + normSq (L e.1 e.2) = 2 * normSq (L e.1 e.2) := by
      rw [herm e.1 e.2,normSq_star]; grind only
    rw [sumOverCongr _ edge, ←sumOverMulLeft]
    grind only
  rw [first,seidelTraceEdges xs nd eps symm _ (hadamardHermitian L herm)]
  rw [sumOverMulLeft,sumOverMulLeft,←sumOverAdd,sumOverMulLeft]
  apply sumOverCongr; intro e
  have h := normSq_signedReal (eps e.1 e.2) (L e.1 e.2)
  unfold hadamard
  grind only

/-- Equation (169) applied to the actual matrix K². -/
theorem squareLinearEqSOS [DecidableEq α] (xs : List α) (nd : xs.Nodup) (eps : α → α → Bool)
    (symm : ∀ i j, eps j i=eps i j) (K : Matrix α R) (herm : Hermitian K) :
    realTrace xs (square xs (square xs K)) - realTrace xs (hadamard (square xs K)) +
      seidelTrace xs eps (hadamard (square xs K)) = 4*linearResidual xs eps K :=
  linearEqSOS xs nd eps symm _ (squareHermitian xs K herm)

def idEntry [DecidableEq α] (i j : α) : ComplexScalar R := if i=j then 1 else 0

/-- Cross-multiplied entry identity (157). This expresses the Seidel matrix
in terms of the four-form projection in odd-Pauli frame coordinates. -/
def SeidelRelation [DecidableEq α] (d : R) (eps : α → α → Bool) (P : Matrix α R) : Prop :=
  ∀ i j, 2 * seidel eps i j = ofReal (3*d) * P i j - ofReal (d-2) * idEntry i j

private theorem leftReal (r : R) (z : ComplexScalar R) : (ofReal r * z).re = r*z.re := by
  simp only [re_mul,re_ofReal,im_ofReal]; grind only

private theorem projectRelationTrace [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d : R)
    (eps : α → α → Bool) (P M : Matrix α R) (rel : SeidelRelation d eps P) :
    2*seidelTrace xs eps M = 3*d*realTrace xs (matMul xs P M) - (d-2)*realTrace xs M := by
  unfold seidelTrace realTrace trace matMul
  simp only [reSum]
  simp only [sumOverMulLeft,←Compression.sumOverSub]
  apply sumMem; intro i hi
  rw [←ExteriorPauliBase.sumOnIndex xs i (fun j => (M j i).re) nd hi]
  simp only [sumOverMulLeft,←Compression.sumOverSub]
  apply sumOverCongr; intro j
  have h := congrArg (fun z : ComplexScalar R => (z*M j i).re) (rel i j)
  have ea (z t : ComplexScalar R) : ((2*z)*t).re = 2*(z*t).re := by
    change (ofReal 2 * z * t).re = _; rw [Semiring.mul_assoc,leftReal]
  have eb (a b : ComplexScalar R) : ((a-b)*M j i).re = (a*M j i).re - (b*M j i).re := by
    have q : (a-b)*M j i=a*M j i-b*M j i := by grind only
    rw [q]; rfl
  change ((2*seidel eps i j)*M j i).re = _ at h
  rw [ea,eb] at h
  simp only [Semiring.mul_assoc,leftReal] at h
  by_cases e : i=j
  · subst j; simp only [idEntry,ite_true,Semiring.one_mul] at h ⊢; grind only
  · simp only [idEntry,ite_eq_right e,Semiring.zero_mul,re_zero] at h ⊢; grind only

/-- For arbitrary Hermitian K and an intrinsic Seidel projection relation,
(146) follows with the actual matrix traces in the sector dictionary (163).
The first residual is already expanded into its squares. -/
theorem frameDefectEqSOS [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d di : R) (unit : d*di=1)
    (eps : α → α → Bool) (symm : ∀ i j, eps j i=eps i j) (P K : Matrix α R)
    (rel : SeidelRelation d eps P) (herm : Hermitian K) :
    let B2 := square xs (hadamard K)
    let C := hadamard (square xs K)
    let wedge4 := realTrace xs (square xs (square xs K))
    let y := realTrace xs (matMul xs P B2)
    let u := realTrace xs (matMul xs P C)
    let x := realTrace xs B2 - y
    8*di^2*wedge4 + 12*di*u + 4*y - 2*x =
      16*di*edgeTriangle xs eps K + 32*di^2*linearResidual xs eps K := by
  dsimp only
  let b := square xs (hadamard K)
  let c := hadamard (square xs K)
  let i4 := realTrace xs (square xs (square xs K))
  have st := curvatureEqSOS xs nd eps symm K herm
  change realTrace xs c - realTrace xs b + seidelTrace xs eps b = 4*edgeTriangle xs eps K at st
  have sr := squareLinearEqSOS xs nd eps symm K herm
  change i4 - realTrace xs c + seidelTrace xs eps c = 4*linearResidual xs eps K at sr
  have fb := projectRelationTrace xs nd d eps P b rel
  have fc := projectRelationTrace xs nd d eps P c rel
  change 8*di^2*i4 + 12*di*realTrace xs (matMul xs P c) + 4*realTrace xs (matMul xs P b) -
    2*(realTrace xs b-realTrace xs (matMul xs P b)) = _
  grind only

/-- Concrete frame entries in (155),(157). With inverse d and inverse 3
these satisfy the needed Seidel relation for every choice of symmetric signs. -/
def frameProjection [DecidableEq α] (d di third : R) (eps : α → α → Bool) : Matrix α R :=
  fun i j => ofReal (di*third) * (2*seidel eps i j + ofReal (d-2)*idEntry i j)

theorem frameProjectionRelation [DecidableEq α] (d di third : R) (ud : d*di=1) (ut : 3*third=1)
    (eps : α → α → Bool) : SeidelRelation d eps (frameProjection d di third eps) := by
  intro i j
  have h : ofReal (3*d) * ofReal (di*third) = (1 : ComplexScalar R) := by
    apply ComplexScalar.ext <;> simp <;> grind only
  unfold frameProjection
  rw [←Semiring.mul_assoc,h,Semiring.one_mul]; grind only

/-- Trace dictionary (163): the two unconstrained fields have no role in the
mixed defect. The four relevant fields below are actual finite matrix traces. -/
def frameTerms (xs : List α) (P K : Matrix α R) (s : SectorDefectAccounting.SectorTerms R) :
    SectorDefectAccounting.SectorTerms R :=
  let b := square xs (hadamard K)
  let c := hadamard (square xs K)
  let y := realTrace xs (matMul xs P b)
  { s with
    mixed := realTrace xs b-y
    alternating := y
    overlap := realTrace xs (matMul xs P c)
    wedgeFourth := realTrace xs (square xs (square xs K))}

/-- (138)–(146) for the explicit Seidel-frame model; the scalar hypotheses
only supply inverses of d and 3. No trace reduction or inequality is assumed. -/
theorem mixedDefectEqSOS [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d di third : R)
    (ud : d*di=1) (ut : 3*third=1) (eps : α → α → Bool) (symm : ∀ i j, eps j i=eps i j)
    (K : Matrix α R) (herm : Hermitian K) (s : SectorDefectAccounting.SectorTerms R) :
    SectorDefectAccounting.mixedDefect di (frameTerms xs (frameProjection d di third eps) K s) =
      4*di*curvature xs eps K + 32*di^2*linearResidual xs eps K := by
  rw [curvatureEqSOS xs nd eps symm K herm]
  have h := frameDefectEqSOS xs nd d di ud eps symm _ K (frameProjectionRelation d di third ud ut eps) herm
  dsimp only at h
  unfold SectorDefectAccounting.mixedDefect frameTerms
  grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem edgeTriangleNonnegative (xs : List α) (eps : α → α → Bool) (K : Matrix α R) :
    0 ≤ edgeTriangle xs eps K := by
  apply Compression.sumOverNonnegative; intro e _
  apply Compression.sumOverNonnegative; intro c _
  exact squareNonnegative _

theorem linearResidualNonnegative (xs : List α) (eps : α → α → Bool) (K : Matrix α R) :
    0 ≤ linearResidual xs eps K :=
  Compression.sumOverNonnegative _ _ (fun _ _ => squareNonnegative _)

theorem mixedDefectNonnegative [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d di third : R)
    (ud : d*di=1) (ut : 3*third=1) (hdi : 0≤di) (eps : α → α → Bool) (symm : ∀ i j, eps j i=eps i j)
    (K : Matrix α R) (herm : Hermitian K) (s : SectorDefectAccounting.SectorTerms R) :
    0 ≤ SectorDefectAccounting.mixedDefect di (frameTerms xs (frameProjection d di third eps) K s) := by
  rw [mixedDefectEqSOS xs nd d di third ud ut eps symm K herm s,curvatureEqSOS xs nd eps symm K herm]
  have h₁ := OrderedRing.mul_nonneg hdi (edgeTriangleNonnegative xs eps K)
  have h₂ := OrderedRing.mul_nonneg (squareNonnegative di) (linearResidualNonnegative xs eps K)
  grind only
end Order

/-- Conditions (172)–(173) are sufficient for simultaneous vanishing of
both square sums. The blocks may have arbitrary sizes. -/
theorem blockDiagonalSharpness {β : Type} (xs : List α) (nd : xs.Nodup)
    (eps : α → α → Bool) (K : Matrix α R) (block : α → β) (real : ∀ i j, (K i j).im=0)
    (sparse : ∀ i j, block i ≠ block j → K i j=0)
    (signBlock : ∀ i j, i≠j → block i=block j → eps i j=false) :
    edgeTriangle xs eps K=0 ∧ linearResidual xs eps K=0 := by
  have separated (i j : α) (apart : block i ≠ block j) (c : α) :
      K i c * star (K j c) = 0 ∧ K i c * K c j=0 := by
    by_cases e : block i=block c
    · have ne : block c ≠ block j := fun q => apart (e.trans q)
      rw [sparse j c (Ne.symm ne),sparse c j ne]
      have sz : star (0 : ComplexScalar R)=0 := star_ofReal (0:R)
      rw [sz]; grind only
    · rw [sparse i c e]; grind only
  have imSum {T : Type} (ls : List T) (f : T → ComplexScalar R) :
      (sumOver ls f).im = sumOver ls (fun a => (f a).im) := by
    induction ls with
    | nil => rfl
    | cons a ls ih => change (f a+sumOver ls f).im = (f a).im+_; rw [im_add,ih]; rfl
  constructor
  · unfold edgeTriangle
    rw [←zeroSum (C:=R) (wedgePairs xs)]; apply sumMem; intro e he
    rw [←zeroSum (C:=R) xs]; apply sumOverCongr; intro c
    by_cases q : block e.1=block e.2
    · simp [rho,signBlock _ _ (distinctPair xs nd e he) q,im_mul,real] <;> grind only
    · rw [(separated _ _ q c).1]; cases eps e.1 e.2 <;> simp [rho] <;> grind only
  · unfold linearResidual
    rw [←zeroSum (C:=R) (wedgePairs xs)]; apply sumMem; intro e he
    by_cases q : block e.1=block e.2
    · simp only [rho,signBlock _ _ (distinctPair xs nd e he) q, square,matMul,imSum,im_mul,real]
      have terms (c : α) : (K e.1 c).re*0 + 0*(K c e.2).re=0 := by grind only
      rw [sumOverCongr xs terms,zeroSum]; grind only
    · have van : square xs K e.1 e.2=0 := (sumOverCongr xs (fun c => (separated _ _ q c).2)).trans (zeroSum _)
      rw [van]; cases eps e.1 e.2 <;> simp [rho] <;> grind only

section Pauli
open SymmetricDefect (chi anti axisAnti phase)
variable {C : Type} [CommRing C]

def oddWord : {n : Nat} → Word n → Bool
  | _,.empty => false
  | _,.cons a p => (a == .y) ^^ oddWord p

def oddWords (n : Nat) : List (Word n) := (words n).filter oddWord

theorem oddWordTransposeSign {n : Nat} (p : Word n) : wordSign p = (phase (oddWord p) : C) := by
  induction p with
  | empty => simp [wordSign,oddWord,phase]
  | cons a p ih =>
    rw [wordSign,ih]
    cases a <;> cases e : oddWord p <;> simp [axisSign,oddWord,e,phase] <;> grind only

private theorem factorWordSum {n : Nat} (head : Axis → C) (tail : Word n → C) (f : Word (n+1) → C)
    (fac : ∀ a x, f (.cons a x) = head a * tail x) :
    sumOver (words (n+1)) f = (head .identity+head .x+head .y+head .z)*sumOver (words n) tail := by
  rw [words,sumOverFlatMap,sumOverMulLeft]
  apply sumOverCongr; intro x
  simp only [sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons,fac]
  grind only

private theorem twistedAxis (a b : Axis) :
    let h c := axisSign c * phase (axisAnti c a) * phase (axisAnti c b)
    h .identity + h .x + h .y + h .z = 2 * axisSign a * axisSign b * (phase (axisAnti a b) : C) := by
  cases a <;> cases b <;> simp [axisAnti,axisSign,phase] <;> grind only

/-- Gauss transform of the transpose sign. Unlike ordinary character
orthogonality this is nonzero at every frequency. -/
theorem transposeGauss {n : Nat} (a b : Word n) :
    sumOver (words n) (fun c => wordSign c * (chi c a : C) * chi c b) =
    (2:C)^n * wordSign a * wordSign b * chi a b := by
  induction a with
  | empty => cases b; simp [words,wordSign,chi,anti,phase,sumOver]; grind only
  | cons a as ih =>
    cases b with
    | cons b bs =>
      let g (c : Axis) : C := axisSign c * phase (axisAnti c a) * phase (axisAnti c b)
      let tail (w : Word _) : C := wordSign w * chi w as * chi w bs
      rw [factorWordSum g tail _ (by intro c w; simp only [g,tail,wordSign,SymmetricDefect.chiCons]; grind only)]
      have eq := twistedAxis (C:=C) a b
      change g .identity+g .x+g .y+g .z = _ at eq
      rw [eq]
      unfold tail
      rw [ih,wordSign,wordSign,SymmetricDefect.chiCons,Semiring.pow_succ]; grind only

private theorem oddSelection {T : Type} (xs : List T) (keep : T → Bool) (f : T → C) :
    2*sumOver (xs.filter keep) f = sumOver xs f - sumOver xs (fun x => phase (keep x)*f x) := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons x xs ih =>
    rw [List.filter_cons]
    cases h : keep x <;> simp [h,phase,sumOver,List.map_cons,List.sum_cons] at ih ⊢ <;> grind only

noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

/-- Exact odd-label character kernel. On two odd word labels the two
transpose signs in the Gauss correction cancel. -/
theorem oddCharacterKernel {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    2*sumOver (oddWords n) (fun c => (chi c a : C)*chi c b) =
      (if a=b then (2:C)^n*(2:C)^n else 0) - (2:C)^n*chi a b := by
  unfold oddWords
  rw [oddSelection,SymmetricDefect.characterOrthogonality]
  have h := transposeGauss (C:=C) a b
  simp only [oddWordTransposeSign,ha,hb] at h
  have ph : (phase true : C) = -1 := rfl
  rw [ph] at h
  have assoc : sumOver (words n) (fun c => (phase (oddWord c) : C) * (chi c a * chi c b)) =
      sumOver (words n) (fun c => (phase (oddWord c) : C) * chi c a * chi c b) :=
    sumOverCongr _ (fun _ => (Semiring.mul_assoc _ _ _).symm)
  rw [assoc,h]
  have power (k : Nat) : (4:C)^k=(2:C)^k*(2:C)^k := by
    induction k with
    | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
    | succ k ih => rw [Semiring.pow_succ,Semiring.pow_succ,ih]; grind only
  rw [power]; grind only

private def heads {n : Nat} (w : Word n) : List (Word (n+1)) :=
  [.cons .identity w,.cons .x w,.cons .y w,.cons .z w]

private def tailWord {n : Nat} : Word (n+1) → Word n | .cons _ w => w

private theorem headTail {n : Nat} {p : Word (n+1)} {w : Word n} (hp : p∈heads w) : tailWord p=w := by
  simp only [heads,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> rfl

private theorem headsNodup {n : Nat} (w : Word n) : (heads w).Nodup := by simp [heads]

theorem allWordsNodup (n : Nat) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    have inner (ws : List (Word n)) (nd : ws.Nodup) : (ws.flatMap heads).Nodup := by
      induction ws with
      | nil => simp
      | cons w ws ih =>
        obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
        rw [List.flatMap_cons,List.nodup_append]
        refine ⟨headsNodup w,ih tail,?_⟩
        intro p hp q hq eq
        subst q
        obtain ⟨v,hv,e⟩ := List.mem_flatMap.mp hq
        rw [←headTail hp,headTail e] at fresh
        exact fresh hv
    exact inner _ ih

theorem oddWordsNodup (n : Nat) : (oddWords n).Nodup :=
  (allWordsNodup n).filter oddWord

private theorem antiSelf {n : Nat} (v : Word n) : anti v v=false := by
  induction v with
  | empty => rfl
  | cons t ts ih => cases t <;> simp [anti,axisAnti,ih]

/-- In the odd Pauli frame I−Σ is precisely the restricted symplectic
character table, including its +1 diagonal. -/
private theorem seidelEntry {n : Nat} (a b : Word n) :
    seidel anti a b = idEntry (R:=R) a b - (chi a b : ComplexScalar R) := by
  by_cases e : a=b
  · subst b
    simp [seidel,idEntry,chi,antiSelf,phase]; grind only
  · cases h : anti a b <;> simp [seidel,idEntry,e,chi,h,sign,phase] <;>
      apply ComplexScalar.ext <;> simp <;> grind only

/-- Formula for P in terms of the restricted character table. -/
private theorem projectionEntry {n : Nat} (d di third : R) (ud : d*di=1) (a b : Word n) :
    frameProjection d di third anti a b =
      ofReal third * (idEntry a b - (2*ofReal di)*(chi a b : ComplexScalar R)) := by
  unfold frameProjection
  rw [seidelEntry]
  have dR : ofReal (d-2) = ofReal d - (2:ComplexScalar R) := by
    change ofReal (d-2) = ofReal d - ofReal 2
    apply ComplexScalar.ext <;> simp <;> grind only
  have it : ofReal (di*third) = ofReal di * ofReal third := by apply ComplexScalar.ext <;> simp <;> grind only
  have u : ofReal d * ofReal di = (1:ComplexScalar R) := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [dR,it]; grind only

/-- For actual odd Pauli indices, the explicit Seidel-frame matrix of
(157) really is idempotent. No projector or spectrum assumption is used. -/
theorem oddFrameIdempotent {n : Nat} (di third : R) (unit : (2:R)^n*di=1) (ut : 3*third=1)
    (a b : Word n) (ha : a∈oddWords n) (hb : b∈oddWords n) :
    let P := frameProjection ((2:R)^n) di third (fun p q : Word n => anti p q)
    square (oddWords n) P a b = P a b := by
  let xs := oddWords n
  let D : ComplexScalar R := (2:ComplexScalar R)^n
  let v := ofReal di
  let t := ofReal third
  let I (i j : Word n) := idEntry (R:=R) i j
  let X (i j : Word n) := chi i j (C:=ComplexScalar R)
  let Q i j := t*(I i j-2*v*X i j)
  have pe (i j : Word n) : frameProjection ((2:R)^n) di third anti i j=Q i j :=
    projectionEntry _ di third unit i j
  change matMul xs _ _ a b=_
  simp only [matMul,pe,Q]
  have mulId (i : Word n) (hi : i∈xs) (f : Word n → ComplexScalar R) :
      sumOver xs (fun c => I i c*f c) = f i := by
    rw [←ExteriorPauliBase.sumOnIndex xs i f (oddWordsNodup n) hi]
    apply sumOverCongr; intro c
    by_cases eq : i=c <;> simp [I,idEntry,eq] <;> grind only
  have idMul (j : Word n) (hj : j∈xs) (f : Word n → ComplexScalar R) :
      sumOver xs (fun c => f c * I c j) = f j := by
    calc
      _ = sumOver xs (fun c => I j c*f c) := by
        apply sumOverCongr; intro c
        by_cases eq : c=j
        · subst c; simp [I,idEntry]; grind only
        · simp [I,idEntry,eq,Ne.symm eq]; grind only
      _ = _ := mulId j hj f
  have dPow (k : Nat) : ofReal ((2:R)^k) = (2:ComplexScalar R)^k := by
    induction k with
    | zero => simp only [Semiring.pow_zero]; rfl
    | succ k ih =>
      rw [Semiring.pow_succ,Semiring.pow_succ]
      have h (r : R) : ofReal (r*2) = ofReal r*(2:ComplexScalar R) := by
        change ofReal (r*2)=ofReal r*ofReal 2
        apply ComplexScalar.ext <;> simp <;> grind only
      rw [h,ih]
  have cd : D*v=1 := by
    dsimp only [D,v]; rw [←dPow]
    apply ComplexScalar.ext <;> simp <;> grind only
  have ct : 3*t=1 := by
    dsimp only [t]
    change ofReal 3*ofReal third=ofReal 1
    apply ComplexScalar.ext <;> simp <;> grind only
  have char := oddCharacterKernel (C:=ComplexScalar R) a b (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2
  have xc : 2*sumOver xs (fun c => X a c * X c b)= D*D*I a b - D*X a b := by
    calc
      _ = 2*sumOver xs (fun c => X c a*X c b) := congrArg (fun z => 2*z) (sumOverCongr xs
        (fun c => congrArg (fun z => z*X c b) (SymmetricDefect.chiSymm (C:=ComplexScalar R) a c)))
      _ = _ := by dsimp only [D,I,X,xs]; by_cases eq : a=b <;> simp [idEntry,eq] at char ⊢ <;> grind only
  let F c := I a c*I c b
  let G c := I a c*X c b
  let H c := X a c*I c b
  let Z c := X a c*X c b
  have expan (c : Word n) : t*(I a c-2*v*X a c) * (t*(I c b-2*v*X c b)) =
      t*t*F c - (2*v*t*t)*G c - (2*v*t*t)*H c + (4*v*v*t*t)*Z c := by
    dsimp only [F,G,H,Z]; grind only
  rw [sumOverCongr xs expan,sumOverAdd,Compression.sumOverSub,Compression.sumOverSub,←sumOverMulLeft,
    ←sumOverMulLeft,←sumOverMulLeft,←sumOverMulLeft]
  unfold F G H Z
  rw [mulId a ha,idMul b hb (fun c => X a c),mulId a ha]
  grind only
end Pauli
end RankSeven.MixedDefect
