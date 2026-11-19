import Rank7PhysicalComparison

/-! Joint shifts of the two physical projected mixed Pauli probes. -/
namespace RankSeven.JointProbePayment
open Lean.Grind Pauli ComplexScalar
open SectorDefectAccounting (wedgePairs mixedDefect symmetricDefect anticommutingDefect)
open PhysicalDefectAssembly (pairedState pairedDensity physicalSectorTerms frameDefects)
open MixedDefect (rho oddWords)
open SymmetricDefect (anti chi)
variable {R α : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

/-- Real coordinates for the signed mixed projection on one orientation of
each odd Pauli edge. The two Hermitian orientations account for the factor two. -/
def hs (xs : List α) (f g : α×α → R) : R :=
  2*sumOver (wedgePairs xs) (fun e => f e*g e)

def signedCoordinates (eps : α → α → Bool) (M : α → α → ComplexScalar R) (e : α×α) : R :=
  rho (eps e.1 e.2) (M e.1 e.2)

def signedProjection (eps : α → α → Bool) (M : α → α → ComplexScalar R) (i j : α) : ComplexScalar R :=
  if eps i j then ofReal (M i j).re else ⟨0,(M i j).im⟩

def shifted (L U V : α×α → R) (s t : R) (e : α×α) : R := L e-s*U e-t*V e

def pairSpectrum (i j : Fin 7) (v : Fin 7) : R := if v=i ∨ v=j then 1 else 0

/-- K of the actual two-column spectral projection: its fourth-copy construction
uses the same complex column frame as the physical density. -/
def pairCoordinates {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (i j : Fin 7) :=
  signedCoordinates anti (PhysicalMixedFrame.K half (pairedState A (pairSpectrum i j)))

def sharedProbe {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (e : Word n × Word n) : R :=
  pairCoordinates half A 0 1 e+pairCoordinates half A 0 2 e

def densityCoordinates {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :=
  signedCoordinates anti (PhysicalMixedFrame.K half (pairedDensity A mu))

theorem pairProjectionIdempotent {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (i j : Fin 7)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let P := pairedState A (pairSpectrum i j)
    matMul (qubitIndices n) P P=P := by
  dsimp only
  rw [←PhysicalDefectAssembly.pairedState_mul _ _ _ orth]
  apply congrArg (pairedState A); funext v
  unfold pairSpectrum
  split <;> grind only

private theorem sumAppend (xs ys : List α) (f : α → R) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons a xs ih => simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *; grind only

private theorem doubleSum (xs : List α) (f : α → α → R) :
    sumOver xs (fun i => sumOver xs (f i))=sumOver xs (fun i => f i i)+
      sumOver (wedgePairs xs) (fun e => f e.1 e.2+f e.2 e.1) := by
  induction xs with
  | nil => simp [wedgePairs,sumOver]; grind only
  | cons a xs ih =>
    rw [wedgePairs,sumAppend]
    have e : sumOver (xs.map (fun b => (a,b))) (fun ij => f ij.1 ij.2+f ij.2 ij.1) =
        sumOver xs (fun b => f a b+f b a) := by simp only [sumOver,List.map_map,Function.comp_def]
    rw [e,sumOverAdd]
    change f a a+sumOver xs (f a)+sumOver xs (fun i => f i a+sumOver xs (f i))=(f a a + sumOver xs (fun i => f i i))+_
    rw [sumOverAdd,ih]; grind only

private theorem sumZero {T : Type} (xs : List T) : sumOver xs (fun _ => (0:R))=0 := by
  induction xs with
  | nil => rfl
  | cons a as ih => change 0+sumOver as _=0; rw [ih,Semiring.add_zero]

section Ordered
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The edge inner product equals the real Hilbert–Schmidt inner product
of the full, signed-projected Hermitian matrices. -/
theorem signedHilbertSchmidt (xs : List α) (eps : α → α → Bool) (symm : ∀ i j, eps j i=eps i j)
    (diag : ∀ i, eps i i=false) (A B : α → α → ComplexScalar R) (aHerm : MixedDefect.Hermitian A)
    (bHerm : MixedDefect.Hermitian B) :
    sumOver xs (fun i => sumOver xs (fun j =>
      (star (signedProjection eps A i j)*signedProjection eps B i j).re)) =
      hs xs (signedCoordinates eps A) (signedCoordinates eps B) := by
  let f i j := signedCoordinates eps A (i,j)*signedCoordinates eps B (i,j)
  have entry (i j) : (star (signedProjection eps A i j)*signedProjection eps B i j).re = f i j := by
    cases h : eps i j <;> simp [f,rho,signedCoordinates,signedProjection,h] <;> grind only
  have swap (i j) : f j i=f i j := by
    dsimp only [f,signedCoordinates]
    rw [symm i j,aHerm i j,bHerm i j]
    cases eps i j <;> simp [rho] <;> grind only
  have zero (i) : f i i=0 := by
    have e := congrArg ComplexScalar.im (aHerm i i)
    simp only [im_star] at e
    have z : (A i i).im=0 := by grind
    simp [f,signedCoordinates,diag,rho,z] <;> grind only
  simp only [entry]
  rw [doubleSum,sumOverCongr _ zero,sumZero,show ∀ x:R, 0+x=x from fun _ => by grind only]
  unfold hs; rw [sumOverMulLeft]
  apply sumOverCongr; intro e; rw [swap e.1 e.2]
  dsimp only [f]; grind only

theorem hsNonnegative (xs : List α) (f : α×α → R) : 0≤hs xs f f := by
  have h := Compression.sumOverNonnegative (wedgePairs xs) (fun e => f e*f e) (fun e _ => by have := squareNonnegative (f e); grind only)
  unfold hs; grind only

end Ordered

/-- Exact joint square before discarding its nonnegative shifted residual. -/
theorem jointShiftIdentity (xs : List α) (L U V : α×α → R) (s t : R) :
    hs xs L L = hs xs (shifted L U V s t) (shifted L U V s t)+
      2*s*hs xs U L+2*t*hs xs V L-s^2*hs xs U U-t^2*hs xs V V-2*s*t*hs xs U V := by
  unfold hs
  simp only [sumOverMulLeft,←sumOverAdd,←Compression.sumOverSub]
  apply sumOverCongr; intro e; unfold shifted; grind only

private theorem edgeRight {x : α×α} {xs : List α} (hx : x∈wedgePairs xs) : x.2∈xs := by
  induction xs with
  | nil => simp [wedgePairs] at hx
  | cons a xs ih =>
    rcases List.mem_append.mp hx with h|h
    · obtain ⟨b,mem,rfl⟩ := List.mem_map.mp h
      exact List.mem_cons_of_mem a mem
    · exact List.mem_cons_of_mem a (ih h)

theorem densityResidual {n : Nat} (half : R) (unit : 2*half=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let L := densityCoordinates half A mu
    2*MixedDefect.linearResidual (oddWords n) anti K = hs (oddWords n) L L := by
  dsimp only; unfold MixedDefect.linearResidual hs
  congr 1
  apply congrArg List.sum; apply List.map_congr_left; intro e he
  have entry := PhysicalMixedFrame.KProduct half unit (pairedState A mu) (pairedState A mu) e.1 e.2 (edgeRight he)
  rw [←PhysicalDefectAssembly.pairedDensity_eq_square A mu orth] at entry
  change (rho (anti e.1 e.2) (matMul _ _ _ e.1 e.2))^2=_
  rw [entry]
  unfold densityCoordinates signedCoordinates; grind only

section Physical
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem nonnegativePower (h : R) (hh : 0≤h) (n : Nat) : 0≤h^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hh

/-- The mixed defect alone supplies sixteen copies of the squared norm of
the actual signed-projected density. Its curvature summand is retained. -/
theorem physicalMixedResidual (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let n := k+3
    let d := (2:R)^n
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let L := densityCoordinates half A mu
    d^2*mixedDefect (half^n) (physicalSectorTerms half inv24 k A mu) =
      4*d*MixedDefect.curvature (oddWords n) anti K+16*hs (oddWords n) L L := by
  have id := SectorDefectAccounting.dimensionInverse half unit (k+3)
  have re := densityResidual half unit A mu orth
  have mix := PhysicalMixedDefect.physicalMixedDefectEqSquares half inv24 unit unit24 k A mu orth
  dsimp only at mix re ⊢
  rw [mix,←re]
  have z (d inv S T : R) (u : d*inv=1) : d^2*(4*inv*S+32*inv^2*T)=4*d*S+16*(2*T) := by
    have square := congrArg (fun x : R => x^2) u; grind only
  exact z _ _ _ _ id

/-- Physical simultaneous payment without counting any two probe norms separately. -/
theorem physicalShiftedDefect (half inv24 : R) (unit : 2*half=1) (unit24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (s t : R) :
    let n := k+3
    let xs := oddWords n
    let L := densityCoordinates half A mu
    let U := sharedProbe half A
    let V := pairCoordinates half A 0 1
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let c := SymmetricDefect.traceWord imaginaryUnit (pairedDensity A mu)
    let sector := physicalSectorTerms half inv24 k A mu
    (2:R)^(n+n)*symmetricDefect (half^n) sector +
      4*(2:R)^n*MixedDefect.curvature xs anti K+
      4*(half^n)^2*(PhysicalAntiQuartic.unorderedAntiMass c).re+
      16*(hs xs (shifted L U V s t) (shifted L U V s t)+2*s*hs xs U L+2*t*hs xs V L-
        s^2*hs xs U U-t^2*hs xs V V-2*s*t*hs xs U V) ≤ frameDefects half inv24 k A mu := by
  have mix := physicalMixedResidual half inv24 unit unit24 k A mu orth
  have antiBound := AntiDefectTransport.physicalAnticommutingCharge half inv24 unit unit24 k A mu orth
  have scale := nonnegativePower half (by grind only) (k+3)
  have combined := OrderedRing.mul_le_mul_of_nonneg_left antiBound scale
  dsimp only at mix combined ⊢
  rw [←jointShiftIdentity,Semiring.pow_add]
  unfold frameDefects SectorDefectAccounting.totalDefect
  dsimp only
  rw [mix]
  grind only


/-- The two polarization lower bounds give a joint shift with its exact
cross Gram. All three Gram entries are computed from the same edge vectors. -/
theorem polarizedShift (xs : List α) (L U V : α×α → R) (s t g delta H H1 : R)
    (s0 : 0≤s) (t0 : 0≤t)
    (shared : H+delta*(2*hs xs U V)≤2*hs xs U L)
    (highest : delta*(2*hs xs V V)+H1+g*(2*hs xs U V)≤2*hs xs V L) :
    24*s*H-12*s^2*(2*hs xs U U)+12*t*(2*delta-t)*(2*hs xs V V)+24*t*H1+
      24*(s*delta+t*g-s*t)*(2*hs xs U V) ≤ 24*hs xs L L := by
  have res := hsNonnegative xs (shifted L U V s t)
  have left := OrderedRing.mul_le_mul_of_nonneg_left shared s0
  have right := OrderedRing.mul_le_mul_of_nonneg_left highest t0
  rw [jointShiftIdentity xs L U V s t]; grind only

/-- On the full shift rectangle s≤2g, t≤2Δ the cross Gram contributes
a nonnegative receipt whenever the two physical probes have positive overlap. -/
theorem crossShiftNonnegative {s t g delta cross : R} (s0 : 0≤s) (t0 : 0≤t)
    (sc : s≤2*g) (tc : t≤2*delta) (cross0 : 0≤cross) : 0≤(s*delta+t*g-s*t)*cross := by
  have l := OrderedRing.mul_nonneg s0 (show 0≤2*delta-t by grind only)
  have r := OrderedRing.mul_nonneg t0 (show 0≤2*g-s by grind only)
  apply OrderedRing.mul_nonneg _ cross0
  grind only

end Physical

section Fourier
variable {T C : Type} [CommRing C]
open PhysicalMixedFrame (K pairs form dual)
open SymmetricDefect (traceWord signedResolution)

private theorem sumPair (xs : List T) (ys : List α) (f : T×α → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun a => sumOver ys (fun b => f (a,b))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro a; simp [sumOver,List.map_map,Function.comp_def]

private theorem sumSq (xs : List T) (f : T → C) :
    (sumOver xs f)^2=sumOver xs (fun a => sumOver xs (fun b => f a*f b)) := by
  rw [Semiring.pow_two,sumOverMulRight]; apply sumOverCongr; intro a; exact sumOverMulLeft _ _ _

private theorem cycle (xs : List α) (ys : List T) (zs : List T) (f : α → T → T → C) :
    sumOver xs (fun i => sumOver ys (fun j => sumOver zs (f i j))) =
      sumOver ys (fun j => sumOver zs (fun k => sumOver xs (fun i => f i j k))) := by
  rw [sumOverSwap xs ys]; apply sumOverCongr; intro j; rw [sumOverSwap]

private theorem complexPowerInverse (half : R) (unit : 2*half=1) (n : Nat) :
    (2:ComplexScalar R)^n*(ofReal half)^n=1 := by
  have h : (2:ComplexScalar R)*ofReal half=1 := by
    change ofReal (2:R)*ofReal half=ofReal (1:R); apply ComplexScalar.ext <;> simp <;> grind only
  exact SectorDefectAccounting.dimensionInverse _ h n

/-- The diagonal of the physical Λ² operator is a transpose-signed Pauli
Fourier transform of the squared density coefficients. -/
theorem diagonalFourier {n : Nat} (half : R) (unit : 2*half=1)
    (A : Basis n → Basis n → ComplexScalar R) (p : Word n) :
    K half A p p=(ofReal half^n)^2*sumOver (words n) (fun r =>
      chi p r*wordSign r*(traceWord imaginaryUnit A r)^2) := by
  let X := qubitIndices n
  let ed := pairs n
  let P := wordEntry (imaginaryUnit (R:=R)) p
  let d := (2:ComplexScalar R)^n
  let di := (ofReal half)^n
  let f (r : Word n) (u : Basis n × Basis n) := A u.1 u.2*wordEntry imaginaryUnit r u.2 u.1
  have tr (r : Word n) : traceWord imaginaryUnit A r=sumOver ed (f r) := (sumPair X X (f r)).symm
  let source := sumOver ed (fun x => sumOver ed (fun y => A x.1 x.2*A y.1 y.2*P x.2 y.2*P y.1 x.1))
  have fourier : sumOver (words n) (fun r => chi p r*wordSign r*(traceWord imaginaryUnit A r)^2) = d*source := by
    simp only [tr,sumSq,sumOverMulLeft]
    rw [cycle]
    unfold source; rw [sumOverMulLeft]
    apply sumOverCongr; intro x; rw [sumOverMulLeft]; apply sumOverCongr; intro y
    have e := congrArg (fun z : ComplexScalar R => A x.1 x.2*A y.1 y.2*z)
      (signedResolution imaginaryUnit imaginaryUnit_sq p x.2 x.1 y.1 y.2)
    rw [sumOverMulLeft] at e
    refine (sumOverCongr (words n) (g:=fun r => A x.1 x.2*A y.1 y.2*
      (chi p r*wordEntry imaginaryUnit r x.2 x.1*wordEntry imaginaryUnit r y.1 y.2)) ?_).trans (e.trans ?_)
    · intro r; dsimp only [f]
      rw [wordEntryTranspose imaginaryUnit r y.2 y.1]; grind only
    · dsimp only [d,P]; grind only
  have matrix : K half A p p=di*source := by
    unfold K source matMul ed pairs
    apply congrArg (fun z => di*z)
    simp only [sumPair,sumOverMulLeft,tensor,form,dual]
    apply sumOverCongr; intro a
    rw [sumOverSwap X X (fun b c => sumOver X (fun d =>
      P b a*(A a c*A b d*P c d)))]
    apply sumOverCongr; intro b; apply sumOverCongr; intro c; apply sumOverCongr; intro d
    dsimp only [P]; grind only
  rw [matrix,fourier]
  have u : d*di=1 := complexPowerInverse half unit n
  change di*source=di^2*(d*source)
  grind only

private theorem positiveMinusNegative (xs : List T) (keep : T → Bool) (f : T → C) :
    2*sumOver (xs.filter keep) f=sumOver xs f-sumOver xs (fun i => SymmetricDefect.phase (keep i)*f i) := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons a xs ih => rw [List.filter_cons]; cases h : keep a <;> simp [h,SymmetricDefect.phase,sumOver] at ih ⊢ <;> grind only

private def characterSum {n : Nat} (f : Word n → C) : C :=
  sumOver (words n) (fun a => sumOver (words n) (fun b => chi a b*(f a)^2*(f b)^2))

/-- Parseval on the odd Pauli labels, with the complete transpose Gauss
correction retained; the off-diagonal correction is the physical character sum. -/
theorem oddFourierNorm {n : Nat} (f : Word n → C) :
    2*sumOver (oddWords n) (fun p => (sumOver (words n) (fun a => chi p a*wordSign a*(f a)^2))^2) =
      (4:C)^n*sumOver (words n) (fun a => (f a)^4)-(2:C)^n*characterSum f := by
  let g a := (wordSign a : C)*(f a)^2
  let T (p : Word n) := sumOver (words n) (fun a => chi p a*g a)
  have term (p : Word n) : sumOver (words n) (fun a => chi p a*wordSign a*(f a)^2)=T p := by
    apply sumOverCongr; intro a; dsimp [g]; grind only
  have signedSq (a : Word n) : (g a)^2=(f a)^4 := by
    dsimp only [g]; have := wordSignSquare (C:=C) a; grind only
  rw [sumOverCongr _ (fun p => congrArg (fun x:C => x^2) (term p)),oddWords,positiveMinusNegative]
  have parseval := SymmetricDefect.fourierParseval g
  change sumOver (words n) (fun p => T p^2)=_ at parseval
  rw [parseval,sumOverCongr _ signedSq]
  congr 1
  simp only [T,sumSq,←MixedDefect.oddWordTransposeSign,sumOverMulLeft]
  rw [cycle]; unfold characterSum; rw [sumOverMulLeft]
  apply sumOverCongr; intro a; rw [sumOverMulLeft]; apply sumOverCongr; intro b
  have u := congrArg (fun z:C => z*(g a*g b)) (MixedDefect.transposeGauss (C:=C) a b)
  rw [sumOverMulRight] at u
  refine (sumOverCongr _ (g:=fun p => wordSign p*chi p a*chi p b*(g a*g b)) ?_).trans (u.trans ?_)
  · intro p; grind only
  · have sa := wordSignSquare (C:=C) a; have sb := wordSignSquare (C:=C) b
    dsimp only [g]; grind only

private theorem signedMass {n : Nat} (f : Word n → C) :
    (sumOver (words n) (fun p => (f p)^2))^2-characterSum f=2*PhysicalAntiQuartic.antiMass f := by
  unfold characterSum PhysicalAntiQuartic.antiMass
  rw [sumSq,←Compression.sumOverSub,sumOverMulLeft]
  apply sumOverCongr; intro a; rw [←Compression.sumOverSub,sumOverMulLeft]; apply sumOverCongr; intro b
  cases bit : anti a b <;> simp [chi,SymmetricDefect.phase,bit] <;> grind only

private theorem powFour (n : Nat) : (4:C)^n=((2:C)^n)^2 := by
  induction n with
  | zero => simp only [Semiring.pow_zero]; grind only
  | succ n ih => simp only [Semiring.pow_succ,ih]; grind only

/-- The diagonal fourth price on the actual skew Pauli coordinates: its
excess over the unsigned spectral trace is the ordered anticommuting mass. -/
theorem diagonalTraceBalance {n : Nat} (half : R) (unit : 2*half=1) (A : Basis n → Basis n → ComplexScalar R) :
    let xs := qubitIndices n
    let D := (2:ComplexScalar R)^n
    let di := (ofReal half)^n
    let c := traceWord imaginaryUnit A
    2*D*sumOver (oddWords n) (fun p => (K half A p p)^2) =
      di*sumOver (words n) (fun p => (c p)^4) - (trace xs (matMul xs A A))^2+
      2*di^2*PhysicalAntiQuartic.antiMass c := by
  let D := (2:ComplexScalar R)^n
  let di := (ofReal half)^n
  let c := traceWord imaginaryUnit A
  let F p := sumOver (words n) (fun a => chi p a*wordSign a*(c a)^2)
  let total := sumOver (oddWords n) (fun p => F p^2)
  let moment := sumOver (words n) (fun p => (c p)^4)
  let Z := trace (qubitIndices n) (matMul (qubitIndices n) A A)
  have od := oddFourierNorm c
  rw [powFour] at od
  change 2*total=D^2*moment-D*characterSum c at od
  have mass := signedMass c
  rw [SymmetricDefect.pauliParseval imaginaryUnit imaginaryUnit_sq A] at mass
  change (D*Z)^2-characterSum c=2*PhysicalAntiQuartic.antiMass c at mass
  have inverse : D*di=1 := complexPowerInverse half unit n
  have per (p : Word n) : (K half A p p)^2=di^4*(F p)^2 := by
    rw [diagonalFourier half unit]
    change (di^2*F p)^2=_; grind only
  change 2*D*sumOver (oddWords n) (fun p => (K half A p p)^2)=di*moment-Z^2+2*di^2*_
  rw [sumOverCongr _ per,←sumOverMulLeft]
  change 2*D*(di^4*total)=_
  have e := congrArg (fun z : ComplexScalar R => (D*di^4)*z) od
  have z := congrArg (fun w : ComplexScalar R => di^2*w) mass
  have u2 := congrArg (fun w : ComplexScalar R => w^2) inverse
  have u3 := congrArg (fun w : ComplexScalar R => w^3) inverse
  grind only

private theorem castMul (r t : R) : ofReal (r*t)=ofReal r*ofReal t := by
  apply ComplexScalar.ext <;> simp <;> grind only

private theorem scaledRe (r : R) (z : ComplexScalar R) : (ofReal r*z).re=r*z.re := by
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

section Ordered
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem physicalDiagonalBalance {n : Nat} (half : R) (unit : 2*half=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let D := (2:R)^n
    let di := half^n
    let c := traceWord imaginaryUnit (pairedDensity A mu)
    let F := K half (pairedState A mu)
    let xs := oddWords n
    let p4 := sumOver (List.finRange 7) (fun i => (mu i)^4)
    2*D*MixedDefect.realTrace xs (MixedDefect.hadamard (MixedDefect.square xs F))=
      di*PhysicalDefectAssembly.pauliDensityFourth A mu - p4^2+2*di^2*(PhysicalAntiQuartic.antiMass c).re := by
  let xs := oddWords n
  let X := pairedDensity A mu
  let mat := K half (pairedState A mu)
  have traceDiag : trace xs (MixedDefect.hadamard (MixedDefect.square xs mat))=
      sumOver xs (fun p => (K half X p p)^2) := by
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    have h := PhysicalMixedFrame.KProduct half unit (pairedState A mu) (pairedState A mu) p p hp
    rw [←PhysicalDefectAssembly.pairedDensity_eq_square A mu orth] at h
    change (matMul xs mat mat p p)*(matMul xs mat mat p p)=_
    rw [show matMul xs mat mat p p=K half X p p from h]; grind only
  have e := diagonalTraceBalance half unit X
  dsimp only at e
  rw [←traceDiag,show trace (qubitIndices n) (matMul (qubitIndices n) X X)=
    ofReal (sumOver (List.finRange 7) (fun i => (mu i)^4)) from (AntiDefectTransport.pairedDensityPowerTraces A mu orth).1] at e
  let D := (2:R)^n
  let di := half^n
  have d : ofReal D=(2:ComplexScalar R)^n := PhysicalPairedReduction.realEmbeddingPow (2:R) n
  have inv : ofReal di=(ofReal half)^n := PhysicalPairedReduction.realEmbeddingPow half n
  rw [←d,←inv,←PhysicalPairedReduction.realEmbeddingPow,←PhysicalPairedReduction.realEmbeddingPow] at e
  have c2 : (2:ComplexScalar R)=ofReal (2:R) := rfl
  rw [c2,←castMul,←castMul] at e
  have v := congrArg ComplexScalar.re e
  simp only [scaledRe,re_add,re_sub,re_ofReal] at v
  rw [AntiDefectTransport.physicalDensityWordFourth A mu] at v
  exact v

end Ordered

end Fourier

section Assembly
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
open MixedDefect (realTrace square hadamard seidelTrace)
open SymmetricDefect (traceWord)
open PhysicalMixedFrame (K)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum {T : Type} (xs : List T) (f : T → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=(f a).re+_; rw [ComplexScalar.re_add,ih]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem seidelProjectionTrace [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d : R)
    (eps : α → α → Bool) (P M : α → α → ComplexScalar R) (rel : MixedDefect.SeidelRelation d eps P) :
    2*seidelTrace xs eps M=3*d*realTrace xs (matMul xs P M)-(d-2)*realTrace xs M := by
  unfold seidelTrace realTrace trace matMul
  simp only [reSum,sumOverMulLeft,←Compression.sumOverSub]
  apply congrArg List.sum; apply List.map_congr_left; intro i hi
  rw [←ExteriorPauliBase.sumOnIndex xs i (fun j => (M j i).re) nd hi]
  simp only [sumOverMulLeft,←Compression.sumOverSub]
  apply sumOverCongr; intro j
  have h := congrArg (fun z : ComplexScalar R => (z*M j i).re) (rel i j)
  have scale (z t : ComplexScalar R) : ((2*z)*t).re=2*(z*t).re := by
    change (ofReal 2*z*t).re=_; rw [Semiring.mul_assoc,scaledRe]
  have sub (a b : ComplexScalar R) : ((a-b)*M j i).re=(a*M j i).re-(b*M j i).re := by
    rw [show (a-b)*M j i=a*M j i-b*M j i from by grind only]; rfl
  change ((2*_)*M j i).re=_ at h
  rw [scale,sub] at h
  simp only [Semiring.mul_assoc,scaledRe] at h
  by_cases e : i=j
  · subst j; simp only [MixedDefect.idEntry,ite_true,Semiring.one_mul] at h ⊢; grind only
  · simp only [MixedDefect.idEntry,ite_eq_right e,Semiring.zero_mul,re_zero] at h ⊢; grind only

/-- The physical anticommuting defect consists of two copies of the ordered
Pauli mass J and eight copies of the *same* mixed norm paid by the mixed sector. -/
theorem physicalAnticommutingResidual (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let n := k+3
    let D := (2:R)^n
    let di := half^n
    let L := densityCoordinates half A mu
    let c := traceWord imaginaryUnit (pairedDensity A mu)
    let sector := physicalSectorTerms half inv24 k A mu
    let p4 := sumOver (List.finRange 7) (fun i => (mu i)^4)
    let p8 := sumOver (List.finRange 7) (fun i => (mu i)^8)
    di*anticommutingDefect D (p4^2) p8 sector =
      2*di^2*(PhysicalAntiQuartic.antiMass c).re+8*hs (oddWords n) L L := by
  let n := k+3
  let D := (2:R)^n
  let di := half^n
  let third := 8*inv24
  let xs := oddWords n
  let F := K half (pairedState A mu)
  let M := hadamard (square xs F)
  let P := MixedTransport.P (n:=n) half third
  let sector := physicalSectorTerms half inv24 k A mu
  let p4 := sumOver (List.finRange 7) (fun i => (mu i)^4)
  let p8 := sumOver (List.finRange 7) (fun i => (mu i)^8)
  let c := traceWord imaginaryUnit (pairedDensity A mu)
  let L := densityCoordinates half A mu
  have ut : 3*third=1 := by unfold third; grind only
  have inverse : D*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have proj := seidelProjectionTrace xs (MixedDefect.oddWordsNodup n) D anti P M
    (MixedDefect.frameProjectionRelation D di third inverse ut anti)
  have overlap := MixedTransport.physicalOverlapPrice half inv24 third h2 h24 ut k A mu orth
  change realTrace xs (matMul xs P M)=sector.overlap at overlap
  rw [overlap] at proj
  have herm : MixedDefect.Hermitian (pairedState A mu) := by
    intro i j; exact (congrFun (congrFun (PhysicalDefectAssembly.pairedStateHermitian A mu) j) i).symm
  have linear := MixedDefect.squareLinearEqSOS xs (MixedDefect.oddWordsNodup n) anti
    (fun i j => PauliEdgeBlocks.antiSymm j i) F (PhysicalMixedFrame.KHermitian half _ herm)
  have hsn := densityResidual half h2 A mu orth
  change 2*MixedDefect.linearResidual xs anti F = hs xs L L at hsn
  have wedge := PhysicalMixedSpectrum.fourthTraceEqSpectrum half h2 A mu orth
  change realTrace xs (square xs (square xs F))=sector.wedgeFourth at wedge
  change realTrace xs (square xs (square xs F))-realTrace xs M+seidelTrace xs anti M=4*MixedDefect.linearResidual xs anti F at linear
  rw [wedge] at linear
  have pairs := SectorDefectAccounting.wedgeFourthSpectrum (List.finRange 7) mu
  change 2*sector.wedgeFourth=p4^2-p8 at pairs
  have diagonal := physicalDiagonalBalance half h2 A mu orth
  change 2*D*realTrace xs M = di*sector.pauliFourth-p4^2+2*di^2*(PhysicalAntiQuartic.antiMass c).re at diagonal
  change di*(3*D*p4^2-2*D*p8+6*D^2*sector.overlap-sector.pauliFourth)=
    2*di^2*(PhysicalAntiQuartic.antiMass c).re+8*hs xs L L
  have scaled : di*(3*D*p4^2-2*D*p8+6*D^2*sector.overlap-sector.pauliFourth)=
      3*p4^2-2*p8+6*D*sector.overlap-di*sector.pauliFourth := by
    have norm (u v a b c e : R) (hv : u*v=1) : v*(3*u*a-2*u*b+6*u^2*c-e)=3*a-2*b+6*u*c-v*e := by
      calc
        _ = 3*(u*v)*a-2*(u*v)*b+6*(u*v)*u*c-v*e := by grind only
        _ = _ := by rw [hv]; grind only
    exact norm _ _ _ _ _ _ inverse
  rw [scaled]
  have core (p4Sq p8 wedge diag sgn res norm overl mass d di c4 : R)
      (s : 2*sgn=3*d*overl-(d-2)*diag) (l : wedge-diag+sgn=4*res) (r : 2*res=norm)
      (w : 2*wedge=p4Sq-p8) (v : 2*d*diag=di*c4-p4Sq+2*di^2*mass) :
      3*p4Sq-2*p8+6*d*overl-di*c4=2*di^2*mass+8*norm := by grind only
  exact core _ _ _ _ _ _ _ _ _ _ _ _ proj linear hsn pairs diagonal

/-- Complete normalization of the simultaneous physical payments. -/
theorem physicalJointResidual (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let n := k+3
    let D := (2:R)^n
    let di := half^n
    let L := densityCoordinates half A mu
    let F := K half (pairedState A mu)
    let c := traceWord imaginaryUnit (pairedDensity A mu)
    let xs := oddWords n
    frameDefects half inv24 k A mu =
      D^2*symmetricDefect di (physicalSectorTerms half inv24 k A mu)+4*D*MixedDefect.curvature xs anti F+
      2*di^2*(PhysicalAntiQuartic.antiMass c).re+24*hs xs L L := by
  have mixed := physicalMixedResidual half inv24 h2 h24 k A mu orth
  have antiBound := physicalAnticommutingResidual half inv24 h2 h24 k A mu orth
  dsimp only at mixed antiBound ⊢
  unfold frameDefects SectorDefectAccounting.totalDefect; dsimp only
  rw [mixed,antiBound]; grind only

/-- Both actual probes are shifted in one square. The remaining positive terms
keep their symmetric, curvature, and anticommuting normalizations exactly. -/
theorem physicalJointShift (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (s t : R) :
    let n := k+3
    let D := (2:R)^n
    let di := half^n
    let L := densityCoordinates half A mu
    let U := sharedProbe half A
    let V := pairCoordinates half A 0 1
    let F := K half (pairedState A mu)
    let c := traceWord imaginaryUnit (pairedDensity A mu)
    let xs := oddWords n
    frameDefects half inv24 k A mu =
      D^2*symmetricDefect di (physicalSectorTerms half inv24 k A mu)+4*D*MixedDefect.curvature xs anti F+
      2*di^2*(PhysicalAntiQuartic.antiMass c).re+
      24*(hs xs (shifted L U V s t) (shifted L U V s t)+2*s*hs xs U L+2*t*hs xs V L-
        s^2*hs xs U U-t^2*hs xs V V-2*s*t*hs xs U V) := by
  dsimp only; rw [←jointShiftIdentity]
  exact physicalJointResidual half inv24 h2 h24 k A mu orth

def entryProduct (A B : α → α → ComplexScalar R) (a b : α) := A a b*B a b

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem productHermitian (A B : α → α → ComplexScalar R)
    (aH : MixedDefect.Hermitian A) (bH : MixedDefect.Hermitian B) : MixedDefect.Hermitian (entryProduct A B) := by
  intro i j; unfold entryProduct; rw [aH i j,bH i j,star_mul]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- Polarization for distinct physical probes. The final two terms are
the signed four-form contribution and the diagonal Pauli matching cost. -/
theorem polarizedProjectionTrace [DecidableEq α] (xs : List α) (nd : xs.Nodup) (d : R)
    (eps : α → α → Bool) (symm : ∀ i j,eps j i=eps i j) (P A B : α → α → ComplexScalar R)
    (rel : MixedDefect.SeidelRelation d eps P) (aH : MixedDefect.Hermitian A) (bH : MixedDefect.Hermitian B) :
    4*hs xs (signedCoordinates eps A) (signedCoordinates eps B) =
      2*realTrace xs (matMul xs A B)+3*d*realTrace xs (matMul xs P (entryProduct A B))-
      d*realTrace xs (entryProduct A B) := by
  let M := entryProduct A B
  let z (a b : α) := (A a b*B b a).re
  have tr : realTrace xs (matMul xs A B)=sumOver xs (fun i => sumOver xs (z i)) := by
    unfold realTrace trace matMul; simp only [reSum]; rfl
  have diagonal : sumOver xs (fun a => z a a)=realTrace xs M := by
    unfold realTrace trace M entryProduct; rw [reSum]
  have edge := MixedDefect.seidelTraceEdges xs nd eps symm M (productHermitian A B aH bH)
  have proj := seidelProjectionTrace xs nd d eps P M rel
  have localEq : 2*hs xs (signedCoordinates eps A) (signedCoordinates eps B) =
      realTrace xs (matMul xs A B)-realTrace xs M+seidelTrace xs eps M := by
    rw [tr,doubleSum,diagonal,edge]
    rw [show ∀ x y:R, x+y-x=y from fun _ _ => by grind only]
    unfold hs
    simp only [sumOverMulLeft,←sumOverAdd]
    apply sumOverCongr; intro e
    dsimp only [z,M,entryProduct,signedCoordinates]
    rw [aH e.1 e.2,bH e.1 e.2]
    cases b : eps e.1 e.2 <;> simp [rho,MixedDefect.sign] <;> grind only
  change 4*hs xs (signedCoordinates eps A) (signedCoordinates eps B) =
    2*realTrace xs (matMul xs A B)+3*d*realTrace xs (matMul xs P M)-d*realTrace xs M
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem maskSum (i j : Fin 7) (ne : i≠j) (f : Fin 7 → R) :
    sumOver (List.finRange 7) (fun v => pairSpectrum i j v*f v)=f i+f j := by
  let l := List.finRange 7
  have ei := ExteriorPauliBase.sumOnIndex l i f (List.nodup_finRange 7) (List.mem_finRange _)
  have ej := ExteriorPauliBase.sumOnIndex l j f (List.nodup_finRange 7) (List.mem_finRange _)
  rw [←ei,←ej,←sumOverAdd]
  apply sumOverCongr; intro v
  unfold pairSpectrum; by_cases a : v=i <;> by_cases b : v=j <;> simp [a,b,eq_comm,ne] <;> grind only

/-- The unprojected pair/density overlap is exactly tᵢtⱼ in the physical frame. -/
theorem pairBaseline {n : Nat} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) (i j : Fin 7) (ne : i≠j) :
    let B := K half (pairedState A (pairSpectrum i j))
    let C := K half (pairedDensity A mu)
    realTrace (oddWords n) (matMul (oddWords n) B C)=(mu i)^2*(mu j)^2 := by
  let xs := oddWords n
  let sites := qubitIndices n
  let P := pairedState A (pairSpectrum i j)
  let C := pairedDensity A mu
  let lambda (v : Fin 7) := pairSpectrum i j v*(mu v)^2
  let N := pairedState A lambda
  have hN : matMul sites P C=N := (PhysicalDefectAssembly.pairedState_mul A _ _ orth).symm
  have tr : trace xs (matMul xs (K half P) (K half C)) = trace xs (K half N) := by
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    rw [PhysicalMixedFrame.KProduct half unit P C p p hp,hN]
  have sq : square sites N=pairedState A (fun v => lambda v*lambda v) :=
    (PhysicalDefectAssembly.pairedState_mul A _ _ orth).symm
  have sum1 : sumOver (List.finRange 7) lambda=(mu i)^2+(mu j)^2 := maskSum i j ne _
  have sum2 : sumOver (List.finRange 7) (fun v => lambda v*lambda v)=(mu i)^4+(mu j)^4 := by
    rw [←maskSum i j ne (fun v => (mu v)^4)]
    apply sumOverCongr; intro v; unfold lambda pairSpectrum; split <;> grind only
  have trace1 := AntiDefectTransport.pairedTraceEqSpectrum A lambda orth
  have trace2 := AntiDefectTransport.pairedTraceEqSpectrum A (fun v => lambda v*lambda v) orth
  have identity := PhysicalMixedFrame.oddTrace half unit N
  change 2*trace xs (K half N)=(trace sites N)^2-trace sites (square sites N) at identity
  rw [sq,trace2,sum2,trace1,sum1,←PhysicalPairedReduction.realEmbeddingPow] at identity
  rw [←tr] at identity
  have re := congrArg ComplexScalar.re identity
  change ((ofReal (2:R))*_).re=_ at re
  simp only [scaledRe,re_sub,re_ofReal] at re
  change (trace xs (matMul xs (K half P) (K half C))).re=(mu i)^2*(mu j)^2
  grind

/-- Each actual two-column probe has a spectral baseline plus its four-form
trace and minus its diagonal matching charge, with all constants explicit. -/
theorem physicalPairPolarization {n : Nat} (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (i j : Fin 7) (ne : i≠j) :
    let D := (2:R)^n
    let xs := oddWords n
    let L := densityCoordinates half A mu
    let V := pairCoordinates half A i j
    let B := K half (pairedState A (pairSpectrum i j))
    let C := K half (pairedDensity A mu)
    let M := entryProduct B C
    4*hs xs V L = 2*(mu i)^2*(mu j)^2+
      3*D*realTrace xs (matMul xs (MixedTransport.P half third) M)-D*realTrace xs M := by
  let P := pairedState A (pairSpectrum i j)
  let C := pairedDensity A mu
  have ph : MixedDefect.Hermitian P := by intro a b; exact (congrFun (congrFun (PhysicalDefectAssembly.pairedStateHermitian A _) b) a).symm
  have ch : MixedDefect.Hermitian C := by intro a b; exact (congrFun (congrFun (PhysicalDefectAssembly.pairedDensityHermitian A mu) b) a).symm
  have pr := polarizedProjectionTrace (oddWords n) (MixedDefect.oddWordsNodup n) ((2:R)^n) anti
    (fun i j => PauliEdgeBlocks.antiSymm j i) (MixedTransport.P half third) (K half P) (K half C)
    (MixedDefect.frameProjectionRelation _ _ _ (SectorDefectAccounting.dimensionInverse half h2 n) h3 anti)
    (PhysicalMixedFrame.KHermitian half _ ph) (PhysicalMixedFrame.KHermitian half _ ch)
  have base := pairBaseline half h2 A mu orth i j ne
  change realTrace (oddWords n) (matMul (oddWords n) (K half P) (K half C))=_ at base
  rw [base] at pr
  dsimp only
  change 4*hs _ (signedCoordinates anti (K half P)) (signedCoordinates anti (K half C))=_
  rw [pr]; grind only

/-- Physical skew-Pauli amplitude between the two frame columns. Its modulus
is that of the corresponding antiunitary matrix element. -/
def pairAmplitude {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (i j : Fin 7) : ComplexScalar R :=
  sumOver (PhysicalMixedFrame.pairs n) (fun x => PhysicalMixedFrame.dual p x*(A x.1 i*A x.2 j))

def pairWeight {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (i j : Fin 7) : R :=
  normSq (pairAmplitude A p i j)

def matchingScore {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (weight : Fin 7 → R) (p : Word n) : R :=
  sumOver (wedgePairs (List.finRange 7)) (fun e => weight e.1*weight e.2*pairWeight A p e.1 e.2)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem embedSum {T : Type} (xs : List T) (f : T → R) :
    ofReal (sumOver xs f)=sumOver xs (fun x => ofReal (f x)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ofReal (f i+sumOver xs f)=ofReal (f i)+sumOver xs _
    rw [←ih]; apply ComplexScalar.ext <;> simp <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem skewAmplitude {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n)
    (hp : p∈oddWords n) (i j : Fin 7) : pairAmplitude A p j i= -pairAmplitude A p i j := by
  let xs := qubitIndices n
  have odd := (List.mem_filter.mp hp).2
  have sign : (wordSign p : ComplexScalar R)= -1 := by rw [MixedDefect.oddWordTransposeSign,odd]; rfl
  have neg (x : ComplexScalar R) : -x=(-1)*x := by grind only
  rw [neg]; unfold pairAmplitude PhysicalMixedFrame.pairs
  simp only [sumPair,sumOverMulLeft]
  rw [sumOverSwap xs xs (fun a b => PhysicalMixedFrame.dual p (a,b)*(A a j*A b i))]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b
  unfold PhysicalMixedFrame.dual
  rw [wordEntryTranspose imaginaryUnit p b a,sign]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem spectralDiagonal {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (w : Fin 7 → R) (p : Word n) :
    K half (pairedState A w) p p = (ofReal half)^n*
      ofReal (sumOver (List.finRange 7) (fun i => sumOver (List.finRange 7) (fun j => w i*w j*pairWeight A p i j))) := by
  let xs := PhysicalMixedFrame.pairs n
  let lbl := List.finRange 7
  let keys := productIndices lbl lbl
  let H (x : Basis n×Basis n) (e : Fin 7×Fin 7) := A x.1 e.1*A x.2 e.2
  let weight (e : Fin 7×Fin 7) := ofReal (w e.1*w e.2)
  let f := PhysicalMixedFrame.form (n:=n) (R:=R)
  let b := PhysicalMixedFrame.dual (n:=n) (R:=R)
  let amp (e : Fin 7×Fin 7) := pairAmplitude A p e.1 e.2
  have N (x y : Basis n×Basis n) : tensor (pairedState A w) (pairedState A w) x y =
      sumOver keys (fun e => weight e*H x e*star (H y e)) := by
    unfold tensor pairedState RectangularPairedReduction.rankSevenCoefficients
    rw [sumOverMulRight,sumPair]; apply sumOverCongr; intro i; rw [sumOverMulLeft]
    apply sumOverCongr; intro j; dsimp only [H,weight,ComplexPauliMoment.conjugate]
    rw [star_mul,castMul]; grind only
  have dualStar (x : Basis n×Basis n) : star (b p x)=f x p :=
    ComplexPauliMoment.wordHermitian p x.2 x.1
  have gram (e : Fin 7×Fin 7) : (weight e*amp e*star (amp e))=
      sumOver xs (fun x => sumOver xs (fun y => b p x*(weight e*H x e*star (H y e)*f y p))) := by
    change weight e*(sumOver xs (fun x => b p x*H x e))*star (sumOver xs (fun x => b p x*H x e))=_
    rw [ComplexExterior.starSumOver,sumOverMulLeft xs (fun x => b p x*H x e) (weight e),sumOverMulRight]
    apply sumOverCongr; intro x; rw [sumOverMulLeft]
    apply sumOverCongr; intro y; rw [star_mul,dualStar]; grind only
  have data : sumOver lbl (fun i => sumOver lbl (fun j => ofReal (w i*w j*pairWeight A p i j))) =
      sumOver keys (fun e => weight e*amp e*star (amp e)) := by
    rw [sumPair]; apply sumOverCongr; intro i; apply sumOverCongr; intro j
    dsimp only [weight,amp,pairWeight]; rw [castMul,←star_mul_self]; grind only
  unfold K
  congr 1
  simp only [embedSum]
  rw [data,sumOverCongr keys gram]
  change sumOver xs (fun x => b p x * sumOver xs (fun y => tensor (pairedState A w) (pairedState A w) x y*f y p))=_
  simp only [N,sumOverMulLeft,sumOverMulRight]
  rw [cycle keys xs xs]

/-- The diagonal K entry is the physical seven-site matching score at each
odd Pauli word, with the exact factor 2/D. -/
theorem physicalMatchingScore {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (w : Fin 7 → R) (p : Word n) (hp : p∈oddWords n) :
    K half (pairedState A w) p p=ofReal (2*half^n*matchingScore A w p) := by
  rw [spectralDiagonal]
  let term (i j : Fin 7) := w i*w j*pairWeight A p i j
  have symm (i j) : term j i=term i j := by
    dsimp only [term,pairWeight]; rw [skewAmplitude A p hp i j]
    simp only [normSq,re_neg,im_neg]; grind only
  have diag (i) : term i i=0 := by
    have f := skewAmplitude A p hp i i
    have r := congrArg ComplexScalar.re f; have t := congrArg ComplexScalar.im f
    rw [re_neg] at r; rw [im_neg] at t
    have z : pairAmplitude A p i i = 0 := ComplexScalar.ext (by change _=0; grind) (by change _=0; grind)
    dsimp only [term,pairWeight]; rw [z]; simp [normSq]; grind only
  have split := doubleSum (List.finRange 7) term
  rw [sumOverCongr _ diag,sumZero] at split
  have sum : sumOver (List.finRange 7) (fun i => sumOver (List.finRange 7) (term i))=2*matchingScore A w p := by
    rw [split]; dsimp only [matchingScore]; rw [sumOverMulLeft]
    rw [show ∀ z:R, 0+z=z from fun _ => by grind only]; apply sumOverCongr; intro e
    rw [symm e.1 e.2]; dsimp only [term]; grind only
  change (ofReal half)^n*ofReal (sumOver _ (fun i => sumOver _ (term i)))=_
  rw [sum,castMul,castMul,castMul,PhysicalPairedReduction.realEmbeddingPow]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem pairWeightSymm {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (p : Word n) (hp : p∈oddWords n) (i j : Fin 7) : pairWeight A p j i=pairWeight A p i j := by
  unfold pairWeight; rw [skewAmplitude A p hp i j]
  simp only [normSq,re_neg,im_neg]; grind only

private theorem pairWeightSelf {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (p : Word n) (hp : p∈oddWords n) (i : Fin 7) : pairWeight A p i i=0 := by
  have f := skewAmplitude A p hp i i
  have r := congrArg ComplexScalar.re f; have t := congrArg ComplexScalar.im f
  rw [re_neg] at r; rw [im_neg] at t
  have z : pairAmplitude A p i i=0 := ComplexScalar.ext (by change _=0; grind) (by change _=0; grind)
  unfold pairWeight; rw [z]; simp [normSq]; grind only

/-- Individual matching probabilities are genuine squared matrix elements
of the skew Pauli operator on the two selected frame columns. -/
theorem physicalPairWeight {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (i j : Fin 7) (ne : i≠j) (p : Word n) (hp : p∈oddWords n) :
    K half (pairedState A (pairSpectrum i j)) p p=ofReal (2*half^n * pairWeight A p i j) := by
  let w := pairSpectrum (R:=R) i j
  have inner (a) : sumOver (List.finRange 7) (fun b => w a*w b*pairWeight A p a b)=
      w a*(pairWeight A p a i+pairWeight A p a j) := by
    rw [←maskSum i j ne (fun b => pairWeight A p a b),sumOverMulLeft]
    apply sumOverCongr; intro b; dsimp [w]; grind only
  rw [spectralDiagonal,sumOverCongr _ inner,maskSum i j ne (fun a => pairWeight A p a i+pairWeight A p a j),
    pairWeightSelf A p hp i,pairWeightSelf A p hp j,pairWeightSymm A p hp i j]
  rw [←PhysicalPairedReduction.realEmbeddingPow,←castMul]; congr 1; grind only

/-- Actual projected source polarization with the literature's per-word
matching probability p_ij and weighted matching score s_C exposed. -/
theorem physicalMatchingPolarization {n : Nat} (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (i j : Fin 7) (ne : i≠j) :
    let D := (2:R)^n
    let xs := oddWords n
    let L := densityCoordinates half A mu
    let V := pairCoordinates half A i j
    let B := K half (pairedState A (pairSpectrum i j))
    let C := K half (pairedDensity A mu)
    let M := entryProduct B C
    4*hs xs V L = 2*(mu i)^2*(mu j)^2+3*D*realTrace xs (matMul xs (MixedTransport.P half third) M)-
      4*half^n*sumOver xs (fun p => pairWeight A p i j * matchingScore A (fun v => (mu v)^2) p) := by
  let xs := oddWords n
  let D := (2:R)^n
  let di := half^n
  let B := K half (pairedState A (pairSpectrum i j))
  let C := K half (pairedDensity A mu)
  let M := entryProduct B C
  let score p := pairWeight A p i j * matchingScore A (fun v => (mu v)^2) p
  have diagonal : realTrace xs M=(2*di)^2*sumOver xs score := by
    unfold realTrace trace; rw [reSum,sumOverMulLeft]
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    change (K half (pairedState A (pairSpectrum i j)) p p*K half (pairedDensity A mu) p p).re=_
    rw [physicalPairWeight half A i j ne p hp,pairedDensity,physicalMatchingScore half A _ p hp,←castMul,re_ofReal]
    dsimp only [score,di]; grind only
  have pol := physicalPairPolarization half third h2 h3 A mu orth i j ne
  dsimp only at pol ⊢
  have scaled : D*realTrace xs M=4*di*sumOver xs score := by
    rw [diagonal]
    have inv : D*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
    calc
      _ = 4*(D*di)*di*sumOver xs score := by grind only
      _ = _ := by rw [inv]; grind only
  rw [pol,scaled]

end Assembly

end RankSeven.JointProbePayment

#print axioms RankSeven.JointProbePayment.signedHilbertSchmidt
#print axioms RankSeven.JointProbePayment.jointShiftIdentity
#print axioms RankSeven.JointProbePayment.densityResidual
#print axioms RankSeven.JointProbePayment.physicalMixedResidual
#print axioms RankSeven.JointProbePayment.polarizedShift
#print axioms RankSeven.JointProbePayment.diagonalFourier
#print axioms RankSeven.JointProbePayment.physicalDiagonalBalance
#print axioms RankSeven.JointProbePayment.physicalAnticommutingResidual
#print axioms RankSeven.JointProbePayment.physicalJointResidual
#print axioms RankSeven.JointProbePayment.physicalJointShift
#print axioms RankSeven.JointProbePayment.physicalPairPolarization
#print axioms RankSeven.JointProbePayment.physicalMatchingScore
#print axioms RankSeven.JointProbePayment.physicalPairWeight
#print axioms RankSeven.JointProbePayment.physicalMatchingPolarization
