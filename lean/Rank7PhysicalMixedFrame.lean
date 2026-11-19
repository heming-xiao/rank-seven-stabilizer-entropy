import Rank7MixedDefect
import Rank7RectangularPairedReduction

/-! Physical odd-Pauli realization of the exterior square and of the
single mixed-plus-alternating four-copy space. -/
namespace RankSeven.PhysicalMixedFrame

open Lean.Grind Pauli ComplexScalar GenericExteriorKernel
open MixedDefect (oddWord oddWords)
open FourCopySectors (transposition)
variable {R : Type} [CommRing R]

abbrev Pair (n : Nat) := Basis n × Basis n
def pairs (n : Nat) : List (Pair n) := productIndices (qubitIndices n) (qubitIndices n)
def form {n : Nat} (x : Pair n) (p : Word n) : ComplexScalar R := wordEntry imaginaryUnit p x.1 x.2
def dual {n : Nat} (p : Word n) (x : Pair n) : ComplexScalar R := wordEntry imaginaryUnit p x.2 x.1

/-- The antisymmetric-frame matrix of Λ²N, with a factor 1/d from the
two normalized Pauli two-forms. -/
def K {n : Nat} (half : R) (N : Basis n → Basis n → ComplexScalar R) (p q : Word n) : ComplexScalar R :=
  ofReal half ^ n * matMul (pairs n) (dual (R:=R)) (matMul (pairs n) (tensor N N) form) p q

def doubledWord {n : Nat} (p : Word n) (x : Four (Basis n)) : ComplexScalar R :=
  form x.1 p * form x.2 p

private theorem minusFilter {C S : Type} [CommRing C] (xs : List S) (keep : S → Bool) (f : S → C) :
    2*sumOver (xs.filter keep) f = sumOver xs f - sumOver xs (fun x => SymmetricDefect.phase (keep x)*f x) := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons a xs ih =>
    rw [List.filter_cons]
    cases h : keep a <;> simp [h,SymmetricDefect.phase,sumOver] at ih ⊢ <;> grind only

private theorem formConjugate {n : Nat} (x : Pair n) (p : Word n) :
    star (form (R:=R) x p) = dual p x := ComplexPauliMoment.wordHermitian p x.1 x.2

private def rowContraction {α : Type} (x y : Four α) : Four α := ((x.1.1,x.2.1),(y.1.2,y.2.2))
private def colContraction {α : Type} (x y : Four α) : Four α := ((x.1.2,x.2.2),(y.1.1,y.2.1))

private theorem bitReshuffle : ∀ a b c d e f g h : Bool,
    allowedBit (rowContraction ((a,b),(c,d)) ((e,f),(g,h))) (colContraction ((a,b),(c,d)) ((e,f),(g,h))) =
    allowedBit ((a,b),(c,d)) ((e,f),(g,h)) := by decide

private theorem reshuffle (n : Nat) (x y : Four (Basis n)) :
    allowedTwirlEntry n (rowContraction x y) (colContraction x y) = allowedTwirlEntry n x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (allowedBit (rowContraction (firstBits x) (firstBits y)) (colContraction (firstBits x) (firstBits y)) &&
      allowedTwirlEntry n (rowContraction (remainingBits x) (remainingBits y)) (colContraction (remainingBits x) (remainingBits y))) = _
    rw [bitReshuffle,ih]; rfl

/-- The complete doubled Pauli Gram is the unnormalized physical four-copy
twirl. The identification is an actual one-bit contraction identity. -/
theorem doubledResolution {n : Nat} (x y : Four (Basis n)) :
    sumOver (words n) (fun p => doubledWord p x * star (doubledWord (R:=R) p y)) =
    unnormalizedTwirl imaginaryUnit x y := by
  have entry (p : Word n) : doubledWord p x * star (doubledWord (R:=R) p y) =
      tensorFour (wordEntry imaginaryUnit p) (rowContraction x y) (colContraction x y) := by
    simp only [doubledWord,star_mul,formConjugate]; rfl
  rw [sumOverCongr _ entry]
  change unnormalizedTwirl _ _ _ = _
  rw [unnormalizedTwirlEntry _ imaginaryUnit_fourth,unnormalizedTwirlEntry _ imaginaryUnit_fourth,reshuffle]

private theorem swapDoubled {n : Nat} (p : Word n) (x : Four (Basis n)) :
    doubledWord p (reorder x transposition) = (wordSign p : ComplexScalar R)*doubledWord p x := by
  change wordEntry _ p x.1.2 x.1.1 * wordEntry _ p x.2.1 x.2.2 =
    wordSign p * (wordEntry _ p x.1.1 x.1.2 * wordEntry _ p x.2.1 x.2.2)
  rw [wordEntryTranspose]; grind only

/-- Odd Pauli two-form squares give exactly the copy-pair antisymmetrized
twirl, for any number of qubits. The left factor two is essential. -/
theorem oddDoubledResolution {n : Nat} (x y : Four (Basis n)) :
    2*sumOver (oddWords n) (fun p => doubledWord p x * star (doubledWord (R:=R) p y)) =
      unnormalizedTwirl imaginaryUnit x y - unnormalizedTwirl imaginaryUnit (reorder x transposition) y := by
  rw [oddWords,minusFilter,doubledResolution,←doubledResolution (R:=R) (reorder x transposition) y]
  congr 1
  apply sumOverCongr; intro p
  rw [swapDoubled,MixedDefect.oddWordTransposeSign]
  grind only

local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem unitChi {n : Nat} (p : Word n) : SymmetricDefect.chi (SymmetricDefect.unitWord n) p = (1:ComplexScalar R) := by
  induction p with
  | empty => rfl
  | cons a p ih =>
    rw [SymmetricDefect.unitWord,SymmetricDefect.chiCons,ih]
    cases a <;> simp [SymmetricDefect.phase,SymmetricDefect.axisAnti] <;> grind only

private theorem unitEntry {n : Nat} (x y : Basis n) :
    wordEntry (imaginaryUnit (R:=R)) (SymmetricDefect.unitWord n) x y = if x=y then 1 else 0 := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    have e := ih x y
    cases a <;> cases b <;> by_cases h : x=y <;> simp [SymmetricDefect.unitWord,wordEntry,entry,e,h] <;> grind only

private theorem allPairResolution {n : Nat} (x y : Pair n) :
    sumOver (words n) (fun p => form (R:=R) x p * dual p y) =
      (2:ComplexScalar R)^n * (if x=y then 1 else 0) := by
  have e := SymmetricDefect.signedResolution (imaginaryUnit (R:=R)) imaginaryUnit_sq (SymmetricDefect.unitWord n)
    x.1 x.2 y.2 y.1
  simp only [unitChi,Semiring.one_mul,unitEntry] at e
  unfold form dual
  rw [e]
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  by_cases h : a=c <;> by_cases k : b=d <;> simp [h,k,eq_comm] <;> grind only

/-- Completeness of the actual odd Pauli two-form frame, including the
exchange term with its sign, in ordered pair coordinates. -/
theorem oddPairResolution {n : Nat} (x y : Pair n) :
    2*sumOver (oddWords n) (fun p => form (R:=R) x p * dual p y) =
    (2:ComplexScalar R)^n * ((if x=y then 1 else 0) - (if x.swap=y then 1 else 0)) := by
  rw [oddWords,minusFilter,allPairResolution]
  have e (p : Word n) : SymmetricDefect.phase (oddWord p) * (form (R:=R) x p * dual p y) =
      form x.swap p * dual p y := by
    rw [←MixedDefect.oddWordTransposeSign]; unfold form
    change _ = wordEntry _ p x.2 x.1 * _
    rw [wordEntryTranspose _ p x.2 x.1]; have unit := wordSignSquare (C:=ComplexScalar R) p; grind only
  rw [sumOverCongr _ e,allPairResolution]; grind only

private theorem sumPairs {C α β : Type} [CommRing C] (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f = sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]
  apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem sumMem {C α : Type} [CommRing C] (xs : List α) {f g : α → C}
    (e : ∀ x∈xs, f x=g x) : sumOver xs f=sumOver xs g :=
  congrArg List.sum (List.map_congr_left e)

private theorem pairNodup (n : Nat) : (pairs n).Nodup :=
  HyperplaneInduction.pairsNodup _ _ (HyperplaneIncidence.normalsNodup n) (HyperplaneIncidence.normalsNodup n)
private theorem pairFull {n : Nat} (x : Pair n) : x∈pairs n :=
  HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _)

private theorem dimInv (half : R) (unit : 2*half=1) (n : Nat) :
    (ofReal half)^n * (2:ComplexScalar R)^n=1 := by
  have h : ofReal half * (2:ComplexScalar R)=1 := by
    change ofReal half*ofReal 2=ofReal 1
    apply ComplexScalar.ext <;> simp <;> grind only
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
  | succ n ih => simp only [Semiring.pow_succ]; grind only

private theorem twoHalf (half : R) (unit : 2*half=1) : 2*ofReal half=(1:ComplexScalar R) := by
  change ofReal 2*ofReal half=ofReal 1
  apply ComplexScalar.ext <;> simp <;> grind only

private theorem pairProjector (half : R) (unit : 2*half=1) {n : Nat} (x y : Pair n) :
    ofReal half ^ n * sumOver (oddWords n) (fun p => form (R:=R) x p * dual p y) =
      ofReal half * ((if x=y then 1 else 0)-(if x.swap=y then 1 else 0)) := by
  have h := oddPairResolution (R:=R) x y
  have d := dimInv half unit n
  have t := twoHalf half unit
  let s := sumOver (oddWords n) (fun p => form (R:=R) x p * dual p y)
  let k : ComplexScalar R := (if x=y then 1 else 0)-(if x.swap=y then 1 else 0)
  change 2*s=(2:ComplexScalar R)^n*k at h
  change _*s=ofReal half*k
  calc
    _ = ofReal half*(ofReal half^n*(2*s)) := by
      calc
        _ = (2*ofReal half)*(ofReal half^n*s) := by rw [t]; simp only [Semiring.one_mul]
        _ = _ := by grind only
    _ = _ := by rw [h,←Semiring.mul_assoc (ofReal half^n),d,Semiring.one_mul]

def imageForm {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (x : Pair n) (p : Word n) :=
  matMul (pairs n) (tensor N N) form x p

/-- The pair-tensor action is the actual antisymmetric matrix map
P ↦ N P Nᵀ, also before imposing a parity on p. -/
theorem imageFormMatrix {n : Nat} (N : Basis n → Basis n → ComplexScalar R)
    (x : Pair n) (p : Word n) :
    imageForm N x p =
      matMul (qubitIndices n) (matMul (qubitIndices n) N (wordEntry imaginaryUnit p)) (transpose N) x.1 x.2 := by
  unfold imageForm matMul pairs
  rw [sumPairs,sumOverSwap]
  apply sumOverCongr; intro b
  rw [sumOverMulRight]
  apply sumOverCongr; intro a
  simp only [tensor,form,transpose]; grind only

/-- K_ab=d⁻¹ Tr(P_a N P_b Nᵀ) with the physical Pauli matrices. -/
theorem KTrace (half : R) {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (p q : Word n) :
    K half N p q = ofReal half^n * trace (qubitIndices n) (matMul (qubitIndices n)
      (wordEntry imaginaryUnit p) (matMul (qubitIndices n) (matMul (qubitIndices n) N (wordEntry imaginaryUnit q)) (transpose N))) := by
  apply congrArg (fun z => ofReal half^n*z)
  change sumOver (pairs n) (fun s => dual p s * imageForm N s q)=_
  unfold pairs; rw [sumPairs,sumOverSwap]
  apply sumOverCongr; intro y
  apply sumOverCongr; intro x
  rw [imageFormMatrix]; rfl

theorem imageSkew {n : Nat} (N : Basis n → Basis n → ComplexScalar R) (x : Pair n)
    (p : Word n) (hp : p∈oddWords n) : imageForm N x.swap p = -imageForm N x p := by
  have odd := (List.mem_filter.mp hp).2
  have sg : (wordSign p : ComplexScalar R)= -1 := by rw [MixedDefect.oddWordTransposeSign,odd]; rfl
  unfold imageForm matMul pairs
  rw [sumPairs,sumPairs,sumOverSwap]
  have neg {α : Type} (xs : List α) (f : α → ComplexScalar R) :
      -sumOver xs f = sumOver xs (fun a => -f a) := by
    induction xs with
    | nil => change -(0:ComplexScalar R)=0; grind only
    | cons a xs ih =>
      change -(f a+sumOver xs f)= -f a+sumOver xs (fun a => -f a)
      rw [←ih]; grind only
  rw [neg]; apply sumOverCongr; intro a
  rw [neg]; apply sumOverCongr; intro b
  unfold form tensor
  change (N x.2 b*N x.1 a)* wordEntry imaginaryUnit p b a = -((N x.1 a*N x.2 b)*wordEntry imaginaryUnit p a b)
  rw [wordEntryTranspose _ p b a,sg]; grind only

/-- The odd Pauli coefficients reconstruct every antisymmetric matrix. -/
theorem skewReconstruct (half : R) (unit : 2*half=1) {n : Nat} (F : Pair n → ComplexScalar R)
    (skew : ∀ x, F x.swap= -F x) (x : Pair n) :
    ofReal half^n * sumOver (oddWords n) (fun p =>
      form x p * sumOver (pairs n) (fun s => dual p s*F s)) = F x := by
  let xs := pairs n
  let ω := ofReal half^n
  have swap : sumOver (oddWords n) (fun p => form x p*sumOver xs (fun s => dual p s*F s)) =
      sumOver xs (fun s => sumOver (oddWords n) (fun p => form x p*dual p s) * F s) := by
    simp only [sumOverMulLeft,sumOverMulRight]
    rw [sumOverSwap]
    apply sumOverCongr; intro s; apply sumOverCongr; intro p; grind only
  have sel (z : Pair n) : sumOver xs (fun s => (if z=s then 1 else 0)*F s) = F z := by
    rw [←ExteriorPauliBase.sumOnIndex xs z F (pairNodup n) (pairFull z)]
    apply sumOverCongr; intro s; by_cases e : z=s <;> simp [e] <;> grind only
  change ω*_ = _
  rw [swap,sumOverMulLeft]
  calc
    _ = sumOver xs (fun s => ofReal half*(((if x=s then 1 else 0)*F s)-((if x.swap=s then 1 else 0)*F s))) := by
      apply sumOverCongr; intro s
      have e := pairProjector half unit x s
      change ω * _ = _ at e
      grind only
    _ = _ := by rw [←sumOverMulLeft,Compression.sumOverSub,sel,sel,skew]; have e:=twoHalf half unit; grind only

theorem frameImage (half : R) (unit : 2*half=1) {n : Nat}
    (N : Basis n → Basis n → ComplexScalar R) (q : Word n) (hq : q∈oddWords n) (x : Pair n) :
    matMul (oddWords n) form (K half N) x q = imageForm N x q := by
  have e := skewReconstruct half unit (fun y => imageForm N y q) (fun y => imageSkew N y q hq) x
  rw [sumOverMulLeft] at e
  unfold matMul K
  refine (sumOverCongr (oddWords n) (fun p => ?_)).trans e
  change form x p*(ofReal half^n * sumOver (pairs n) (fun s => dual p s*imageForm N s q)) =
    ofReal half^n*(form x p*sumOver (pairs n) (fun s => dual p s*imageForm N s q))
  grind only

/-- Composition of the actual odd-frame matrices agrees with exterior-square
composition; the right column is an actual odd coordinate. -/
theorem KProduct (half : R) (unit : 2*half=1) {n : Nat}
    (A B : Basis n → Basis n → ComplexScalar R) (a b : Word n) (hb : b∈oddWords n) :
    matMul (oddWords n) (K half A) (K half B) a b =
    K half (matMul (qubitIndices n) A B) a b := by
  let xs := pairs n
  let μ := ofReal half^n
  have e : matMul (oddWords n) (K half A) (K half B) a b =
      μ*matMul (oddWords n) (matMul xs dual (matMul xs (tensor A A) form)) (K half B) a b := by
    unfold matMul K
    rw [sumOverMulLeft]
    apply sumOverCongr; intro c
    unfold μ xs; simp only [matMul]; grind only
  rw [e]
  apply congrArg (fun z => μ*z)
  simp only [matMulAssoc] 
  rw [tensorMatMul (qubitIndices n) (qubitIndices n) A B A B]
  change matMul xs dual (matMul xs (tensor A A) (matMul (oddWords n) form (K half B))) a b =
    matMul xs dual (matMul xs (matMul xs (tensor A A) (tensor B B)) form) a b
  rw [matMulAssoc xs xs (tensor A A)]
  unfold matMul
  apply sumOverCongr; intro u; apply congrArg (fun z => dual a u*z)
  apply sumOverCongr; intro v
  exact congrArg (fun z => tensor A A u v*z) (frameImage half unit B b hb v)

theorem KFourthEntry (half : R) (unit : 2*half=1) {n : Nat}
    (N : Basis n → Basis n → ComplexScalar R) (a b : Word n) (hb : b∈oddWords n) :
    MixedDefect.square (oddWords n) (MixedDefect.square (oddWords n) (K half N)) a b =
      K half (MixedDefect.square (qubitIndices n) (MixedDefect.square (qubitIndices n) N)) a b := by
  change sumOver _ _ = _
  refine (sumMem (oddWords n) (g:=fun c => K half (MixedDefect.square (qubitIndices n) N) a c *
    K half (MixedDefect.square (qubitIndices n) N) c b) ?_).trans ?_
  · intro c hc; change (matMul _ _ _ a c)*(matMul _ _ _ c b) = _
    rw [KProduct half unit N N a c hc,KProduct half unit N N c b hb]; rfl
  · exact KProduct half unit _ _ a b hb

/-- The trace of the physical odd-Pauli matrix is the second elementary
symmetric polynomial of N. Neither diagonalization nor positivity is used. -/
theorem oddTrace (half : R) (unit : 2*half=1) {n : Nat} (N : Basis n → Basis n → ComplexScalar R) :
    2*trace (oddWords n) (K half N) =
      (trace (qubitIndices n) N)^2-trace (qubitIndices n) (MixedDefect.square (qubitIndices n) N) := by
  let xs := pairs n
  let T := tensor N N
  let μ := ofReal half^n
  have expand : trace (oddWords n) (K half N) =
      sumOver xs (fun u => sumOver xs (fun v =>
        (μ*sumOver (oddWords n) (fun a => form u a*dual a v))*T v u)) := by
    unfold trace K matMul
    simp only [sumOverMulLeft,sumOverMulRight]
    rw [sumOverSwap (oddWords n) xs]
    conv => lhs; arg 2; intro i; rw [sumOverSwap]
    rw [sumOverSwap xs xs]
    apply sumOverCongr; intro u; apply sumOverCongr; intro v; apply sumOverCongr; intro a
    unfold μ T; grind only
  have sel (v u : Pair n) : sumOver xs (fun s => (if v=s then 1 else 0)*T s u) = T v u := by
    rw [←ExteriorPauliBase.sumOnIndex xs v (fun s => T s u) (pairNodup n) (pairFull v)]
    apply sumOverCongr; intro s; by_cases e : v=s <;> simp [e] <;> grind only
  have tr : trace (oddWords n) (K half N) =
      ofReal half*(sumOver xs (fun u => T u u)-sumOver xs (fun u => T u.swap u)) := by
    rw [expand,←Compression.sumOverSub,sumOverMulLeft]
    apply sumOverCongr; intro u
    change sumOver xs (fun v => (ofReal half^n*_)*_) = _
    simp only [pairProjector half unit]
    rw [←sel u u,←sel u.swap u,←Compression.sumOverSub,sumOverMulLeft]
    apply sumOverCongr; intro v; grind only
  have idTr : sumOver xs (fun u => T u u)=(trace (qubitIndices n) N)^2 := by
    unfold xs pairs T; rw [sumPairs]; unfold tensor trace
    simp only [←sumOverMulLeft,←sumOverMulRight]; grind only
  have swapTr : sumOver xs (fun u => T u.swap u) = trace (qubitIndices n) (MixedDefect.square (qubitIndices n) N) := by
    unfold xs pairs T; rw [sumPairs]
    apply sumOverCongr; intro u; apply sumOverCongr; intro v
    change N v u*N u v=N u v*N v u; grind only
  rw [tr,idTr,swapTr,←Semiring.mul_assoc,twoHalf half unit,Semiring.one_mul]

/-- The fourth trace in the exact mixed SOS is the physical Λ² trace at
N⁴, namely twice the trace equals (Tr N⁴)² − Tr N⁸. -/
theorem KFourthTrace (half : R) (unit : 2*half=1) {n : Nat} (N : Basis n → Basis n → ComplexScalar R) :
    let sites := qubitIndices n
    let four := MixedDefect.square sites (MixedDefect.square sites N)
    2*trace (oddWords n) (MixedDefect.square (oddWords n) (MixedDefect.square (oddWords n) (K half N))) =
      (trace sites four)^2-trace sites (MixedDefect.square sites four) := by
  dsimp only
  have e := sumMem (oddWords n) (fun a ha => KFourthEntry half unit N a a ha)
  change 2*sumOver (oddWords n) _ = _
  rw [e]; exact oddTrace half unit _

theorem KHermitian (half : R) {n : Nat} (N : Basis n → Basis n → ComplexScalar R)
    (herm : MixedDefect.Hermitian N) : MixedDefect.Hermitian (K half N) := by
  open PhysicalPairedReduction in
  have df : dagger (form (R:=R) (n:=n))=dual := by funext p x; exact formConjugate x p
  open PhysicalPairedReduction in
  have dt : dagger (tensor N N)=tensor N N := by
    funext x y
    change star (N y.1 x.1*N y.2 x.2)=N x.1 y.1*N x.2 y.2
    rw [star_mul,←herm,←herm]
  open PhysicalPairedReduction in
  have dg : dagger (matMul (pairs n) dual (matMul (pairs n) (tensor N N) form)) =
      matMul (pairs n) dual (matMul (pairs n) (tensor N N) form) := by
    rw [daggerProduct,daggerProduct,dt,df,←df,daggerInvolution,matMulAssoc]
  intro a b
  unfold K; rw [star_mul,←PhysicalPairedReduction.realEmbeddingPow,star_ofReal]
  exact congrArg (fun z => ofReal (half^n)*z) (congrFun (congrFun dg b) a).symm

/-- On the doubled physical Pauli two-forms the fourth tensor power has
entry K_ab², with precisely the two inverse-dimension normalizers. -/
theorem doubledTensorEntry (half : R) {n : Nat} (N : Basis n → Basis n → ComplexScalar R)
    (a b : Word n) :
    (ofReal half^n)^2 * sumOver (fourIndices (qubitIndices n)) (fun x => star (doubledWord a x)*
      sumOver (fourIndices (qubitIndices n)) (fun y => tensorFour N x y*doubledWord b y)) =
      MixedDefect.hadamard (K half N) a b := by
  let sites := pairs n
  let L (r : Pair n) := dual (R:=R) a r
  let Q := tensor N N
  let V (r : Pair n) := form (R:=R) r b
  let F (x : Pair n) := sumOver sites (fun y => Q x y*V y)
  have inner (x : Four (Basis n)) : sumOver (fourIndices (qubitIndices n)) (fun y =>
      tensorFour N x y*doubledWord b y)=F x.1*F x.2 := by
    refine (sumOverCongr _ (g:=fun y => (Q x.1 y.1*V y.1)*(Q x.2 y.2*V y.2)) (fun y => ?_)).trans ?_
    · change (Q x.1 y.1*Q x.2 y.2)*(V y.1*V y.2)=_; grind only
    · exact factorProductSum sites sites (fun y => Q x.1 y*V y) (fun y => Q x.2 y*V y)
  have outer : sumOver (fourIndices (qubitIndices n)) (fun x =>
      star (doubledWord (R:=R) a x)*(F x.1*F x.2))=
      (sumOver sites (fun x => L x*F x))*(sumOver sites (fun x => L x*F x)) := by
    refine (sumOverCongr _ (g:=fun x => (L x.1*F x.1)*(L x.2*F x.2)) (fun x => ?_)).trans ?_
    · simp only [doubledWord,star_mul,formConjugate,L]; grind only
    · exact factorProductSum sites sites (fun x => L x*F x) (fun x => L x*F x)
  simp only [inner,outer,MixedDefect.hadamard]
  change (ofReal half^n)^2 * (_*_) = (ofReal half^n * sumOver sites (fun x => L x*F x))*
    (ofReal half^n * sumOver sites (fun x => L x*F x))
  grind only

section Sectors
open FourCopySectors ExteriorPauliBase
local instance {C : Type} [CommRing C] : IntCast C := Ring.intCast

private def plusWeight (p : Perm) : Int := if klein p then 3 else 0
private def minusWeight (p : Perm) : Int := if klein (reorder transposition p) then 3 else 0

set_option maxRecDepth 10000 in
private theorem parityTable : permutations.all (fun p =>
    decide (coefficient .antisymmetric p+coefficient .mixedOdd p=plusWeight p-minusWeight p) &&
    decide (reorder transposition p ∈ permutations) && decide (reorder transposition (reorder transposition p)=p))
    = true := by decide

private theorem castSum {C α : Type} [CommRing C] (xs : List α) (f : α → Int) :
    sumOver xs (fun i => Int.cast (R:=C) (f i))=Int.cast (R:=C) (sumOver xs f) := by
  induction xs with
  | nil => exact (Ring.intCast_ofNat 0).symm
  | cons a xs ih =>
    change Int.cast (f a) + sumOver xs (fun i => Int.cast (f i)) = Int.cast (f a+sumOver xs f)
    rw [Ring.intCast_add,ih]

/-- On Klein-fixed rows, the antisymmetric sector plus the odd line of the
(2,2)-sector is the projector antisymmetrizing the first tensor pair. -/
theorem paritySectors {C α β : Type} [CommRing C] (T : Four α → Four β → C)
    (fix : ∀ p∈permutations, klein p=true → ∀ x y, T (reorder x p) y=T x y) (x : Four α) (y : Four β) :
    rawBlock .antisymmetric T x y + rawBlock .mixedOdd T x y =
      12*(T x y-T (reorder x transposition) y) := by
  unfold rawBlock act
  rw [←sumOverAdd]
  have row (p : Perm) (hp : p∈permutations) :
      Int.cast (coefficient .antisymmetric p)*T (reorder x p) y +
      Int.cast (coefficient .mixedOdd p)*T (reorder x p) y =
      Int.cast (plusWeight p)*T x y - Int.cast (minusWeight p)*T (reorder x transposition) y := by
    have h := List.all_eq_true.mp parityTable p hp
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    have c := congrArg (Int.cast (R:=C)) h.1.1
    have reord : reorder (reorder x transposition) (reorder transposition p)=reorder x p := by
      change ((position (reorder x transposition) _,position (reorder x transposition) _),
        (position (reorder x transposition) _,position (reorder x transposition) _)) = _
      simp only [position_reorder]
      exact congrArg (reorder x) h.2
    simp only [Ring.intCast_add,Ring.intCast_sub] at c
    have a : Int.cast (R:=C) (plusWeight p)*T (reorder x p) y = Int.cast (plusWeight p)*T x y := by
      by_cases e : klein p=true
      · rw [fix p hp e]
      · simp [plusWeight,e]; grind only
    have b : Int.cast (R:=C) (minusWeight p)*T (reorder x p) y =
        Int.cast (minusWeight p)*T (reorder x transposition) y := by
      by_cases e : klein (reorder transposition p)=true
      · rw [←reord,fix _ h.1.2 e]
      · simp [minusWeight,e]; grind only
    rw [←a,←b,←Semiring.right_distrib,c]; grind only
  rw [sumMem permutations row,Compression.sumOverSub,←sumOverMulRight,←sumOverMulRight,castSum,castSum]
  have p : sumOver permutations plusWeight=12 := by decide
  have m : sumOver permutations minusWeight=12 := by decide
  rw [p,m,show Int.cast (R:=C) (12:Int)=(12:C) from Ring.intCast_ofNat 12]; grind only

/-- Unconditional physical parity realization (150)–(153) with both
projectors in the project's 24-scaled convention. -/
theorem oddSectorGram {n : Nat} (x y : Four (Basis n)) :
    let T := @unnormalizedTwirl (ComplexScalar R) _ n imaginaryUnit
    rawBlock .antisymmetric T x y + rawBlock .mixedOdd T x y =
      24*sumOver (oddWords n) (fun p => doubledWord p x*star (doubledWord p y)) := by
  dsimp only
  rw [paritySectors,←oddDoubledResolution]; grind only
  intro p hp k u v
  rw [unnormalizedTwirlEntry _ imaginaryUnit_fourth,unnormalizedTwirlEntry _ imaginaryUnit_fourth,kleinTwirl n p hp k]

private def addM {C α β : Type} [CommRing C] (A B : α → β → C) (i : α) (j : β) := A i j + B i j

private theorem mulAddLeft {C α β γ : Type} [CommRing C] (xs : List β)
    (A B : α → β → C) (T : β → γ → C) :
    matMul xs (addM A B) T=addM (matMul xs A T) (matMul xs B T) := by
  funext i j; unfold matMul addM
  rw [←sumOverAdd]; apply sumOverCongr; intro k; grind only

private theorem mulAddRight {C α β γ : Type} [CommRing C] (xs : List β)
    (T : α → β → C) (A B : β → γ → C) :
    matMul xs T (addM A B)=addM (matMul xs T A) (matMul xs T B) := by
  funext i j; unfold matMul addM
  rw [←sumOverAdd]; apply sumOverCongr; intro k; grind only

private theorem trAdd {C α : Type} [CommRing C] (xs : List α) (A B : α → α → C) :
    trace xs (addM A B)=trace xs A+trace xs B := sumOverAdd _ _ _

theorem pairedParityTwice {C α : Type} [CommRing C] (xs : List (Four α)) (closed : PermutedList xs)
    (H F : Four α → Four α → C) (h : Equivariant H) (f : Equivariant F) :
    let P := fun x y => rawBlock .antisymmetric F x y+rawBlock .mixedOdd F x y
    pairedFrameTrace xs H P P = 24*(pairedFrameTrace xs H (rawBlock .antisymmetric F) F+
      pairedFrameTrace xs H (rawBlock .mixedOdd F) F) := by
  dsimp only
  change pairedFrameTrace xs H (addM _ _) (addM _ _) = _
  have ex (A B U V : Four α → Four α → C) :
      pairedFrameTrace xs H (addM A B) (addM U V) = pairedFrameTrace xs H A U+
        pairedFrameTrace xs H B U+(pairedFrameTrace xs H A V+pairedFrameTrace xs H B V) := by
    simp only [pairedFrameTrace,mulAddRight,mulAddLeft,trAdd]
  rw [ex]
  simp only [pairedBlockOrthogonality xs closed _ _ H F F h f,ite_true,reduceCtorEq,ite_false]
  grind only

private theorem squarePull {C α β : Type} [CommRing C] (xs : List α) (ys : List β)
    (H : α → α → C) (L : α → β → C) (T : β → α → C) :
    let F := matMul ys L T
    let G := matMul xs T (matMul xs H L)
    pairedFrameTrace xs H F F=trace ys (matMul ys G G) := by
  dsimp only
  let X := matMul xs H L
  let F := matMul ys L T
  have e : matMul xs H F=matMul ys X T := (matMulAssoc xs ys H L T).symm
  change trace xs (matMul xs (matMul xs (matMul xs H F) H) F)=_
  rw [e,matMulAssoc _ _ X,matMulAssoc _ _ X,traceMatMulSwap xs ys X]
  simp only [matMulAssoc,F,X]

open RectangularPairedReduction (scaleMatrix)

private theorem scLeft {α β γ : Type} (xs : List β) (s : ComplexScalar R)
    (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    matMul xs (scaleMatrix s A) B=scaleMatrix s (matMul xs A B) := by
  funext i j; unfold matMul scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro k; grind only

private theorem scRight {α β γ : Type} (xs : List β) (s : ComplexScalar R)
    (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    matMul xs A (scaleMatrix s B)=scaleMatrix s (matMul xs A B) := by
  funext i j; unfold matMul scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro k; grind only

private theorem scBlock {α β : Type} (s : Sector) (k : ComplexScalar R)
    (A : Four α → Four β → ComplexScalar R) :
    rawBlock s (scaleMatrix k A)=scaleMatrix k (rawBlock s A) := by
  funext i j; unfold rawBlock act scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro p; grind only

private theorem scTrace {α : Type} (xs : List α) (s : ComplexScalar R) (A : α → α → ComplexScalar R) :
    trace xs (scaleMatrix s A)=s*trace xs A := (sumOverMulLeft xs _ s).symm

/-- Exact paired trace of the squared Hadamard matrix of the literal odd
Pauli frame. The block normalization is the raw 24-scaled S4 convention.
A is arbitrary and μ may be any real diagonal. -/
theorem physicalParityTrace (half inv24 : R) (unit24 : 24*inv24=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let src := fourIndices (List.finRange 7)
    let H := tensorFour (PhysicalPairedReduction.diagonal mu)
    let F := RectangularPairedReduction.normalizedFrame half A
    let B := MixedDefect.hadamard (K half (SymmetricDefect.orbitMatrix A mu))
    (ofReal (half^n))^2*(pairedFrameTrace src H (rawBlock .antisymmetric F) F+
      pairedFrameTrace src H (rawBlock .mixedOdd F) F) = 24*trace (oddWords n) (MixedDefect.square (oddWords n) B) := by
  let src := fourIndices (List.finRange 7)
  let amb := fourIndices (qubitIndices n)
  let os := oddWords n
  let r := ofReal (half^n)
  let H := tensorFour (PhysicalPairedReduction.diagonal mu)
  let F := RectangularPairedReduction.normalizedFrame half A
  let U := tensorFour A
  let V := transpose (tensorFour (ComplexPauliMoment.conjugate A))
  let D (x : Four (Basis n)) (p : Word n) := doubledWord (R:=R) p x
  let E (p : Word n) (x : Four (Basis n)) := star (D x p)
  let T := @unnormalizedTwirl (ComplexScalar R) _ n imaginaryUnit
  let L := matMul amb V D
  let J := matMul amb E U
  let G := matMul src J (matMul src H L)
  let N := SymmetricDefect.orbitMatrix A mu
  let B := MixedDefect.hadamard (K half N)
  let P := addM (rawBlock .antisymmetric F) (rawBlock .mixedOdd F)
  have allS := fullPermuted (List.finRange 7) (List.nodup_finRange 7) (fun i => List.mem_finRange i)
  have allA := fullPermuted (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  have ve : Equivariant V := fun p hp i j => tensorEquivariant _ p hp j i
  have gram : addM (rawBlock .antisymmetric T) (rawBlock .mixedOdd T)=scaleMatrix 24 (matMul os D E) := by
    funext x y; exact oddSectorGram x y
  have block (s : Sector) : rawBlock s F = scaleMatrix r (matMul amb (matMul amb V (rawBlock s T)) U) := by
    change rawBlock s (scaleMatrix r (matMul amb (matMul amb V T) U))=_
    rw [scBlock,blockLeft,blockRight amb allA s V T ve]
  have pp : P = scaleMatrix (24*r) (matMul os L J) := by
    unfold P; rw [block,block]
    have dist (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R) :
        addM (scaleMatrix r A) (scaleMatrix r B)=scaleMatrix r (addM A B) := by
      funext i j; unfold addM scaleMatrix; grind only
    rw [dist,←mulAddLeft,←mulAddRight,gram,scRight,scLeft]
    have e : matMul amb (matMul amb V (matMul os D E)) U=matMul os L J := by simp only [L,J,matMulAssoc]
    rw [e]; funext i j; unfold scaleMatrix; grind only
  have tensorN : tensorFour N=matMul src (matMul src U H) V := by
    unfold N SymmetricDefect.orbitMatrix; rw [←RectangularPairedReduction.rankSevenCoefficients_eq]
    exact RectangularPairedReduction.fourCoefficients _ _ _ _
  have ge : G=matMul amb E (matMul amb (tensorFour N) D) := by
    rw [tensorN]; simp only [G,J,L,matMulAssoc]
  have bg : B = scaleMatrix (r^2) G := by
    funext a b
    rw [ge]; unfold B scaleMatrix r
    rw [PhysicalPairedReduction.realEmbeddingPow]; exact (doubledTensorEntry half N a b).symm
  have e₁ := pairedParityTwice src allS H F (tensorEquivariant _) (normalizedFrameStructure half A).1
  change pairedFrameTrace src H P P = _ at e₁
  rw [pp,RectangularPairedReduction.pairedFrameTraceScale,squarePull] at e₁
  change (24*r)*(24*r)*trace os (matMul os G G)=_ at e₁
  change r^2*_=24*trace os (MixedDefect.square os B)
  rw [bg]; simp only [MixedDefect.square,scLeft,scRight,scTrace]
  have z : 24*ofReal inv24=(1:ComplexScalar R) := by
    change ofReal 24*ofReal inv24=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  have ec := congrArg (fun c => ofReal inv24*c) e₁
  change _ = ofReal inv24*(24*_) at ec
  rw [←Semiring.mul_assoc (ofReal inv24) 24,CommSemiring.mul_comm (ofReal inv24) 24,z,Semiring.one_mul] at ec
  rw [←ec]
  calc
    _ = (24*ofReal inv24)*(24*(r^2*(r^2*trace os (matMul os G G)))) := by grind only
    _ = _ := by rw [z,Semiring.one_mul]

theorem pairedMixedLines {C α : Type} [CommRing C] (xs : List (Four α)) (closed : PermutedList xs)
    (H F : Four α → Four α → C) (he : Equivariant H) (fe : Equivariant F) :
    pairedFrameTrace xs H (rawBlock .mixedEven F) F=pairedFrameTrace xs H (rawBlock .mixedOdd F) F := by
  rw [←traceBlockFrame xs closed .mixedEven H F F he,←traceBlockFrame xs closed .mixedOdd H F F he,
    rawBlockTrace,rawBlockTrace]
  apply equalMixedTrace
  exact permTraceClass xs closed _ (mulEquivariant xs closed _ F
    (mulEquivariant xs closed _ H (mulEquivariant xs closed H F he fe) he) fe)

/-- Exactly the mixed and alternating terms used by Rank7PhysicalDefectAssembly. -/
theorem physicalMixedPlusAlternating (half inv24 : R) (unit24 : 24*inv24=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let B := MixedDefect.hadamard (K half (SymmetricDefect.orbitMatrix A mu))
    (half^n)^2*(SymmetricDefect.rawSector half A mu .antisymmetric+
      SymmetricDefect.rawSector half A mu .mixedEven)=
      24*MixedDefect.realTrace (oddWords n) (MixedDefect.square (oddWords n) B) := by
  have ec := physicalParityTrace half inv24 unit24 A mu
  dsimp only at ec ⊢
  let src := fourIndices (List.finRange 7)
  let H := tensorFour (PhysicalPairedReduction.diagonal mu)
  let F := RectangularPairedReduction.normalizedFrame half A
  have full := fullPermuted (List.finRange 7) (List.nodup_finRange 7) (fun i => List.mem_finRange i)
  rw [←pairedMixedLines src full H F (tensorEquivariant _) (normalizedFrameStructure half A).1] at ec
  rw [←PhysicalPairedReduction.realEmbeddingPow (half^n) 2] at ec
  have er := congrArg ComplexScalar.re ec
  change (ofReal ((half^n)^2)*(_+_)).re=(ofReal (24:R)*_).re at er
  simp only [ComplexScalar.re_mul,ComplexScalar.re_add,ofReal,Semiring.zero_mul] at er
  change (half^n)^2*(SymmetricDefect.rawSector half A mu .antisymmetric+
      SymmetricDefect.rawSector half A mu .mixedEven)-0=24*MixedDefect.realTrace _ _-0 at er
  grind only

end Sectors
end RankSeven.PhysicalMixedFrame

#print axioms RankSeven.PhysicalMixedFrame.oddDoubledResolution
#print axioms RankSeven.PhysicalMixedFrame.oddPairResolution
#print axioms RankSeven.PhysicalMixedFrame.KTrace
#print axioms RankSeven.PhysicalMixedFrame.KProduct
#print axioms RankSeven.PhysicalMixedFrame.KHermitian
#print axioms RankSeven.PhysicalMixedFrame.KFourthTrace
#print axioms RankSeven.PhysicalMixedFrame.oddSectorGram
#print axioms RankSeven.PhysicalMixedFrame.doubledTensorEntry
#print axioms RankSeven.PhysicalMixedFrame.physicalMixedPlusAlternating
