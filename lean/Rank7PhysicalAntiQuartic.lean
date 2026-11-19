import Rank7SymmetricDefect
import Rank7AnticommutingDefect
import Rank7MixedDefect

/-! Physical Pauli multiplication and the quartic expansion of the
anticommuting defect. Signs use the Hermitian matrices I,X,Y,Z. -/
namespace RankSeven.PhysicalAntiQuartic

open Lean.Grind Pauli SymmetricDefect
variable {C : Type} [CommRing C]

def axisProductLabel : Axis → Axis → Axis
  | .identity,b => b
  | a,.identity => a
  | .x,.y | .y,.x => .z
  | .y,.z | .z,.y => .x
  | .z,.x | .x,.z => .y
  | _,_ => .identity

def productLabel : {n : Nat} → Word n → Word n → Word n
  | _,.empty,.empty => .empty
  | _,.cons a p,.cons b q => .cons (axisProductLabel a b) (productLabel p q)

def axisCocycle (i : C) : Axis → Axis → C
  | .x,.y | .y,.z | .z,.x => i
  | .y,.x | .z,.y | .x,.z => -i
  | _,_ => 1

def cocycle (i : C) : {n : Nat} → Word n → Word n → C
  | _,.empty,.empty => 1
  | _,.cons a p,.cons b q => axisCocycle i a b * cocycle i p q

theorem labelComm {n : Nat} (p q : Word n) : productLabel p q=productLabel q p := by
  induction p with
  | empty => cases q; rfl
  | cons a p ih => cases q with
    | cons b q => simp only [productLabel,ih q]; cases a <;> cases b <;> rfl

theorem labelAssoc {n : Nat} (p q r : Word n) :
    productLabel (productLabel p q) r=productLabel p (productLabel q r) := by
  induction p with
  | empty => cases q; cases r; rfl
  | cons a p ih => cases q with
    | cons b q => cases r with
      | cons c r => simp only [productLabel,ih q r]; cases a <;> cases b <;> cases c <;> rfl

private theorem axisCocycleLaw (i : C) (a b c : Axis) (isq : i^2= -1) :
    axisCocycle i a b*axisCocycle i (axisProductLabel a b) c =
    axisCocycle i b c*axisCocycle i a (axisProductLabel b c) := by
  cases a <;> cases b <;> cases c <;> simp [axisCocycle,axisProductLabel] <;> grind

theorem cocycleLaw {n : Nat} (i : C) (isq : i^2= -1) (p q r : Word n) :
    cocycle i p q*cocycle i (productLabel p q) r = cocycle i q r*cocycle i p (productLabel q r) := by
  induction p with
  | empty => cases q; cases r; rfl
  | cons a p ih => cases q with
    | cons b q => cases r with
      | cons c r => simp only [cocycle,productLabel]; have := axisCocycleLaw i a b c isq; have := ih q r; grind

private theorem axisSwap (i : C) (a b : Axis) : axisCocycle i a b = phase (axisAnti a b)*axisCocycle i b a := by
  cases a <;> cases b <;> simp [axisCocycle,axisAnti,phase] <;> grind

theorem cocycleSwap {n : Nat} (i : C) (p q : Word n) : cocycle i p q=chi p q*cocycle i q p := by
  induction p with
  | empty => cases q; simp [cocycle,chi,anti,phase]; grind
  | cons a p ih => cases q with
    | cons b q => rw [cocycle,cocycle,chiCons,axisSwap i a b,ih q]; grind

private theorem axisProduct (i : C) (isq : i^2= -1) (p q : Axis) (a b : Bool) :
    matMul [false,true] (entry i p) (entry i q) a b = axisCocycle i p q*entry i (axisProductLabel p q) a b := by
  cases p <;> cases q <;> cases a <;> cases b <;>
    simp [matMul,sumOver,entry,axisCocycle,axisProductLabel] <;> grind

/-- Matrix multiplication on the actual binary computational basis. -/
theorem physicalWordProduct {n : Nat} (i : C) (isq : i^2= -1) (p q : Word n) (a b : Basis n) :
    matMul (qubitIndices n) (wordEntry i p) (wordEntry i q) a b =
      cocycle i p q*wordEntry i (productLabel p q) a b := by
  induction p with
  | empty => cases q; simp [matMul,qubitIndices,sumOver,wordEntry,productLabel,cocycle]; grind
  | cons p ps ih =>
    cases q with
    | cons q qs =>
      rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩
      change matMul (productIndices [false,true] (qubitIndices _))
        (tensor (entry i p) (wordEntry i ps)) (tensor (entry i q) (wordEntry i qs)) (a,x) (b,y)=_
      rw [←tensorMatMul]
      change matMul _ _ _ a b*matMul _ _ _ x y=_
      rw [axisProduct i isq,ih]; simp only [cocycle,productLabel,wordEntry]; grind

theorem wordCommutation {n : Nat} (i : C) (isq : i^2= -1) (p q : Word n) (a b : Basis n) :
    matMul (qubitIndices n) (wordEntry i p) (wordEntry i q) a b =
      chi p q*matMul (qubitIndices n) (wordEntry i q) (wordEntry i p) a b := by
  rw [physicalWordProduct i isq,physicalWordProduct i isq,cocycleSwap i p q,labelComm p q]; grind

/-- Low bit of the power of i is anticommutation; this Boolean is the
sign left after the single factor i is removed for an anticommuting pair. -/
def axisReversed : Axis → Axis → Bool
  | .y,.x | .z,.y | .x,.z => true
  | _,_ => false

def negativeProduct : {n : Nat} → Word n → Word n → Bool
  | _,.empty,.empty => false
  | _,.cons a p,.cons b q =>
    axisReversed a b ^^ negativeProduct p q ^^ (axisAnti a b && anti p q)

private theorem localPhaseBits (i : C) (a b : Axis) :
    axisCocycle i a b=phase (axisReversed a b)*(if axisAnti a b then i else 1) := by
  cases a <;> cases b <;> simp [axisCocycle,axisReversed,axisAnti,phase] <;> grind

theorem cocyclePhaseBits {n : Nat} (i : C) (isq : i^2= -1) (p q : Word n) :
    cocycle i p q=phase (negativeProduct p q)*(if anti p q then i else 1) := by
  induction p with
  | empty => cases q; simp [cocycle,negativeProduct,phase,anti] <;> grind
  | cons a p ih =>
    cases q with
    | cons b q =>
      rw [cocycle,localPhaseBits,ih q]
      simp only [negativeProduct,anti]
      cases axisReversed a b <;> cases negativeProduct p q <;> cases axisAnti a b <;> cases anti p q <;>
        simp [phase] <;> grind

theorem anticommutingProductSign {n : Nat} (i : C) (isq : i^2= -1) (p q : Word n) (h : anti p q=true) :
    cocycle i p q=i*phase (negativeProduct p q) := by rw [cocyclePhaseBits i isq,h]; grind

noncomputable local instance {n} : DecidableEq (Word n) := Classical.typeDecidableEq _

theorem labelSelf {n : Nat} (p : Word n) : productLabel p p=unitWord n := by
  induction p with
  | empty => rfl
  | cons a p ih => simp only [productLabel,unitWord,ih]; cases a <;> rfl

theorem labelUnit {n : Nat} (p : Word n) : productLabel (unitWord n) p=p := by
  induction p with
  | empty => rfl
  | cons a p ih => simp only [unitWord,productLabel,axisProductLabel,ih]

theorem cocycleSelf {n : Nat} (i : C) (p : Word n) : cocycle i p p=1 := by
  induction p with
  | empty => rfl
  | cons a p ih => rw [cocycle,ih]; cases a <;> simp [axisCocycle] <;> grind

private theorem pairSum {α β : Type} (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro x
  simp [sumOver,List.map_map,Function.comp_def]

theorem physicalWordTrace {n : Nat} (i : C) (p : Word n) :
    trace (qubitIndices n) (wordEntry i p) = if p=unitWord n then (2:C)^n else 0 := by
  induction p with
  | empty => simp [qubitIndices,trace,wordEntry,unitWord,sumOver] <;> grind
  | cons a p ih =>
    change sumOver (productIndices [false,true] (qubitIndices _))
      (fun b => entry i a b.1 b.1*wordEntry i p b.2 b.2)=_
    rw [factorProductSum [false,true] (qubitIndices _) (fun b => entry i a b b) (fun x => wordEntry i p x x)]
    unfold trace at ih; rw [ih]
    cases a <;> by_cases e : p=unitWord _ <;> simp [sumOver,entry,unitWord,e,Semiring.pow_succ] <;> grind

abbrev Matrix (α : Type) (C : Type) := α → α → C

def scale {α : Type} (z : C) (A : Matrix α C) : Matrix α C := fun x y => z*A x y
def matrixSum {α β : Type} (xs : List β) (A : β → Matrix α C) : Matrix α C := fun x y => sumOver xs (fun b => A b x y)

private theorem scaleLeft {α : Type} (xs : List α) (c : C) (A B : Matrix α C) :
    matMul xs (scale c A) B=scale c (matMul xs A B) := by
  funext x y; simp only [matMul,scale,sumOverMulLeft]; apply sumOverCongr; intro z; grind

private theorem scaleRight {α : Type} (xs : List α) (c : C) (A B : Matrix α C) :
    matMul xs A (scale c B)=scale c (matMul xs A B) := by
  funext x y; simp only [matMul,scale,sumOverMulLeft]; apply sumOverCongr; intro z; grind

private theorem sumLeft {α β : Type} (xs : List α) (ys : List β) (F : β → Matrix α C) (A : Matrix α C) :
    matMul xs (matrixSum ys F) A=matrixSum ys (fun b => matMul xs (F b) A) := by
  funext x y; simp only [matMul,matrixSum,sumOverMulRight]; rw [sumOverSwap]

private theorem sumRight {α β : Type} (xs : List α) (ys : List β) (A : Matrix α C) (F : β → Matrix α C) :
    matMul xs A (matrixSum ys F)=matrixSum ys (fun b => matMul xs A (F b)) := by
  funext x y; simp only [matMul,matrixSum,sumOverMulLeft]; rw [sumOverSwap]

private theorem traceSum {α β : Type} (xs : List α) (ys : List β) (F : β → Matrix α C) :
    trace xs (matrixSum ys F)=sumOver ys (fun b => trace xs (F b)) := by
  unfold trace matrixSum; rw [sumOverSwap]

private theorem traceScale {α : Type} (xs : List α) (z : C) (A : Matrix α C) :
    trace xs (scale z A)=z*trace xs A := (sumOverMulLeft _ _ _).symm

theorem productMatrix {n : Nat} (i : C) (isq : i^2= -1) (p q : Word n) :
    matMul (qubitIndices n) (wordEntry i p) (wordEntry i q)=scale (cocycle i p q) (wordEntry i (productLabel p q)) := by
  funext x y; exact physicalWordProduct i isq p q x y

def quadTrace {α : Type} (xs : List α) (A B K D : Matrix α C) : C :=
  trace xs (matMul xs (matMul xs (matMul xs A B) K) D)

def quadLabel {n : Nat} (a b c p : Word n) := productLabel (productLabel (productLabel a b) c) p

def quadPhase {n : Nat} (i : C) (a b c p : Word n) :=
  cocycle i a b*cocycle i (productLabel a b) c*cocycle i (productLabel (productLabel a b) c) p

/-- All physical four-word traces vanish off zero total label. -/
theorem physicalQuadTrace {n : Nat} (i : C) (isq : i^2= -1) (a b c p : Word n) :
    quadTrace (qubitIndices n) (wordEntry i a) (wordEntry i b) (wordEntry i c) (wordEntry i p) =
      if quadLabel a b c p=unitWord n then (2:C)^n*quadPhase i a b c p else 0 := by
  unfold quadTrace quadLabel quadPhase
  rw [productMatrix i isq,scaleLeft,productMatrix i isq,scaleLeft,scaleLeft,productMatrix i isq,
    traceScale,traceScale,traceScale,physicalWordTrace]
  split <;> grind

private theorem unitChi {n : Nat} (p : Word n) : (chi (unitWord n) p : C)=1 := by
  induction p with
  | empty => rfl
  | cons a p ih => rw [unitWord,chiCons,ih]; cases a <;> simp [phase,axisAnti] <;> grind

local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem idEntry {n : Nat} (i : C) (u v : Basis n) :
    wordEntry i (unitWord n) u v=if u=v then 1 else 0 := by
  induction n with
  | zero => cases u; cases v; simp [unitWord,wordEntry]; grind
  | succ n ih =>
    rcases u with ⟨a,u⟩; rcases v with ⟨b,v⟩
    cases a <;> cases b <;> by_cases e : u=v <;> simp [unitWord,wordEntry,entry,ih,e] <;> grind

private theorem select {n : Nat} (p : Basis n) (f : Basis n → C) :
    sumOver (qubitIndices n) (fun x => if p=x then f x else 0)=f p :=
  ExteriorPauliBase.sumOnIndex _ _ _ (HyperplaneIncidence.normalsNodup _) (qubitIndicesComplete _)

theorem pauliReconstruction {n : Nat} (i : C) (isq : i^2= -1) (A : Matrix (Basis n) C) (x y : Basis n) :
    sumOver (words n) (fun p => traceWord i A p*wordEntry i p x y)=(2:C)^n*A x y := by
  let xs := qubitIndices n
  let d := (2:C)^n
  have kernel (a b : Basis n) : sumOver (words n) (fun p => wordEntry i p b a*wordEntry i p x y)=
      if x=a then (if y=b then d else 0) else 0 := by
    have h := signedResolution i isq (unitWord n) b a x y
    simp only [unitChi,Semiring.one_mul,idEntry] at h
    rw [h]; by_cases e : x=a <;> by_cases f : y=b <;> simp [d,e,f,eq_comm (a:=b) (b:=y)] <;> grind
  unfold traceWord trace matMul
  simp only [sumOverMulRight]
  rw [sumOverSwap (words n) xs]
  calc
    _ = sumOver xs (fun a => if x=a then d*A a y else 0) := by
      apply sumOverCongr; intro a
      rw [sumOverSwap (words n) xs]
      calc
        _ = sumOver xs (fun b => A a b * (if x=a then (if y=b then d else 0) else 0)) := by
          apply sumOverCongr; intro b; rw [←kernel,sumOverMulLeft]
          apply sumOverCongr; intro p; grind
        _ = sumOver xs (fun b => if y=b then (if x=a then d*A a b else 0) else 0) := by
          apply sumOverCongr; intro b; by_cases e : x=a <;> by_cases f : y=b <;> simp [e,f] <;> grind
        _ = _ := select y _
    _ = _ := select x _

def synthesis {n : Nat} (i di : C) (c : Word n → C) : Matrix (Basis n) C :=
  scale di (matrixSum (words n) (fun a => scale (c a) (wordEntry i a)))

theorem physicalSynthesis {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (A : Matrix (Basis n) C) : synthesis i di (traceWord i A)=A := by
  funext x y
  change di*sumOver _ (fun a => traceWord i A a*wordEntry i a x y)=_
  rw [pauliReconstruction i isq]; grind

private theorem cocycleUnit {n : Nat} (i : C) (a : Word n) : cocycle i a (unitWord n)=1 := by
  induction a with
  | empty => rfl
  | cons a p ih => rw [unitWord,cocycle,ih]; cases a <;> simp [axisCocycle] <;> grind

theorem physicalConjugation {n : Nat} (i : C) (isq : i^2= -1) (p a : Word n) :
    let xs := qubitIndices n
    matMul xs (matMul xs (wordEntry i p) (wordEntry i a)) (wordEntry i p) =
      scale (chi p a) (wordEntry i a) := by
  dsimp only
  have lbl : productLabel (productLabel p a) p=a := by
    rw [labelComm p a,labelAssoc,labelSelf,labelComm _ (unitWord n),labelUnit]
  rw [productMatrix i isq,scaleLeft,productMatrix i isq,lbl]
  have h := cocycleLaw i isq a p p
  rw [labelSelf,cocycleSelf,cocycleUnit] at h
  rw [labelComm a p] at h
  have sw := cocycleSwap i p a
  funext x y; unfold scale; grind

def cubicWord {α : Type} (xs : List α) (P A B K : Matrix α C) : C :=
  trace xs (matMul xs (matMul xs (matMul xs P A) (matMul xs P B)) (matMul xs P K))

/-- This is precisely the extra character occurring in the t₁t₃ cycle. -/
theorem cubicCorrection {n : Nat} (i : C) (isq : i^2= -1) (p a b c : Word n) :
    cubicWord (qubitIndices n) (wordEntry i p) (wordEntry i a) (wordEntry i b) (wordEntry i c) =
    chi p a*chi p c*quadTrace (qubitIndices n) (wordEntry i a) (wordEntry i b) (wordEntry i c) (wordEntry i p) := by
  let xs := qubitIndices n
  let P := wordEntry i p; let A := wordEntry i a; let B := wordEntry i b; let K := wordEntry i c
  have grouped : matMul xs (matMul xs (matMul xs P A) (matMul xs P B)) (matMul xs P K) =
      matMul xs (matMul xs (matMul xs P A) P) (matMul xs B (matMul xs P K)) := by simp only [matMulAssoc]
  have swap : matMul xs P K = scale (chi p c) (matMul xs K P) := by
    funext x y; exact wordCommutation i isq p c x y
  change trace xs _ = _*quadTrace xs A B K P
  rw [grouped,swap]
  change trace xs (matMul xs (matMul xs (matMul xs (wordEntry i p) (wordEntry i a)) (wordEntry i p)) _) = _
  rw [physicalConjugation i isq,scaleLeft,scaleRight,scaleRight,traceScale,traceScale]
  unfold quadTrace; simp only [matMulAssoc]
  change _ = _*trace xs (matMul xs A (matMul xs B (matMul xs K P)))
  grind

private theorem twoSumSquare {α : Type} (xs : List α) (f : α → C) :
    (sumOver xs f)^2=sumOver xs (fun a => sumOver xs (fun b => f a*f b)) := by
  calc
    _ = sumOver xs f*sumOver xs f := by grind
    _ = _ := by rw [sumOverMulRight]; apply sumOverCongr; intro a; exact sumOverMulLeft _ _ _

def antiMass {n : Nat} (c : Word n → C) : C :=
  sumOver (words n) (fun a => sumOver (words n) (fun b => if anti a b then (c a)^2*(c b)^2 else 0))

theorem pairSource {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (A : Matrix (Basis n) C) :
    let d := (2:C)^n
    let c := traceWord i A
    3*d*(trace (qubitIndices n) (matMul (qubitIndices n) A A))^2 -
       3*sumOver (words n) (fun a => (c a)^2*traceWordSquare i A a) = 6*di*antiMass c := by
  dsimp only
  let c := traceWord i A
  let ws := words n
  let d := (2:C)^n
  let unsigned := (sumOver ws (fun a => (c a)^2))^2
  let signed := sumOver ws (fun a => sumOver ws (fun b => chi a b*(c a)^2*(c b)^2))
  have gap : unsigned-signed=2*antiMass c := by
    unfold unsigned signed antiMass
    rw [twoSumSquare,←Compression.sumOverSub,sumOverMulLeft]; apply sumOverCongr; intro a
    rw [←Compression.sumOverSub,sumOverMulLeft]; apply sumOverCongr; intro b
    unfold chi; cases anti a b <;> simp [phase] <;> grind
  have signedEq : signed=d*sumOver ws (fun a => (c a)^2*traceWordSquare i A a) := by
    unfold signed; rw [sumOverMulLeft]; apply sumOverCongr; intro a
    have e := congrArg (fun z => (c a)^2*z) (fourierTrace i isq A a)
    rw [sumOverMulLeft] at e
    calc
      _ = sumOver ws (fun b => (c a)^2*(chi a b*(c b)^2)) := by apply sumOverCongr; intro b; grind
      _ = _ := by rw [e]; unfold d; grind
  have tr := pauliParseval i isq A
  change sumOver ws (fun a => (c a)^2)=d*_ at tr
  unfold unsigned at gap
  rw [tr,signedEq] at gap
  change d*di=1 at inv
  change 3*d*_-3*sumOver ws (fun a => (c a)^2*traceWordSquare i A a)=6*di*antiMass c
  grind

private theorem quadRotate {α : Type} (xs : List α) (P A B K : Matrix α C) :
    quadTrace xs P A B K=quadTrace xs A B K P := by
  unfold quadTrace; simp only [matMulAssoc]
  rw [traceMatMulSwap xs xs P]; simp only [matMulAssoc]

def wordSum4 {n : Nat} (f : Word n → Word n → Word n → Word n → C) :=
  sumOver (words n) (fun p => sumOver (words n) (fun a => sumOver (words n) (fun b => sumOver (words n) (f p a b))))

private theorem reverseThree {α : Type} (xs : List α) (f : α → α → α → C) :
    sumOver xs (fun a => sumOver xs (fun b => sumOver xs (f a b))) =
    sumOver xs (fun t => sumOver xs (fun b => sumOver xs (fun a => f a b t))) := by
  calc
    _ = sumOver xs (fun b => sumOver xs (fun a => sumOver xs (f a b))) := sumOverSwap _ _ _
    _ = sumOver xs (fun b => sumOver xs (fun t => sumOver xs (fun a => f a b t))) := by
      apply sumOverCongr; intro b; exact sumOverSwap _ _ _
    _ = _ := sumOverSwap _ _ _

private theorem expandQuad {n : Nat} (i di : C) (c : Word n → C) :
    let xs := qubitIndices n
    let A := synthesis i di c
    quadTrace xs A A A A = di^4*wordSum4 (fun p a b t =>
      c p*c a*c b*c t*quadTrace xs (wordEntry i a) (wordEntry i b) (wordEntry i t) (wordEntry i p)) := by
  dsimp only
  unfold synthesis quadTrace
  simp only [scaleLeft,scaleRight,sumLeft,sumRight,traceScale,traceSum]
  unfold wordSum4
  simp only [sumOverMulLeft]
  apply sumOverCongr; intro p
  conv => lhs; rw [reverseThree]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro t
  have e := quadRotate (qubitIndices n) (wordEntry i p) (wordEntry i a) (wordEntry i b) (wordEntry i t)
  unfold quadTrace at e
  grind

private theorem expandCubic {n : Nat} (i di : C) (c : Word n → C) (p : Word n) :
    let xs := qubitIndices n
    let A := synthesis i di c
    cubicWord xs (wordEntry i p) A A A =
      di^3*sumOver (words n) (fun a => sumOver (words n) (fun b => sumOver (words n) (fun t =>
       c a*c b*c t*cubicWord xs (wordEntry i p) (wordEntry i a) (wordEntry i b) (wordEntry i t)))) := by
  dsimp only
  unfold synthesis cubicWord
  simp only [scaleLeft,scaleRight,sumLeft,sumRight,traceScale,traceSum,sumOverMulLeft]
  conv => lhs; rw [reverseThree]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro t; grind

/-- Ordered coefficient version of the four-distinct-label correction; the
same expression also includes the correction from repeated labels. -/
noncomputable def orderedQuartic {n : Nat} (i : C) (c : Word n → C) : C :=
  wordSum4 (fun p a b t => if quadLabel a b t p=unitWord n then
    c p*c a*c b*c t*(chi p a*chi p t-1)*quadPhase i a b t p else 0)

theorem quarticCorrection {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (A : Matrix (Basis n) C) :
    let xs := qubitIndices n
    let d := (2:C)^n
    let c := traceWord i A
    sumOver (words n) (fun p => c p*cubicWord xs (wordEntry i p) A A A) -
      d*quadTrace xs A A A A=di^2*orderedQuartic i c := by
  dsimp only
  let c := traceWord i A
  have cube (p : Word n) := expandCubic i di c p
  have four := expandQuad i di c
  have synth : synthesis i di c=A := physicalSynthesis i isq di inv A
  simp only [synth] at cube four
  change sumOver (words n) (fun p => c p*cubicWord _ _ A A A) - _ = _
  rw [four]; simp only [cube]
  unfold orderedQuartic wordSum4
  simp only [sumOverMulLeft]
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro p
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro a
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro b
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro t
  rw [cubicCorrection i isq,physicalQuadTrace i isq]
  split <;> grind

open FourCopySectors
open ExteriorPauliBase (permutations oddPermutation)
open GenericExteriorKernel (reorder)
attribute [local instance] Ring.intCast

private theorem intSum {α : Type} (xs : List α) (f : α → Int) :
    Int.cast (R:=C) (sumOver xs f)=sumOver xs (fun p => Int.cast (R:=C) (f p)) := by
  induction xs with
  | nil => exact Ring.intCast_ofNat 0
  | cons a xs ih => change Int.cast (R:=C) (f a+sumOver xs f)=_ ; rw [Ring.intCast_add,ih]; rfl

private theorem countTerm (w : Perm → Int) (z : C) :
    sumOver permutations (fun p => Int.cast (R:=C) (w p)*z)=Int.cast (R:=C) (sumOver permutations w)*z := by
  rw [←sumOverMulRight,←intSum]

/-- The even elements outside the Klein four form the class of the eight
three-cycles. The four Klein elements each contribute the identity trace. -/
theorem alternatingClassTrace {α : Type} (xs : List (Four α)) (closed : PermutedList xs)
    (K : Matrix (Four α) C) (equiv : Equivariant K) (fixed : KleinFixed K) :
    trace xs (rawBlock .antisymmetric K) = 4*permTrace xs K ident+8*permTrace xs K rotation-
      12*permTrace xs K transposition := by
  let wi (p : Perm) : Int := if klein p then 1 else 0
  let wr (p : Perm) : Int := if !klein p && !oddPermutation p then 1 else 0
  let wt (p : Perm) : Int := if oddPermutation p then -1 else 0
  have counts : (sumOver permutations wi,sumOver permutations wr,sumOver permutations wt)=(4,8,-12) := by decide
  have tab : permutations.all (fun p => (if klein p then !oddPermutation p else
    oddPermutation p || permutations.any (fun h => conjugate h p == rotation)))=true := by decide
  rw [rawBlockTrace]
  unfold characterTrace
  calc
    _ = sumOver permutations (fun p => Int.cast (R:=C) (wi p)*permTrace xs K ident+
          Int.cast (R:=C) (wr p)*permTrace xs K rotation+Int.cast (R:=C) (wt p)*permTrace xs K transposition) := by
      apply congrArg List.sum; apply List.map_congr_left; intro p hp
      have info := List.all_eq_true.mp tab p hp
      by_cases hk : klein p=true
      · have even : oddPermutation p=false := by simpa [hk] using info
        have e : permTrace xs K p=permTrace xs K ident := by apply sumOverCongr; intro x; exact fixed p hp hk x x
        simp [wi,wr,wt,hk,even,coefficient,e] <;> grind
      · by_cases ho : oddPermutation p=true
        · have e := oddTrace xs closed K equiv fixed p hp ho
          simp [wi,wr,wt,hk,ho,coefficient,e,Ring.intCast_neg] <;> grind
        · rw [ite_eq_right hk,Bool.eq_false_iff.mpr ho,Bool.false_or] at info
          obtain ⟨h,hh,raw⟩ := List.any_eq_true.mp info
          have e := beq_iff_eq.mp raw
          have tr := permTraceClass xs closed K equiv h hh p hp
          rw [e] at tr
          simp [wi,wr,wt,hk,ho,coefficient,tr] <;> grind
    _ = _ := by
      rw [sumOverAdd,sumOverAdd,countTerm,countTerm,countTerm]
      simp only [Prod.mk.injEq] at counts
      rw [counts.1,counts.2.1,counts.2.2]
      simp [Ring.intCast_neg] <;> grind

private theorem idTensor {α : Type} (xs : List α) (X : Matrix α C) :
    permTrace (fourIndices xs) (tensorFour X) ident=(trace xs X)^4 := by
  change sumOver (productIndices (productIndices xs xs) (productIndices xs xs))
    (fun uv => (X uv.1.1 uv.1.1*X uv.1.2 uv.1.2)*(X uv.2.1 uv.2.1*X uv.2.2 uv.2.2))=_
  let d (v : α × α) := X v.1 v.1 * X v.2 v.2
  rw [factorProductSum (productIndices xs xs) (productIndices xs xs) d d]
  unfold d
  rw [factorProductSum xs xs (fun x => X x x) (fun x => X x x)]
  unfold trace; grind

private theorem rotationTensor {α : Type} (xs : List α) (X : Matrix α C) :
    permTrace (fourIndices xs) (tensorFour X) rotation=trace xs X*trace xs (matMul xs (matMul xs X X) X) := by
  change sumOver (productIndices (productIndices xs xs) (productIndices xs xs))
    (fun uv => (X uv.1.2 uv.1.1*X uv.2.1 uv.1.2)*(X uv.1.1 uv.2.1*X uv.2.2 uv.2.2))=_
  let f a b c := X a c*X c b*X b a
  have cubed : trace xs (matMul xs (matMul xs X X) X) =
      sumOver xs (fun a => sumOver xs (fun b => sumOver xs (f a b))) := by
    unfold f trace matMul; simp only [sumOverMulRight]
  rw [cubed]
  calc
    _ = (sumOver xs (fun a => sumOver xs (fun b => sumOver xs (f a b))))*trace xs X := by
      simp only [pairSum,sumOverMulRight]
      apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro c
      change _ = f a b c*sumOver xs (fun t => X t t)
      rw [sumOverMulLeft]; apply sumOverCongr; intro t; unfold f; grind
    _ = _ := CommSemiring.mul_comm _ _

def wordFrame {n : Nat} (i : C) (A : Matrix (Basis n) C) : Matrix (Four (Basis n)) C :=
  matrixSum (words n) (fun p => tensorFour (matMul (qubitIndices n) (wordEntry i p) A))

private theorem permSum {α ι : Type} (xs : List (Four α)) (ls : List ι) (F : ι → Matrix (Four α) C) (p : Perm) :
    permTrace xs (matrixSum ls F) p = sumOver ls (fun k => permTrace xs (F k) p) := by
  unfold permTrace matrixSum; rw [sumOverSwap]

private theorem wordFrameStruct {n : Nat} (i : C) (isq : i^2= -1) (A : Matrix (Basis n) C) :
    Equivariant (wordFrame i A) ∧ KleinFixed (wordFrame i A) := by
  let xs := fourIndices (qubitIndices n)
  let J : Matrix (Four (Basis n)) C := unnormalizedTwirl i
  have factor : wordFrame i A = matMul xs J (tensorFour A) := by
    unfold wordFrame
    change _ = matMul xs (matrixSum (words n) fun p => tensorFour (wordEntry i p)) (tensorFour A)
    rw [sumLeft]; simp only [fourMatMul]; rfl
  constructor
  · intro p hp x y; apply sumOverCongr; intro w; exact tensorEquivariant _ p hp x y
  · rw [factor]; apply mulFixedLeft; intro p hp h x y
    have fourth : i^4=1 := by grind
    unfold J
    rw [unnormalizedTwirlEntry i fourth,unnormalizedTwirlEntry i fourth,kleinTwirl n p hp h]

private theorem squareTraceSwap {α : Type} (xs : List α) (P A : Matrix α C) :
    trace xs (matMul xs (matMul xs P A) (matMul xs P A)) =
    trace xs (matMul xs (matMul xs A P) (matMul xs A P)) := by
  simp only [matMulAssoc]
  rw [traceMatMulSwap xs xs P]; simp only [matMulAssoc]

/-- Newton's alternating trace after the Klein-four identifications, keeping
the physical word matrices under all three remaining trace evaluations. -/
theorem alternatingNewton {n : Nat} (i : C) (isq : i^2= -1) (A : Matrix (Basis n) C) :
    let xs := qubitIndices n
    let c := traceWord i A
    trace (fourIndices xs) (rawBlock .antisymmetric (wordFrame i A)) =
      4*sumOver (words n) (fun p => (c p)^4)+
      8*sumOver (words n) (fun p => c p*cubicWord xs (wordEntry i p) A A A)-
      12*sumOver (words n) (fun p => (c p)^2*traceWordSquare i A p) := by
  dsimp only
  obtain ⟨equ,fix⟩ := wordFrameStruct i isq A
  rw [alternatingClassTrace _ (fullPermuted _ (HyperplaneIncidence.normalsNodup n) qubitIndicesComplete) _ equ fix]
  unfold wordFrame
  simp only [permSum,idTensor,rotationTensor,transpositionTensor]
  have one (p : Word n) : trace (qubitIndices n) (matMul (qubitIndices n) (wordEntry i p) A) = traceWord i A p :=
    traceMatMulSwap _ _ _ _
  have two (p : Word n) := squareTraceSwap (qubitIndices n) (wordEntry i p) A
  simp only [one,two,traceWordSquare,cubicWord]
  congr 2
  apply congrArg; funext p; grind

/-- Four times the physical anticommuting defect, with 24 d² c_F represented
by its actual unnormalized antisymmetric four-copy trace. No projected-edge
or scalar quartic input is required. -/
def fourDelta {n : Nat} (i : C) (A : Matrix (Basis n) C) : C :=
  let xs := qubitIndices n
  let d := (2:C)^n
  12*d*(trace xs (matMul xs A A))^2 - 8*d*quadTrace xs A A A A +
    trace (fourIndices xs) (rawBlock .antisymmetric (wordFrame i A)) -
    4*sumOver (words n) (fun p => (traceWord i A p)^4)

theorem orderedPhysicalDefect {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (A : Matrix (Basis n) C) :
    fourDelta i A=24*di*antiMass (traceWord i A)+8*di^2*orderedQuartic i (traceWord i A) := by
  have pair := pairSource i isq di inv A
  have quart := quarticCorrection i isq di inv A
  unfold fourDelta
  dsimp only
  rw [alternatingNewton i isq A]
  dsimp only at pair quart ⊢
  grind

open AnticommutingDefect (affineEdge inversionPhase)
open GenericExteriorKernel (position)

private theorem boolPhase (a b : Bool) : phase (a^^b)=(phase a : C)*phase b := by
  cases a <;> cases b <;> simp [phase] <;> grind

def quarticPhase {n : Nat} (i : C) (u : Four (Word n)) : C := quadPhase i u.1.1 u.1.2 u.2.1 u.2.2

private def swapAt {α : Type} (j : Fin 3) (u : Four α) : Four α :=
  match j.val with
  | 0 => ((u.1.2,u.1.1),u.2)
  | 1 => ((u.1.1,u.2.1),(u.1.2,u.2.2))
  | _ => (u.1,(u.2.2,u.2.1))

private def swappedPair {α : Type} (j : Fin 3) (u : Four α) : α × α :=
  match j.val with | 0 => u.1 | 1 => (u.1.2,u.2.1) | _ => u.2

private theorem threeCases : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2 := by decide

private theorem swapPhase {n : Nat} (i : C) (isq : i^2= -1) (u : Four (Word n)) (j : Fin 3) :
    quarticPhase i (swapAt j u)=chi (swappedPair j u).1 (swappedPair j u).2 * quarticPhase i u := by
  obtain ⟨⟨a,b⟩,c,d⟩ := u
  rcases threeCases j with h|h|h <;> subst j <;> dsimp only [swapAt,swappedPair,quarticPhase,quadPhase]
  · change cocycle i b a*cocycle i (productLabel b a) c*cocycle i (productLabel (productLabel b a) c) d =
      chi a b*(cocycle i a b*cocycle i (productLabel a b) c*cocycle i (productLabel (productLabel a b) c) d)
    simp only [labelComm b a]
    rw [cocycleSwap i b a,chiSymm b a]; grind
  · have la : productLabel (productLabel a c) b = productLabel (productLabel a b) c := by
      rw [labelAssoc,labelComm c b,←labelAssoc]
    change cocycle i a c*cocycle i (productLabel a c) b*cocycle i (productLabel (productLabel a c) b) d =
      chi b c*(cocycle i a b*cocycle i (productLabel a b) c*cocycle i (productLabel (productLabel a b) c) d)
    rw [la,cocycleLaw i isq a c b,cocycleLaw i isq a b c,cocycleSwap i c b,chiSymm c b,labelComm c b]
    grind
  · change cocycle i a b*cocycle i (productLabel a b) d*cocycle i (productLabel (productLabel a b) d) c=
       chi c d*(cocycle i a b*cocycle i (productLabel a b) c*cocycle i (productLabel (productLabel a b) c) d)
    have e := cocycleLaw i isq (productLabel a b) d c
    have f := cocycleLaw i isq (productLabel a b) c d
    rw [labelComm d c,cocycleSwap i d c,chiSymm d c] at e
    grind

private def walk {α : Type} (u : Four α) : List (Fin 3) → Four α
  | [] => u
  | j::js => walk (swapAt j u) js

private def paths : List (List (Fin 3)) :=
  [[],[0]].flatMap fun x => [[],[1],[1,0]].flatMap fun y =>
    [[],[2],[2,1],[2,1,0]].map fun z => x++y++z

private theorem swapTable (eta alpha beta : Bool) (p : Perm) (hp : p∈permutations) (j : Fin 3) :
    swapAt j p∈permutations ∧ inversionPhase (affineEdge eta alpha beta) (swapAt j p) =
      (affineEdge eta alpha beta (swappedPair j p).1 (swappedPair j p).2 ^^ inversionPhase (affineEdge eta alpha beta) p) := by
  have all : ∀ e a b : Bool, permutations.all (fun s => (List.finRange 3).all (fun k =>
    decide (swapAt k s∈permutations) &&
    (inversionPhase (affineEdge e a b) (swapAt k s) ==
      (affineEdge e a b (swappedPair k s).1 (swappedPair k s).2 ^^ inversionPhase (affineEdge e a b) s))))=true := by decide
  have fact := List.all_eq_true.mp (List.all_eq_true.mp (all eta alpha beta) p hp) j (List.mem_finRange j)
  exact ⟨_root_.of_decide_eq_true (Bool.and_eq_true_iff.mp fact).1,beq_iff_eq.mp (Bool.and_eq_true_iff.mp fact).2⟩

theorem relativePermutationPhase {n : Nat} (i : C) (isq : i^2= -1) (u : Four (Word n)) (eta alpha beta : Bool)
    (graph : ∀ j k, anti (position u j) (position u k)=affineEdge eta alpha beta j k)
    (p : Perm) (hp : p∈permutations) :
    quarticPhase i (reorder u p)=phase (inversionPhase (affineEdge eta alpha beta) p)*quarticPhase i u := by
  let edge := affineEdge eta alpha beta
  have run (path : List (Fin 3)) (s : Perm) (mem : s∈permutations)
      (current : quarticPhase i (reorder u s)=phase (inversionPhase edge s)*quarticPhase i u) :
      quarticPhase i (reorder u (walk s path))=phase (inversionPhase edge (walk s path))*quarticPhase i u := by
    induction path generalizing s with
    | nil => exact current
    | cons j js ih =>
      obtain ⟨mem',bit⟩ := swapTable eta alpha beta s mem j
      apply ih (swapAt j s) mem'
      have perm : reorder u (swapAt j s)=swapAt j (reorder u s) := by rcases threeCases j with h|h|h <;> subst j <;> rfl
      have e : chi (swappedPair j (reorder u s)).1 (swappedPair j (reorder u s)).2 =
          (phase (edge (swappedPair j s).1 (swappedPair j s).2) : C) := by
        rcases threeCases j with h|h|h <;> subst j <;>
          exact congrArg phase (graph _ _)
      rw [perm,swapPhase i isq,e,current]
      change _=phase (inversionPhase (affineEdge eta alpha beta) (swapAt j s))*_
      rw [bit,boolPhase]; unfold edge; grind
  have tab : permutations.all (fun p => paths.any (fun path => walk ident path == p)) = true := by decide
  obtain ⟨path,_,he⟩ := List.any_eq_true.mp (List.all_eq_true.mp tab p hp)
  rw [←beq_iff_eq.mp he]
  apply run path ident (by decide)
  have inv : ∀ e a b : Bool, inversionPhase (affineEdge e a b) ident=false := by decide
  unfold edge; rw [inv]; change _=1*_; rw [Semiring.one_mul]; rfl

def affineWords {n : Nat} (a r t : Word n) : Four (Word n) :=
  ((a,productLabel a r),(productLabel a t,productLabel a (productLabel r t)))

private def axisFrame (a r t : Axis) : Four Axis :=
  ((a,axisProductLabel a r),(axisProductLabel a t,axisProductLabel a (axisProductLabel r t)))

private theorem fourCases : ∀ j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide

private theorem axisFrameEdges (a r t : Axis) (j k : Fin 4) :
    axisAnti (position (axisFrame a r t) j) (position (axisFrame a r t) k) =
      affineEdge (axisAnti r t) (axisAnti a r) (axisAnti a t) j k := by
  cases a <;> cases r <;> cases t <;> revert j k <;> decide

theorem affineWordEdges {n : Nat} (a r t : Word n) (j k : Fin 4) :
    anti (position (affineWords a r t) j) (position (affineWords a r t) k) =
      affineEdge (anti r t) (anti a r) (anti a t) j k := by
  induction a with
  | empty =>
    cases r; cases t
    rcases fourCases j with e|e|e|e <;> subst j <;> rcases fourCases k with e|e|e|e <;> subst k <;> rfl
  | cons a aa ih => cases r with
    | cons r rr => cases t with
      | cons t tt =>
        have point (m : Fin 4) : position (affineWords (.cons a aa) (.cons r rr) (.cons t tt)) m =
          .cons (position (axisFrame a r t) m) (position (affineWords aa rr tt) m) := by
          rcases fourCases m with h|h|h|h <;> subst m <;> rfl
        have xorEdges : ∀ e f g u v w : Bool, ∀ j k : Fin 4,
            (affineEdge e f g j k ^^ affineEdge u v w j k) = affineEdge (e^^u) (f^^v) (g^^w) j k := by decide
        rw [point j,point k]; simp only [anti,axisFrameEdges,ih,xorEdges]

def physicalCorrection {n : Nat} (i : C) (u : Four (Word n)) : C :=
  let ((a,_),(c,d)) := u
  (chi d a*chi d c-1)*quarticPhase i u

def relativeSign (b : Bool) : Int := if b then -1 else 1

private theorem castPhase (b : Bool) : Int.cast (R:=C) (relativeSign b)=phase b := by
  cases b <;> simp [relativeSign,phase,Ring.intCast_neg] <;> grind

/-- The literal sum over all 24 physical orderings, including repeated
labels with multiplicity. This is the signed coefficient in (121). -/
theorem permutationCorrection {n : Nat} (i : C) (isq : i^2= -1) (a r t : Word n) :
    let u := affineWords a r t
    sumOver permutations (fun p => physicalCorrection i (reorder u p)) =
      if anti r t then 0 else if anti a r || anti a t then 32*phase (anti a t)*quarticPhase i u else 0 := by
  let u := affineWords a r t
  let eta := anti r t; let alpha := anti a r; let beta := anti a t
  let edge := affineEdge eta alpha beta
  let ordinary (p : Perm) : Int := relativeSign (inversionPhase edge p)
  let corrected (p : Perm) : Int := relativeSign (inversionPhase edge p ^^ edge p.2.2 p.1.1 ^^ edge p.2.2 p.2.1)
  let S := sumOver permutations ordinary
  let T := sumOver permutations corrected
  have phys : sumOver permutations (fun p => physicalCorrection i (reorder u p)) =
      Int.cast (R:=C) (T-S)*quarticPhase i u := by
    dsimp only [T,S]; rw [←Compression.sumOverSub,intSum,sumOverMulRight]
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    have rel := relativePermutationPhase i isq u eta alpha beta (affineWordEdges a r t) p hp
    change (chi (position u p.2.2) (position u p.1.1)*chi (position u p.2.2) (position u p.2.1)-1)*
      quarticPhase i (reorder u p) = _
    rw [rel]
    change (phase (anti (position u p.2.2) (position u p.1.1))*phase (anti (position u p.2.2) (position u p.2.1))-1) * _ = _
    rw [affineWordEdges,affineWordEdges,Ring.intCast_sub]
    simp only [corrected,ordinary,castPhase,boolPhase,edge,eta,alpha,beta]; grind
  have table : (S,T)=(if eta then (0,0) else if alpha || beta then
      (-8*relativeSign beta,24*relativeSign beta) else (24,24)) :=
    AnticommutingDefect.quarticPhaseSums eta alpha beta
  have eval (e h b : Bool) (s v : Int) (z : C) (tbl : (s,v)=(if e then (0,0) else if h || b then
      (-8*relativeSign b,24*relativeSign b) else (24,24))) :
      Int.cast (R:=C) (v-s)*z=if e then 0 else if h || b then 32*phase b*z else 0 := by
    cases e <;> cases h <;> cases b <;> simp [relativeSign,phase] at tbl ⊢
    all_goals obtain ⟨rfl,rfl⟩ := tbl; simp [Ring.intCast_neg] <;> grind
  exact phys.trans (eval eta alpha beta S T _ table)

private theorem orbitInvariant {α β : Type} (F : Four α → β) (swap : ∀ j u, F (swapAt j u)=F u)
    (u : Four α) (p : Perm) (hp : p∈permutations) : F (reorder u p)=F u := by
  have tab : permutations.all (fun p => paths.any (fun path => walk ident path == p))=true := by decide
  obtain ⟨path,_,he⟩ := List.any_eq_true.mp (List.all_eq_true.mp tab p hp)
  have visit (path : List (Fin 3)) (s : Perm) : F (reorder u (walk s path))=F (reorder u s) := by
    induction path generalizing s with
    | nil => rfl
    | cons j js ih =>
      have perm : reorder u (swapAt j s)=swapAt j (reorder u s) := by rcases threeCases j with h|h|h <;> subst j <;> rfl
      rw [walk,ih,perm,swap]
  rw [←beq_iff_eq.mp he,visit]; rfl

def totalLabel {n : Nat} (u : Four (Word n)) := quadLabel u.1.1 u.1.2 u.2.1 u.2.2

private theorem totalInvariant {n : Nat} (u : Four (Word n)) (p : Perm) (hp : p∈permutations) :
    totalLabel (reorder u p)=totalLabel u := by
  apply orbitInvariant _ _ _ _ hp
  intro j u; obtain ⟨⟨a,b⟩,c,d⟩ := u
  rcases threeCases j with h|h|h <;> subst j
  · change productLabel (productLabel (productLabel b a) c) d=productLabel (productLabel (productLabel a b) c) d
    rw [labelComm b a]
  · change productLabel (productLabel (productLabel a c) b) d=productLabel (productLabel (productLabel a b) c) d
    rw [labelAssoc a c b,labelComm c b,←labelAssoc]
  · change productLabel (productLabel (productLabel a b) d) c=productLabel (productLabel (productLabel a b) c) d
    rw [labelAssoc (productLabel a b) d c,labelComm d c,←labelAssoc]

def monomial {n : Nat} (c : Word n → C) (u : Four (Word n)) := c u.1.1*c u.1.2*c u.2.1*c u.2.2

private theorem monomialInvariant {n : Nat} (c : Word n → C) (u : Four (Word n)) (p : Perm) (hp : p∈permutations) :
    monomial c (reorder u p)=monomial c u := by
  apply orbitInvariant _ _ _ _ hp
  intro j u; obtain ⟨⟨a,b⟩,t,d⟩ := u
  rcases threeCases j with h|h|h <;> subst j
  · change c b*c a*c t*c d=c a*c b*c t*c d; grind
  · change c a*c t*c b*c d=c a*c b*c t*c d; grind
  · change c a*c b*c d*c t=c a*c b*c t*c d; grind

private theorem cancelAdd {n : Nat} (a b : Word n) : productLabel a (productLabel a b)=b := by
  rw [←labelAssoc,labelSelf,labelUnit]

private theorem labelZero {n : Nat} (a b : Word n) :
    productLabel a b=unitWord n ↔ a=b := by
  constructor
  · intro h
    have e := congrArg (productLabel a) h
    rw [cancelAdd,labelComm a (unitWord n),labelUnit] at e
    exact e.symm
  · rintro rfl; exact labelSelf _

theorem zeroFrame {n : Nat} (u : Four (Word n)) (h : totalLabel u=unitWord n) :
    u=affineWords u.1.1 (productLabel u.1.1 u.1.2) (productLabel u.1.1 u.2.1) := by
  obtain ⟨⟨a,b⟩,t,d⟩ := u
  change productLabel (productLabel (productLabel a b) t) d=unitWord n at h
  have hd := (labelZero _ _).mp h
  change ((a,b),(t,d))=((a,productLabel a (productLabel a b)),
    (productLabel a (productLabel a t),productLabel a (productLabel (productLabel a b) (productLabel a t))))
  rw [cancelAdd,cancelAdd,←labelAssoc a (productLabel a b),cancelAdd,←labelAssoc b a t,labelComm b a,hd]

noncomputable def orderedTerm {n : Nat} (i : C) (c : Word n → C) (u : Four (Word n)) :=
  if totalLabel u=unitWord n then monomial c u*physicalCorrection i u else 0

/-- This weight is the physical cyclic product sign on noncommuting isotropic
quartets, and vanishes on all other label sets. -/
noncomputable def planeTerm {n : Nat} (i : C) (c : Word n → C) (u : Four (Word n)) : C :=
  let a := u.1.1
  let r := productLabel a u.1.2
  let t := productLabel a u.2.1
  if totalLabel u=unitWord n ∧ anti r t=false ∧ (anti a r || anti a t)=true then
    monomial c u * phase (anti a t) * quarticPhase i u else 0

private theorem sumZero {α : Type} (xs : List α) (f : α → C) (zero : ∀ x∈xs, f x=0) : sumOver xs f=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change f x+sumOver xs f=0
                    rw [zero _ List.mem_cons_self,ih (fun i hi => zero i (List.mem_cons_of_mem _ hi))]; grind

theorem orbitWeight {n : Nat} (i : C) (isq : i^2= -1) (c : Word n → C) (u : Four (Word n)) :
    sumOver permutations (fun p => orderedTerm i c (reorder u p))=32*planeTerm i c u := by
  by_cases zero : totalLabel u=unitWord n
  · let a := u.1.1
    let r := productLabel a u.1.2
    let t := productLabel a u.2.1
    have form : u=affineWords a r t := zeroFrame _ zero
    have per := permutationCorrection i isq a r t
    dsimp only at per; rw [←form] at per
    calc
      _ = monomial c u * sumOver permutations (fun p => physicalCorrection i (reorder u p)) := by
        rw [sumOverMulLeft]; apply congrArg List.sum; apply List.map_congr_left; intro p hp
        simp only [orderedTerm,totalInvariant _ _ hp,zero,ite_true,monomialInvariant _ _ _ hp]
      _ = _ := by
        rw [per]; unfold planeTerm
        change _=32*(if totalLabel u=unitWord n ∧ anti r t=false ∧ (anti a r || anti a t)=true then _ else 0)
        cases h : anti r t <;> cases h' : anti a r || anti a t <;> simp [zero] <;> grind
  · have z : sumOver permutations (fun p => orderedTerm i c (reorder u p))=0 := by
      apply sumZero; intro p hp; simp [orderedTerm,totalInvariant _ _ hp,zero]
    rw [z]; simp [planeTerm,zero]; grind

private theorem wordsComplete {n : Nat} (p : Word n) : p∈words n := by
  induction p with
  | empty => exact List.mem_cons_self
  | cons a p ih =>
    apply List.mem_flatMap.mpr; refine ⟨p,ih,?_⟩; cases a <;> simp

private def digit : Axis → Nat | .identity => 0 | .x => 1 | .y => 2 | .z => 3

def wordKey : {n : Nat} → Word n → Nat
  | _, .empty => 0
  | _, .cons a p => 4*wordKey p+digit a

private theorem keyInjective {n : Nat} (p q : Word n) (e : wordKey p=wordKey q) : p=q := by
  induction p with
  | empty => cases q; rfl
  | cons a p ih =>
    cases q with
    | cons b q =>
      cases a <;> cases b <;> simp only [wordKey,digit] at e <;> first | (congr 1; exact ih q (by omega)) | omega

local instance {n : Nat} (u : Four (Word n)) : Decidable (ExteriorIsometry.apart wordKey u) := by
  unfold ExteriorIsometry.apart; infer_instance

private theorem apartInvariant {n : Nat} (u : Four (Word n)) (p : Perm) (hp : p∈permutations) :
    ExteriorIsometry.apart wordKey (reorder u p)=ExteriorIsometry.apart wordKey u := by
  apply orbitInvariant _ _ _ _ hp
  intro j u; obtain ⟨⟨a,b⟩,t,d⟩ := u
  rcases threeCases j with h|h|h <;> subst j <;> apply propext
  · change ExteriorIsometry.apart wordKey ((b,a),(t,d)) ↔ _
    unfold ExteriorIsometry.apart; grind only
  · change ExteriorIsometry.apart wordKey ((a,t),(b,d)) ↔ _
    unfold ExteriorIsometry.apart; grind only
  · change ExteriorIsometry.apart wordKey ((a,b),(d,t)) ↔ _
    unfold ExteriorIsometry.apart; grind only

private theorem permSumEq {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private def average {n : Nat} (f : Four (Word n) → C) (u : Four (Word n)) :=
  sumOver permutations (fun p => f (reorder u p))

private theorem compose {α : Type} (u : Four α) (p q : Perm) :
    reorder (reorder u p) q=reorder u (reorder p q) := by
  change ((position (reorder u p) _,position (reorder u p) _),(position (reorder u p) _,position (reorder u p) _))=_
  simp only [GenericExteriorKernel.position_reorder]; rfl

private theorem averageInvariant {n : Nat} (f : Four (Word n) → C) (u : Four (Word n)) (p : Perm) (hp : p∈permutations) :
    average f (reorder u p)=average f u := by
  have table : permutations.all (fun p => decide ((permutations.map (reorder p)).Perm permutations))=true := by decide
  have h := permSumEq (_root_.of_decide_eq_true (List.all_eq_true.mp table p hp)) (fun q => f (reorder u q))
  simpa only [sumOver,List.map_map,Function.comp_def,average,compose] using h

private theorem totalAverage {n : Nat} (f : Four (Word n) → C) : sumOver (fourIndices (words n)) (average f)=
    24*sumOver (fourIndices (words n)) f := by
  let xs := fourIndices (words n)
  have move := fullPermuted (words n) (MixedDefect.allWordsNodup n) wordsComplete
  have reindexed (p : Perm) (hp : p∈permutations) : sumOver xs (fun u => f (reorder u p))=sumOver xs f := by
    simpa only [sumOver,List.map_map,Function.comp_def] using permSumEq (move p hp) f
  have cnt : sumOver permutations (fun _ => (1:Int))=24 := by decide
  unfold average
  rw [sumOverSwap]; change sumOver permutations (fun p => sumOver xs (fun u => f (reorder u p)))=_
  calc
    _ = sumOver permutations (fun _ => Int.cast (R:=C) (1:Int)*sumOver xs f) := by
      apply congrArg List.sum; apply List.map_congr_left; intro p hp; rw [reindexed _ hp,Ring.intCast_ofNat 1]; grind
    _ = _ := by rw [countTerm,cnt,Ring.intCast_ofNat 24]

theorem sumDistinct {n : Nat} (i : C) (isq : i^2= -1) (inv24 : C) (unit24 : 24*inv24=1) (c : Word n → C) :
    let ts := fourIndices (words n)
    sumOver ts (fun u => if ExteriorIsometry.apart wordKey u then orderedTerm i c u else 0) =
      32*sumOver (ts.filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c) := by
  dsimp only
  let f (u : Four (Word n)) := if ExteriorIsometry.apart wordKey u then orderedTerm i c u else 0
  have avg (u : Four (Word n)) : average f u=if ExteriorIsometry.apart wordKey u then 32*planeTerm i c u else 0 := by
    by_cases h : ExteriorIsometry.apart wordKey u
    · rw [ite_eq_left h,←orbitWeight i isq c u]; apply congrArg List.sum; apply List.map_congr_left; intro p hp
      unfold f; exact ite_eq_left ((apartInvariant u p hp).mpr h)
    · rw [ite_eq_right h]; apply sumZero; intro p hp; unfold f; exact ite_eq_right (fun k => h ((apartInvariant u p hp).mp k))
  have sorting := ExteriorIsometry.orderedToSorted (words n) wordsComplete (MixedDefect.allWordsNodup n) wordKey (average f)
    (averageInvariant f) (fun u h => by rw [avg,ite_eq_right h])
  rw [totalAverage] at sorting
  have ag : sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (average f)=
      32*sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c) := by
    rw [sumOverMulLeft]; apply congrArg List.sum; apply List.map_congr_left; intro u hu
    have h := _root_.of_decide_eq_true (List.mem_filter.mp hu).2
    change wordKey u.1.1 < wordKey u.1.2 ∧ wordKey u.1.2 < wordKey u.2.1 ∧ wordKey u.2.1 < wordKey u.2.2 at h
    rw [avg,ite_eq_left (by unfold ExteriorIsometry.apart; omega)]
  rw [ag] at sorting
  have cancel (a b : C) (eq : 24*a=24*b) : a=b := by
    have mul := congrArg (fun z => inv24*z) eq
    simp only [←Semiring.mul_assoc,CommSemiring.mul_comm inv24 24,unit24,Semiring.one_mul] at mul
    exact mul
  exact cancel _ _ sorting

private theorem sumFourList {α : Type} (xs : List α) (f : Four α → C) :
    sumOver (fourIndices xs) f=sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun t => sumOver xs (fun d => f ((a,b),(t,d)))))) := by
  simp only [fourIndices,pairSum]

theorem orderedQuartic_sum {n : Nat} (i : C) (c : Word n → C) :
    orderedQuartic i c=sumOver (fourIndices (words n)) (orderedTerm i c) := by
  rw [sumFourList]; unfold orderedQuartic wordSum4
  let xs := words n
  let f (p a b t : Word n) := if quadLabel a b t p=unitWord n then
    c p*c a*c b*c t*(chi p a*chi p t-1)*quadPhase i a b t p else 0
  change sumOver xs (fun p => sumOver xs (fun a => sumOver xs (fun b => sumOver xs (f p a b))))=_
  calc
    _ = sumOver xs (fun a => sumOver xs (fun p => sumOver xs (fun b => sumOver xs (f p a b)))) := sumOverSwap _ _ _
    _ = sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun p => sumOver xs (f p a b)))) := by
      apply sumOverCongr; intro a; exact sumOverSwap _ _ _
    _ = sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun t => sumOver xs (fun p => f p a b t)))) := by
      apply sumOverCongr; intro a; apply sumOverCongr; intro b; exact sumOverSwap _ _ _
    _ = _ := by
      apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro t; apply sumOverCongr; intro p
      unfold f orderedTerm totalLabel monomial physicalCorrection quarticPhase
      dsimp only; split <;> grind

private theorem antiDiagonal {n : Nat} (a : Word n) : anti a a=false := by
  induction a with
  | empty => rfl
  | cons a w ih => cases a <;> simp [anti,axisAnti,ih]

private theorem unitCocycle {n : Nat} (i : C) (a : Word n) : cocycle i (unitWord n) a=1 := by
  rw [cocycleSwap,unitChi,cocycleUnit]; grind

private theorem cancelAtRight {n : Nat} (a b : Word n) : productLabel (productLabel a b) b=a := by
  rw [labelAssoc,labelSelf,labelComm _ (unitWord _),labelUnit]

private theorem cancelAtEnds {n : Nat} (a b : Word n) : productLabel (productLabel a b) a=b := by
  rw [labelComm a b,cancelAtRight]

def pairWeight {n : Nat} (c : Word n → C) (a b : Word n) : C :=
  if anti a b then -2*(c a)^2*(c b)^2 else 0

private theorem pairDiagonal {n : Nat} (c : Word n → C) (a : Word n) : pairWeight c a a=0 := by
  simp [pairWeight,antiDiagonal]

private theorem antiPairSymmetry {n : Nat} (a b : Word n) : anti a b=anti b a := by
  induction a with
  | empty => cases b; rfl
  | cons a as ih => cases b with
    | cons b bs => simp only [anti,ih]; cases a <;> cases b <;> rfl

theorem repeatedFourWords {n : Nat} (i : C) (isq : i^2= -1) (c : Word n → C) (a b : Word n) :
    orderedTerm i c ((a,a),(b,b))=pairWeight c a b ∧ orderedTerm i c ((a,b),(b,a))=pairWeight c a b ∧
    orderedTerm i c ((a,b),(a,b))=0 := by
  have h := cocycleLaw i isq a b b
  rw [cocycleSelf,labelSelf,cocycleUnit] at h
  have hs := antiPairSymmetry b a
  constructor
  · simp only [orderedTerm,totalLabel,quadLabel,labelSelf,labelUnit,ite_true,physicalCorrection,
      quarticPhase,quadPhase,cocycleSelf,unitCocycle,monomial,chi,hs,antiDiagonal,phase,pairWeight]
    cases anti a b <;> simp <;> grind
  constructor
  · simp only [orderedTerm,totalLabel,quadLabel,cancelAtRight,labelSelf,ite_true,physicalCorrection,
      quarticPhase,quadPhase,cancelAtRight,cocycleSelf,monomial,h,chi,antiDiagonal,phase,pairWeight]
    cases anti a b <;> simp <;> grind
  · simp only [orderedTerm,totalLabel,quadLabel,cancelAtEnds,labelSelf,ite_true,physicalCorrection,
      quarticPhase,monomial,chi,phase]; cases anti b a <;> simp <;> grind

private theorem repeatedClass {n : Nat} (a b t d : Word n) (zero : totalLabel ((a,b),(t,d))=unitWord n)
    (rep : ¬ ExteriorIsometry.apart wordKey ((a,b),(t,d))) :
    (a=b ∧ t=d) ∨ (a=t ∧ b=d) ∨ (a=d ∧ b=t) := by
  change productLabel (productLabel (productLabel a b) t) d=unitWord n at zero
  have hd := (labelZero _ _).mp zero
  by_cases ab : a=b
  · subst b; rw [labelSelf,labelUnit] at hd; exact Or.inl ⟨rfl,hd⟩
  by_cases at' : a=t
  · subst t; rw [cancelAtEnds] at hd; exact Or.inr (Or.inl ⟨rfl,hd⟩)
  by_cases bt : b=t
  · subst t; rw [cancelAtRight] at hd; exact Or.inr (Or.inr ⟨hd,rfl⟩)
  have ad : a≠d := by
    rintro rfl
    have e := congrArg (productLabel a) hd
    rw [labelAssoc a b t,cancelAdd,labelSelf] at e
    exact bt ((labelZero _ _).mp e)
  have bd : b≠d := by
    rintro rfl
    have e := congrArg (productLabel b) hd
    rw [labelComm a b,labelAssoc b a t,cancelAdd,labelSelf] at e
    exact at' ((labelZero _ _).mp e)
  have td : t≠d := by
    rintro rfl
    have e := congrArg (fun z => productLabel z t) hd
    change productLabel (productLabel (productLabel a b) t) t=productLabel t t at e
    rw [cancelAtRight,labelSelf] at e
    exact ab ((labelZero _ _).mp e)
  exact False.elim (rep ⟨fun e => ab (keyInjective _ _ e),fun e => at' (keyInjective _ _ e),
    fun e => ad (keyInjective _ _ e),fun e => bt (keyInjective _ _ e),fun e => bd (keyInjective _ _ e),
    fun e => td (keyInjective _ _ e)⟩)

noncomputable def repeatedWeight {n : Nat} (c : Word n → C) (u : Four (Word n)) : C :=
  (if u.1.1=u.1.2 then (if u.2.1=u.2.2 then pairWeight c u.1.1 u.2.1 else 0) else 0)+
    (if u.1.2=u.2.1 then (if u.1.1=u.2.2 then pairWeight c u.1.1 u.1.2 else 0) else 0)

theorem repeatedPointwise {n : Nat} (i : C) (isq : i^2= -1) (c : Word n → C) (u : Four (Word n)) :
    (if ExteriorIsometry.apart wordKey u then 0 else orderedTerm i c u)=repeatedWeight c u := by
  obtain ⟨⟨a,b⟩,t,d⟩ := u
  by_cases aabb : a=b ∧ t=d
  · obtain ⟨rfl,rfl⟩ := aabb
    have rep : ¬ ExteriorIsometry.apart wordKey ((a,a),(t,t)) := fun e => e.1 rfl
    rw [ite_eq_right rep,(repeatedFourWords i isq c a t).1]
    by_cases h : a=t
    · subst t; simp [repeatedWeight,pairDiagonal]; grind
    · simp [repeatedWeight,h]; grind
  by_cases abba : a=d ∧ b=t
  · obtain ⟨rfl,rfl⟩ := abba
    have rep : ¬ ExteriorIsometry.apart wordKey ((a,b),(b,a)) := fun e => e.2.2.1 rfl
    rw [ite_eq_right rep,(repeatedFourWords i isq c a b).2.1]
    by_cases h : a=b
    · subst b; simp [repeatedWeight,pairDiagonal]; grind
    · simp [repeatedWeight,h]; grind
  have zero : repeatedWeight c ((a,b),(t,d))=0 := by
    unfold repeatedWeight; dsimp only
    by_cases h : a=b <;> by_cases k : t=d <;> by_cases l : b=t <;> by_cases m : a=d <;> simp only [h,k,l,m,ite_true,ite_false] <;> grind
  rw [zero]
  by_cases s : ExteriorIsometry.apart wordKey ((a,b),(t,d))
  · exact ite_eq_left s
  rw [ite_eq_right s]
  by_cases z : totalLabel ((a,b),(t,d))=unitWord n
  · rcases repeatedClass _ _ _ _ z s with bad|⟨rfl,rfl⟩|bad
    · exact False.elim (aabb bad)
    · exact (repeatedFourWords i isq c a b).2.2
    · exact False.elim (abba bad)
  · exact ite_eq_right z

private theorem wordSelect {n : Nat} (a : Word n) (f : Word n → C) :
    sumOver (words n) (fun d => if a=d then f d else 0)=f a :=
  ExteriorPauliBase.sumOnIndex _ _ _ (MixedDefect.allWordsNodup n) (wordsComplete a)

private theorem sumIfFixed {α : Type} (xs : List α) (e : Prop) [Decidable e] (f : α → C) :
    sumOver xs (fun i => if e then f i else 0)=if e then sumOver xs f else 0 := by
  by_cases h : e
  · simp only [h,ite_true]
  · simp only [h,ite_false]; exact sumZero _ _ (fun _ _ => rfl)

theorem repeatedMass {n : Nat} (c : Word n → C) :
    sumOver (fourIndices (words n)) (repeatedWeight c) = -4*antiMass c := by
  let xs := words n
  let mass := sumOver xs (fun a => sumOver xs (fun b => pairWeight c a b))
  have massEq : mass= -2*antiMass c := by
    unfold mass xs antiMass; rw [sumOverMulLeft]; apply sumOverCongr; intro a
    rw [sumOverMulLeft]; apply sumOverCongr; intro b
    unfold pairWeight; cases anti a b <;> simp <;> grind
  unfold repeatedWeight; rw [sumOverAdd,sumFourList,sumFourList]
  change _+_ = _
  have aabb : sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun t => sumOver xs (fun d =>
        if a=b then (if t=d then pairWeight c a t else 0) else 0))))=mass := by
    apply sumOverCongr; intro a
    calc
      _ = sumOver xs (fun b => if a=b then sumOver xs (fun t => pairWeight c a t) else 0) := by
        apply sumOverCongr; intro b
        by_cases h : a=b
        · simp only [h,ite_true]; apply sumOverCongr; intro t
          exact wordSelect t (fun _ => pairWeight c b t)
        · simp only [h,ite_false]; apply sumZero; intro t _; exact sumZero _ _ (fun _ _ => rfl)
      _ = _ := wordSelect a (fun _ => sumOver xs (fun t => pairWeight c a t))
  have abba : sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun t => sumOver xs (fun d =>
        if b=t then (if a=d then pairWeight c a b else 0) else 0))))=mass := by
    apply sumOverCongr; intro a; apply sumOverCongr; intro b
    calc
      _ = sumOver xs (fun t => if b=t then pairWeight c a b else 0) := by
        apply sumOverCongr; intro t; rw [sumIfFixed]
        by_cases h : b=t
        · simp only [h,ite_true]; exact wordSelect a (fun _ => pairWeight c a t)
        · simp only [h,ite_false]
      _ = _ := wordSelect b (fun _ => pairWeight c a b)
  change _+_ = _
  rw [aabb,abba,massEq]; grind

theorem groupedQuartic {n : Nat} (i : C) (isq : i^2= -1) (inv24 : C) (unit24 : 24*inv24=1) (c : Word n → C) :
    orderedQuartic i c =
      32*sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c)-4*antiMass c := by
  let ts := fourIndices (words n)
  have split (u : Four (Word n)) : orderedTerm i c u =
      (if ExteriorIsometry.apart wordKey u then orderedTerm i c u else 0)+repeatedWeight c u := by
    rw [←repeatedPointwise i isq c]; by_cases e : ExteriorIsometry.apart wordKey u <;> simp only [e,ite_true,ite_false] <;> grind
  rw [orderedQuartic_sum]
  calc
    _ = sumOver ts (fun u => (if ExteriorIsometry.apart wordKey u then orderedTerm i c u else 0)+repeatedWeight c u) :=
      sumOverCongr _ split
    _ = _ := by unfold ts; rw [sumOverAdd,sumDistinct i isq inv24 unit24,repeatedMass]; grind

theorem groupedPhysicalDefect {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (inv24 : C) (unit24 : 24*inv24=1) (A : Matrix (Basis n) C) :
    let c := traceWord i A
    fourDelta i A=(24*di-32*di^2)*antiMass c + 256*di^2*
      sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c) := by
  dsimp only; rw [orderedPhysicalDefect i isq di inv,groupedQuartic i isq inv24 unit24]; grind

private theorem sumApp {α : Type} (xs ys : List α) (f : α → C) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons x xs ih =>
    simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *
    grind

private theorem doublePairSum {α : Type} (xs : List α) (f : α → α → C) (sym : ∀ a b, f a b=f b a)
    (diag : ∀ a, f a a=0) :
    sumOver xs (fun a => sumOver xs (f a))=2*sumOver (SectorDefectAccounting.wedgePairs xs) (fun ab => f ab.1 ab.2) := by
  induction xs with
  | nil => simp [SectorDefectAccounting.wedgePairs,sumOver]; grind
  | cons a xs ih =>
    have head : sumOver (xs.map (fun y => (a,y))) (fun ab => f ab.1 ab.2)=sumOver xs (f a) := by
      simp [sumOver,List.map_map,Function.comp_def]
    have tail : sumOver xs (fun b => f b a+sumOver xs (f b))=sumOver xs (f a)+sumOver xs (fun b => sumOver xs (f b)) := by
      rw [sumOverAdd]; have same : sumOver xs (fun b => f b a)=sumOver xs (f a) := sumOverCongr _ (fun b => sym b a)
      rw [same]
    rw [SectorDefectAccounting.wedgePairs,sumApp,head]
    change (f a a+sumOver xs (f a))+sumOver xs (fun b => f b a+sumOver xs (f b))=_
    rw [diag,tail,ih]; grind

def unorderedAntiMass {n : Nat} (c : Word n → C) : C :=
  sumOver (SectorDefectAccounting.wedgePairs (words n)) (fun ab => if anti ab.1 ab.2 then (c ab.1)^2*(c ab.2)^2 else 0)

theorem antiMass_twice {n : Nat} (c : Word n → C) : antiMass c=2*unorderedAntiMass c := by
  apply doublePairSum
  · intro a b; rw [antiPairSymmetry a b]; cases anti b a <;> simp <;> grind
  · intro a; simp [antiDiagonal]

/-- The physical form of Eq. (106) in the four-Delta convention. The
two inner coefficients are the ones in the expansion of Delta itself. -/
theorem physicalAntiQuarticExpansion {n : Nat} (i : C) (isq : i^2= -1) (di : C) (inv : (2:C)^n*di=1)
    (inv24 : C) (unit24 : 24*inv24=1) (A : Matrix (Basis n) C) :
    let c := traceWord i A
    fourDelta i A=4*(4*(3*(2:C)^n-4)*di^2*unorderedAntiMass c + 64*di^2*
      sumOver ((fourIndices (words n)).filter (ExteriorIsometry.increasing wordKey)) (planeTerm i c)) := by
  dsimp only; rw [groupedPhysicalDefect i isq di inv inv24 unit24,antiMass_twice]
  have scale : (2:C)^n*di^2=di := by rw [Semiring.pow_succ,Semiring.pow_one,←Semiring.mul_assoc,inv,Semiring.one_mul]
  grind

def cyclicAnticommuting {n : Nat} (u : Four (Word n)) : Bool :=
  anti u.1.1 u.1.2 && anti u.1.2 u.2.1 && anti u.2.1 u.2.2 && anti u.2.2 u.1.1

/-- Every cyclic anticommuting traversal of an isotropic parallelogram
gives exactly the same physical four-word product sign. -/
theorem cyclicQuarticPhase {n : Nat} (i : C) (isq : i^2= -1) (a r t : Word n)
    (iso : anti r t=false) (p : Perm) (hp : p∈permutations)
    (cyc : cyclicAnticommuting (reorder (affineWords a r t) p)=true) :
    quarticPhase i (reorder (affineWords a r t) p)=phase (anti a t)*quarticPhase i (affineWords a r t) := by
  have phaseEq := relativePermutationPhase i isq (affineWords a r t) _ _ _ (affineWordEdges a r t) p hp
  rw [iso] at phaseEq
  let edge := affineEdge false (anti a r) (anti a t)
  have graph (j k) : anti (position (affineWords a r t) j) (position (affineWords a r t) k)=edge j k := by
    rw [affineWordEdges,iso]
  change (anti (position _ p.1.1) (position _ p.1.2) && anti (position _ p.1.2) (position _ p.2.1) &&
    anti (position _ p.2.1) (position _ p.2.2) && anti (position _ p.2.2) (position _ p.1.1))=true at cyc
  simp only [graph] at cyc
  have h := List.all_eq_true.mp (AnticommutingDefect.cyclicPhase (anti a r) (anti a t)) p hp
  change (!(_ && _ && _ && _) || (inversionPhase edge p == anti a t))=true at h
  rw [cyc] at h
  have e : inversionPhase edge p=anti a t := beq_iff_eq.mp h
  exact phaseEq.trans (congrArg (fun z => phase z*quarticPhase i (affineWords a r t)) e)

theorem cyclicOrderExists {n : Nat} (a r t : Word n) (iso : anti r t=false) (active : (anti a r || anti a t)=true) :
    ∃ p∈permutations, cyclicAnticommuting (reorder (affineWords a r t) p)=true := by
  have tbl : ∀ h k : Bool, (h || k)=true → permutations.any (fun p =>
      let e := affineEdge false h k
      e p.1.1 p.1.2 && e p.1.2 p.2.1 && e p.2.1 p.2.2 && e p.2.2 p.1.1)=true := by decide
  obtain ⟨p,hp,he⟩ := List.any_eq_true.mp (tbl _ _ active)
  refine ⟨p,hp,?_⟩
  change (anti (position _ p.1.1) (position _ p.1.2) && anti (position _ p.1.2) (position _ p.2.1) &&
    anti (position _ p.2.1) (position _ p.2.2) && anti (position _ p.2.2) (position _ p.1.1))=true
  simpa only [affineWordEdges,iso] using he
end RankSeven.PhysicalAntiQuartic

#print axioms RankSeven.PhysicalAntiQuartic.physicalAntiQuarticExpansion
#print axioms RankSeven.PhysicalAntiQuartic.groupedQuartic
#print axioms RankSeven.PhysicalAntiQuartic.cyclicQuarticPhase
#print axioms RankSeven.PhysicalAntiQuartic.cyclicOrderExists
