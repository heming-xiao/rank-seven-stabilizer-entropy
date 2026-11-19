import Rank7StabilizerOddSector

namespace RankSeven.StabilizerSectorKernel

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerOddSector
variable {R C : Type} [CommRing R] [CommRing C]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem embedding {α : Type} (xs : List α) (f : α→R) : ofReal (sumOver xs f)=sumOver xs (fun i => ofReal (f i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ofReal (f i+sumOver xs f)=ofReal (f i)+sumOver xs _
    rw [←ih]; apply ComplexScalar.ext <;> simp <;> grind only

private theorem realPhase (b : Bool) : ofReal (phase b:R)=(phase b:ComplexScalar R) := by
  cases b <;> apply ComplexScalar.ext <;> simp [phase] <;> grind only

private theorem cDim (m : Nat) : ofReal ((2:R)^m)=(2:ComplexScalar R)^m := by
  rw [PhysicalPairedReduction.realEmbeddingPow]; rfl

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem invDimension (half : R) (h2 : 2*half=1) (n : Nat) : (ofReal half)^n*(2:ComplexScalar R)^n=1 := by
  have e := SectorDefectAccounting.dimensionInverse half h2 n
  have m : ofReal ((2:R)^n*half^n)=ofReal ((2:R)^n)*ofReal (half^n) := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [e,cDim,PhysicalPairedReduction.realEmbeddingPow] at m; change 1=(2:ComplexScalar R)^n*(ofReal half)^n at m; grind only

theorem quotientComplex {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (g : Word n) (hg : g∈G.labels) :
    sumOver T.reps (fun a => (chi a g:ComplexScalar R))=if g=unitWord n then (2:ComplexScalar R)^n else 0 := by
  have h := congrArg (fun u : R => ofReal u) (quotientSum half h2 T g hg)
  rw [embedding] at h; simp only [chi,realPhase] at h ⊢
  rw [h]; by_cases e : g=unitWord n <;> simp only [e,ite_true,ite_false,cDim] <;> rfl

def complexTransform {n : Nat} (half : R) (G : MaximalFamily n) (f : Word n→ComplexScalar R) (a : Word n) :=
  (ofReal half)^n*sumOver G.labels (fun g => chi a g*f g)

theorem complexPairing {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (T : Transversal G)
    (f u : Word n→ComplexScalar R) :
    sumOver T.reps (fun a => complexTransform half G f a*complexTransform half G u a)=
    (ofReal half)^n*sumOver G.labels (fun g => f g*u g) := by
  let h := (ofReal half)^n
  have expand (a : Word n) : complexTransform half G f a*complexTransform half G u a=
      h^2*sumOver G.labels (fun p => sumOver G.labels (fun q => chi a (wordAdd p q)*(f p*u q))) := by
    let L := sumOver G.labels (fun p => chi a p*f p)
    let M := sumOver G.labels (fun q => chi a q*u q)
    have eq : L*M=sumOver G.labels (fun p => sumOver G.labels (fun q => chi a (wordAdd p q)*(f p*u q))) := by
      unfold L M; rw [sumOverMulRight]; apply sumOverCongr; intro p; rw [sumOverMulLeft]; apply sumOverCongr; intro q
      rw [characterAddRight]; grind only
    change h*L*(h*M)=_; grind only
  rw [sumOverCongr _ expand,←sumOverMulLeft,sumOverSwap T.reps G.labels]
  have sum (p : Word n) (hp : p∈G.labels) :
      sumOver T.reps (fun a => sumOver G.labels (fun q => chi a (wordAdd p q)*(f p*u q)))=(2:ComplexScalar R)^n*(f p*u p) := by
    rw [sumOverSwap]
    have ineq (q : Word n) (hq : q∈G.labels) : sumOver T.reps (fun a => chi a (wordAdd p q)*(f p*u q))=
        if p=q then (2:ComplexScalar R)^n*(f p*u q) else 0 := by
      rw [←sumOverMulRight,quotientComplex half h2 T _ (addMem G _ _ hp hq)]; simp only [wordAddEqZero]
      by_cases e : p=q <;> simp [e] <;> grind only
    rw [AnticommutingDefect.sumCongrMem _ _ _ ineq,ExteriorPauliBase.sumOnIndex _ p _ G.nodup hp]
  rw [AnticommutingDefect.sumCongrMem _ _ _ sum,←sumOverMulLeft]
  have iv : h*(2:ComplexScalar R)^n=1 := invDimension half h2 n
  change h^2*((2:ComplexScalar R)^n*_)=h*_; grind only

theorem cosetWordKernel {n : Nat} (half : R) (h2 : 2*half=1) (G : MaximalFamily n) (v : Word n) (i j l k : Basis n) :
    sumOver (words n) (fun p => if wordAdd p v∈G.labels then wordEntry (imaginaryUnit (R:=R)) p i j*wordEntry imaginaryUnit p l k else 0)=
    sumOver G.labels (fun g => chi v g*(wordEntry imaginaryUnit g i k*wordEntry imaginaryUnit g l j)) := by
  let W (p : Word n) := wordEntry (imaginaryUnit (R:=R)) p
  let F p := W p i j*W p l k
  let h := (ofReal half)^n
  let d := (2:ComplexScalar R)^n
  have iv : h*d=1 := invDimension half h2 n
  have expand (p : Word n) : (if wordAdd p v∈G.labels then F p else 0)=
      h*sumOver G.labels (fun g => chi v g*(chi g p*F p)) := by
    have eq (g : Word n) : chi v g*(chi g p*F p)=chi (wordAdd p v) g*F p := by rw [charAddLeft,chiSymm g p]; grind only
    rw [sumOverCongr _ eq,←sumOverMulRight,chiSum]
    by_cases mem : wordAdd p v∈G.labels <;> simp only [mem,ite_false,ite_true] <;> change _=h*_ <;> grind only
  change sumOver (words n) (fun p => if wordAdd p v∈G.labels then F p else 0)=_
  rw [sumOverCongr _ expand,←sumOverMulLeft,sumOverSwap]
  have each (g : Word n) : sumOver (words n) (fun p => chi v g*(chi g p*F p))=
      d*(chi v g*(W g i k*W g l j)) := by
    rw [←sumOverMulLeft]
    have eq (p : Word n) : chi g p*F p=chi g p*W p i j*W p l k := by unfold F; grind only
    rw [sumOverCongr _ eq]; have res := signedResolution (imaginaryUnit (R:=R)) imaginaryUnit_sq g i j l k
    change sumOver (words n) (fun p => chi g p*W p i j*W p l k)=d*W g i k*W g l j at res
    rw [res]; grind only
  rw [sumOverCongr _ each,←sumOverMulLeft]
  change h*(d*_)=_; grind only

theorem kernelAsBlocks {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (v : Word n) (i j l k : Basis n) :
    (ofReal half)^n*sumOver (words n) (fun p => if wordAdd p v∈G.labels then wordEntry imaginaryUnit p i j*wordEntry imaginaryUnit p l k else 0)=
    sumOver T.reps (fun a => block half L a i k*block half L (wordAdd a v) l j) := by
  rw [cosetWordKernel half h2]
  let f g := lifted (R:=R) L g i k
  let u g := chi v g*lifted (R:=R) L g l j
  have first (a : Word n) : block half L a i k=complexTransform half G f a := rfl
  have second (a : Word n) : block half L (wordAdd a v) l j=complexTransform half G u a := by
    unfold block raw complexTransform; congr 1; apply sumOverCongr; intro p; unfold u; rw [charAddLeft]; grind only
  simp only [first,second]; rw [complexPairing half h2 T f u]
  congr 1; apply sumOverCongr; intro p; unfold f u lifted
  cases b : L.sign p <;> simp [phase] <;> grind only

end RankSeven.StabilizerSectorKernel

#print axioms RankSeven.StabilizerSectorKernel.complexPairing
#print axioms RankSeven.StabilizerSectorKernel.cosetWordKernel
#print axioms RankSeven.StabilizerSectorKernel.kernelAsBlocks

