import Rank7JointProbeGram
import Rank7PhysicalCutCapacities

/-! Compression of a unitary Pauli bilinear form to seven complex columns. -/
namespace RankSeven.PauliPairContraction
open Lean.Grind Pauli ComplexScalar JointProbePayment
open PhysicalPairedReduction (dagger)
open ComplexPauliMoment (conjugate)
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def image {α β : Type} (xs : List β) (M : α → β → ComplexScalar R) (z : β → ComplexScalar R) (a : α) :=
  sumOver xs (fun b => M a b*z b)
def normSum {α : Type} (xs : List α) (z : α → ComplexScalar R) := sumOver xs (fun a => normSq (z a))

private theorem realSum {α : Type} (xs : List α) (z : α → ComplexScalar R) :
    (sumOver xs z).re=sumOver xs (fun x => (z x).re) := by
  induction xs with
  | nil => rfl
  | cons u xs ih => change (z u+sumOver xs z).re=_; rw [re_add,ih]; rfl

theorem imageNorm {α β : Type} [DecidableEq β] (xs : List α) (ys : List β) (nd : ys.Nodup) (full : ∀ u,u∈ys)
    (M : α → β → ComplexScalar R) (gram : ∀ i j,matMul xs (dagger M) M i j=if i=j then 1 else 0)
    (z : β → ComplexScalar R) : normSum xs (image ys M z)=normSum ys z := by
  let Z (i : β) (_ : Unit) := z i
  let V := matMul ys M Z
  have id (i : β) : matMul ys (matMul xs (dagger M) M) Z i ()=z i := by
    change sumOver ys (fun j => matMul xs (dagger M) M i j*z j)=_
    simp only [gram]
    rw [←ExteriorPauliBase.sumOnIndex ys i z nd (full i)]; apply sumOverCongr; intro j
    by_cases h : i=j <;> simp [h] <;> grind only
  have c : matMul xs (dagger V) V () ()=matMul ys (dagger Z) Z () () := by
    change matMul xs (dagger (matMul ys M Z)) (matMul ys M Z) () ()=_
    rw [PhysicalPairedReduction.daggerProduct,matMulAssoc,←matMulAssoc xs ys (dagger M) M Z]
    change sumOver ys (fun i => dagger Z () i*matMul ys (matMul xs (dagger M) M) Z i ())=_
    simp only [id]; rfl
  change sumOver xs (fun i => star (image ys M z i)*image ys M z i)=sumOver ys (fun i => star (z i)*z i) at c
  have re := congrArg ComplexScalar.re c
  simpa only [realSum,re_star_mul_self,normSum] using re

private theorem unitEntry {n : Nat} (u v : Basis n) :
    wordEntry (imaginaryUnit (R:=R)) (SymmetricDefect.unitWord n) u v=if u=v then 1 else 0 := by
  induction n with
  | zero => cases u; cases v; simp [SymmetricDefect.unitWord,wordEntry]; grind only
  | succ n ih =>
    rcases u with ⟨a,u⟩; rcases v with ⟨b,v⟩
    cases a <;> cases b <;> by_cases h : u=v <;> simp [SymmetricDefect.unitWord,wordEntry,entry,ih,h] <;> grind only

theorem wordIsometry {n : Nat} (p : Word n) (z : Basis n → ComplexScalar R) :
    normSum (qubitIndices n) (image (qubitIndices n) (wordEntry imaginaryUnit p) z)=normSum (qubitIndices n) z := by
  apply imageNorm _ _ (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  intro i j
  have h : dagger (wordEntry (imaginaryUnit (R:=R)) p)=wordEntry imaginaryUnit p := by
    funext a b; exact ComplexPauliMoment.wordHermitian p b a
  rw [h,PhysicalAntiQuartic.physicalWordProduct imaginaryUnit imaginaryUnit_sq,PhysicalAntiQuartic.cocycleSelf,
    PhysicalAntiQuartic.labelSelf,unitEntry,Semiring.one_mul]

private theorem pairSum {α β : Type} (xs : List α) (ys : List β) (f : α×β → ComplexScalar R) :
    sumOver (productIndices xs ys) f=sumOver xs (fun i => sumOver ys (fun j => f (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i
  simp [sumOver,List.map_map,Function.comp_def]

theorem amplitudeMatrix {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    (fun i j => pairAmplitude A p j i)=matMul (qubitIndices n) (transpose A) (matMul (qubitIndices n) (wordEntry imaginaryUnit p) A) := by
  funext i j
  unfold pairAmplitude PhysicalMixedFrame.pairs
  rw [pairSum,sumOverSwap]
  change sumOver _ (fun b => sumOver _ (fun a => wordEntry imaginaryUnit p b a*(A a j*A b i)))=_
  unfold matMul transpose; simp only [sumOverMulLeft]; apply sumOverCongr; intro b; apply sumOverCongr; intro a; grind only

theorem amplitudeSkew {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n)
    (hp : p∈MixedDefect.oddWords n) (i j : Fin 7) : pairAmplitude A p j i= -pairAmplitude A p i j := by
  have odd := (List.mem_filter.mp hp).2
  have sign : (wordSign p : ComplexScalar R)= -1 := by rw [MixedDefect.oddWordTransposeSign,odd]; rfl
  have neg (x : ComplexScalar R) : -x=(-1)*x := by grind only
  rw [neg]; unfold pairAmplitude PhysicalMixedFrame.pairs
  simp only [pairSum,sumOverMulLeft]
  rw [sumOverSwap (qubitIndices n) _ (fun a b => PhysicalMixedFrame.dual p (a,b)*(A a j*A b i))]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b
  unfold PhysicalMixedFrame.dual
  rw [wordEntryTranspose imaginaryUnit p b a,sign]; grind only

theorem pairWeightSymm {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n)
    (hp : p∈MixedDefect.oddWords n) (i j : Fin 7) : pairWeight A p i j=pairWeight A p j i := by
  unfold pairWeight; rw [amplitudeSkew A p hp i j]; simp only [normSq,re_neg,im_neg]; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem conjugateOrth {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (i j : Fin 7) :
    sumOver (qubitIndices n) (fun x => star (conjugate A x i)*conjugate A x j)=if i=j then 1 else 0 := by
  unfold conjugate; simp only [star_star]
  calc
    _ = sumOver (qubitIndices n) (fun x => star (A x j)*A x i) := by apply sumOverCongr; intro x; grind only
    _ = _ := by rw [orth]; by_cases e : i=j <;> simp [e,eq_comm]

/-- The real sum of squared complex coordinates of the actual Pauli
bilinear compression is contractive on every input vector. -/
theorem physicalSkewContraction {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (z : Fin 7 → ComplexScalar R) :
    let src := List.finRange 7
    normSum src (image src (fun i j => pairAmplitude A p j i) z)≤normSum src z := by
  let src := List.finRange 7
  let xs := qubitIndices n
  let Z (i : Fin 7) (_ : Unit) := z i
  let L := image src A z
  let v := image xs (wordEntry imaginaryUnit p) L
  have normA := imageNorm xs src (List.nodup_finRange 7) (fun x => List.mem_finRange x) A orth z
  have nw := wordIsometry p L
  have b := PhysicalCutCapacities.frameBessel src xs (List.nodup_finRange 7) (fun x => List.mem_finRange x)
    (conjugate A) (conjugateOrth A orth) v
  have h (i : Fin 7) : image src (fun i j => pairAmplitude A p j i) z i=
      sumOver xs (fun t => star (conjugate A t i)*v t) := by
    change matMul src (fun i j => pairAmplitude A p j i) Z i ()=_
    rw [amplitudeMatrix,matMulAssoc,matMulAssoc]
    unfold conjugate; simp only [star_star]; rfl
  dsimp only; unfold normSum
  rw [sumOverCongr src (g:=fun i => normSq (sumOver xs (fun t => star (conjugate A t i)*v t))) (fun i => congrArg normSq (h i))]
  change _≤normSum src z
  exact Std.le_trans b (Std.le_of_eq (nw.trans normA))

/-- Every true Pauli edge vector satisfies the seven degree inequalities. -/
theorem physicalDegree {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (i : Fin 7) :
    sumOver (List.finRange 7) (fun j => pairWeight A p i j)≤1 := by
  let src := List.finRange 7
  let z (j : Fin 7) : ComplexScalar R := if i=j then 1 else 0
  have h (j : Fin 7) : image src (fun s t => pairAmplitude A p t s) z j=pairAmplitude A p i j := by
    unfold image
    rw [←ExteriorPauliBase.sumOnIndex src i (fun k => pairAmplitude A p k j) (List.nodup_finRange 7) (List.mem_finRange i)]
    apply sumOverCongr; intro k; by_cases e : i=k <;> simp [z,e] <;> grind only
  have hz : normSum src z=1 := by
    unfold normSum; rw [←ExteriorPauliBase.sumOnIndex src i (fun _ => (1:R)) (List.nodup_finRange 7) (List.mem_finRange i)]
    apply sumOverCongr; intro k; by_cases e : i=k <;> simp [z,e,normSq] <;> grind only
  have e := physicalSkewContraction A orth p z
  change sumOver src (fun j => normSq (image src (fun s t => pairAmplitude A p t s) z j))≤normSum src z at e
  simpa only [h,hz,pairWeight] using e

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem filterSum {C T : Type} [CommRing C] (xs : List T) (keep : T → Bool) (f : T → C) :
    sumOver (xs.filter keep) f=sumOver xs (fun i => if keep i then f i else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons]; cases h : keep a <;> simp [h,sumOver] at ih ⊢ <;> grind only

/-- Compression of the physical bilinear form to any set of source labels
retains the full contraction inequality on vectors supported on those labels. -/
theorem subsetContraction {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (keep : Fin 7 → Bool)
    (z : Fin 7 → ComplexScalar R) :
    let xs := (List.finRange 7).filter keep
    normSum xs (image xs (fun i j => pairAmplitude A p j i) z)≤normSum xs z := by
  let all := List.finRange 7
  let sub := all.filter keep
  let ext (i : Fin 7) := if keep i then z i else 0
  let H i j := pairAmplitude A p j i
  have eq (i : Fin 7) : image all H ext i=image sub H z i := by
    unfold image sub; rw [filterSum]
    apply sumOverCongr; intro j; unfold ext; cases keep j <;> simp <;> grind only
  have nrm : normSum all ext=normSum sub z := by
    unfold normSum sub; rw [filterSum]; apply sumOverCongr; intro i; unfold ext
    cases keep i <;> simp [normSq] <;> grind only
  have restrict (v : Fin 7 → ComplexScalar R) : normSum sub v≤normSum all v := by
    unfold normSum sub; rw [filterSum]
    have h := Compression.sumOverNonnegative all (fun i => normSq (v i)-(if keep i then normSq (v i) else 0))
      (fun i _ => by cases keep i <;> simp <;> have := normSq_nonnegative (v i) <;> grind only)
    rw [Compression.sumOverSub] at h; grind only
  have h := physicalSkewContraction A orth p ext
  change normSum all (image all H ext)≤normSum all ext at h
  rw [nrm,funext eq] at h
  exact Std.le_trans (restrict _) h

end Order

end RankSeven.PauliPairContraction

#print axioms RankSeven.PauliPairContraction.amplitudeSkew
#print axioms RankSeven.PauliPairContraction.physicalSkewContraction
#print axioms RankSeven.PauliPairContraction.physicalDegree
#print axioms RankSeven.PauliPairContraction.subsetContraction
