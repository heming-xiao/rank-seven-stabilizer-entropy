import Rank7StabilizerSectorKernel

namespace RankSeven.StabilizerExteriorTrace

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPopulationRounding StabilizerSmallCodes StabilizerPairedCharacters StabilizerOddSector StabilizerSectorKernel
open PhysicalMixedFrame (pairs Pair)
open JointProbePayment (pairAmplitude pairWeight)
variable {R C : Type} [CommRing R] [CommRing C]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem prodSum {α β : Type} (xs : List α) (ys : List β) (F : α×β→C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

def amplitude {n : Nat} (x y : Basis n→ComplexScalar R) (p : Word n) :=
  sumOver (pairs n) (fun e => (x e.1*y e.2)*wordEntry imaginaryUnit p e.2 e.1)

def coordinate {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n) (x y : Basis n→ComplexScalar R) :=
  sumOver (pairs n) (fun e => (star (x e.1)*y e.2)*block half L a e.1 e.2)

theorem frameAmplitude {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) (i j : Fin 7) :
    amplitude (fun t => A t i) (fun t => A t j) p=pairAmplitude A p i j := by
  unfold amplitude pairAmplitude PhysicalMixedFrame.dual; apply sumOverCongr; intro e; grind only

theorem coordinatePop {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n) (x : Basis n→ComplexScalar R) :
    (coordinate half L a x x).re=pop half L a x := by
  unfold coordinate pop SlaterUnionBound.energy pairs; rw [prodSum]
  congr 1; apply sumOverCongr; intro i
  change sumOver _ (fun j => (star (x i)*x j)*block half L a i j)=star (x i)*sumOver _ (fun j => block half L a i j*x j)
  rw [sumOverMulLeft]; apply sumOverCongr; intro j; grind only

private theorem factorCross {α : Type} (xs : List α) (u v : α→α→C) :
    sumOver (productIndices xs xs) (fun e => sumOver (productIndices xs xs) (fun f => u f.1 e.1*v f.2 e.2))=
      sumOver (productIndices xs xs) (fun e => u e.1 e.2)*sumOver (productIndices xs xs) (fun f => v f.1 f.2) := by
  simp only [prodSum]
  rw [sumOverSwap xs xs u,sumOverSwap xs xs v]
  simp only [←sumOverMulLeft,←sumOverMulRight]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The two source bilinear forms restricted to one physical Pauli coset.
Both factors on the right are actual compressed character projectors. -/
theorem amplitudeCoset {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (w : Word n) (x y u v : Basis n→ComplexScalar R) :
    (ofReal half)^n*sumOver (words n) (fun p => if wordAdd p w∈G.labels then amplitude x y p*star (amplitude u v p) else 0)=
      sumOver T.reps (fun a => coordinate half L (wordAdd a w) u x*coordinate half L (wordAdd a z.offset) v y) := by
  let ps := pairs n
  let W (p : Word n) := wordEntry (imaginaryUnit (R:=R)) p
  let B a := block half L a
  let F (e f : Pair n) := (x e.1*y e.2)*(star (u f.1)*star (v f.2))
  let K (p : Word n) (e f : Pair n) := if wordAdd p w∈G.labels then W p e.2 e.1*W p f.1 f.2 else 0
  let h := (ofReal half)^n
  have expand (p : Word n) : (if wordAdd p w∈G.labels then amplitude x y p*star (amplitude u v p) else 0)=
      sumOver ps (fun e => sumOver ps (fun f => F e f*K p e f)) := by
    by_cases mm : wordAdd p w∈G.labels
    · unfold amplitude; simp only [mm,ite_true,ComplexExterior.starSumOver,star_mul,ComplexPauliMoment.wordHermitian,sumOverMulRight]
      apply sumOverCongr; intro e; rw [sumOverMulLeft]; apply sumOverCongr; intro f; simp only [F,K,mm,ite_true,W]; grind only
    · simp only [mm,ite_false,K,Semiring.mul_zero]
      have zero (xs : List (Pair n)) : sumOver xs (fun _ => (0:ComplexScalar R))=0 := by
        induction xs with | nil => rfl | cons a xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
      rw [zero,zero]
  change h*sumOver (words n) _=_
  rw [sumOverCongr _ expand,sumOverSwap (words n) ps,sumOverMulLeft]; 
  have move (e : Pair n) : h*sumOver (words n) (fun p => sumOver ps (fun f => F e f*K p e f))=
      sumOver ps (fun f => sumOver T.reps (fun a => F e f*(B a e.2 f.2*B (wordAdd a w) f.1 e.1))) := by
    rw [sumOverSwap,sumOverMulLeft]; apply sumOverCongr; intro f; rw [←sumOverMulLeft,←sumOverMulLeft]
    have res := kernelAsBlocks half h2 L T w e.2 e.1 f.1 f.2
    change h*sumOver (words n) (fun p => K p e f)=sumOver T.reps (fun a => B a e.2 f.2*B (wordAdd a w) f.1 e.1) at res
    rw [←res]; grind only
  rw [sumOverCongr ps move]
  have cycle (S : Pair n→Pair n→Word n→ComplexScalar R) :
      sumOver ps (fun e => sumOver ps (fun f => sumOver T.reps (S e f)))=
      sumOver T.reps (fun a => sumOver ps (fun e => sumOver ps (fun f => S e f a))) := by
    have ins (e : Pair n) := sumOverSwap ps T.reps (S e)
    simp only [ins]; rw [sumOverSwap]
  rw [cycle]; apply sumOverCongr; intro a
  let U (s i : Basis n) := (star (u s)*x i)*B (wordAdd a w) s i
  let V (t j : Basis n) := (star (v t)*y j)*B (wordAdd a z.offset) t j
  have tr (s t : Basis n) : B a s t=B (wordAdd a z.offset) t s :=
    congrFun (congrFun (conjugateBlock half L z a) t) s
  have e (i : Pair n) (j : Pair n) :
      F i j*(B a i.2 j.2*B (wordAdd a w) j.1 i.1)=U j.1 i.1*V j.2 i.2 := by
    rw [tr i.2 j.2]; unfold F U V; grind only
  simp only [e]
  exact factorCross (qubitIndices n) U V

def compressed {n : Nat} {α : Type} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→α→ComplexScalar R) (i j : α) := coordinate half L a (fun x => A x i) (fun x => A x j)

def mass {n : Nat} {α : Type} (xs : List α) (half : R) {G : MaximalFamily n} (L : Lift G) (A : Basis n→α→ComplexScalar R) (a : Word n) :=
  sumOver xs (fun i => pop half L a (fun x => A x i))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum {α : Type} (xs : List α) (f : α→ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=_; rw [re_add,ih]; rfl

theorem compressedGram {n : Nat} {α : Type} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n)
    (A : Basis n→α→ComplexScalar R) :
    let amb := qubitIndices n
    let F := matMul amb (block half L a) A
    compressed half L a A=matMul amb (PhysicalPairedReduction.dagger F) F := by
  let amb := qubitIndices n
  let B := block half L a
  let gram := blockIsometry half h2 L a
  dsimp only
  rw [PhysicalPairedReduction.daggerProduct,matMulAssoc,←matMulAssoc amb amb (PhysicalPairedReduction.dagger B) B A,gram]
  funext i j; unfold compressed coordinate pairs; rw [prodSum]; apply sumOverCongr; intro x
  change sumOver amb (fun y => (star (A x i)*A y j)*B x y)=star (A x i)*sumOver amb (fun y => B x y*A y j)
  rw [sumOverMulLeft]; apply sumOverCongr; intro y; grind only

theorem gramCross {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ)
    (F : β→α→ComplexScalar R) (U : γ→α→ComplexScalar R) :
    0≤(trace xs (matMul xs (matMul ys (PhysicalPairedReduction.dagger F) F) (matMul zs (PhysicalPairedReduction.dagger U) U))).re := by
  let B := matMul xs F (PhysicalPairedReduction.dagger U)
  have eq : trace xs (matMul xs (matMul ys (PhysicalPairedReduction.dagger F) F) (matMul zs (PhysicalPairedReduction.dagger U) U))=
      trace ys (matMul zs B (PhysicalPairedReduction.dagger B)) := by
    unfold B; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerInvolution]
    rw [matMulAssoc ys xs,traceMatMulSwap xs ys (PhysicalPairedReduction.dagger F)]
    simp only [matMulAssoc]
  rw [eq]; unfold trace matMul
  rw [reSum]; apply Compression.sumOverNonnegative; intro i _
  rw [reSum]; apply Compression.sumOverNonnegative; intro j _
  change 0≤(B i j*star (B i j)).re; rw [CommSemiring.mul_comm,re_star_mul_self]; exact normSq_nonnegative _

theorem compressedCross {α : Type} {n : Nat} (xs : List α) (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (a b : Word n) (A : Basis n→α→ComplexScalar R) :
    0≤sumOver xs (fun i => sumOver xs (fun j => (compressed half L a A j i*compressed half L b A i j).re)) := by
  let amb := qubitIndices n
  have pos := gramCross xs amb amb (matMul amb (block half L b) A) (matMul amb (block half L a) A)
  rw [←compressedGram half h2 L b A,←compressedGram half h2 L a A] at pos
  unfold trace matMul at pos; simp only [reSum] at pos
  have e (i j : α) : compressed half L a A j i*compressed half L b A i j=compressed half L b A i j*compressed half L a A j i := CommSemiring.mul_comm _ _
  simp only [e]; exact pos

theorem diagonalReal {α : Type} {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (a : Word n) (A : Basis n→α→ComplexScalar R) (i : α) :
    compressed half L a A i i=ofReal (pop half L a (fun x => A x i)) := by
  apply ComplexScalar.ext
  · exact coordinatePop half L a _
  · let F := matMul (qubitIndices n) (block half L a) A
    rw [compressedGram half h2 L a A]; change (sumOver (qubitIndices n) (fun j => star (F j i)*F j i)).im=0
    have zero {β : Type} (ys : List β) (f : β→ComplexScalar R) : (sumOver ys (fun i => star (f i)*f i)).im=0 := by
      induction ys with
      | nil => rfl
      | cons i ys ih => change (star (f i)*f i+sumOver ys (fun j => star (f j)*f j)).im=0; rw [im_add,star_mul_self,im_ofReal,ih]; grind only
    exact zero _ _

theorem sourceTraceBound {α : Type} {n : Nat} (xs : List α) (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (a b : Word n) (A : Basis n→α→ComplexScalar R) :
    sumOver xs (fun i => sumOver xs (fun j => (compressed half L a A i i*compressed half L b A j j-
      compressed half L a A j i*compressed half L b A i j).re))≤mass xs half L A a*mass xs half L A b := by
  have pos := compressedCross xs half h2 L a b A
  let p (a : Word n) (i : α) := pop half L a (fun x => A x i)
  have diag (i j : α) : (compressed half L a A i i*compressed half L b A j j).re=p a i*p b j := by
    rw [diagonalReal half h2 L a A i,diagonalReal half h2 L b A j]; unfold p; simp only [re_mul,re_ofReal,im_ofReal]; grind only
  have product : sumOver xs (fun i => sumOver xs (fun j => p a i*p b j))=mass xs half L A a*mass xs half L A b := by
    simp only [←sumOverMulLeft,←sumOverMulRight]; rfl
  simp only [re_sub,Compression.sumOverSub,diag,product]; grind only

def residual {n : Nat} {α : Type} (A : Basis n→α→ComplexScalar R) (p : Word n) (i j : α) : R :=
  let b (i j : α) := amplitude (fun x => A x i) (fun x => A x j) p
  (b i j*star (b i j)-b i j*star (b j i)).re

def wedgePrice {n : Nat} {α : Type} (xs : List α) (A : Basis n→α→ComplexScalar R) (p : Word n) :=
  sumOver (SectorDefectAccounting.wedgePairs xs) (fun ij => normSq (amplitude (fun x => A x ij.1) (fun x => A x ij.2) p))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem amplitudeTranspose {n : Nat} (p : Word n) (x y : Basis n→ComplexScalar R) :
    amplitude y x p=(wordSign p:ComplexScalar R)*amplitude x y p := by
  unfold amplitude pairs; simp only [prodSum,sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b
  rw [wordEntryTranspose imaginaryUnit p b a]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumAppend {α : Type} (xs ys : List α) (f : α→R) : sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih => simp only [List.cons_append,sumOver,List.map_cons,List.sum_cons] at *; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem residualSum {α : Type} {n : Nat} (xs : List α) (A : Basis n→α→ComplexScalar R) (p : Word n) :
    sumOver xs (fun i => sumOver xs (residual A p i))=if MixedDefect.oddWord p then 4*wedgePrice xs A p else 0 := by
  let b (i j : α) := amplitude (fun x => A x i) (fun x => A x j) p
  let B (i j : α) := normSq (b i j)
  have swap (i j : α) : b j i=phase (MixedDefect.oddWord p)*b i j := by
    rw [←MixedDefect.oddWordTransposeSign]; exact amplitudeTranspose p _ _
  have point (i j : α) : residual A p i j=if MixedDefect.oddWord p then 2*B i j else 0 := by
    change (b i j*star (b i j)-b i j*star (b j i)).re=_
    rw [swap i j]; cases h : MixedDefect.oddWord p <;> simp only [phase,Bool.false_eq_true,ite_true,ite_false,star_mul,B]
    all_goals simp only [normSq,re_sub,re_mul,im_mul,re_star,im_star,re_neg,im_neg,re_one,im_one]; grind only
  have symmetry (i j : α) : residual A p i j=residual A p j i := by
    simp only [point]; cases h : MixedDefect.oddWord p <;> simp only [Bool.false_eq_true,ite_true,ite_false]
    unfold B; rw [swap i j,h]; simp only [phase,ite_true,normSq,re_mul,im_mul,re_neg,im_neg,re_one,im_one]; grind only
  have diagonal (i : α) : residual A p i i=0 := by unfold residual; simp only [re_sub]; grind only
  have doubleSum (ys : List α) : sumOver ys (fun i => sumOver ys (residual A p i))=
      2*sumOver (SectorDefectAccounting.wedgePairs ys) (fun ij => residual A p ij.1 ij.2) := by
    induction ys with
    | nil => change (0:R)=2*0; grind only
    | cons a ys ih =>
      rw [SectorDefectAccounting.wedgePairs,sumAppend]
      have map : sumOver (ys.map (fun y => (a,y))) (fun ij => residual A p ij.1 ij.2)=sumOver ys (residual A p a) := by simp [sumOver,List.map_map,Function.comp_def]
      rw [map]
      change (residual A p a a+sumOver ys (residual A p a))+sumOver ys (fun i => residual A p i a+sumOver ys (residual A p i))=_
      rw [sumOverAdd,ih,diagonal]
      have e (i : α) : residual A p i a=residual A p a i := symmetry i a
      rw [sumOverCongr ys e]; grind only
  rw [doubleSum]; simp only [point]; cases h : MixedDefect.oddWord p
  · simp only [Bool.false_eq_true,ite_false]
    have zero (ys : List (α×α)) : sumOver ys (fun _ => (0:R))=0 := by
      induction ys with | nil => rfl | cons i ys ih => change 0+sumOver ys _=0; rw [ih]; grind only
    rw [zero]; grind only
  · simp only [ite_true,←sumOverMulLeft]; change 2*(2*wedgePrice xs A p)=4*wedgePrice xs A p; grind only

theorem residualCoset {α : Type} {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (w : Word n) (A : Basis n→α→ComplexScalar R) (i j : α) :
    half^n*sumOver (words n) (fun p => if wordAdd p w∈G.labels then residual A p i j else 0)=
      sumOver T.reps (fun a => (compressed half L (wordAdd a w) A i i*compressed half L (wordAdd a z.offset) A j j-
        compressed half L (wordAdd a w) A j i*compressed half L (wordAdd a z.offset) A i j).re) := by
  let x (i : α) (v : Basis n) := A v i
  let m (p : Word n) := wordAdd p w∈G.labels
  let b (i j : α) p := amplitude (x i) (x j) p
  let F i j k l (p : Word n) := if wordAdd p w∈G.labels then b i j p*star (b k l p) else 0
  let V i j k l a := compressed half L (wordAdd a w) A k i*compressed half L (wordAdd a z.offset) A l j
  have coset (i j k l : α) : half^n*sumOver (words n) (fun p => (F i j k l p).re)=
      sumOver T.reps (fun a => (V i j k l a).re) := by
    have e := congrArg ComplexScalar.re (amplitudeCoset half h2 L T z w (x i) (x j) (x k) (x l))
    change ((ofReal half)^n*sumOver (words n) (F i j k l)).re=(sumOver T.reps (V i j k l)).re at e
    rw [←PhysicalPairedReduction.realEmbeddingPow,re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,reSum,reSum] at e; grind only
  have eq (p : Word n) : (if wordAdd p w∈G.labels then residual A p i j else 0)=(F i j i j p).re-(F i j j i p).re := by
    by_cases h : wordAdd p w∈G.labels <;> simp only [h,ite_true,ite_false,F,residual,b,x,re_sub,re_zero] <;> grind only
  rw [sumOverCongr _ eq,Compression.sumOverSub]
  change half^n*(_-_) = sumOver T.reps (fun a => (V i j i j a-V i j j i a).re)
  simp only [re_sub,Compression.sumOverSub]; have q := coset i j i j; have t := coset i j j i; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem nestedCycle {α β : Type} (xs : List α) (ys : List β) (f : α→α→β→R) :
    sumOver xs (fun i => sumOver xs (fun j => sumOver ys (f i j)))=
      sumOver ys (fun a => sumOver xs (fun i => sumOver xs (fun j => f i j a))) := by
  simp only [sumOverSwap xs ys]

/-- The normalized skew Pauli trace in a single coset is at most half
the matching product of its trace-one character masses. -/
theorem cosetWedgePrice {α : Type} {n : Nat} (xs : List α) (half : R) (h2 : 2*half=1)
    {G : MaximalFamily n} (L : Lift G) (T : Transversal G) (z : TransposeOffset G) (w : Word n) (A : Basis n→α→ComplexScalar R) :
    2*JointProbeGram.oddAverage half (fun p => if wordAdd p w∈G.labels then wedgePrice xs A p else 0)≤
      sumOver T.reps (fun a => mass xs half L A (wordAdd a w)*mass xs half L A (wordAdd a z.offset)) := by
  let os := MixedDefect.oddWords n
  let ws := words n
  let f (p : Word n) := if wordAdd p w∈G.labels then wedgePrice xs A p else 0
  let V (i j : α) (a : Word n) := (compressed half L (wordAdd a w) A i i*compressed half L (wordAdd a z.offset) A j j-
        compressed half L (wordAdd a w) A j i*compressed half L (wordAdd a z.offset) A i j).re
  let d (i j : α) (p : Word n) := if wordAdd p w∈G.labels then residual A p i j else 0
  have formula (i j : α) : half^n*sumOver ws (d i j)=sumOver T.reps (V i j) := residualCoset half h2 L T z w A i j
  have filt (ys : List (Word n)) : sumOver (ys.filter MixedDefect.oddWord) f=sumOver ys (fun p => if MixedDefect.oddWord p then f p else 0) := by
    induction ys with
    | nil => rfl
    | cons p ys ih => rw [List.filter_cons]; cases e : MixedDefect.oddWord p <;> simp [e,sumOver] at ih ⊢ <;> grind only
  have zero (ys : List α) : sumOver ys (fun _ => (0:R))=0 := by
    induction ys with | nil => rfl | cons i ys ih => change 0+sumOver ys _=0; rw [ih]; grind only
  have row (p : Word n) : sumOver xs (fun i => sumOver xs (fun j => d i j p))=4*(if MixedDefect.oddWord p then f p else 0) := by
    by_cases h : wordAdd p w∈G.labels
    · simp only [d,h,ite_true,f]; rw [residualSum]; cases MixedDefect.oddWord p <;> simp <;> grind only
    · simp only [d,h,ite_false,f,zero]; split <;> grind only
  have eq : sumOver xs (fun i => sumOver xs (fun j => half^n*sumOver ws (d i j)))=
      half^n*(4*sumOver os f) := by
    simp only [←sumOverMulLeft,nestedCycle,row,←show sumOver os f=sumOver ws (fun p => if MixedDefect.oddWord p then f p else 0) from filt ws]
  simp only [formula,nestedCycle] at eq
  have e := Compression.sumOverNonnegative T.reps
    (fun a => (mass xs half L A (wordAdd a w)*mass xs half L A (wordAdd a z.offset))-sumOver xs (fun i => sumOver xs (fun j => V i j a)))
    (fun a _ => by have b := sourceTraceBound xs half h2 L (wordAdd a w) (wordAdd a z.offset) A
                   change sumOver xs (fun i => sumOver xs (fun j => V i j a))≤_ at b; grind only)
  rw [Compression.sumOverSub,eq] at e
  change 2*(2*half^n*sumOver os f)≤_; grind only

end RankSeven.StabilizerExteriorTrace

#print axioms RankSeven.StabilizerExteriorTrace.amplitudeCoset
#print axioms RankSeven.StabilizerExteriorTrace.compressedCross
#print axioms RankSeven.StabilizerExteriorTrace.sourceTraceBound
#print axioms RankSeven.StabilizerExteriorTrace.residualCoset
#print axioms RankSeven.StabilizerExteriorTrace.cosetWedgePrice

