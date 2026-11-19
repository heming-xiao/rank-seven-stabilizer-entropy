import Rank7SlaterUnionBound

/-! Odd-rank leakage of two anticommuting Pauli words on an arbitrary
physical frame. The proof uses the unnormalized top Slater vector. -/
namespace RankSeven.PhysicalOddLeakage
open Lean.Grind Pauli ComplexScalar OddTensorUncertainty SlaterAlternant SlaterUnionBound
open PhysicalPairedReduction (dagger)
open PauliPairContraction (image normSum)
open PhysicalCompressionEffect (OrthonormalFrame)
open OddCutReserve (PairLeakage cutLeak)
variable {R α β γ : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def word {n : Nat} (p : Word n) := wordEntry (imaginaryUnit (R:=R)) p

def compression {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n) :=
  let xs := qubitIndices n
  matMul xs (dagger A) (matMul xs (word p) A)

private theorem unitEntry (n : Nat) (u v : Basis n) : word (R:=R) (SymmetricDefect.unitWord n) u v=ident u v := by
  unfold word ident
  induction n with
  | zero => cases u; cases v; simp [wordEntry,SymmetricDefect.unitWord]; grind only
  | succ n ih => obtain ⟨a,u⟩ := u; obtain ⟨b,v⟩ := v; cases a <;> cases b <;> by_cases h : u=v <;> simp [wordEntry,entry,SymmetricDefect.unitWord,ih,h] <;> grind only

private theorem wordHerm {n : Nat} (p : Word n) : dagger (word (R:=R) p)=word p := by
  funext i j; exact ComplexPauliMoment.wordHermitian p j i

private theorem wordGram {n : Nat} (p : Word n) : matMul (qubitIndices n) (dagger (word (R:=R) p)) (word p)=ident := by
  rw [wordHerm]; funext i j; unfold word
  rw [PhysicalAntiQuartic.physicalWordProduct imaginaryUnit imaginaryUnit_sq,PhysicalAntiQuartic.cocycleSelf,
    PhysicalAntiQuartic.labelSelf,Semiring.one_mul]; exact unitEntry n i j

private theorem identityAction [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ i,i∈xs) (A : α→β→ComplexScalar R) :
    matMul xs ident A=A := by
  funext i j; change sumOver xs (fun k => ident i k*A k j)=A i j
  rw [←ExteriorPauliBase.sumOnIndex xs i (fun k => A k j) nd (full i)]
  apply sumOverCongr; intro k; by_cases h : i=k <;> simp only [ident,h,ite_true,ite_false,Semiring.one_mul,Semiring.zero_mul]

private theorem negLeft (xs : List β) (A B : α→β→ComplexScalar R) (M : β→γ→ComplexScalar R) :
    matMul xs (fun i j => A i j-B i j) M = fun i j => matMul xs A M i j-matMul xs B M i j := by
  funext i j; unfold matMul; rw [←Compression.sumOverSub]; apply sumOverCongr; intro k; grind only

private theorem negRight (xs : List β) (M : α→β→ComplexScalar R) (A B : β→γ→ComplexScalar R) :
    matMul xs M (fun i j => A i j-B i j) = fun i j => matMul xs M A i j-matMul xs M B i j := by
  funext i j; unfold matMul; rw [←Compression.sumOverSub]; apply sumOverCongr; intro k; grind only

theorem compressionHerm {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n) :
    dagger (compression A p)=compression A p := by
  unfold compression; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerProduct,
    PhysicalPairedReduction.daggerInvolution,wordHerm,matMulAssoc]

/-- The omitted part of the actual Pauli image is a Gram factor for
I−H†H, where H=A†WA is the compression of that same word. -/
theorem compressionComplement {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) :
    Gram (fun i j => ident i j-matMul (List.finRange m) (dagger (compression A p)) (compression A p) i j) := by
  let xs := qubitIndices n
  let ys := List.finRange m
  let W := word (R:=R) p
  let X := matMul xs W A
  let H := compression A p
  let Y := matMul ys A H
  let G := matMul ys (dagger H) H
  have x : matMul xs (dagger X) X=ident := by
    unfold X; rw [PhysicalPairedReduction.daggerProduct,matMulAssoc,←matMulAssoc xs xs (dagger W) W A,wordGram,
      identityAction xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)]
    exact orth
  have raw : matMul xs (dagger A) X=H := rfl
  have rev : matMul xs (dagger X) A=dagger H := by
    rw [←raw]; conv => rhs; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerInvolution]
  have xy : matMul xs (dagger X) Y=G := by unfold Y G; rw [←matMulAssoc,rev]
  have yx : matMul xs (dagger Y) X=G := by unfold Y G; rw [PhysicalPairedReduction.daggerProduct,matMulAssoc,raw]
  have yy : matMul xs (dagger Y) Y=G := by
    unfold Y G; rw [PhysicalPairedReduction.daggerProduct,matMulAssoc,←matMulAssoc xs ys (dagger A) A H,orth,
      identityAction ys (List.nodup_finRange _) (fun i => List.mem_finRange i)]
  let L i j := X i j-Y i j
  have starL : dagger L=fun i j => dagger X i j-dagger Y i j := by
    funext i j; change star (X j i-Y j i)=star (X j i)-star (Y j i)
    apply ComplexScalar.ext <;> simp <;> grind only
  refine ⟨Basis n,xs,L,?_⟩
  change (fun i j => ident i j-G i j)=matMul xs (dagger L) L
  rw [starL]; unfold L; rw [negLeft,negRight,negRight,x,xy,yx,yy]
  funext i j; grind only

private theorem sumEmbed {ι : Type} (xs : List ι) (a : ι → R) :
    sumOver xs (fun i => ofReal (a i))=ofReal (sumOver xs a) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ofReal (a i)+sumOver xs _=ofReal (a i+sumOver xs a)
    rw [ih]; apply ComplexScalar.ext <;> simp <;> grind only

private theorem reSum {ι : Type} (xs : List ι) (a : ι → ComplexScalar R) :
    (sumOver xs a).re=sumOver xs (fun i => (a i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (a i+sumOver xs a).re=_; rw [re_add,ih]; rfl

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem determinantReal {m : Nat} (H : Mx (Fin m) R) (herm : dagger H=H) : (determinant m H).im=0 := by
  let xs := indices (List.finRange m) m
  let z := slater (C:=ComplexScalar R) m
  let Z i (_ : Unit) := z i
  let M := matrix H m
  let E := matMul xs (dagger Z) (matMul xs M Z)
  let mass := normSum xs z
  let d := determinant m H
  have eh : dagger E=E := by
    unfold E; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerProduct,
      PhysicalPairedReduction.daggerInvolution,matMulAssoc]
    change matMul xs (dagger Z) (matMul xs (dagger (matrix H m)) Z)=_
    rw [matrixDagger,herm]
  have conj := congrFun (congrFun eh ()) ()
  change star (E () ())=E () () at conj
  have scale : E () ()=ofReal mass*d := by
    change sumOver xs (fun i => star (z i)*image xs M z i)=_
    have eq (i : Sites (Fin m) m) : image xs M z i=z i*d := topEigenvector m H i
    simp only [eq,←Semiring.mul_assoc,star_mul_self,←sumOverMulRight,sumEmbed]
    rfl
  rw [scale] at conj
  have ic := congrArg ComplexScalar.im conj
  simp only [im_star,im_mul,re_ofReal,im_ofReal,Semiring.zero_mul,Semiring.add_zero] at ic
  have mn : 0<mass := slaterMassPositive m
  by_cases h : 0<d.im
  · have pos := OrderedRing.mul_pos mn h; change d.im=0; grind only
  · by_cases h' : d.im<0
    · have pos := OrderedRing.mul_pos mn (show 0< -d.im by grind only); change d.im=0; grind only
    · change d.im=0; grind only

def frameSlater {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) :=
  image (indices (List.finRange m) m) (matrix A m) (slater m)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem frameSlaterMass {n m : Nat} (A : Basis n → Fin m → ComplexScalar R)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) :
    normSum (indices (qubitIndices n) m) (frameSlater A)=normSum (indices (List.finRange m) m) (slater (C:=ComplexScalar R) m) := by
  apply PauliPairContraction.imageNorm _ _ (indicesNodup _ (List.nodup_finRange _) _) (indicesFull _ (fun i => List.mem_finRange i) _)
  intro i j; rw [matrixDagger,matrixComp,orth,matrixIdent]; rfl

theorem frameDeterminantExpectation {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n) :
    expectation m (frameSlater A) p=normSum (indices (List.finRange m) m) (slater (C:=ComplexScalar R) m)*(determinant m (compression A p)).re := by
  let src := indices (List.finRange m) m
  let amb := indices (qubitIndices n) m
  let F := matrix A m
  let z := slater (C:=ComplexScalar R) m
  let Z i (_ : Unit) := z i
  let V := matMul src F Z
  let P := pauli (R:=R) m p
  let H := compression A p
  have back : matMul amb (dagger F) (matMul amb P F)=matrix H m := by
    unfold F P pauli H compression word; rw [matrixDagger,matrixComp,matrixComp]
  have t : matMul amb (dagger V) (matMul amb P V)=matMul src (dagger Z) (matMul src (matrix H m) Z) := by
    unfold V; rw [PhysicalPairedReduction.daggerProduct,←back]; simp only [matMulAssoc]
  have e : expectation m (frameSlater A) p=(matMul amb (dagger V) (matMul amb P V) () ()).re := (reSum _ _).symm
  rw [e,t]
  change energy src (matrix H m) z=normSum src z*(determinant m H).re
  exact energyEigen _ _ _ _ (fun i _ _ => topEigenvector m H i)

theorem determinantUncertainty {n m : Nat} (A : Basis n → Fin m → ComplexScalar R)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) (odd : m%2=1) (p q : Word n) (anti : SymmetricDefect.anti p q=true) :
    normSq (determinant m (compression A p))+normSq (determinant m (compression A q))≤1 := by
  let mass := normSum (indices (List.finRange m) m) (slater (C:=ComplexScalar R) m)
  let dp := determinant m (compression A p)
  let dq := determinant m (compression A q)
  have pos : 0<mass := slaterMassPositive m
  have equal := frameSlaterMass A orth
  have nz : 0<normSum (indices (qubitIndices n) m) (frameSlater A) := equal ▸ pos
  have u := pauliUncertainty m odd p q anti (frameSlater A) nz
  rw [frameDeterminantExpectation,frameDeterminantExpectation,equal] at u
  change (mass*dp.re)^2+(mass*dq.re)^2≤mass^2 at u
  have a : dp.im=0 := determinantReal _ (compressionHerm A p)
  have b : dq.im=0 := determinantReal _ (compressionHerm A q)
  change dp.re^2+dp.im^2+(dq.re^2+dq.im^2)≤1
  rw [a,b]; apply Classical.byContradiction; intro no
  have bad := OrderedRing.mul_pos (OrderedRing.mul_pos pos pos) (show 0<dp.re^2+dq.re^2-1 by grind only)
  grind only

def traceLoss {n m : Nat} (A : Basis n → Fin m → ComplexScalar R) (p : Word n) :=
  let H := compression A p
  (trace (List.finRange m) (fun i j => ident i j-matMul (List.finRange m) (dagger H) H i j)).re

/-- On every orthonormal frame of odd size, the true Pauli compression
losses of two anticommuting words sum to at least one. -/
theorem oddFrameLeakage {n m : Nat} (A : Basis n → Fin m → ComplexScalar R)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) (odd : m%2=1) (p q : Word n) (anti : SymmetricDefect.anti p q=true) :
    1≤traceLoss A p+traceLoss A q := by
  have u := determinantUncertainty A orth odd p q anti
  have a := determinantLeakage m _ (compressionComplement A p orth)
  have b := determinantLeakage m _ (compressionComplement A q orth)
  change 1-traceLoss A p≤normSq (determinant m (compression A p)) at a
  change 1-traceLoss A q≤normSq (determinant m (compression A q)) at b
  grind only
def sublabel (r : Fin 7) (i : Fin (r.val+1)) : Fin 7 := ⟨i.val,by have := i.isLt; have := r.isLt; omega⟩

def restrictFrame {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (r : Fin 7) (x : Basis n) (i : Fin (r.val+1)) := A x (sublabel r i)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem restrictedOrth {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (r : Fin 7) :
    matMul (qubitIndices n) (dagger (restrictFrame A r)) (restrictFrame A r)=ident := by
  funext i j; change sumOver _ (fun x => star (A x (sublabel r i))*A x (sublabel r j))=_
  rw [orth]; unfold ident
  have same : sublabel r i=sublabel r j ↔ i=j := ⟨fun e => Fin.ext (congrArg (fun k : Fin 7 => k.val) e), fun e => e ▸ rfl⟩
  simp only [same]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem cutSum (r : Fin 7) (f : Fin 7 → R) :
    sumOver (List.finRange (r.val+1)) (fun i => f (sublabel r i))=
      sumOver PauliReserveSlots.labels (fun i => PauliReserveSlots.cut r i*f i) := by
  have table : ∀ r : Fin 7, (List.finRange (r.val+1)).map (sublabel r)=PauliReserveSlots.labels.filter (fun i => decide (i≤r)) := by decide
  have mapped : sumOver ((List.finRange (r.val+1)).map (sublabel r)) f=sumOver (List.finRange (r.val+1)) (fun i => f (sublabel r i)) := by
    simp only [sumOver,List.map_map,Function.comp_def]
  rw [←mapped,table]
  have filter (xs : List (Fin 7)) : sumOver (xs.filter (fun i => decide (i≤r))) f=sumOver xs (fun i => PauliReserveSlots.cut r i*f i) := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      rw [List.filter_cons]
      by_cases h : a≤r <;> simp [h,PauliReserveSlots.cut,sumOver] at ih ⊢ <;> grind only
  exact filter _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem traceLossEqCut {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (r : Fin 7) (p : Word n) :
    traceLoss (restrictFrame A r) p=cutLeak A r p := by
  let xs := List.finRange (r.val+1)
  let M i j := normSq (FrameExteriorSector.framedWord A p i j)
  let m (i j : Fin (r.val+1)) := M (sublabel r i) (sublabel r j)
  let c := PauliReserveSlots.cut (R:=R) r
  let L := PauliReserveSlots.labels
  have eq (i j) : compression (restrictFrame A r) p i j=FrameExteriorSector.framedWord A p (sublabel r i) (sublabel r j) := rfl
  have left : traceLoss (restrictFrame A r) p=sumOver xs (fun _ => (1:R))-sumOver xs (fun i => sumOver xs (m i)) := by
    unfold traceLoss trace
    change (sumOver xs (fun i => ident i i-sumOver xs (fun j =>
      star (compression (restrictFrame A r) p j i)*compression (restrictFrame A r) p j i))).re=_
    simp only [reSum,re_sub,ident,ite_true,re_one,re_star_mul_self,eq,Compression.sumOverSub]
    rw [sumOverSwap xs xs (fun i j => M (sublabel r j) (sublabel r i))]
  have mask (i) : c i*1=c i*c i := by unfold c PauliReserveSlots.cut; split <;> grind only
  have size : sumOver xs (fun _ => (1:R))=sumOver L (fun i => c i*c i) := by
    have h := cutSum r (fun _ => (1:R)); exact h.trans (sumOverCongr L mask)
  have row (i : Fin 7) : sumOver xs (fun j => M i (sublabel r j))=sumOver L (fun j => c j*M i j) := cutSum r (M i)
  have block : sumOver xs (fun i => sumOver xs (m i))=sumOver L (fun i => sumOver L (fun j => c i*c j*M i j)) := by
    dsimp only [m]; simp only [row]
    rw [cutSum r (fun i => sumOver L (fun j => c j*M i j))]
    apply sumOverCongr; intro i; rw [sumOverMulLeft]; apply sumOverCongr; intro j; grind only
  rw [left,size,block]; rfl

/-- Every odd rank prefix of the original seven physical columns has
unit paired leakage, for every anticommuting pair, including ranks
three, five, and seven. -/
theorem physicalOddCut {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (r : Fin 7)
    (odd : (r.val+1)%2=1) : PairLeakage A r := by
  intro p q ant
  have h := oddFrameLeakage (restrictFrame A r) (restrictedOrth A orth r) odd p q ant
  simpa only [traceLossEqCut] using h

theorem physicalOddCuts {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    PairLeakage A 2 ∧ PairLeakage A 4 ∧ PairLeakage A 6 :=
  ⟨physicalOddCut A orth 2 (by decide),physicalOddCut A orth 4 (by decide),physicalOddCut A orth 6 (by decide)⟩

end Order

end RankSeven.PhysicalOddLeakage

#print axioms RankSeven.PhysicalOddLeakage.compressionComplement
#print axioms RankSeven.PhysicalOddLeakage.determinantReal
#print axioms RankSeven.PhysicalOddLeakage.frameSlaterMass
#print axioms RankSeven.PhysicalOddLeakage.frameDeterminantExpectation
#print axioms RankSeven.PhysicalOddLeakage.determinantUncertainty
#print axioms RankSeven.PhysicalOddLeakage.oddFrameLeakage
#print axioms RankSeven.PhysicalOddLeakage.traceLossEqCut
#print axioms RankSeven.PhysicalOddLeakage.physicalOddCut
#print axioms RankSeven.PhysicalOddLeakage.physicalOddCuts

