import Rank7PackingInterpolation
import Rank7PhysicalCutCapacities
import Rank7PhysicalDirectedCapacity
import Rank7PhysicalTwoHoleUpper

/-! Exact suffix-gap expansion of the four-site probability product and its
normalized physical overlap debit on an orthonormal rank-seven frame. -/
namespace RankSeven.PackingPolynomial

open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation
attribute [local instance] Semiring.natCast
variable {R : Type} [CommRing R]

/-- Stable binary partitions certify the exact permutation of the 2401 ordered gap assignments. -/
private def radix : Nat → List Gap → List Gap
  | 0,xs => xs
  | k+1,xs =>
    let left (m : Gap) := !(key m).testBit k
    radix k (xs.filter left) ++ radix k (xs.filter (fun m => !(left m)))

private theorem radixPerm (k : Nat) (xs : List Gap) : (radix k xs).Perm xs := by
  induction k generalizing xs with
  | zero => exact List.Perm.refl _
  | succ k ih => exact ((ih _).append (ih _)).trans (List.filter_append_perm _ xs)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem sortedAssignmentList :
    radix 12 (fullGaps.flatMap assignments) = fourIndices (List.finRange 7) := by decide

private theorem assignmentPerm : (fullGaps.flatMap assignments).Perm (fourIndices (List.finRange 7)) := by
  rw [←sortedAssignmentList]; exact (radixPerm _ _).symm


private theorem sumPerm {α : Type} {xs ys : List α} (p : xs.Perm ys) (f : α → R) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem productPerm {α : Type} {xs ys : List α} (p : xs.Perm ys) (f : α → R) :
    (xs.map f).prod=(ys.map f).prod := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,List.prod_cons]; rw [ih]
  | swap => simp only [List.map_cons,List.prod_cons]; grind
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private def slots {α : Type} (q : Four α) := [q.1.1,q.1.2,q.2.1,q.2.2]

private theorem sameMonomial (b : Fin 7 → R) (m q : Gap) (hq : q∈assignments m) : monomial b q=monomial b m := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hq)
  have tab : ExteriorPauliBase.permutations.all (fun p => decide ((slots p).Perm ([0,1,2,3] : List (Fin 4))))=true := by decide
  let f (j : Fin 4) := b (GenericExteriorKernel.position m j)
  have eq := productPerm (_root_.of_decide_eq_true (List.all_eq_true.mp tab p hp)) f
  change f p.1.1*(f p.1.2*(f p.2.1*(f p.2.2*1)))=b m.1.1*(b m.1.2*(b m.2.1*(b m.2.2*1))) at eq
  change f p.1.1*f p.1.2*f p.2.1*f p.2.2=b m.1.1*b m.1.2*b m.2.1*b m.2.2
  grind

def suffix (b : Fin 7 → R) (i : Fin 7) := sumOver (List.finRange 7) fun j => if i≤j then b j else 0

private def allows (w : Wedge7) (q : Gap) := decide (w.i≤q.1.1 ∧ w.j≤q.1.2 ∧ w.k≤q.2.1 ∧ w.m≤q.2.2)

private theorem suffixProduct (b : Fin 7 → R) (w : Wedge7) :
    amplitude (suffix b) w=sumOver (fourIndices (List.finRange 7)) (fun q => if allows w q then monomial b q else 0) := by
  let xs := List.finRange 7
  let h (i j : Fin 7) : R := if i≤j then b j else 0
  let ff (ij : Fin 7 × Fin 7) := h w.i ij.1*h w.j ij.2
  let gg (kl : Fin 7 × Fin 7) := h w.k kl.1*h w.m kl.2
  have prod (q : Gap) : (if allows w q then monomial b q else 0)=ff q.1*gg q.2 := by
    unfold allows monomial ff gg h
    by_cases a : w.i≤q.1.1 <;> by_cases e : w.j≤q.1.2 <;> by_cases c : w.k≤q.2.1 <;> by_cases d : w.m≤q.2.2 <;>
      simp [a,e,c,d] <;> grind
  rw [sumOverCongr _ prod]
  change amplitude (suffix b) w=sumOver (productIndices (productIndices xs xs) (productIndices xs xs)) _
  rw [factorProductSum (productIndices xs xs) (productIndices xs xs) ff gg]
  unfold ff gg; rw [factorProductSum xs xs (h w.i) (h w.j),factorProductSum xs xs (h w.k) (h w.m)]
  change suffix b w.i*suffix b w.j*suffix b w.k*suffix b w.m=(suffix b w.i*suffix b w.j)*(suffix b w.k*suffix b w.m); grind

private theorem sumCount {α : Type} (xs : List α) (p : α → Bool) (z : R) :
    sumOver xs (fun a => if p a then z else 0)=Nat.cast (xs.countP p)*z := by
  induction xs with
  | nil => change 0=(Nat.cast 0:R)*z; rw [Semiring.natCast_zero]; grind
  | cons a xs ih =>
    change (if p a then z else 0)+sumOver xs (fun a => if p a then z else 0)=_
    rw [ih,List.countP_cons]; cases p a <;> simp only [Bool.false_eq_true,ite_false,ite_true,Semiring.natCast_add] <;> grind

private theorem perGap (b : Fin 7 → R) (w : Wedge7) (m : Gap) :
    sumOver (assignments m) (fun q => if allows w q then monomial b q else 0)=Nat.cast (forwardCost m w)*monomial b m := by
  have changeOrder : sumOver (assignments m) (fun q => if allows w q then monomial b q else 0)=
      sumOver (assignments m) (fun q => if allows w q then monomial b m else 0) := by
    apply congrArg List.sum; apply List.map_congr_left; intro q hq; rw [sameMonomial b m q hq]
  rw [changeOrder]; exact sumCount _ _ _

theorem wedgeSuffixExpansion
    (b : Fin 7 → R) (w : Wedge7) :
    amplitude (suffix b) w=sumOver fullGaps (fun m => Nat.cast (forwardCost m w)*monomial b m) := by
  rw [suffixProduct,←sumPerm assignmentPerm,sumOverFlatMap,sumOverCongr _ (perGap b w)]

theorem evaluatedSuffix
    (x : Wedge7 → R) (b : Fin 7 → R) :
    evaluate x (amplitude (suffix b))=sumOver fullGaps (fun m => monomial b m*score x (forwardCost m)) := by
  unfold evaluate
  have expand (w : Wedge7) : amplitude (suffix b) w*x w=sumOver fullGaps (fun m => monomial b m*(Nat.cast (forwardCost m w)*x w)) := by
    rw [wedgeSuffixExpansion,sumOverMulRight]; apply sumOverCongr; intro m; grind
  rw [sumOverCongr _ expand,sumOverSwap]; apply sumOverCongr; intro m; exact (sumOverMulLeft _ _ _).symm

theorem spectralGainExpansion
    (x : Wedge7 → R) (b : Fin 7 → R) :
    gain x (amplitude (suffix b))=sumOver fullGaps (fun m => monomial b m*gain x (fun w => Nat.cast (forwardCost m w))) := by
  unfold gain; rw [evaluatedSuffix,evaluatedSuffix,←Compression.sumOverSub]
  apply sumOverCongr; intro m
  change monomial b m*score x (forwardCost m)-monomial b m*score referenceWeight (forwardCost m)=monomial b m*(score x (forwardCost m)-score referenceWeight (forwardCost m))
  grind


def forwardGap (t : Fin 7 → R) (i : Fin 7) : R :=
  if h : i.val+1<7 then t i-t ⟨i.val+1,h⟩ else t i

theorem suffixForwardGap (t : Fin 7 → R) (i : Fin 7) : suffix (forwardGap t) i=t i := by
  have e : ∀ i : Fin 7, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by decide
  have faces : List.finRange 7=([0,1,2,3,4,5,6] : List (Fin 7)) := by decide
  rcases e i with h|h|h|h|h|h|h <;> subst i <;>
    simp (config := { decide := true }) [suffix,faces,forwardGap,sumOver] <;> grind

def link (x : Wedge7 → R) (i j : Fin 7) : R := sumOver wedges fun w => if occupied w i && occupied w j then x w else 0

private theorem linkEval (x : Wedge7 → R) (i j : Fin 7) : evaluate x (fun w => Nat.cast (pairColumn i j w))=link x i j := by
  unfold evaluate link; apply sumOverCongr; intro w; unfold pairColumn
  dsimp only; cases occupied w i && occupied w j <;> simp <;> grind

theorem referenceLink (i j : Fin 7) (h : i≠j) : link (referenceWeight (R:=R)) i j=2 := by
  let keep (w : Wedge7) := (occupied w i && occupied w j) && SectorDefectAccounting.planeFlag w
  have cnt : ∀ i j : Fin 7, i≠j →
      wedges.countP (fun w => (occupied w i && occupied w j) && SectorDefectAccounting.planeFlag w)=2 := by decide
  have eq (w : Wedge7) : (if occupied w i && occupied w j then referenceWeight (R:=R) w else 0)=
      (if keep w then 1 else 0) := by
    unfold keep referenceWeight; cases occupied w i && occupied w j <;> cases SectorDefectAccounting.planeFlag w <;> rfl
  unfold link; rw [sumOverCongr _ eq,sumCount]
  change Nat.cast (wedges.countP (fun w => (occupied w i && occupied w j) && SectorDefectAccounting.planeFlag w))*(1:R)=2
  rw [cnt _ _ h]; grind

private theorem debitGains (x : Wedge7 → R) :
    gain x (fun w => Nat.cast (pairColumn 0 1 w))=link x 0 1-2 ∧
    gain x (fun w => Nat.cast (sharedColumn w))=link x 0 1+link x 0 2-4 := by
  have shared (x : Wedge7 → R) : evaluate x (fun w => Nat.cast (sharedColumn w))=link x 0 1+link x 0 2 := by
    rw [←linkEval,←linkEval]; unfold evaluate; rw [←sumOverAdd]; apply sumOverCongr; intro w
    dsimp only [sharedColumn]; rw [Semiring.natCast_add]; grind
  unfold gain; rw [linkEval,linkEval,referenceLink 0 1 (by decide),shared,shared,referenceLink 0 1 (by decide),referenceLink 0 2 (by decide)]
  constructor <;> grind

private theorem exteriorGainNormalized (mu : Fin 7 → R) (entries : Compression.HermitianEntries Wedge7 R) :
    SectorDefectAccounting.exteriorGain (amplitude mu) entries=
      gain (fun w => entries.realPart w w) (amplitude (suffix (forwardGap fun i => (mu i)^2))) := by
  rw [SectorDefectAccounting.gainDifference]; unfold gain SectorDefectAccounting.normOverlap Compression.diagonalLoss evaluate
  have a (w : Wedge7) : amplitude (suffix (forwardGap fun i => (mu i)^2)) w=(amplitude mu w)^2 := by
    unfold amplitude product4; simp only [suffixForwardGap]; grind
  have ref (w : Wedge7) : (SectorDefectAccounting.referenceEntries R).realPart w w=referenceWeight w := by
    simp only [SectorDefectAccounting.referenceEntries,referenceWeight,true_and]
  simp only [a,ref]

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem gapNonnegative (t : Fin 7 → R) (sorted : ∀ i j : Fin 7, i≤j → t j≤t i) (last : 0≤t 6) (i : Fin 7) :
    0≤forwardGap t i := by
  unfold forwardGap; split
  next hi =>
    have h := sorted i ⟨i.val+1,hi⟩ (show i.val≤i.val+1 by omega)
    grind
  next hi =>
    have e : i=6 := by apply Fin.ext; omega
    subst i; exact last

def physicalWeights (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (w : Wedge7) :=
  (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w

theorem physicalRows (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    (∀ w, 0≤physicalWeights half unit k A w) ∧ RowsHold (physicalWeights half unit k A) := by
  have effect := PhysicalCompressionEffect.rankSevenPhysicalEffect half unit k A orth
  refine ⟨fun w => (Compression.HermitianEntries.effectDiagonalBounds _ wedges wedgesNodup effect w (memWedges w)).1,?_⟩
  intro r legal; cases r with
  | directed i j =>
    have ne : i≠j := by intro e; subst j; simp [Row.legal] at legal
    have h := PhysicalDirectedCapacity.physicalDirectedCapacity half unit k A orth i j ne
    change _≤(Nat.cast 2:R)
    have two : (Nat.cast 2:R)=2 := by grind
    rw [two]; exact h
  | triple a b c =>
    have ord := _root_.of_decide_eq_true legal
    have h := PhysicalCutCapacities.physicalTripleCapacity half unit k A orth a b c ord.1 ord.2
    change _≤(Nat.cast 1:R)
    have one : (Nat.cast 1:R)=1 := by grind
    rw [one]; exact h
  | omitPair i j =>
    have h := PhysicalTwoHoleUpper.physicalOmittedPairCapacity half unit k A orth i j
      (_root_.of_decide_eq_true legal)
    change _≤(Nat.cast 1:R)
    have one : (Nat.cast 1:R)=1 := by grind
    rw [one]; exact h


/-- In dimension eight all 98 legal packing rows hold on the actual frame. -/
theorem physicalRowsEight (half : R) (unit : 2*half=1)
    (A : Basis 3 → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    (∀ w, 0≤physicalWeights half unit 0 A w) ∧ RowsHold (physicalWeights half unit 0 A) :=
  physicalRows half unit 0 A orth

theorem physicalSignedForwardDebit
    (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (mu : Fin 7 → R) (sorted : ∀ i j : Fin 7, i≤j → (mu j)^2≤(mu i)^2) :
    let b := forwardGap fun i => (mu i)^2
    let x := physicalWeights half unit k A
    SectorDefectAccounting.exteriorGain (amplitude mu) (PhysicalCompressionEffect.physicalEntries half unit k A)≤
      (b 0*b 2*b 6*(b 5+b 6))*(link x 0 1+link x 0 2-4)+
      ((b 6)^2*b 1*(b 0+b 1+b 2))*(link x 0 1-2) := by
  dsimp only
  let b := forwardGap fun i => (mu i)^2
  let x := physicalWeights half unit k A
  obtain ⟨pos,rows⟩ := physicalRows half unit k A orth
  have bn (i : Fin 7) : 0≤b i := gapNonnegative _ sorted (RankSeven.squareNonnegative _) i
  have pay := signedForwardDebit x pos rows b bn
  rw [←spectralGainExpansion x b] at pay
  rw [(debitGains x).1,(debitGains x).2] at pay
  rw [exteriorGainNormalized]; exact pay

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- Exact normalized physical exterior gain in all 210 sorted forward coefficients. -/
theorem physicalExteriorExpansion (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) :
    let x := physicalWeights half unit k A
    let b := forwardGap fun i => (mu i)^2
    SectorDefectAccounting.exteriorGain (amplitude mu) (PhysicalCompressionEffect.physicalEntries half unit k A)=
      sumOver fullGaps (fun m => monomial b m*gain x (fun w => Nat.cast (forwardCost m w))) := by
  rw [exteriorGainNormalized,spectralGainExpansion]; rfl

theorem physicalRestoredProbeSum (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (mu : Fin 7 → R) (sorted : ∀ i j : Fin 7, i≤j → (mu j)^2≤(mu i)^2)
    (z y : R) (z0 : 0≤z) (zHalf : 2*z≤1) (y0 : 0≤y) (yHalf : 2*y≤1) :
    let b := forwardGap fun i => (mu i)^2
    sumOver restoredGaps (fun m => monomial b m*gain (physicalWeights half unit k A) (probeCost m z y))≤0 := by
  obtain ⟨pos,rows⟩ := physicalRows half unit k A orth
  exact restoredProbeSum _ pos rows _ (gapNonnegative _ sorted (RankSeven.squareNonnegative _)) z y z0 zHalf y0 yHalf

end RankSeven.PackingPolynomial

#print axioms RankSeven.PackingPolynomial.wedgeSuffixExpansion
#print axioms RankSeven.PackingPolynomial.physicalExteriorExpansion
#print axioms RankSeven.PackingPolynomial.physicalRows
#print axioms RankSeven.PackingPolynomial.physicalRowsEight
#print axioms RankSeven.PackingPolynomial.physicalSignedForwardDebit
#print axioms RankSeven.PackingPolynomial.physicalRestoredProbeSum
