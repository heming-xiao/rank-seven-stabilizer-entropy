import Rank7WeightedProbeShift

/-! The ordered anticommuting Pauli mass on two physical spectrum slots. -/
namespace RankSeven.PauliReserveSlots
open Lean.Grind Pauli ComplexScalar SymmetricDefect
open PhysicalDefectAssembly (pairedState pairedDensity)
open PhysicalPairedReduction (dagger diagonal)
open FrameExteriorSector (framedWord)
open PhysicalCompressionEffect (OrthonormalFrame)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
abbrev labels := List.finRange 7

def coeff {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (t : Fin 7 → R) (p : Word n) :=
  (traceWord imaginaryUnit (pairedState A t) p).re

def neighborhood {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (t : Fin 7 → R) (p : Word n) :=
  sumOver (words n) (fun w => if anti p w then (coeff A t w)^2 else 0)

def reserve {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (parts other : Fin 7 → R) :=
  (half^n)^2*sumOver (words n) (fun p => (coeff A parts p)^2*neighborhood A other p)

def crossLoss (M : Fin 7 → Fin 7 → R) (a b : Fin 7 → R) :=
  sumOver labels (fun i => a i*b i)-sumOver labels (fun i => sumOver labels (fun j => a i*b j*M i j))

private theorem realSum {T : Type} (xs : List T) (f : T → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=_; rw [re_add,ih]; rfl

private theorem embedMul (a b : R) : ofReal (a*b)=ofReal a*ofReal b := by apply ComplexScalar.ext <;> simp <;> grind only

private theorem scRe (a : R) (b : ComplexScalar R) : (ofReal a*b).re=a*b.re := by
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

private theorem wordHerm {n : Nat} (p : Word n) :
    dagger (wordEntry (imaginaryUnit (R:=R)) p)=wordEntry imaginaryUnit p := by
  funext i j; exact ComplexPauliMoment.wordHermitian p j i

theorem framedHerm {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    dagger (framedWord A p)=framedWord A p := by
  change dagger (matMul _ (dagger A) (matMul _ (wordEntry imaginaryUnit p) A))=_
  rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerProduct,
    PhysicalPairedReduction.daggerInvolution,wordHerm,matMulAssoc]; rfl

theorem framedDegree {n : Nat} [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (p : Word n) (j : Fin 7) :
    sumOver labels (fun i => normSq (framedWord A p i j))≤1 := by
  let xs := qubitIndices n
  let z a := A a j
  let v := PauliPairContraction.image xs (wordEntry imaginaryUnit p) z
  have c := PhysicalCutCapacities.frameBessel labels xs (List.nodup_finRange 7) (fun i => List.mem_finRange i) A orth v
  have e := PauliPairContraction.wordIsometry p z
  have q := congrArg ComplexScalar.re (orth j j)
  simp only [ite_true,re_one,realSum,re_star_mul_self] at q
  change PauliPairContraction.normSum xs v=PauliPairContraction.normSum xs z at e
  change PauliPairContraction.normSum xs z=1 at q
  exact Std.le_trans c (Std.le_of_eq (e.trans q))

private theorem sourceSquare {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (t : Fin 7 → R) (p : Word n) :
    (traceWordSquare imaginaryUnit (pairedState A t) p).re =
      sumOver labels (fun i => sumOver labels (fun j => t i*t j*normSq (framedWord A p i j))) := by
  let xs := qubitIndices n
  let src := labels
  let W := wordEntry (imaginaryUnit (R:=R)) p
  let H := framedWord A p
  let T := diagonal t
  let B := matMul xs (matMul src T (dagger A)) W
  have amb : matMul xs (pairedState A t) W=matMul src A B := by
    unfold pairedState; rw [←RectangularPairedReduction.rankSevenCoefficients_eq]
    change matMul xs (matMul src (matMul src A T) (dagger A)) W=_
    unfold B; simp only [matMulAssoc]
  have loc : matMul xs B A=matMul src T H := by
    unfold B H framedWord; simp only [matMulAssoc]; rfl
  have cyc : trace xs (matMul xs (matMul src A B) (matMul src A B)) =
      trace src (matMul src (matMul xs B A) (matMul xs B A)) := by
    rw [matMulAssoc,traceMatMulSwap xs src A]; simp only [matMulAssoc]
  change (trace xs (matMul xs (matMul xs (pairedState A t) W) (matMul xs (pairedState A t) W))).re=_
  rw [amb,cyc,loc]
  change (sumOver src (fun i => sumOver src (fun j => matMul src T H i j*matMul src T H j i))).re=_
  simp only [realSum]
  apply sumOverCongr; intro i; apply sumOverCongr; intro j
  have h := congrFun (congrFun (framedHerm A p) i) j
  change star (H j i)=H i j at h
  have h' : H j i=star (H i j) := by rw [←h,star_star]
  change (matMul src (diagonal t) H i j*matMul src (diagonal t) H j i).re=_
  rw [PhysicalPairedReduction.diagonalAction src (List.nodup_finRange 7) t H i j (List.mem_finRange _),
    PhysicalPairedReduction.diagonalAction src (List.nodup_finRange 7) t H j i (List.mem_finRange _)]
  change (ofReal (t i)*H i j*(ofReal (t j)*H j i)).re=_
  rw [h']
  have prod : ofReal (t i)*H i j*(ofReal (t j)*star (H i j))=ofReal (t i*t j)* (star (H i j)*H i j) := by rw [embedMul]; grind only
  rw [prod,scRe,re_star_mul_self]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem coefficientReal {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (t : Fin 7 → R) (p : Word n) :
    ofReal (coeff A t p)=traceWord imaginaryUnit (pairedState A t) p := by
  let xs := qubitIndices n
  let C := pairedState A t
  let W := wordEntry (imaginaryUnit (R:=R)) p
  let H := matMul xs C W
  have e : star (trace xs H)=trace xs (dagger H) := ComplexExterior.starSumOver _ _
  unfold H at e
  rw [PhysicalPairedReduction.daggerProduct,wordHerm,PhysicalDefectAssembly.pairedStateHermitian,traceMatMulSwap xs xs W] at e
  change star (traceWord imaginaryUnit C p)=traceWord imaginaryUnit C p at e
  have im := congrArg ComplexScalar.im e
  rw [im_star] at im
  apply ComplexScalar.ext
  · rfl
  · change 0=(traceWord imaginaryUnit C p).im; grind only

/-- Twice the actual anticommuting-neighborhood weight equals the
dimension times the spectral commutator loss. -/
theorem neighborhoodFourier {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (t : Fin 7 → R) (p : Word n) :
    2*neighborhood A t p=(2:R)^n*crossLoss (fun i j => normSq (framedWord A p i j)) t t := by
  let xs := qubitIndices n
  let ws := words n
  let C := pairedState A t
  let f w := (traceWord imaginaryUnit C w)^2
  have parse := SymmetricDefect.pauliParseval imaginaryUnit imaginaryUnit_sq C
  have sign := SymmetricDefect.fourierTrace imaginaryUnit imaginaryUnit_sq C p
  have ex : 2*sumOver ws (fun w => if anti p w then f w else 0)=sumOver ws f-sumOver ws (fun w => chi p w*f w) := by
    rw [sumOverMulLeft,←Compression.sumOverSub]; apply sumOverCongr; intro w; cases h : anti p w <;> simp [h,chi,phase] <;> grind only
  change sumOver ws f=_ at parse
  change sumOver ws (fun w => chi p w*f w)=_ at sign
  rw [parse,sign,←PhysicalDefectAssembly.pairedState_mul A t t orth,AntiDefectTransport.pairedTraceEqSpectrum A _ orth] at ex
  have e := congrArg ComplexScalar.re ex
  change (ofReal (2:R)*_).re = ((ofReal (2:R))^n*ofReal (sumOver (List.finRange 7) (fun i => t i*t i))-
    (ofReal (2:R))^n*traceWordSquare imaginaryUnit C p).re at e
  rw [←PhysicalPairedReduction.realEmbeddingPow,re_sub,scRe,scRe,scRe,re_ofReal,sourceSquare,realSum] at e
  have re (w : Word n) : (if anti p w then f w else 0).re=(if anti p w then (coeff A t w)^2 else 0) := by
    cases anti p w <;> simp only [Bool.false_eq_true,ite_false,ite_true,re_zero]
    change ((traceWord imaginaryUnit (pairedState A t) w)^2).re=_
    rw [←coefficientReal,←PhysicalPairedReduction.realEmbeddingPow,re_ofReal]
  rw [sumOverCongr ws re] at e
  dsimp only [labels,ws] at e
  unfold crossLoss neighborhood labels; grind only


/-- Zero-based cut r is the one-particle spectral projection of rank r+1. -/
def cut (r i : Fin 7) : R := if i≤r then 1 else 0

def gap (t : Fin 7 → R) (r : Fin 7) : R :=
  match r.val with
  | 0 => t 0-t 1 | 1 => t 1-t 2 | 2 => t 2-t 3 | 3 => t 3-t 4
  | 4 => t 4-t 5 | 5 => t 5-t 6 | _ => t 6

private def combine (g : Fin 7 → R) (i : Fin 7) := sumOver labels (fun r => g r*cut r i)

private theorem casesSeven : ∀ i : Fin 7,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by decide

private theorem gapNonnegative (t : Fin 7 → R) (sorted : PauliMatchingPrices.SortedSpectrum t) (r : Fin 7) :
    0≤gap t r := by
  obtain ⟨s0,s1,s2,s3,s4,s5,s6⟩ := sorted
  rcases casesSeven r with q|q|q|q|q|q|q <;> subst r <;> dsimp [gap] <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem combineGap (t : Fin 7 → R) : combine (gap t)=t := by
  funext i
  have ls : labels=[0,1,2,3,4,5,6] := by decide
  rcases casesSeven i with q|q|q|q|q|q|q <;> subst i <;>
    simp +decide [combine,ls,cut,gap,sumOver] <;> grind only

private theorem sumLe {T : Type} (xs : List T) (f g : T → R) (h : ∀ i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have e := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at e; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem lossSwap (m : Fin 7 → Fin 7 → R) (symm : ∀ i j,m j i=m i j) (a b : Fin 7 → R) :
    crossLoss m a b=crossLoss m b a := by
  unfold crossLoss
  congr 1
  · apply sumOverCongr; intro i; grind only
  · rw [sumOverSwap]; apply sumOverCongr; intro i; apply sumOverCongr; intro j; rw [symm j i]; grind only

private theorem nestedLoss (m : Fin 7 → Fin 7 → R) (pos : ∀ i j,0≤m i j)
    (bound : ∀ i,sumOver labels (m i)≤1) (r s : Fin 7) (rs : r≤s) :
    0≤crossLoss m (cut r) (cut s) := by
  unfold crossLoss
  have e := sumLe labels (fun i => sumOver labels (fun j => cut (R:=R) r i*cut s j*m i j))
    (fun i => cut r i*cut s i) (fun i _ => by
      by_cases inside : i≤r
      · have large : i≤s := by omega
        simp only [cut,inside,large,ite_true,Semiring.one_mul]
        apply Std.le_trans _ (bound i)
        apply sumLe; intro j _; split <;> simp only [Semiring.one_mul,Semiring.zero_mul] <;> have := pos i j <;> grind only
      · simp only [cut,inside,ite_false,Semiring.zero_mul]; exact (Std.le_of_eq (by
          have zero (l : List (Fin 7)) : sumOver l (fun _ => (0:R))=0 := by
            induction l with
            | nil => rfl
            | cons j l ih => change 0+sumOver l _=0; rw [ih]; grind only
          exact zero _)))
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem lossCombine (m : Fin 7 → Fin 7 → R) (g b : Fin 7 → R) :
    crossLoss m (combine g) b=sumOver labels (fun r => g r*crossLoss m (cut r) b) := by
  unfold crossLoss combine
  have sub (x u v : R) : x*(u-v)=x*u-x*v := by grind only
  simp only [sub,Compression.sumOverSub,sumOverMulRight,sumOverMulLeft]
  congr 1
  · rw [sumOverSwap]; apply sumOverCongr; intro r; apply sumOverCongr; intro i; grind only
  · rw [sumOverSwap labels labels (fun r i => sumOver labels (fun j => g r*(cut r i*b j*m i j)))]
    apply sumOverCongr; intro i; rw [sumOverSwap]
    apply sumOverCongr; intro r; apply sumOverCongr; intro j; grind only

/-- The one-word commutator loss dominates the sum of squared gap losses.
Nested cuts also give nonnegative contributions on every off-diagonal pair. -/
theorem cutLossBound (m : Fin 7 → Fin 7 → R) (sym : ∀ i j,m j i=m i j) (pos : ∀ i j,0≤m i j)
    (deg : ∀ i,sumOver labels (m i)≤1) (t : Fin 7 → R) (sorted : PauliMatchingPrices.SortedSpectrum t) :
    sumOver labels (fun r => (gap t r)^2*crossLoss m (cut r) (cut r))≤crossLoss m t t := by
  let g := gap t
  let B r s := crossLoss m (cut r) (cut s)
  have b0 (r s : Fin 7) : 0≤B r s := by
    by_cases rs : r≤s
    · exact nestedLoss m pos deg r s rs
    · dsimp only [B]; rw [lossSwap m sym]; exact nestedLoss m pos deg s r (by omega)
  have norm : crossLoss m t t=sumOver labels (fun r => g r*sumOver labels (fun s => g s*B r s)) := by
    rw [←combineGap t,lossCombine]; apply sumOverCongr; intro r
    rw [lossSwap m sym,lossCombine]; apply congrArg (fun z => g r*z); apply sumOverCongr; intro s
    change g s*crossLoss m (cut s) (cut r)=g s*crossLoss m (cut r) (cut s); rw [lossSwap m sym]
  rw [norm]; apply sumLe; intro r hr
  have all : g r*B r r≤sumOver labels (fun s => g s*B r s) := by
    rw [←ExteriorPauliBase.sumOnIndex labels r (fun s => g s*B r s) (List.nodup_finRange 7) hr]
    apply sumLe; intro s _; split
    · exact Std.le_refl _
    · exact OrderedRing.mul_nonneg (gapNonnegative t sorted _) (b0 _ _)
  have e := OrderedRing.mul_le_mul_of_nonneg_left all (gapNonnegative t sorted r)
  change g r^2*B r r≤_; grind only


private theorem powerNonnegative (h : R) (hh : 0≤h) (n : Nat) : 0≤h^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hh

theorem neighborhoodCuts {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (t : Fin 7 → R) (sorted : PauliMatchingPrices.SortedSpectrum t) (p : Word n) :
    sumOver labels (fun r => (gap t r)^2*neighborhood A (cut r) p)≤neighborhood A t p := by
  let m i j := normSq (framedWord A p i j)
  have sy (i j : Fin 7) : m j i=m i j := by
    have h := congrFun (congrFun (framedHerm A p) i) j
    change star (framedWord A p j i)=framedWord A p i j at h
    change _=normSq (framedWord A p i j); rw [←h,normSq_star]
  have deg (i : Fin 7) : sumOver labels (m i)≤1 := by
    rw [sumOverCongr labels (g:=fun j => m j i) (fun j => sy j i)]; exact framedDegree A orth p i
  have c := cutLossBound m sy (fun _ _ => normSq_nonnegative _) deg t sorted
  let d := (2:R)^n
  have cd := OrderedRing.mul_le_mul_of_nonneg_left c (powerNonnegative 2 (by grind only) n)
  have row (r : Fin 7) : 2*neighborhood A (cut r) p=d*crossLoss m (cut r) (cut r) := neighborhoodFourier A orth (cut r) p
  have current : 2*neighborhood A t p=d*crossLoss m t t := neighborhoodFourier A orth t p
  have sum : 2*sumOver labels (fun r => (gap t r)^2*neighborhood A (cut r) p)=d*sumOver labels (fun r => (gap t r)^2*crossLoss m (cut r) (cut r)) := by
    rw [sumOverMulLeft,sumOverMulLeft]; apply sumOverCongr; intro r
    have q := congrArg (fun z => (gap t r)^2*z) (row r); grind only
  change d*_≤d*_ at cd; rw [←sum,←current] at cd; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem reserveSwap {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (u v : Fin 7 → R) :
    reserve half A u v=reserve half A v u := by
  unfold reserve neighborhood; apply congrArg (fun t => (half^n)^2*t)
  simp only [sumOverMulLeft]; rw [sumOverSwap]; apply sumOverCongr; intro p; apply sumOverCongr; intro q
  rw [PauliEdgeBlocks.antiSymm p q]; cases anti q p <;> simp <;> grind only

theorem oneSlotBound {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (t z : Fin 7 → R) (sorted : PauliMatchingPrices.SortedSpectrum t) :
    sumOver labels (fun r => (gap t r)^2*reserve half A z (cut r))≤reserve half A z t := by
  have each (p : Word n) := OrderedRing.mul_le_mul_of_nonneg_left (neighborhoodCuts A orth t sorted p)
    (squareNonnegative (coeff A z p))
  have b := sumLe (words n) _ _ (fun p _ => each p)
  let scale := (half^n)^2
  change sumOver (words n) (fun p => (coeff A z p)^2*sumOver labels (fun r => (gap t r)^2*neighborhood A (cut r) p))≤
    sumOver (words n) (fun p => (coeff A z p)^2*neighborhood A t p) at b
  have m := OrderedRing.mul_le_mul_of_nonneg_left b (squareNonnegative (half^n))
  change _≤scale*sumOver (words n) (fun p => (coeff A z p)^2*neighborhood A t p) at m
  apply Std.le_trans _ m
  apply Std.le_of_eq
  unfold reserve; change sumOver labels (fun r => (gap t r)^2*(scale*sumOver (words n) _))=scale*sumOver (words n) _
  simp only [sumOverMulLeft]
  rw [sumOverSwap]; apply sumOverCongr; intro p; apply sumOverCongr; intro r; grind only

/-- All 49 squared-gap ordered slot prices can be retained at once in
the physical anticommuting reserve. Cut indices are zero-based. -/
theorem allCutSlots {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (t : Fin 7 → R) (sorted : PauliMatchingPrices.SortedSpectrum t) :
    sumOver labels (fun r => sumOver labels (fun s => (gap t r)^2*(gap t s)^2*reserve half A (cut r) (cut s)))≤
      reserve half A t t := by
  apply Std.le_trans _ (oneSlotBound half A orth t t sorted)
  apply sumLe; intro r _
  rw [reserveSwap half A t (cut r)]
  have e := OrderedRing.mul_le_mul_of_nonneg_left (oneSlotBound half A orth t (cut r) sorted)
    (squareNonnegative (gap t r))
  apply Std.le_trans _ e
  apply Std.le_of_eq
  rw [sumOverMulLeft]; apply sumOverCongr; intro s; grind only

theorem reserveNonnegative {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (u v : Fin 7 → R) :
    0≤reserve half A u v := by
  apply OrderedRing.mul_nonneg (squareNonnegative _)
  apply Compression.sumOverNonnegative; intro p _
  apply OrderedRing.mul_nonneg (squareNonnegative _)
  apply Compression.sumOverNonnegative; intro q _; split
  · exact squareNonnegative _
  · exact Std.le_refl _

/-- The diagonal two-slot mass is exactly the term in the physical
defect decomposition, with the same dimension normalization. -/
theorem sameSlot {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (t : Fin 7 → R) :
    reserve half A t t=(half^n)^2*(PhysicalAntiQuartic.antiMass (traceWord imaginaryUnit (pairedState A t))).re := by
  unfold reserve PhysicalAntiQuartic.antiMass neighborhood
  apply congrArg (fun w => (half^n)^2*w)
  simp only [sumOverMulLeft,realSum]
  apply sumOverCongr; intro p; apply sumOverCongr; intro q
  cases anti p q <;> simp only [Bool.false_eq_true,ite_false,ite_true,Semiring.mul_zero,re_zero]
  rw [←coefficientReal,←coefficientReal,←PhysicalPairedReduction.realEmbeddingPow,←PhysicalPairedReduction.realEmbeddingPow,←embedMul,re_ofReal]

/-- The true physical defect pays both the matching receipt and the full
collection of anticommuting cut slots, without allocating a slot twice. -/
theorem physicalReceiptWithCutSlots (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : PauliMatchingPrices.SortedSpectrum (fun i => (mu i)^2))
    (s t : R) (s0 : 0≤s) (t0 : 0≤t) :
    let n := k+3
    let d := (2:R)^n
    let di := half^n
    let wt := fun i => (mu i)^2
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    let os := MixedDefect.oddWords n
    let slots := sumOver labels (fun r => sumOver labels (fun j =>
      (gap wt r)^2*(gap wt j)^2*reserve half A (cut r) (cut j)))
    d^2*SectorDefectAccounting.symmetricDefect di (PhysicalDefectAssembly.physicalSectorTerms half inv24 k A mu)+
      4*d*MixedDefect.curvature os anti K+2*slots+(WeightedProbeShift.physicalPayment half h2 k A mu).receipt s t≤
      PhysicalDefectAssembly.frameDefects half inv24 k A mu := by
  let wt := fun i => (mu i)^2
  have slots := allCutSlots half A orth wt sorted
  rw [sameSlot] at slots
  have e := WeightedProbeShift.physicalDefectReceipt half inv24 third h2 h24 h3 k A mu orth sorted s t s0 t0
  dsimp only at e ⊢; unfold pairedDensity at e
  dsimp only [wt] at slots
  grind only


end Order
end RankSeven.PauliReserveSlots

#print axioms RankSeven.PauliReserveSlots.neighborhoodFourier
#print axioms RankSeven.PauliReserveSlots.cutLossBound
#print axioms RankSeven.PauliReserveSlots.neighborhoodCuts
#print axioms RankSeven.PauliReserveSlots.reserveSwap
#print axioms RankSeven.PauliReserveSlots.oneSlotBound
#print axioms RankSeven.PauliReserveSlots.allCutSlots
#print axioms RankSeven.PauliReserveSlots.reserveNonnegative
#print axioms RankSeven.PauliReserveSlots.sameSlot
#print axioms RankSeven.PauliReserveSlots.physicalReceiptWithCutSlots
