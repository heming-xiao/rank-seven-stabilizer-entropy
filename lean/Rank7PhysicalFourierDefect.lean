import Rank7HeadPauliFourier

/-! The physical shared Gram is the sum of its ordinary diagonal Fourier
defect and the signed cross term on the true Pauli expectations. -/
namespace RankSeven.PhysicalFourierDefect
open Lean.Grind Pauli ComplexScalar SymmetricDefect HeadPauliFourier ThreeLegFourier
open PhysicalPairedReduction (dagger)
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
open JointProbeGram (oddAverage)
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def diagonalDefect {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :=
  half^n*sumOver (words n) (fun v => (middle (localH A v))^2*(1-(head (localH A v))^2))

def signedCross {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :=
  half^n*sumOver (words n) (fun v => head (localH A v)*middle (localH A v)*crossWeight (localH A v))

def outsideDefect {n : Nat} [LE R] [DecidableRel ((·≤·) : R→R→Prop)] (half : R)
    (A : Basis n → Fin 7 → ComplexScalar R) :=
  half^n*sumOver (words n) (fun v => if 2*(head (localH A v))^2≤1 then localDefect (localH A v) else 0)

private theorem unitEntry (n : Nat) (i j : Basis n) :
    wordEntry (imaginaryUnit (R:=R)) (unitWord n) i j=SlaterUnionBound.ident i j := by
  unfold SlaterUnionBound.ident
  induction n with
  | zero => cases i; cases j; simp [unitWord,wordEntry]; grind only
  | succ n ih =>
    obtain ⟨a,i⟩ := i; obtain ⟨b,j⟩ := j
    cases a <;> cases b <;> by_cases h : i=j <;> simp [unitWord,wordEntry,entry,ih,h] <;> grind only

theorem topThreeOrth {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    matMul (qubitIndices n) (dagger (firstThree A)) (firstThree A)=SlaterUnionBound.ident := by
  funext i j; change sumOver _ (fun x => star (A x (PhysicalOddLeakage.sublabel 2 i))*A x (PhysicalOddLeakage.sublabel 2 j))=_
  rw [orth]; unfold SlaterUnionBound.ident
  have eq : PhysicalOddLeakage.sublabel 2 i=PhysicalOddLeakage.sublabel 2 j ↔ i=j :=
    ⟨fun h => Fin.ext (congrArg (fun x : Fin 7 => x.val) h),fun e => e ▸ rfl⟩
  simp only [eq]

private theorem wordUnitCompressed {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    localH A (unitWord n)=SlaterUnionBound.ident := by
  let xs := qubitIndices n
  let F := firstThree A
  have eq : matMul xs (wordEntry (imaginaryUnit (R:=R)) (unitWord n)) F=F := by
    funext i j
    change sumOver xs (fun l => wordEntry imaginaryUnit (unitWord n) i l*F l j)=F i j
    rw [←ExteriorPauliBase.sumOnIndex xs i (fun l => F l j) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n i)]
    apply sumOverCongr; intro l; rw [unitEntry]; by_cases h : i=l <;> simp [SlaterUnionBound.ident,h] <;> grind only
  change matMul xs (dagger F) (matMul xs (wordEntry imaginaryUnit (unitWord n)) F)=_
  rw [eq]; exact topThreeOrth A orth

private theorem chiId {n : Nat} (p : Word n) : (chi (unitWord n) p:R)=1 := by
  induction p with
  | empty => rfl
  | cons a p ih => rw [unitWord,chiCons,ih]; simp [axisAnti,phase]; grind only

private theorem chiZero {n : Nat} (f : Word n→R) : fourier f (unitWord n)=sumOver (words n) f := by
  unfold fourier; simp only [chiId,Semiring.one_mul]

private theorem symmetricFourier {n : Nat} (f g : Word n → R) :
    sumOver (words n) (fun a => f a*fourier g a)=sumOver (words n) (fun b => g b*fourier f b) := by
  unfold fourier; simp only [sumOverMulLeft]; rw [sumOverSwap]; apply sumOverCongr; intro b; apply sumOverCongr; intro a
  rw [chiSymm a b]; grind only

private theorem powerSquare (n : Nat) : (4:R)^n=((2:R)^n)^2 := by
  induction n with
  | zero => simp [Semiring.pow_zero]; grind only
  | succ n ih => simp only [Semiring.pow_succ,ih]; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem totalMoments {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    sumOver (words n) (fun v => (head (localH A v))^2)=(2:R)^n ∧
    sumOver (words n) (fun v => (middle (localH A v))^2)=2*(2:R)^n := by
  have o := (ordinaryTransforms (firstThree A) (unitWord n)).2
  change fourier (fun v => (head (localH A v))^2) (unitWord n)=(2:R)^n*(head (localH A (unitWord n)))^2 ∧
    fourier (fun v => (middle (localH A v))^2) (unitWord n)=(2:R)^n*(2-middleLoss (localH A (unitWord n))) at o
  rw [wordUnitCompressed A orth,chiZero,chiZero] at o
  simp (config:={decide:=true}) only [head,middleLoss,SlaterUnionBound.ident,ite_true,ite_false,re_one,normSq_zero,normSq_one] at o
  unfold head; grind only

theorem fourthBalance {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R) :
    let H := localH A
    sumOver (words n) (fun v => (head (H v))^2*(2-middleLoss (H v)))=
      sumOver (words n) (fun v => (head (H v))^2*(middle (H v))^2) := by
  let H := localH A
  let r v := (head (H v))^2
  let u v := (middle (H v))^2
  let d := (2:R)^n
  let di := half^n
  have t (v : Word n) := (ordinaryTransforms (firstThree A) v).2
  change ∀v,fourier r v=d*r v ∧ fourier u v=d*(2-middleLoss (H v)) at t
  have e := symmetricFourier r u
  have a (v : Word n) : r v*fourier u v=d*(r v*(2-middleLoss (H v))) := by rw [(t v).2]; grind only
  have b (v : Word n) : u v*fourier r v=d*(r v*u v) := by rw [(t v).1]; grind only
  rw [sumOverCongr _ a,sumOverCongr _ b,←sumOverMulLeft,←sumOverMulLeft] at e
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have q := congrArg (fun z => di*z) e
  change sumOver _ (fun v => r v*(2-middleLoss (H v)))=sumOver _ (fun v => r v*u v)
  grind only

theorem localDefectSum {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    half^n*sumOver (words n) (fun v => localDefect (localH A v))=2*diagonalDefect half A := by
  let H := localH A
  let ws := words n
  let r v := (head (H v))^2
  let u v := (middle (H v))^2
  let d := (2:R)^n
  have total := totalMoments A orth
  change sumOver ws r=d ∧ sumOver ws u=2*d at total
  have fourth := fourthBalance half h2 A
  change sumOver ws (fun v => r v*(2-middleLoss (H v)))=sumOver ws (fun v => r v*u v) at fourth
  have sub (v : Word n) : r v*(2-middleLoss (H v))=2*r v-r v*middleLoss (H v) := by grind only
  rw [sumOverCongr _ sub,Compression.sumOverSub,←sumOverMulLeft,total.1] at fourth
  have ds (v : Word n) : u v*(1-r v)=u v-r v*u v := by grind only
  change half^n*sumOver ws (fun v => u v*(1-r v)+r v*middleLoss (H v))=2*(half^n*sumOver ws (fun v => u v*(1-r v)))
  rw [sumOverAdd,sumOverCongr _ ds,Compression.sumOverSub,total.2]; grind only
theorem oddSquares {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R) :
    let H := localH A
    let F v := head (H v)*middle (H v)
    2*sumOver (MixedDefect.oddWords n) (fun p => (SixPointRounding.headWeight A p)^2)=
      sumOver (words n) (fun v => (F v)^2)-sumOver (words n) (fun v => F v*crossWeight (H v)) := by
  let H := localH A
  let F v := head (H v)*middle (H v)
  let P := SixPointRounding.headWeight A
  let b v := crossWeight (H v)
  let d := (2:R)^n
  let ws := words n
  let odd := MixedDefect.oddWords n
  have p (v : Word n) : fourier (fun i => wordSign i*F i) v=d*P v := twistedHead A v
  have q (v : Word n) : fourier F v=d*b v := (ordinaryTransforms (firstThree A) v).1
  have s := oddTwistedParseval F
  simp only [p,q,powerSquare] at s
  have pt (v : Word n) : (d*P v)^2=d^2*(P v)^2 := by grind only
  have qt (v : Word n) : F v*(d*b v)=d*(F v*b v) := by grind only
  rw [sumOverCongr _ pt,sumOverCongr _ qt,←sumOverMulLeft,←sumOverMulLeft] at s
  have inv : d*half^n=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have e := congrArg (fun z => (half^n)^2*z) s
  change 2*sumOver odd (fun v => (P v)^2)=sumOver ws (fun v => (F v)^2)-sumOver ws (fun v => F v*b v)
  grind only

/-- The shared Gram κ equals the physical diagonal Fourier defect plus
the signed head/middle cross term, on every orthonormal frame. -/
theorem physicalFourierIdentity (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    (physicalPayment half h2 k A mu).kappa=diagonalDefect half A+signedCross half A := by
  let n := k+3
  let H := localH A
  let r v := head (H v)
  let u v := middle (H v)
  let b v := crossWeight (H v)
  let F v := r v*u v
  let P := SixPointRounding.headWeight A
  let odd := MixedDefect.oddWords n
  let ws := words n
  let di := half^n
  let d := (2:R)^n
  have pq := JointProbeGram.pairWeightAverage half h2 A orth 0 1 (by decide)
  have pr := JointProbeGram.pairWeightAverage half h2 A orth 0 2 (by decide)
  have total : 2*di*sumOver odd P=2 := by
    change 2*di*sumOver odd (fun p => JointProbePayment.pairWeight A p 0 1+JointProbePayment.pairWeight A p 0 2)=2
    rw [sumOverAdd]
    change 2*di*sumOver odd (fun p => JointProbePayment.pairWeight A p 0 1)=1 at pq
    change 2*di*sumOver odd (fun p => JointProbePayment.pairWeight A p 0 2)=1 at pr
    grind only
  have squares := oddSquares half h2 A
  change 2*sumOver odd (fun p => (P p)^2)=sumOver ws (fun v => (F v)^2)-sumOver ws (fun v => F v*b v) at squares
  have us := (totalMoments A orth).2
  change sumOver ws (fun v => (u v)^2)=2*d at us
  have sub (v : Word n) : (u v)^2*(1-(r v)^2)=(u v)^2-(F v)^2 := by unfold F; grind only
  have pp (v : Word n) : P v*(1-P v)=P v-(P v)^2 := by grind only
  change 2*di*sumOver odd (fun p => P p*(1-P p))=di*sumOver ws (fun v => (u v)^2*(1-(r v)^2))+di*sumOver ws (fun v => F v*b v)
  rw [sumOverCongr _ pp,sumOverCongr _ sub,Compression.sumOverSub,Compression.sumOverSub,us]
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have e := congrArg (fun z => di*z) squares; grind only

private theorem sumLe (xs : List α) (f g : α → R) (h : ∀ i,f i≤g i) : sumOver xs f≤sumOver xs g := by
  have s := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i _ => by have := h i; grind only)
  rw [Compression.sumOverSub] at s; grind only

private theorem halfNonnegative (half : R) (h2 : 2*half=1) (n : Nat) : 0≤half^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)

variable [DecidableRel ((·≤·) : R→R→Prop)]

def outsideMass {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) :=
  half^n*sumOver (words n) (fun v => if 2*(head (localH A v))^2≤1 then (middle (localH A v))^2 else 0)

/-- The full Fourier gap is bounded by 5κ. Keeping the off-group
improvement gives 30κ≥6D+the normalized off-group local residual. -/
theorem physicalFourierBounds (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let K := (physicalPayment half h2 k A mu).kappa
    let D := diagonalDefect half A
    0≤D ∧ D≤5*K ∧ 6*D+outsideDefect half A≤30*K := by
  let n := k+3
  let H := localH A
  let K := (physicalPayment half h2 k A mu).kappa
  let D := diagonalDefect half A
  let C := signedCross half A
  let O := outsideDefect half A
  let di := half^n
  let w v := localDefect (H v)
  let t v := head (H v)*middle (H v)*crossWeight (H v)
  let sel v := 2*(head (H v))^2≤1
  let ws := words n
  have points (v : Word n) := physicalLocalPrices (firstThree A) (topThreeOrth A orth) v
  change ∀ v,0≤w v ∧ -4*w v≤10*t v ∧ (sel v → -11*w v≤30*t v) at points
  have raw (v : Word n) : -12*w v+(if sel v then w v else 0)≤30*t v := by
    have h := points v; by_cases p : sel v
    · rw [ite_eq_left p]; have q := h.2.2 p; grind only
    · rw [ite_eq_right p]; grind only
  have s := sumLe ws _ _ raw
  rw [sumOverAdd,←sumOverMulLeft,←sumOverMulLeft] at s
  have s0 := sumLe ws _ _ (fun i => (points i).2.1)
  rw [←sumOverMulLeft,←sumOverMulLeft] at s0
  have dn : 0≤di := halfNonnegative half h2 n
  have z := OrderedRing.mul_le_mul_of_nonneg_left s dn
  have z0 := OrderedRing.mul_le_mul_of_nonneg_left s0 dn
  have id : K=D+C := physicalFourierIdentity half h2 k A mu orth
  have comb : di*sumOver ws w=2*D := localDefectSum half h2 A orth
  have nn := OrderedRing.mul_nonneg dn (Compression.sumOverNonnegative ws w (fun i _ => (points i).1))
  change 0≤D ∧ D≤5*K ∧ 6*D+O≤30*K
  have oe : O=di*sumOver ws (fun v => if sel v then w v else 0) := rfl
  have ce : C=di*sumOver ws t := rfl
  grind only

omit [DecidableRel ((·≤·) : R→R→Prop)] in
private theorem lossPos {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (p : Word n) :
    0≤1-(head (localH A p))^2 ∧ 0≤middleLoss (localH A p) := by
  let H := localH A p
  have orth3 := topThreeOrth A orth
  have gn := PhysicalOddLeakage.compressionComplement (firstThree A) p orth3
  have c (i : Fin 3) := ThreeLegFourier.columnContraction H gn i
  have L : List.finRange 3=[0,1,2] := by decide
  have c0 := c 0; have c1 := c 1; have c2 := c 2
  simp only [L,sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons] at c0 c1 c2
  have n (i j : Fin 3) : 0≤normSq (H i j) := normSq_nonnegative _
  have := n 0 1; have := n 0 2; have := n 1 0; have := n 2 0
  have sq : (head H)^2≤normSq (H 0 0) := by unfold head normSq; have := squareNonnegative (H 0 0).im; grind only
  change 0≤1-(head H)^2 ∧ 0≤2-(normSq (H 1 1)+normSq (H 1 2)+normSq (H 2 1)+normSq (H 2 2))
  grind only

/-- Outside any maximal commuting extension of the large single-column
expectations, all Pauli labels have weak expectation. The entire weak
set already has middle square mass at most 60κ/7. -/
theorem weakMassLocalization (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) :
    let D := diagonalDefect half A
    let mass := outsideMass half A
    mass≤2*D ∧ mass≤2*outsideDefect half A ∧ 7*mass≤60*(physicalPayment half h2 k A mu).kappa := by
  let n := k+3
  let H := localH A
  let D := diagonalDefect half A
  let O := outsideDefect half A
  let M := outsideMass half A
  let K := (physicalPayment half h2 k A mu).kappa
  let w v := (middle (H v))^2*(1-(head (H v))^2)
  let u v := (middle (H v))^2
  let f v := 2*(head (H v))^2≤1
  let ws := words n
  let di := half^n
  have e (v : Word n) : 0≤w v ∧ w v≤localDefect (H v) ∧ (f v → u v≤2*w v) := by
    have r := lossPos A orth v
    have a := squareNonnegative (middle (H v)); have b := squareNonnegative (head (H v))
    have pos := OrderedRing.mul_nonneg a r.1
    have ext := OrderedRing.mul_nonneg b r.2
    change 0≤w v ∧ w v≤w v+(head (H v))^2*middleLoss (H v) ∧ _
    refine ⟨pos,by grind only,?_⟩
    intro z; change 2*(head (H v))^2≤1 at z
    have t := OrderedRing.mul_nonneg a (show 0≤1-2*(head (H v))^2 by grind only)
    dsimp only [u,w]; grind only
  have a := sumLe ws (fun v => if f v then u v else 0) (fun v => 2*w v) (fun v => by
    have h := e v; split <;> grind only)
  have b := sumLe ws (fun v => if f v then u v else 0) (fun v => 2*(if f v then localDefect (H v) else 0)) (fun v => by
    have h := e v; by_cases p : f v <;> simp only [p,ite_true,ite_false] <;> grind only)
  rw [←sumOverMulLeft] at a b
  have pos : 0≤di := halfNonnegative half h2 n
  have a' := OrderedRing.mul_le_mul_of_nonneg_left a pos
  have b' := OrderedRing.mul_le_mul_of_nonneg_left b pos
  have bounds := (physicalFourierBounds half h2 k A mu orth).2.2
  change 6*D+O≤30*K at bounds
  have me : M=di*sumOver ws (fun v => if f v then u v else 0) := rfl
  have de : D=di*sumOver ws w := rfl
  have oe : O=di*sumOver ws (fun v => if f v then localDefect (H v) else 0) := rfl
  change M≤2*D ∧ M≤2*O ∧ 7*M≤60*K; grind only

omit [DecidableRel ((·≤·) : R→R→Prop)] in
theorem heavyCommute {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (p q : Word n)
    (hp : 1<2*(head (localH A p))^2) (hq : 1<2*(head (localH A q))^2) : anti p q=false := by
  have eq (a : Word n) : OddCutReserve.cutLeak A 0 a=1-(head (localH A a))^2 := by
    rw [←PhysicalOddLeakage.traceLossEqCut]
    let F := PhysicalOddLeakage.restrictFrame A 0
    let H := PhysicalOddLeakage.compression F a
    have L : List.finRange 1=[0] := by decide
    change (trace (List.finRange 1) (fun i j => SlaterUnionBound.ident i j-matMul (List.finRange 1) (dagger H) H i j)).re=_
    simp only [trace,matMul,L,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,SlaterUnionBound.ident,ite_true,Semiring.add_zero,
      re_sub,re_one,dagger]
    have real := congrArg ComplexScalar.im (congrFun (congrFun (PhysicalOddLeakage.compressionHerm F a) 0) 0)
    change (star (H 0 0)).im=(H 0 0).im at real; rw [im_star] at real
    have zero : (H 0 0).im=0 := by grind only
    change 1-(star (H 0 0)*H 0 0).re=1-(H 0 0).re^2
    rw [re_star_mul_self]; unfold normSq
    rw [zero]; grind only
  cases h : anti p q with
  | false => rfl
  | true =>
    have l := OddCutReserve.firstPairLeakage A orth p q h
    rw [eq,eq] at l; grind only

end Order

end RankSeven.PhysicalFourierDefect

#print axioms RankSeven.PhysicalFourierDefect.topThreeOrth
#print axioms RankSeven.PhysicalFourierDefect.totalMoments
#print axioms RankSeven.PhysicalFourierDefect.fourthBalance
#print axioms RankSeven.PhysicalFourierDefect.localDefectSum
#print axioms RankSeven.PhysicalFourierDefect.oddSquares
#print axioms RankSeven.PhysicalFourierDefect.physicalFourierIdentity
#print axioms RankSeven.PhysicalFourierDefect.physicalFourierBounds
#print axioms RankSeven.PhysicalFourierDefect.weakMassLocalization
#print axioms RankSeven.PhysicalFourierDefect.heavyCommute

