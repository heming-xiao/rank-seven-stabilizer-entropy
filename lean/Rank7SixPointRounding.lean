import Rank7SixModeProbe
import Rank7PhysicalDirectedCapacity

/-! Six-point rounding of the shared Pauli weight. The hypotheses on the
rounded character sector are explicit. -/
namespace RankSeven.SixPointRounding
open Lean.Grind Pauli ComplexScalar JointProbeGram JointProbePayment WeightedProbeShift
open MixedDefect (oddWords)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

private theorem sumLe {α : Type} (xs : List α) (f g : α → R) (h : ∀ a∈xs,f a≤g a) :
    sumOver xs f≤sumOver xs g := by
  have e := Compression.sumOverNonnegative xs (fun a => g a-f a) (fun a ha => by have := h a ha; grind only)
  rw [Compression.sumOverSub] at e; grind only

private theorem squareSum {α : Type} (xs : List α) (f : α → R) (h : ∀ a∈xs,0≤f a) :
    sumOver xs (fun a => (f a)^2)≤(sumOver xs f)^2 := by
  induction xs with
  | nil => change (0:R)≤0^2; grind only
  | cons a xs ih =>
    have nn y hy := h y (List.mem_cons_of_mem a hy)
    have s := Compression.sumOverNonnegative xs f nn
    have m := OrderedRing.mul_nonneg (h a List.mem_cons_self) s
    have r := ih nn
    change (f a)^2+sumOver xs _≤(f a+sumOver xs f)^2; grind only

private theorem singleOut {α : Type} (xs : List α) (f : α → R) (nn : ∀ a∈xs,0≤f a)
    (x : α) (hx : x∈xs) :
    0≤sumOver xs f-f x ∧ sumOver xs (fun a => (f a)^2)≤(f x)^2+(sumOver xs f-f x)^2 := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    have non y hy := nn y (List.mem_cons_of_mem a hy)
    change 0≤f a+sumOver xs f-f x ∧ (f a)^2+sumOver xs _≤(f x)^2+(f a+sumOver xs f-f x)^2
    cases List.mem_cons.mp hx with
    | inl r =>
      subst x; have p := Compression.sumOverNonnegative xs f non
      have q := squareSum xs f non; grind only
    | inr r =>
      have v := ih non r
      have m := OrderedRing.mul_nonneg (nn a List.mem_cons_self) v.1
      have n := nn a List.mem_cons_self; grind only

/-- Squared masses of paired rank-two character spaces have total at most
twenty when a six-dimensional projection is distributed among them. -/
theorem sixMassSquares {α : Type} (xs : List α) (h : α → R) (bounds : ∀ a∈xs,0≤h a ∧ h a≤4)
    (total : sumOver xs h≤6) : sumOver xs (fun a => (h a)^2)≤20 := by
  classical
  by_cases small : ∀ a∈xs,h a≤3
  · have e := sumLe xs (fun a => (h a)^2) (fun a => 3*h a) (fun a ha => by
      have m := OrderedRing.mul_le_mul_of_nonneg_right (small a ha) (bounds a ha).1; grind only)
    rw [←sumOverMulLeft] at e; grind only
  · have ex : ∃ a∈xs,3≤h a := by
      apply Classical.byContradiction; intro no; apply small; intro a ha
      have h' : ¬3≤h a := fun r => no ⟨a,ha,r⟩; grind only
    obtain ⟨a,ha,lo⟩ := ex
    have r := singleOut xs h (fun y hy => (bounds y hy).1) a ha
    have s := OrderedRing.mul_nonneg (show 0≤6-sumOver xs h by grind only)
      (show 0≤6-h a+(sumOver xs h-h a) by have := (bounds a ha).2; grind only)
    have b := OrderedRing.mul_nonneg (show 0≤4-h a by have := (bounds a ha).2; grind only) (show 0≤h a-2 by grind only)
    grind only

/-- Paired character spaces carry at most five units of the six-leg
exterior trace. Each cross-block contribution is bounded by its two
trace masses' product. -/
theorem sectorFive {α : Type} (xs : List α) (a b tr : α → R)
    (bounds : ∀ j∈xs,0≤a j+b j ∧ a j+b j≤4)
    (total : sumOver xs (fun j => a j+b j)≤6)
    (crossBlock : ∀ j∈xs,tr j≤a j*b j) : sumOver xs tr≤5 := by
  have e := sixMassSquares xs (fun j => a j+b j) bounds total
  have s := sumLe xs (fun j => 4*tr j) (fun j => (a j+b j)^2) (fun j hj => by
    have sq : 0≤(a j-b j)^2 := squareNonnegative _
    have w := crossBlock j hj; grind only)
  rw [←sumOverMulLeft] at s; grind only

def headWeight {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :=
  pairWeight A p 0 1+pairWeight A p 0 2

theorem headWeightLeSix {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) :
    headWeight A p≤sixVertexMass A p := by
  let es := SectorDefectAccounting.wedgePairs ((List.finRange 7).filter (fun i => i.val<6))
  have pairs : es=(0,1)::(0,2)::(es.drop 2) := by decide
  have pos := Compression.sumOverNonnegative (es.drop 2) (fun e => pairWeight A p e.1 e.2)
    (fun e _ => normSq_nonnegative _)
  change pairWeight A p 0 1+pairWeight A p 0 2≤sumOver es _
  conv => rhs; rw [pairs]
  change _≤pairWeight A p 0 1+(pairWeight A p 0 2+sumOver (es.drop 2) (fun e => pairWeight A p e.1 e.2)); grind only

private theorem avgLe (half : R) (h2 : 2*half=1) {n : Nat} (f g : Word n → R)
    (point : ∀ p∈oddWords n,f p≤g p) : oddAverage half f≤oddAverage half g := by
  have pos (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  exact OrderedRing.mul_le_mul_of_nonneg_left (sumLe _ _ _ point) (show 0≤2*half^n by have := pos n; grind only)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgAdd (half : R) {n : Nat} (f g : Word n → R) :
    oddAverage half (fun p => f p+g p)=oddAverage half f+oddAverage half g := by
  unfold oddAverage; rw [sumOverAdd]; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgSub (half : R) {n : Nat} (f g : Word n → R) :
    oddAverage half (fun p => f p-g p)=oddAverage half f-oddAverage half g := by
  unfold oddAverage; rw [Compression.sumOverSub]; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgScale (half c : R) {n : Nat} (f : Word n → R) :
    oddAverage half (fun p => c*f p)=c*oddAverage half f := by
  unfold oddAverage; rw [←sumOverMulLeft]; grind only

/-- All inputs from character-space rounding. The indicator has normalized
mass two, the sector six-mode trace has mass at most five, and the shared
head weight is polarized within a common error on the two parts. -/
structure RoundedSector (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (delta : R) where
  member : Word n → Bool
  mass : oddAverage half (fun p => if member p then (1:R) else 0)=2
  trace : oddAverage half (fun p => if member p then sixVertexMass A p else 0)≤5
  inner : ∀ p∈oddWords n, member p=true → 1-delta≤headWeight A p
  outer : ∀ p∈oddWords n, member p=false → headWeight A p≤delta

/-- The leakage on the two sides of a rounded sector agrees exactly.
Its mass bounds both the six-mode excess and the shared Gram. -/
theorem physicalLeakage (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) (delta : R)
    (C : RoundedSector half A delta) :
    let M := physicalPayment half h2 k A mu
    let leak := oddAverage half (fun p => if C.member p then 0 else headWeight A p)
    oddAverage half (fun p => if C.member p then 1-headWeight A p else 0)=leak ∧
    0≤leak ∧ 2*(1-delta)*leak≤M.kappa ∧ M.sixMass≤5+(2+delta)*leak := by
  let P := headWeight A
  let S := sixVertexMass A
  let ind (p : Word (k+3)) : R := if C.member p then 1 else 0
  let cap (p : Word (k+3)) := if C.member p then S p else 0
  let lin (p : Word (k+3)) := if C.member p then 1-P p else 0
  let out (p : Word (k+3)) := if C.member p then 0 else P p
  have wt : oddAverage half P=2 := by
    have e1 := pairWeightAverage half h2 A orth 0 1 (by decide)
    have e2 := pairWeightAverage half h2 A orth 0 2 (by decide)
    unfold P headWeight; rw [avgAdd,e1,e2]; grind only
  have mass : oddAverage half ind=2 := C.mass
  have trace : oddAverage half cap≤5 := C.trace
  have decomp : P=fun p => ind p-lin p+out p := by
    funext p; cases eq : C.member p <;> simp [ind,lin,out,eq] <;> grind only
  have eq : oddAverage half lin=oddAverage half out := by
    conv at wt => lhs; rw [decomp,avgAdd,avgSub]
    grind only
  have pp (p : Word (k+3)) : 0≤P p := by
    have n1 : 0≤pairWeight A p 0 1 := normSq_nonnegative _
    have n2 : 0≤pairWeight A p 0 2 := normSq_nonnegative _
    dsimp only [P,headWeight]; grind only
  have ub (p : Word (k+3)) (hp : p∈oddWords (k+3)) : P p≤1 := by
    have t := leadingTriangle A orth p hp
    have n : 0≤pairWeight A p 1 2 := normSq_nonnegative _
    dsimp only [P,headWeight]; grind only
  have non := avgLe half h2 (fun _ => 0) out (fun p _ => by
    cases e : C.member p <;> simp only [out,e,Bool.false_eq_true,ite_false,ite_true]; exact pp p; exact Std.le_refl _)
  have zero : oddAverage half (fun _ : Word (k+3) => 0)=0 := by
    simpa only [Semiring.zero_mul] using avgScale half (0:R) P
  rw [zero] at non
  have gram := avgLe half h2 (fun p => (1-delta)*(lin p+out p)) (fun p => P p*(1-P p)) (fun p hp => by
    have l := pp p; have u := ub p hp
    cases e : C.member p with
    | false =>
      have o : P p≤delta := C.outer p hp e
      have m := OrderedRing.mul_nonneg l (show 0≤delta-P p by grind only)
      simp only [lin,out,e,Bool.false_eq_true,ite_false]; grind only
    | true =>
      have i : 1-delta≤P p := C.inner p hp e
      have m := OrderedRing.mul_nonneg (show 0≤P p-(1-delta) by grind only) (show 0≤1-P p by grind only)
      simp only [lin,out,e,ite_true]; grind only)
  rw [avgScale,avgAdd,eq] at gram
  have bound := avgLe half h2 (fun p => P p*S p) (fun p => cap p-(1-delta)*lin p+3*out p) (fun p hp => by
    cases e : C.member p with
    | false =>
      have u : S p≤3 := sixMassLeThree A orth p hp
      have m := OrderedRing.mul_le_mul_of_nonneg_left u (pp p)
      simp only [cap,lin,out,e,Bool.false_eq_true,ite_false]; grind only
    | true =>
      have i : 1-delta≤P p := C.inner p hp e
      have u := ub p hp
      have s : P p≤S p := headWeightLeSix A p
      have m := OrderedRing.mul_nonneg (show 0≤S p-(1-delta) by grind only) (show 0≤1-P p by grind only)
      simp only [cap,lin,out,e,ite_true]; grind only)
  rw [avgAdd,avgSub,avgScale,avgScale,eq] at bound
  change oddAverage half lin=oddAverage half out ∧ 0≤oddAverage half out ∧
    2*(1-delta)*oddAverage half out≤oddAverage half (fun p => P p*(1-P p)) ∧
    oddAverage half (fun p => P p*S p)≤5+(2+delta)*oddAverage half out
  exact ⟨eq,non,by grind only,by grind only⟩

/-- A rounded sector bounds the weighted six-mode price, with its sharp
affine dependence on the common polarization error. -/
theorem sectorSixPrice (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) (delta : R)
    (C : RoundedSector half A delta) (lo : 0≤delta) (hi : delta≤1) :
    let M := physicalPayment half h2 k A mu
    2*(1-delta)*(M.sixMass-5)≤(2+delta)*M.kappa := by
  let M := physicalPayment half h2 k A mu
  have r := physicalLeakage half h2 k A mu orth delta C
  dsimp only at r
  have a := OrderedRing.mul_le_mul_of_nonneg_left r.2.2.1 (show 0≤2+delta by grind only)
  have b := OrderedRing.mul_le_mul_of_nonneg_left r.2.2.2 (show 0≤2*(1-delta) by grind only)
  grind only

theorem roundedSixPrices (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) (delta : R) (C : RoundedSector half A delta) :
    let M := physicalPayment half h2 k A mu
    (10*delta≤3 → 14*M.sixMass≤70+23*M.kappa) ∧ (25*delta≤9 → 32*M.sixMass≤160+59*M.kappa) := by
  let M := physicalPayment half h2 k A mu
  let l := oddAverage half (fun p => if C.member p then 0 else headWeight A p)
  have r := physicalLeakage half h2 k A mu orth delta C
  change _ ∧ 0≤l ∧ 2*(1-delta)*l≤M.kappa ∧ M.sixMass≤5+(2+delta)*l at r
  change (10*delta≤3 → 14*M.sixMass≤70+23*M.kappa) ∧ (25*delta≤9 → 32*M.sixMass≤160+59*M.kappa)
  constructor
  · intro h; have m := OrderedRing.mul_nonneg (show 0≤3-10*delta by grind only) r.2.1; grind only
  · intro h; have m := OrderedRing.mul_nonneg (show 0≤9-25*delta by grind only) r.2.1; grind only

/-- The global coefficient 200/11 needs only a small-Gram rounded-sector
witness. All averaging and the complementary branch use the actual frame. -/
theorem uniformSixPrice (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (small : 200*(physicalPayment half h2 k A mu).kappa<11 → ∃ delta, Nonempty (RoundedSector half A delta) ∧ 25*delta≤9) :
    let M := physicalPayment half h2 k A mu
    11*M.sixMass≤55+200*M.kappa := by
  let M := physicalPayment half h2 k A mu
  by_cases hi : 11≤200*M.kappa
  · exact SixModeProbe.largeKappaSix half h2 k A mu orth hi
  have lo : 200*M.kappa<11 := by grind only
  obtain ⟨delta,⟨C⟩,d⟩ := small lo
  have s := (roundedSixPrices half h2 k A mu orth delta C).2 d
  have g := (physicalJointGram half third h2 h3 k A orth).1
  have p := hsNonnegative (oddWords (k+3)) (sharedProbe half A)
  change 2*hs (oddWords (k+3)) (sharedProbe half A) (sharedProbe half A)=M.kappa at g
  change 32*M.sixMass≤160+59*M.kappa at s
  change 11*M.sixMass≤55+200*M.kappa; grind only

/-- The improved Fourier defect and the two disjoint character regions
force the small-error scale needed up through κ=11/200. Denominators
are cleared so the argument works in an arbitrary ordered ring. -/
theorem fourierErrorScale (kappa D e f delta : R) (small : 200*kappa≤11)
    (en : 0≤e) (fn : 0≤f) (rough : e≤2*D) (fourier : 80*D+9*e≤400*kappa)
    (oneCode : 2*(1-e)^2*f≤D)
    (regions : 2*e*(1-e)*(1-2*f)^2+4*(1-e)^2*f*(1-f)≤D)
    (angle : 2*delta≤3*(e+2*f)) : 25*delta<9 := by
  have ecap : 49*e≤22 := by grind only
  have dcap : 40*D≤11 := by grind only
  have b0 : 0≤1-e := by grind only
  have squareGap := OrderedRing.mul_nonneg (show 0≤49*(1-e)-27 by grind only) (show 0≤49*(1-e)+27 by grind only)
  have bd : D<(1-e)^2 := by grind only
  have fcap : 2*f<1 := by
    apply Classical.byContradiction; intro no
    have m := OrderedRing.mul_nonneg (squareNonnegative (1-e)) (show 0≤2*f-1 by grind only)
    grind only
  have ff := OrderedRing.mul_nonneg fn (show 0≤1-f by grind only)
  have eThird : 3*e<1 := by
    apply Classical.byContradiction; intro no
    have sign := OrderedRing.mul_nonneg b0 (show 0≤3*e-1 by grind only)
    have w := OrderedRing.mul_nonneg sign (squareNonnegative (1-2*f))
    grind only
  have eSixth : 6*e<1 := by
    have sign := OrderedRing.mul_nonneg b0 (show 0≤1-3*e by grind only)
    have w := OrderedRing.mul_nonneg sign ff
    apply Classical.byContradiction; intro no
    have m := OrderedRing.mul_nonneg (show 0≤6*e-1 by grind only) (show 0≤5-6*e by grind only)
    grind only
  have fFine : 80*f<9 := by
    have b2 := OrderedRing.mul_nonneg (show 0≤6*(1-e)-5 by grind only) (show 0≤6*(1-e)+5 by grind only)
    have tmp := OrderedRing.mul_nonneg (show 0≤36*(1-e)^2-25 by grind only) ff
    have extra := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg en b0) (squareNonnegative (1-2*f))
    apply Classical.byContradiction; intro no
    have m := OrderedRing.mul_nonneg (show 0≤80*f-9 by grind only) (show 0≤71-80*f by grind only)
    grind only
  let E := e+2*f
  have total : 120*E<47 := by unfold E; grind only
  have g : 0≤1-E := by grind only
  have efr := OrderedRing.mul_nonneg en fn
  have sqcmp (x : R) (lo : 1-E≤x) : (1-E)^2≤x^2 := by
    have v := OrderedRing.mul_nonneg (show 0≤x-(1-E) by grind only) (show 0≤x+(1-E) by grind only)
    grind only
  have t1 := sqcmp ((1-e)*(1-2*f)) (by dsimp only [E]; grind only)
  have t2 := sqcmp ((1-e)*(1-f)) (by dsimp only [E]; grind only)
  have b := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg en b0) (squareNonnegative (1-2*f))
  have d := OrderedRing.mul_nonneg ff (squareNonnegative (1-e))
  have l := OrderedRing.mul_nonneg en (show 0≤(1-e)*(1-2*f)^2-(1-E)^2 by grind only)
  have r := OrderedRing.mul_nonneg fn (show 0≤(1-e)^2*(1-f)-(1-E)^2 by grind only)
  have cub : 2*E*(1-E)^2≤D := by dsimp only [E] at l r ⊢; grind only
  have bound : 25*E<6 := by
    apply Classical.byContradiction; intro no
    have s := squareNonnegative (25*E-10)
    have w := OrderedRing.mul_nonneg (show 0≤25*E-6 by grind only) (show 0≤625*E^2-1100*E+361 by grind only)
    grind only
  change 2*delta≤3*E at angle; grind only

/-- The squared excess bound now holds on every actual orthonormal frame. -/
theorem physicalSixExcessSquared (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (excess : 5≤(physicalPayment half h2 k A mu).sixMass) :
    let M := physicalPayment half h2 k A mu
    (M.sixMass-5)^2≤M.kappa*(2*PauliReserveSlots.reserve half A (PauliReserveSlots.cut 5) (PauliReserveSlots.cut 5)) :=
  SixModeProbe.sixExcessSquared half inv24 third h2 h24 h3 k A mu orth
    (PhysicalDirectedCapacity.physicalDirectedCapacity half h2 k A orth 6 0 (by decide)) excess

theorem physicalSixWedge (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    SixModeProbe.sixWedge half h2 A≤3 :=
  SixModeProbe.sixWedgeLeThree half h2 k A orth
    (PhysicalDirectedCapacity.physicalDirectedCapacity half h2 k A orth 6 0 (by decide))

/-- A much coarser sector polarization suffices if only the global
coefficient 200/11 is required. -/
theorem uniformSixPriceCoarse (half : R) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (small : 200*(physicalPayment half h2 k A mu).kappa<11 →
      ∃ delta, Nonempty (RoundedSector half A delta) ∧ 411*delta≤378) :
    let M := physicalPayment half h2 k A mu
    11*M.sixMass≤55+200*M.kappa := by
  let M := physicalPayment half h2 k A mu
  by_cases hi : 11≤200*M.kappa
  · exact SixModeProbe.largeKappaSix half h2 k A mu orth hi
  have lo : 200*M.kappa<11 := by grind only
  obtain ⟨delta,⟨C⟩,d⟩ := small lo
  let l := oddAverage half (fun p => if C.member p then 0 else headWeight A p)
  have r := physicalLeakage half h2 k A mu orth delta C
  change _ ∧ 0≤l ∧ 2*(1-delta)*l≤M.kappa ∧ M.sixMass≤5+(2+delta)*l at r
  have m := OrderedRing.mul_nonneg (show 0≤378-411*delta by grind only) r.2.1
  change 11*M.sixMass≤55+200*M.kappa; grind only

end RankSeven.SixPointRounding

#print axioms RankSeven.SixPointRounding.sixMassSquares
#print axioms RankSeven.SixPointRounding.sectorFive
#print axioms RankSeven.SixPointRounding.headWeightLeSix
#print axioms RankSeven.SixPointRounding.physicalLeakage
#print axioms RankSeven.SixPointRounding.sectorSixPrice
#print axioms RankSeven.SixPointRounding.roundedSixPrices
#print axioms RankSeven.SixPointRounding.fourierErrorScale
#print axioms RankSeven.SixPointRounding.uniformSixPrice
#print axioms RankSeven.SixPointRounding.physicalSixWedge
#print axioms RankSeven.SixPointRounding.physicalSixExcessSquared
#print axioms RankSeven.SixPointRounding.uniformSixPriceCoarse

