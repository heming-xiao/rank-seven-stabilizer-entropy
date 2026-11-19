import Rank7PauliReserveSlots

/-! Upper edge-block estimate and the physical antisymmetric restriction
bound for the Pauli anticommuting reserve. -/
namespace RankSeven.ReserveMixedNorm
open Lean.Grind Pauli ComplexScalar SymmetricDefect AnticommutingDefect
open PauliEdgeBlocks PhysicalEdgeSwitching AntiPairIncidence
open PhysicalDefectAssembly (pairedDensity physicalSectorTerms)
open JointProbePayment (hs densityCoordinates)
open PauliReserveSlots (reserve)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem powerPositive (n : Nat) : (0:R)<(2:R)^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)

/-- Complementary upper bound on the literal signed edge adjacency. -/
theorem physicalEdgeUpper (half : R) (h2 : 2*half=1) {n : Nat}
    (s r : Word (n+1)) (sr : anti s r=true) (z : Word (n+1) → R) :
    let xs := perpendicularWords s r
    sumOver xs (fun u => sumOver xs (fun v => z u*physicalEdgeMatrix half s r u v*z v)) ≤
      ((2:R)^n+1)*sumOver xs (fun u => (z u)^2) := by
  let xs := perpendicularWords s r
  let a := (2:R)^n
  let y := switchedVector (edgeNegative s r) z
  let H := kernelImage xs chi y
  let m := sumOver xs (fun u => (z u)^2)
  let b := sumOver xs (fun u => y u*H u)
  have form : sumOver xs (fun u => sumOver xs (fun v => z u*physicalEdgeMatrix half s r u v*z v)) = m-b := by
    rw [←edgeQuadraticSwitch s r (edgeNegative s r) z]
    apply sumCongrMem; intro u hu; apply sumCongrMem; intro v hv
    rw [physicalEdgeEntry half h2 s r u v sr (List.mem_filter.mp hu).2 (List.mem_filter.mp hv).2]
  have one (u : Word (n+1)) : (y u)^2=(z u)^2 := by
    dsimp only [y,switchedVector]; cases edgeNegative s r u <;> simp [phase] <;> grind only
  have nrm := edgeKernelImageNorm half h2 s r sr y
  change sumOver xs (fun u => (H u)^2)=a^2*sumOver xs (fun u => (y u)^2) at nrm
  rw [sumOverCongr xs one] at nrm
  have ex (u) : (a*y u+H u)^2=a^2*(y u)^2+(H u)^2+(2*a)*(y u*H u) := by grind only
  have pos := Compression.sumOverNonnegative xs (fun u => (a*y u+H u)^2) (fun u _ => squareNonnegative _)
  rw [sumOverCongr xs ex,sumOverAdd,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,
    sumOverCongr xs one,nrm] at pos
  change 0≤a^2*m+a^2*m+2*a*b at pos
  have pa : 0<a := powerPositive n
  have bound : 0≤a*m+b := by
    by_cases h : 0≤a*m+b
    · exact h
    · have e := OrderedRing.mul_pos pa (show 0< -(a*m+b) by grind only); grind only
  change _≤(a+1)*m; rw [form]; grind only

private theorem sumLe {α : Type} (xs : List α) (f g : α → R) (h : ∀ i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have e := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at e; grind only

theorem physicalPlaneUpper (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1) {n : Nat}
    (f : Word (n+1) → R) :
    let ws := words (n+1)
    let planes := (fourIndices ws).filter (ExteriorIsometry.increasing PhysicalAntiQuartic.wordKey)
    4*(sumOver planes (PhysicalAntiQuartic.planeTerm imaginaryUnit (fun w => ofReal (f w)))).re≤
      ((2:R)^n+1)*PhysicalAntiQuartic.unorderedAntiMass f := by
  dsimp only; rw [AntiPlaneIncidence.physicalPlaneEdgeSum half inv24 h2 h24,
    AntiPairIncidence.unorderedAntiMass_eq_edgeSquares half h2,sumOverMulLeft]
  apply sumLe; intro s hs
  exact physicalEdgeUpper half h2 s (companion s) (companionAnti s hs) _

/-- Ordered Pauli mass bounds the complete squared signed mixed projection
for an arbitrary physical density, including rank-six and leading-pair cuts. -/
theorem projectedNormLeReserve (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    hs (MixedDefect.oddWords (k+3)) (densityCoordinates half A mu) (densityCoordinates half A mu) ≤
      reserve half A (fun i => (mu i)^2) (fun i => (mu i)^2) := by
  let n := k+3
  let di := half^n
  let d := (2:R)^n
  let a := (2:R)^(k+2)
  let c := traceWord imaginaryUnit (pairedDensity A mu)
  let f (p : Word n) := (c p).re
  let planes := (fourIndices (words n)).filter (ExteriorIsometry.increasing PhysicalAntiQuartic.wordKey)
  let F := (sumOver planes (PhysicalAntiQuartic.planeTerm imaginaryUnit c)).re
  let M := (PhysicalAntiQuartic.unorderedAntiMass c).re
  let J := (PhysicalAntiQuartic.antiMass c).re
  let eta := SectorDefectAccounting.anticommutingDefect d
    ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2) (sumOver (List.finRange 7) (fun i => (mu i)^8))
    (physicalSectorTerms half inv24 k A mu)
  let norm := hs (MixedDefect.oddWords n) (densityCoordinates half A mu) (densityCoordinates half A mu)
  have grouped := AntiDefectTransport.physicalAnticommutingGroupedExpansion half inv24 h2 h24 k A mu orth
  change eta=4*(3*d-4)*di^2*M+64*di^2*F at grouped
  have mixed := JointProbePayment.physicalAnticommutingResidual half inv24 h2 h24 k A mu orth
  change di*eta=2*di^2*J+8*norm at mixed
  have pp := physicalPlaneUpper half inv24 h2 h24 (n:=k+2) f
  have real : (fun p => ofReal (f p))=c := by funext p; exact (AntiDefectTransport.densityTraceWordOfReal A mu p).symm
  dsimp only at pp; rw [real,←AntiDefectTransport.physicalUnorderedAnticommutingMass A mu] at pp
  change 4*F≤(a+1)*M at pp
  have same := congrArg ComplexScalar.re (PhysicalAntiQuartic.antiMass_twice c)
  change J=2*M-0*(PhysicalAntiQuartic.unorderedAntiMass c).im at same
  have Jm : J=2*M := by grind only
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have twice : d=2*a := by change (2:R)^(k+2+1)=_; rw [Semiring.pow_succ]; grind only
  have scale0 : 0≤di := by
    have h : 0≤half := by grind only
    have hpow (m : Nat) : 0≤half^m := by
      induction m with
      | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
      | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih h
    exact hpow n
  have scaled := OrderedRing.mul_le_mul_of_nonneg_left pp (squareNonnegative di)
  have bound : eta≤20*d*di^2*M := by rw [grouped,twice]; grind only
  have total := OrderedRing.mul_le_mul_of_nonneg_left bound scale0
  have cancel : di*(20*d*di^2*M)=20*di^2*M := by
    calc
      _ = (d*di)*(20*di^2*M) := by grind only
      _ = _ := by rw [inv,Semiring.one_mul]
  rw [cancel] at total
  rw [PauliReserveSlots.sameSlot]
  change norm≤di^2*J
  rw [Jm] at mixed ⊢; grind only

/-- Every spectral projection is idempotent in its source coordinates,
so the reserve dominates the projected norm also for the rank-six cut. -/
theorem spectralCutReserve (half inv24 : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (r : Fin 7)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let w := PauliReserveSlots.cut (R:=R) r
    hs (MixedDefect.oddWords (k+3)) (densityCoordinates half A w) (densityCoordinates half A w) ≤
      reserve half A w w := by
  let w := PauliReserveSlots.cut (R:=R) r
  have sq : (fun i => (w i)^2)=w := by funext i; unfold w PauliReserveSlots.cut; split <;> grind only
  have e := projectedNormLeReserve half inv24 h2 h24 k A w orth
  rw [sq] at e; exact e

/-- The leading-pair cut pays κ₁/2 in the normalization used by the
shared/highest probe Gram matrix. -/
theorem highestPairReserve (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne ≤
      2*reserve half A (PauliReserveSlots.cut 1) (PauliReserveSlots.cut 1) := by
  let w := PauliReserveSlots.cut (R:=R) 1
  let os := MixedDefect.oddWords (k+3)
  let V := JointProbePayment.pairCoordinates half A 0 1
  have v : densityCoordinates half A w=V := by
    have sq : (fun i => (w i)^2)=JointProbePayment.pairSpectrum (R:=R) 0 1 := by
      funext i; unfold w PauliReserveSlots.cut JointProbePayment.pairSpectrum
      split <;> split <;> first | omega | grind only | (exfalso; omega)
    unfold densityCoordinates V JointProbePayment.pairCoordinates pairedDensity; rw [sq]
  have e := spectralCutReserve half inv24 h2 h24 k A 1 orth
  change hs os (densityCoordinates half A w) (densityCoordinates half A w)≤reserve half A w w at e
  rw [v] at e
  have gram := (JointProbeGram.physicalJointGram half third h2 h3 k A orth).2.1
  change 2*hs os V V = (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne at gram
  change _≤2*reserve half A w w; rw [←gram]; grind only

/-- The two disjoint diagonal slots pay the leading-pair and rank-six
signed norms simultaneously for an arbitrary sorted physical spectrum. -/
theorem twoDiagonalPayments (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (sort : PauliMatchingPrices.SortedSpectrum (fun i => (mu i)^2)) :
    let t := fun i => (mu i)^2
    let z := densityCoordinates half A (PauliReserveSlots.cut 5)
    let betaSix := 2*hs (MixedDefect.oddWords (k+3)) z z
    (PauliReserveSlots.gap t 1)^4*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne+
      (PauliReserveSlots.gap t 5)^4*betaSix≤2*reserve half A t t := by
  let t := fun i => (mu i)^2
  let g := PauliReserveSlots.gap t
  let J r s := reserve half A (PauliReserveSlots.cut r) (PauliReserveSlots.cut s)
  let X r s := (g r)^2*(g s)^2*J r s
  let xs := List.finRange 7
  have pos (r s : Fin 7) : 0≤X r s := OrderedRing.mul_nonneg
    (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)) (PauliReserveSlots.reserveNonnegative _ _ _ _)
  have diag (r : Fin 7) : X r r≤sumOver xs (X r) := by
    rw [←ExteriorPauliBase.sumOnIndex xs r (X r) (List.nodup_finRange 7) (List.mem_finRange _)]
    apply sumLe; intro s _; split <;> first | exact Std.le_refl _ | exact pos _ _
  let row (r : Fin 7) := sumOver xs (X r)
  have row0 (r : Fin 7) : 0≤row r := Compression.sumOverNonnegative xs _ (fun s _ => pos r s)
  have fin : xs=[0,1,2,3,4,5,6] := by decide
  have sel : X 1 1+X 5 5≤sumOver xs row := by
    have p := diag 1; have q := diag 5
    change X 1 1≤row 1 at p; change X 5 5≤row 5 at q
    rw [fin]; simp only [sumOver,List.map_cons,List.map_nil,List.sum_nil,List.sum_cons]
    have := row0 0; have := row0 2; have := row0 3; have := row0 4; have := row0 6; grind only
  let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne
  let z := densityCoordinates half A (PauliReserveSlots.cut 5)
  let betaSix := 2*hs (MixedDefect.oddWords (k+3)) z z
  have h1 : K≤2*J 1 1 := highestPairReserve half inv24 third h2 h24 h3 k A mu orth
  have h6 := spectralCutReserve half inv24 h2 h24 k A 5 orth
  change hs (MixedDefect.oddWords (k+3)) z z≤J 5 5 at h6
  have b6 : betaSix≤2*J 5 5 := by dsimp only [betaSix]; grind only
  have p4 (i : Fin 7) : 0≤(g i)^4 := by
    have e := squareNonnegative ((g i)^2); grind only
  have one := OrderedRing.mul_le_mul_of_nonneg_left h1 (p4 1)
  have six := OrderedRing.mul_le_mul_of_nonneg_left b6 (p4 5)
  have total : sumOver xs row≤reserve half A t t := PauliReserveSlots.allCutSlots half A orth t sort
  have pay := Std.le_trans sel total
  dsimp only [X] at pay
  change (g 1)^4*K+(g 5)^4*betaSix≤2*reserve half A t t; grind only

end RankSeven.ReserveMixedNorm

#print axioms RankSeven.ReserveMixedNorm.physicalEdgeUpper
#print axioms RankSeven.ReserveMixedNorm.physicalPlaneUpper
#print axioms RankSeven.ReserveMixedNorm.projectedNormLeReserve
#print axioms RankSeven.ReserveMixedNorm.spectralCutReserve
#print axioms RankSeven.ReserveMixedNorm.highestPairReserve
#print axioms RankSeven.ReserveMixedNorm.twoDiagonalPayments
