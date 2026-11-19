import Rank7SharedTwoSlotReserve

namespace RankSeven.PhysicalEndpointReserve

open Lean.Grind Pauli ComplexScalar PauliReserveSlots OddCutReserve
open SharedTwoSlotReserve EndpointReserveSlots
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
open FrameExteriorSector (framedWord)
open SymmetricDefect (anti)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

private theorem sumLe {α : Type} (xs : List α) (f g : α→R) (le : ∀i,f i≤g i) : sumOver xs f≤sumOver xs g := by
  have z := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i _ => by have := le i; grind only)
  rw [Compression.sumOverSub] at z; grind only

/-- An odd test cut bounds both orientations of an arbitrary pair of cuts. -/
theorem unequalCross {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (r s i : Fin 7) (odd : (i.val+1)%2=1) :
    let J j k := reserve half A (cut j) (cut k)
    J r s≤(Nat.cast (s.val+1):R)*J r i+(Nat.cast (r.val+1):R)*J s i := by
  let m (j : Fin 7) : R := Nat.cast (j.val+1)
  let ws := words n
  let d := (2:R)^n
  let di := half^n
  let W (j : Fin 7) (v : Word n) := (coeff A (cut j) v)^2
  let S j k (p q : Word n) := if anti p q then W j p*W k q else 0
  let N j := neighborhood A (cut j)
  let L := cutLeak A i
  let J j k := reserve half A (cut j) (cut k)
  have leak := PhysicalOddLeakage.physicalOddCut A orth i odd
  have sym (u v : Fin 7) (p q : Word n) : S u v p q=S v u q p := by
    unfold S; rw [PauliEdgeBlocks.antiSymm p q]; split <;> grind only
  have inner (u v : Fin 7) (p : Word n) : sumOver ws (S u v p)=W u p*N v p := by
    change _=W u p*sumOver ws (fun q => if anti p q then W v q else 0)
    rw [sumOverMulLeft]; apply sumOverCongr; intro q; unfold S; split <;> grind only
  have sums (u v : Fin 7) (h : Word n → R) :
      sumOver ws (fun p => sumOver ws (fun q => S u v p q*h p))=sumOver ws (fun p => W u p*N v p*h p) := by
    apply sumOverCongr; intro p; rw [←sumOverMulRight,inner]
  have flip : sumOver ws (fun p => sumOver ws (fun q => S r s p q*L q))=sumOver ws (fun q => W s q*N r q*L q) := by
    rw [sumOverSwap]; apply Eq.trans _ (sums s r L)
    apply sumOverCongr; intro q; apply sumOverCongr; intro p; rw [sym]
  have z := sumLe ws (fun p => sumOver ws (S r s p))
    (fun p => sumOver ws (fun q => S r s p q*L p+S r s p q*L q)) (fun p => by
    apply sumLe; intro q
    cases h : anti p q with
    | false => simp only [S,h,Bool.false_eq_true,ite_false,Semiring.zero_mul,Semiring.add_zero]; exact Std.le_refl _
    | true =>
      have pos := OrderedRing.mul_nonneg (squareNonnegative (coeff A (cut r) p)) (squareNonnegative (coeff A (cut s) q))
      change 0≤W r p*W s q at pos
      have l := OrderedRing.mul_le_mul_of_nonneg_left (leak p q h) pos
      simp only [S,h,ite_true]; change _≤W r p*W s q*L p+W r p*W s q*L q
      change W r p*W s q*1≤W r p*W s q*(L p+L q) at l
      grind only)
  simp only [sumOverAdd,inner,sums,flip] at z
  have pow0 (m : Nat) : 0<(2:R)^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by have := OrderedRing.zero_lt_one (R:=R); grind only)
  have cap (u v : Fin 7) : sumOver ws (fun p => W u p*N v p*L p)≤m v*sumOver ws (fun p => W u p*N i p) := by
    have localCap (p : Word n) : W u p*N v p*L p≤m v*(W u p*N i p) := by
      have f := neighborhoodFourier A orth (cut v) p
      have f' := neighborhoodFourier A orth (cut i) p
      change 2*N v p=d*cutLeak A v p at f
      change 2*N i p=d*L p at f'
      have lo := cutLeakUpper A p v
      change cutLeak A v p≤m v at lo
      have bound := OrderedRing.mul_le_mul_of_nonneg_left lo (Std.le_of_lt (pow0 n))
      change d*cutLeak A v p≤d*m v at bound
      have weight := OrderedRing.mul_nonneg (squareNonnegative (coeff A (cut u) p)) (cutLeakNonnegative A orth p i)
      change 0≤W u p*L p at weight
      have z := OrderedRing.mul_le_mul_of_nonneg_left (show 2*N v p≤d*m v by grind only) weight
      have k := congrArg (fun x => (W u p*m v)*x) f'; grind only
    have out := sumLe ws _ _ localCap
    rw [←sumOverMulLeft] at out; exact out
  have le1 := cap r s; have le2 := cap s r
  have full : sumOver ws (fun p => W r p*N s p)≤m s*sumOver ws (fun p => W r p*N i p)+m r*sumOver ws (fun p => W s p*N i p) := by grind only
  have scaled := OrderedRing.mul_le_mul_of_nonneg_left full (squareNonnegative di)
  change di^2*sumOver ws (fun p => W r p*N s p)≤m s*(di^2*sumOver ws (fun p => W r p*N i p))+m r*(di^2*sumOver ws (fun p => W s p*N i p))
  grind only

theorem oddSharedCleared (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) (h q : R) (s : Fin 7) (odd : (s.val+1)%2=1) :
    let K := (physicalPayment half h2 k A mu).kappa
    let J r j := reserve half A (cut r) (cut j)
    h^2*q^2*K≤4*(h^2+3*q^2)*(h^2*J 0 s+q^2*J 2 s) := by
  let J (r i : Fin 7) := reserve half A (cut r) (cut i)
  let K := (physicalPayment half h2 k A mu).kappa
  have a := unequalCross half A orth 0 0 s odd
  have b := unequalCross half A orth 0 2 s odd
  have c := unequalCross half A orth 2 2 s odd
  change J 0 0≤(Nat.cast 1:R)*J 0 s+(Nat.cast 1:R)*J 0 s at a
  change J 0 2≤(Nat.cast 3:R)*J 0 s+(Nat.cast 1:R)*J 2 s at b
  change J 2 2≤(Nat.cast 3:R)*J 2 s+(Nat.cast 3:R)*J 2 s at c
  have co : (Nat.cast 3:R)=3 := by grind only
  simp only [co,Semiring.natCast_one] at a b c
  have a' := OrderedRing.mul_le_mul_of_nonneg_left a (squareNonnegative (h^2))
  have b' := OrderedRing.mul_le_mul_of_nonneg_left b (OrderedRing.mul_nonneg (squareNonnegative h) (squareNonnegative q))
  have c' := OrderedRing.mul_le_mul_of_nonneg_left c (squareNonnegative (q^2))
  have phys := physicalTwoSlots half h2 k A mu orth h q
  change h^2*q^2*K≤2*h^4*J 0 0+4*h^2*q^2*J 0 2+2*q^4*J 2 2 at phys
  change h^2*q^2*K≤4*(h^2+3*q^2)*(h^2*J 0 s+q^2*J 2 s)
  grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]
open UpperEndpoint UpperEndpointPrices
open UpperFrameGain (tail)
open UpperPhysicalInterior (spectrum)
open PhysicalTailBlend (unshiftedDefects)
open JointProbeGram (referenceShared referencePair)
open PhysicalDefectAssembly (frameDefects)

private theorem mulQuot (a : F) {b : F} (hp : 0<b) : b*(a/b)=a := by
  have z := Field.mul_inv_cancel (show b≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

theorem chartSharedPaid (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (p : Inputs F) (wh ws c d : F)
    (chart : (fun i => (mu i)^2)=tail (spectrum p.h p.k p.q) c d) :
    let m := (physicalPayment half h2 k A mu).kappa
    let g := (H p).g2
    let odd := (K p wh ws c d).odd
    (g+odd*g/(H p).oddDen)*m≤sharedSlots half A (fun i => (mu i)^2) := by
  let w := fun i => (mu i)^2
  let m := (physicalPayment half h2 k A mu).kappa
  let h := p.h
  let q := p.q
  let y := 1-c
  let z := d
  let J (i j : Fin 7) := reserve half A (cut i) (cut j)
  let odd := (K p wh ws c d).odd
  let den := h^2+3*q^2
  let g := h^2*q^2
  have raw := physicalTwoSlots half h2 k A mu orth h q
  change h^2*q^2*m≤2*h^4*J 0 0+4*h^2*q^2*J 0 2+2*q^4*J 2 2 at raw
  let T (s : Fin 7) := h^2*J 0 s+q^2*J 2 s
  have a := oddSharedCleared half h2 k A mu orth h q 4 (by decide)
  have b := oddSharedCleared half h2 k A mu orth h q 6 (by decide)
  change g*m≤4*den*T 4 at a; change g*m≤4*den*T 6 at b
  have non : 0≤m := by
    have z := WeightedProbeShift.physicalMomentOrder half h2 k A mu orth
    exact Std.le_trans z.1 z.2.1
  have g0 : 0≤g := OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)
  have dom : 0≤den := by have := squareNonnegative h; have := squareNonnegative q; dsimp only [den]; grind only
  have ratio : (H p).g2=g := by change (h*q)*(h*q)=_; unfold g; grind only
  have denom : (H p).oddDen=den := by change h*h+3*(q*q)=_; unfold den; grind only
  have tang : odd≤y^2+z^2 := by
    have a := squareNonnegative (p.ch-c); have b := squareNonnegative (d-p.dl)
    change (1-p.ch)*(1+p.ch-2*c)+p.dl*(2*d-p.dl)≤(1-c)^2+d^2; grind only
  have T0 (i : Fin 7) : 0≤T i := by
    have hi := OrderedRing.mul_nonneg (squareNonnegative h) (reserveNonnegative half A (cut 0) (cut i))
    have qi := OrderedRing.mul_nonneg (squareNonnegative q) (reserveNonnegative half A (cut 2) (cut i))
    change 0≤h^2*J 0 i+q^2*J 2 i; grind only
  have pay : (odd*g/den)*m≤4*(y^2*T 4+z^2*T 6) := by
    by_cases pos : 0<den
    · have qa := mulQuot (odd*g) pos
      have cert := congrArg (fun x => x*m) qa
      have a' := OrderedRing.mul_le_mul_of_nonneg_left a (squareNonnegative y)
      have b' := OrderedRing.mul_le_mul_of_nonneg_left b (squareNonnegative z)
      have tan := OrderedRing.mul_le_mul_of_nonneg_right tang (OrderedRing.mul_nonneg g0 non)
      apply Classical.byContradiction; intro no
      have gt : 0<(odd*g/den)*m-4*(y^2*T 4+z^2*T 6) := by grind only
      have bad := OrderedRing.mul_pos pos gt; grind only
    · have d0 : den=0 := by grind only
      have q2 := squareNonnegative q; have h2' := squareNonnegative h
      have hzero : h^2=0 := by unfold den at d0; grind only
      have gz : g=0 := by unfold g; rw [hzero,Semiring.zero_mul]
      have yp := OrderedRing.mul_nonneg (squareNonnegative y) (T0 4)
      have zp := OrderedRing.mul_nonneg (squareNonnegative z) (T0 6)
      rw [gz,Field.div_eq_mul_inv]; grind only
  have gaps : gap w 0=h ∧ gap w 2=q ∧ gap w 4=y ∧ gap w 6=z := by
    unfold w; rw [chart]
    simp (config:={decide:=true}) [gap,tail,spectrum,h,q,y,z] <;> grind only
  change ((H p).g2+odd*(H p).g2/(H p).oddDen)*m≤sharedSlots half A w
  rw [ratio,denom]; unfold sharedSlots
  simp only [gaps.1,gaps.2.1,gaps.2.2.1,gaps.2.2.2]
  change (g+odd*g/den)*m≤2*(h^2*h^2*J 0 0+q^2*q^2*J 2 2+
      2*(h^2*q^2*J 0 2+h^2*y^2*J 0 4+h^2*z^2*J 0 6+q^2*y^2*J 2 4+q^2*z^2*J 2 6))
  unfold T at pay; unfold g at *
  grind only

/-- Both quadratic checker coefficients are paid by the actual physical Pauli defect,
before conversion of the two probe Grams into exterior link excesses. -/
theorem chartPauliRemainder (half inv24 third : F) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F) (orth : OrthonormalFrame A)
    (p : Inputs F) (wh ws c d : F) (chart : (fun i => (mu i)^2)=tail (spectrum p.h p.k p.q) c d)
    (cl : p.cl≤c) (cu : c≤p.ch) (du : d≤p.dh) (dl : p.dl≤d) (dl0 : 0≤p.dl)
    (cu1 : p.ch≤1) (ordered : d≤c) (cornerOrder : p.dl≤p.cl) (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q)
    (f0 : 0≤p.f) (f1 : p.f≤1) (u0 : 0≤p.u) (uc : 2*p.u≤3) (w0 : 0≤p.w) (wc : 4*p.w≤7) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    let x := PackingPolynomial.physicalWeights half h2 k A
    let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
    let s := (P p).shift
    let t := p.w*(H p).delta
    let G := (H p).g2
    let O := (K p wh ws c d).odd
    unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)+
      (G+paid p c d+O*G/(H p).oddDen)*M.kappa+((P p).highQuad+O*(H p).k2/2)*M.kappaOne≤
      frameDefects half inv24 k A mu := by
  have high := chartHighestPaid half inv24 third h2 h24 h3 k A mu orth p wh ws c d chart cl cu du dl dl0 cu1 ordered cornerOrder h0 k0 q0 f0 f1 u0 uc w0 wc
  have shared := chartSharedPaid half h2 k A mu orth p wh ws c d chart
  dsimp only at high shared ⊢; grind only

end Field

end RankSeven.PhysicalEndpointReserve

#print axioms RankSeven.PhysicalEndpointReserve.unequalCross
#print axioms RankSeven.PhysicalEndpointReserve.oddSharedCleared
#print axioms RankSeven.PhysicalEndpointReserve.chartSharedPaid
#print axioms RankSeven.PhysicalEndpointReserve.chartPauliRemainder

