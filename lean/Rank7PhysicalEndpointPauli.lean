import Rank7PhysicalUniformTail
import Rank7UpperEndpointPrices
import Rank7UpperPhysicalInterior

namespace RankSeven.PhysicalEndpointPauli

open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram PauliMatchingPrices WeightedProbeShift
open PhysicalTailBlend PauliReserveSlots
open PhysicalCompressionEffect (OrthonormalFrame)
open MixedDefect (oddWords)
open PhysicalDefectAssembly (frameDefects)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem avgLe (half : R) (h2 : 2*half=1) {n : Nat} {f g : Word n → R}
    (h : ∀ p∈oddWords n,f p≤g p) : oddAverage half f≤oddAverage half g := by
  have a := Compression.sumOverNonnegative (oddWords n) (fun x => g x-f x) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at a
  have hh : 0≤half := by grind only
  have hn (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hh
  exact OrderedRing.mul_le_mul_of_nonneg_left (by grind only) (show 0≤2*half^n by have := hn n; grind only)

theorem highestReverse (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    M.highest+sharedGap w*M.cross≤
      2*hs (oddWords (k+3)) (pairCoordinates half A 0 1) (densityCoordinates half A mu) := by
  let w := fun i => (mu i)^2
  let P p := pairWeight A p 0 1
  let S p := P p+pairWeight A p 0 2
  let C := matchingScore A w
  let os := oddWords (k+3)
  have h1 : oddAverage half P=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  obtain ⟨d01,d12,d23,d34,d45,d56,d6⟩ := sort
  change w 1≤w 0 at d01; change w 2≤w 1 at d12; change w 3≤w 2 at d23
  change w 4≤w 3 at d34; change w 5≤w 4 at d45; change w 6≤w 5 at d56; change 0≤w 6 at d6
  have emp : 0≤emptyGap w := OrderedRing.mul_nonneg (by grind only) (by grind only)
  have tl : 0≤tailGap w := OrderedRing.mul_nonneg (squareNonnegative _) (by grind only)
  have id : secondPrice w+leadingGap w=highPrice w := by unfold highPrice secondPrice leadingGap; grind only
  have bd (p : Word (k+3)) (hp : p∈os) : P p*C p≤highPrice w*P p-leadingGap w*(P p*(1-P p))-sharedGap w*(P p*(1-S p)) := by
    have e := (physicalPerWordBounds A orth p hp w ⟨d01,d12,d23,d34,d45,d56,d6⟩).2
    have tr := leadingTriangle A orth p hp
    change S p+pairWeight A p 1 2≤1 at tr
    have f0 := OrderedRing.mul_nonneg emp (show 0≤1-S p-pairWeight A p 1 2 by grind only)
    have f1 := OrderedRing.mul_nonneg tl (show 0≤3-sixVertexMass A p by have := sixMassLeThree A orth p hp; grind only)
    change C p≤secondPrice w+leadingGap w*P p-sharedGap w*(1-S p)-emptyGap w*(1-S p-pairWeight A p 1 2)-tailGap w*(3-sixVertexMass A p) at e
    have full : C p≤highPrice w-leadingGap w*(1-P p)-sharedGap w*(1-S p) := by grind only
    have b := OrderedRing.mul_le_mul_of_nonneg_left full (show 0≤P p from normSq_nonnegative _)
    grind only
  have avg := avgLe half h2 bd
  unfold oddAverage at avg
  simp only [Compression.sumOverSub,←sumOverMulLeft] at avg
  have h1' : 2*half^(k+3)*sumOver os P=1 := h1
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W := ProjectedProbeOverlap.weightedFourWedge 0 1 w (fun j => E.realPart j j)
  let V := pairCoordinates half A 0 1
  let L := densityCoordinates half A mu
  have h := ProjectedProbeOverlap.pairPaymentIdentity half third h2 h3 k A mu orth 0 1 (by decide)
  change 2*hs os V L=w 0*w 1+W-oddAverage half (fun p => P p*C p) at h
  have defHigh : highPrice w=w 0*w 1+referencePair w := by unfold highPrice referencePair; grind only
  change W-referencePair w+leadingGap w*oddAverage half (fun p => P p*(1-P p))+
    sharedGap w*oddAverage half (fun p => P p*(1-S p))≤2*hs os V L
  unfold oddAverage at *
  change 2*half^(k+3)*sumOver os (fun x => P x*C x)≤2*half^(k+3)*(highPrice w*sumOver os P-
    leadingGap w*sumOver os (fun p => P p*(1-P p))-sharedGap w*sumOver os (fun p => P p*(1-S p))) at avg
  have unit := congrArg (fun x => highPrice w*x) h1'
  grind only

/-- The highest probe also pays the reverse shared cross term on the same frame. -/
theorem reverseReceipt (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) (s t : R) (s0 : 0≤s) (t0 : 0≤t) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    unshiftedDefects half inv24 k A mu+2*reserve half A w w+M.receipt s t+24*t*sharedGap w*M.cross≤
      frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let os := oddWords (k+3)
  let L := densityCoordinates half A mu
  let U := sharedProbe half A
  let V := pairCoordinates half A 0 1
  have high := highestReverse half third h2 h3 k A mu orth sort
  have shared := (physicalProbePayments half third h2 h3 k A mu orth sort).2
  change M.highest+sharedGap w*M.cross≤2*hs os V L at high
  change M.shared≤2*hs os U L at shared
  have G := physicalJointGram half third h2 h3 k A orth
  change 2*hs os U U=M.kappa ∧ 2*hs os V V=M.kappaOne ∧ 2*hs os U V=M.cross at G
  have a := OrderedRing.mul_le_mul_of_nonneg_left high t0
  have b := OrderedRing.mul_le_mul_of_nonneg_left shared s0
  have sq : M.receipt s t+24*t*sharedGap w*M.cross≤24*hs os L L := by
    have n := hsNonnegative os (shifted L U V s t)
    rw [jointShiftIdentity os L U V s t]
    unfold Payment.receipt
    rw [←G.2.2] at a
    rw [←G.1,←G.2.1,←G.2.2]; grind only
  have defeq := physicalJointResidual half inv24 h2 h24 k A mu orth
  have anti := sameSlot half A w
  let D := unshiftedDefects half inv24 k A mu
  let X := (PhysicalAntiQuartic.antiMass (SymmetricDefect.traceWord imaginaryUnit (PhysicalDefectAssembly.pairedDensity A mu))).re
  change frameDefects half inv24 k A mu=D+2*(half^(k+3))^2*X+24*hs os L L at defeq
  change reserve half A w w=(half^(k+3))^2*X at anti
  change D+2*reserve half A w w+M.receipt s t+24*t*sharedGap w*M.cross≤_
  rw [defeq,anti]; grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

/-- Dividing only by the positive spectral denominator covers flat and nonflat sixth gaps simultaneously.
The complete anti-Pauli reserve outside the rank-six contribution is retained. -/
theorem fullPenalty (half inv24 third rate : F) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (h3 : 3*third=1) (hRate : 11*rate=200) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (sort : SortedSpectrum (fun i => (mu i)^2))
    (s t f : F) (s0 : 0≤s) (t0 : 0≤t) (f1 : f≤1)
    (pos : 0<spectralPsi half third (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    let W := SixModeProbe.sixWedge half h2 A
    let retained := 2*reserve half A w w-sixCoefficient half third w*betaSix half A
    unshiftedDefects half inv24 k A mu+headReceipt half h2 k A mu s t+24*t*sharedGap w*M.cross+retained
      -24*s*((1-f)*tailGap w*rate*M.kappa)+24*s*f*tailGap w*(3-W)
      -12*s^2*(quadraticPenalty half third w f-1)*M.kappa≤frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let W := SixModeProbe.sixWedge half h2 A
  let X := frameDefects half inv24 k A mu
  let D := unshiftedDefects half inv24 k A mu
  let H := headReceipt half h2 k A mu s t
  let J := reserve half A w w
  let B := betaSix half A
  let cap := spectralPsi half third w
  let e := gap w 5
  let tail := tailGap w
  let psi := sixCoefficient half third w
  let Q := quadraticPenalty half third w f
  change 0<cap at pos
  have norm := Field.mul_inv_cancel (show cap≠0 by grind only)
  have factor := spectralFactor half third h2 h3 w
  change psi=e^2*cap ∧ tail=w 4*e at factor
  have eq : cap*(Q-1)=12*f^2*(w 4)^2 := by
    unfold Q quadraticPenalty; change cap*((1+12*f^2*(w 4)^2/cap)-1)=_
    rw [Field.div_eq_mul_inv]; grind only
  have scaled := congrArg (fun x => 12*s^2*M.kappa*x) eq
  have direct := PhysicalProjectionAngles.uniformPhysicalSixPrice half h2 k A mu orth
  change 11*M.sixMass≤55+200*M.kappa at direct
  have rp := congrArg (fun x => x*M.kappa) hRate
  have lin : M.sixMass-5≤rate*M.kappa := by grind only
  have tail0 : 0≤tail := OrderedRing.mul_nonneg (squareNonnegative _) (by have ord := sort.2.2.2.2.2.1; change w 6≤w 5 at ord; grind only)
  have dk := OrderedRing.mul_le_mul_of_nonneg_left lin (OrderedRing.mul_nonneg s0
    (OrderedRing.mul_nonneg (show 0≤1-f by grind only) tail0))
  have rev := reverseReceipt half inv24 third h2 h24 h3 k A mu orth sort s t s0 t0
  change D+2*J+M.receipt s t+24*t*sharedGap w*M.cross≤X at rev
  have head := headReceiptIdentity half h2 k A mu s t
  change H=M.receipt s t+24*s*tail*(M.sixMass-5) at head
  have sq := signedPrice half third h2 h3 k A mu orth (s*f*w 4) (e*cap)
  change (e*cap)*(24*(s*f*w 4)*(M.sixMass-2-W))≤(e*cap)^2*B+144*(s*f*w 4)^2*M.kappa at sq
  have pay : 24*s*f*tail*(M.sixMass-2-W)≤psi*B+12*s^2*(Q-1)*M.kappa := by
    apply Classical.byContradiction; intro no
    have gt : 0<24*s*f*tail*(M.sixMass-2-W)-(psi*B+12*s^2*(Q-1)*M.kappa) := by grind only
    have bad := OrderedRing.mul_pos pos gt
    rw [factor.1,factor.2] at bad
    grind only
  change D+H+24*t*sharedGap w*M.cross+(2*J-psi*B)-24*s*((1-f)*tail*rate*M.kappa)+24*s*f*tail*(3-W)
      -12*s^2*(Q-1)*M.kappa≤X
  grind only

open UpperEndpoint UpperEndpointPrices UpperPrices
open UpperFrameGain (tail)
open UpperPhysicalInterior (spectrum)

private theorem capTimes {a b : F} (h : 0<b) : b*(a/b)=a := by
  have e := Field.mul_inv_cancel (show b≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

theorem chartReserve (p : Inputs F) (c d half third : F) (h2 : 2*half=1) (h3 : 3*third=1) :
    let w := tail (spectrum p.h p.k p.q) c d
    spectralPsi half third w=actualReserve p.h p.q c d ∧ sharedGap w=p.h*p.q ∧
    leadingGap w=(H p).delta ∧ tailGap w=c-d ∧ w 4=1 ∧
    leadingCoefficient half third w=(H p).anti := by
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have n := congrArg (fun x => x*(3*third)) h2
  have u : 6*(half*third)=1 := by grind only
  have d6 : (6:F)*(1/6)=1 := capTimes (a:=1) (by grind only)
  have d2 : (2:F)*(1/2)=1 := capTimes (a:=1) (by grind only)
  have b6 : (1/6:F)=half*third := by grind only
  have b2 : (1/2:F)=half := by grind only
  have div (a x : F) : a/x=a*(1/x) := by simp only [Field.div_eq_mul_inv,Semiring.one_mul]
  dsimp only
  change _=_ ∧ _=_ ∧ _=p.k*(p.h+p.k+p.q) ∧ _=_ ∧ _=_ ∧ _=p.k*p.k*(p.k*p.k+(p.h*p.h+p.q*p.q)/2)
  simp only [spectralPsi,leadingCoefficient,gap,tailGap,sharedGap,leadingGap,actualReserve,tail,spectrum]
  simp (config := {decide:=true}) only [↓reduceIte,Fin.val_zero,Fin.val_one,Fin.isValue] 
  rw [div (_+_+_+_) 6,div (_+_) 2,b6,b2]
  grind only

theorem chartSorted (p : Inputs F) (c d : F) (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q)
    (dc : d≤c) (c1 : c≤1) (d0 : 0≤d) : SortedSpectrum (tail (spectrum p.h p.k p.q) c d) := by
  simp (config := {decide:=true}) [SortedSpectrum,tail,spectrum] <;> grind only

/-- The mixed cross payment stays nonnegative at every shift in the checker's rectangle. -/
theorem crossPayment {g delta s t : F} (s0 : 0≤s) (t0 : 0≤t) (g0 : 0≤g) (d0 : 0≤delta)
    (sc : 2*s≤3*g) (tc : 4*t≤7*delta) : 0≤s*delta+t*g-s*t := by
  by_cases ord : s≤g
  · have a := OrderedRing.mul_nonneg t0 (show 0≤g-s by grind only)
    have b := OrderedRing.mul_nonneg s0 d0; grind only
  · have a := OrderedRing.mul_nonneg (show 0≤7*delta-4*t by grind only) (show 0≤s-g by grind only)
    have b := OrderedRing.mul_nonneg (show 0≤3*g-2*s by grind only) d0
    have c := OrderedRing.mul_nonneg g0 d0; grind only

/-- Actual shifted payment at the upper-chart spectrum, retaining the entire unused anticommuting reserve. -/
theorem chartPayment (half inv24 third : F) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F) (orth : OrthonormalFrame A)
    (p : Inputs F) (c d : F) (chart : (fun i => (mu i)^2)=tail (spectrum p.h p.k p.q) c d)
    (cl : p.cl≤c) (cu : c≤p.ch) (du : d≤p.dh) (dl : p.dl≤d) (dl0 : 0≤p.dl)
    (cu1 : p.ch≤1) (ordered : d≤c) (cornerOrder : p.dl≤p.cl) (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q)
    (f0 : 0≤p.f) (f1 : p.f≤1) (u0 : 0≤p.u) (uc : 2*p.u≤3) (w0 : 0≤p.w) (wc : 4*p.w≤7) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    let x := PackingPolynomial.physicalWeights half h2 k A
    let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
    let s := (P p).shift
    let t := p.w*(H p).delta
    let retained := 2*reserve half A w w-sixCoefficient half third w*betaSix half A
    unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)+
      paid p c d*M.kappa+((P p).highQuad-(H p).anti)*M.kappaOne+retained≤frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let m := physicalPayment half h2 k A mu
  let x := PackingPolynomial.physicalWeights half h2 k A
  let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
  let U := W 1+W 2-referenceShared w
  let V := W 1-referencePair w
  let g := p.h*p.q
  let z := (H p).delta
  let s := (P p).shift
  let t := p.w*z
  let psi := actualReserve p.h p.q c d
  let six := SixModeProbe.sixWedge half h2 A
  let ret := 2*reserve half A w w-sixCoefficient half third w*betaSix half A
  let D := unshiftedDefects half inv24 k A mu
  let X := frameDefects half inv24 k A mu
  let Q := penalty psi p.f
  let hg := headReceipt half h2 k A mu s t
  have sort : SortedSpectrum w := by
    unfold w; rw [chart]; exact chartSorted p c d h0 k0 q0 ordered (Std.le_trans cu cu1) (Std.le_trans dl0 dl)
  have char := chartReserve p c d half third h2 h3
  rw [←chart] at char
  change spectralPsi half third w=psi ∧ sharedGap w=g ∧ leadingGap w=z ∧ tailGap w=c-d ∧ w 4=1 ∧ _ at char
  have rs := reserveBounds (h:=p.h) (q:=p.q) cl cu du dl dl0 cu1 ordered
  have pos : 0<psi := Std.lt_of_lt_of_le rs.1 rs.2
  have specPos : 0<spectralPsi half third w := char.1 ▸ pos
  have kap := physicalMomentOrder half h2 k A mu orth
  change 0≤m.cross ∧ m.cross≤m.kappa ∧ m.cross≤m.kappaOne ∧ 0≤m.emptyMass at kap
  have kg : 0≤m.kappa := Std.le_trans kap.1 kap.2.1
  have gp : 0≤g := OrderedRing.mul_nonneg h0 q0
  have zp : 0≤z := OrderedRing.mul_nonneg k0 (show 0≤p.h+p.k+p.q by grind only)
  have sh := physicalShiftAndPayment p c d cl cu du dl dl0 cu1 ordered cornerOrder gp f0 f1 u0 uc
  change _ ∧ 0≤s ∧ 2*s≤3*p.h*p.q ∧ _ ∧ paid p c d≤sourcePayment g s (alphaPrice p.f) psi p.f c d at sh
  have cap : 2*s≤3*g := by dsimp only [g]; grind only
  have hc := OrderedRing.mul_le_mul_of_nonneg_right wc zp
  have tp : 0≤t := OrderedRing.mul_nonneg w0 zp
  have tcap : 4*t≤7*z := by dsimp only [t]; grind only
  have crossN := OrderedRing.mul_nonneg (crossPayment sh.2.1 tp gp zp cap tcap) kap.1
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have rate : (11:F)*(200/11)=200 := capTimes (by grind only)
  have recpt := fullPenalty half inv24 third (200/11) h2 h24 h3 rate k A mu orth sort s t p.f sh.2.1 tp f1 specPos
  change D+hg+24*t*sharedGap w*m.cross+ret-24*s*((1-p.f)*tailGap w*(200/11)*m.kappa)+
    24*s*p.f*tailGap w*(3-six)-12*s^2*(quadraticPenalty half third w p.f-1)*m.kappa≤X at recpt
  have capEq : quadraticPenalty half third w p.f=Q := by
    unfold Q penalty quadraticPenalty
    rw [char.1,char.2.2.2.2.1]; have e : (1:F)^2=1 := by grind only
    rw [e,Semiring.mul_one]
  rw [char.2.1,char.2.2.2.1,capEq] at recpt
  have hgEq : hg=24*s*(U+g*m.kappa+z*m.cross+emptyGap w*m.emptyMass)+
      24*t*(V+z*m.kappaOne)-12*s^2*m.kappa-12*t^2*m.kappaOne-24*s*t*m.cross := by
    change 24*s*(U+sharedGap w*m.kappa+leadingGap w*m.cross+emptyGap w*m.emptyMass)+
      24*t*(V+leadingGap w*m.kappaOne)-12*s^2*m.kappa-12*t^2*m.kappaOne-24*s*t*m.cross=_
    rw [char.2.1,char.2.2.1]
  have empt : 0≤emptyGap w := by
    obtain ⟨a,b,j,l,o,y,z⟩ := sort
    exact OrderedRing.mul_nonneg (by grind only) (by grind only)
  have emp := OrderedRing.mul_nonneg sh.2.1 (OrderedRing.mul_nonneg empt kap.2.2.2)
  have sixN := SixPointRounding.physicalSixWedge half h2 k A orth
  change six≤3 at sixN
  have sixPay := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg sh.2.1 f0)
    (OrderedRing.mul_nonneg (show 0≤c-d by grind only) (show 0≤3-six by grind only))
  have paidBd := OrderedRing.mul_le_mul_of_nonneg_right sh.2.2.2.2 kg
  change paid p c d*m.kappa≤12*s*(2*(g-(1-p.f)*(200/11)*(c-d))-Q*s)*m.kappa at paidBd
  have price : ((P p).highQuad-(H p).anti)*m.kappaOne=12*t*(2*z-t)*m.kappaOne := by
    change (12*p.w*(2-p.w)*(z*z)+(H p).anti-(H p).anti)*m.kappaOne=_
    dsimp only [t]; grind only
  change D+24*s*U+24*t*V+paid p c d*m.kappa+((P p).highQuad-(H p).anti)*m.kappaOne+ret≤X
  rw [price]
  rw [hgEq] at recpt
  grind only

end Field

end RankSeven.PhysicalEndpointPauli

#print axioms RankSeven.PhysicalEndpointPauli.highestReverse
#print axioms RankSeven.PhysicalEndpointPauli.reverseReceipt
#print axioms RankSeven.PhysicalEndpointPauli.fullPenalty
#print axioms RankSeven.PhysicalEndpointPauli.chartPayment

