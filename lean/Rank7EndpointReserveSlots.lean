import Rank7PhysicalEndpointPauli

namespace RankSeven.EndpointReserveSlots

open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram WeightedProbeShift PauliReserveSlots
open PhysicalTailBlend OddCutReserve
open PhysicalCompressionEffect (OrthonormalFrame)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

attribute [local instance] Semiring.natCast

/-- Available P₁/P₃ diagonal block and its connections to the two odd tail projections. -/
def sharedSlots {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (w : Fin 7 → R) : R :=
  let g := gap w
  let J r t := reserve half A (cut r) (cut t)
  let X r t := (g r)^2*(g t)^2*J r t
  2*(X 0 0+X 2 2+2*(X 0 2+X 0 4+X 0 6+X 2 4+X 2 6))

def oddHigh (half : R) (w : Fin 7 → R) := half*(gap w 1)^2*((gap w 4)^2+(gap w 6)^2)

private def used : List (Fin 7×Fin 7) :=
  [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,4),(1,6),(2,0),(2,1),(2,2),(2,4),(2,5),(2,6),(4,0),(4,1),(4,2),(4,5),(5,0),(5,2),(5,4),(5,5),(5,6),(6,0),(6,1),(6,2),(6,5)]

private theorem selectedSlots (X : Fin 7 → Fin 7 → R) (sym : ∀ i j,X j i=X i j) (pos : ∀ i j,0≤X i j) :
    X 1 1+X 5 5+X 0 0+X 2 2+2*(X 1 0+X 1 2+X 5 0+X 5 2+X 5 4+X 5 6+
      X 1 4+X 1 6+X 0 2+X 0 4+X 0 6+X 2 4+X 2 6)≤
    sumOver labels (fun i => sumOver labels (X i)) := by
  let es := labels.flatMap (fun i => labels.map (fun j => (i,j)))
  let f (e : Fin 7×Fin 7) := X e.1 e.2
  have eq : es.filter used.contains=used := by decide
  have filt (xs : List (Fin 7×Fin 7)) : sumOver (xs.filter used.contains) f≤sumOver xs f := by
    induction xs with
    | nil => exact Std.le_refl _
    | cons a xs ih =>
      rw [List.filter_cons]; split
      · change f a+sumOver (xs.filter _) f≤f a+sumOver xs f; grind only
      · change sumOver (xs.filter _) f≤f a+sumOver xs f; have h : 0≤f a := pos _ _; grind only
  have bound := filt es; rw [eq] at bound
  have all : sumOver es f=sumOver labels (fun i => sumOver labels (X i)) := by
    rw [show es=labels.flatMap (fun i => labels.map (fun j => (i,j))) by rfl,sumOverFlatMap]
    apply sumOverCongr; intro i; simp only [sumOver,List.map_map,Function.comp_def,f]
  rw [all] at bound
  simp only [used,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,f] at bound
  have s1 := sym 1 0; have s2 := sym 1 2; have s3 := sym 5 0; have s4 := sym 5 2
  have s5 := sym 5 4; have s6 := sym 5 6
  have a1 := sym 1 4; have a2 := sym 1 6; have a3 := sym 0 2; have a4 := sym 0 4
  have a5 := sym 0 6; have a6 := sym 2 4; have a7 := sym 2 6
  change _≤(labels.map (fun i => (labels.map (X i)).sum)).sum
  grind only

theorem physicalSlots (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : PauliMatchingPrices.SortedSpectrum (fun i => (mu i)^2))
    :
    let w := fun i => (mu i)^2
    let K := (physicalPayment half h2 k A mu).kappaOne
    sharedSlots half A w+(leadingCoefficient half third w+oddHigh half w)*K+
      sixCoefficient half third w*betaSix half A≤2*reserve half A w w := by
  have one := firstPairLeakage A orth
  obtain ⟨three,five,seven⟩ := PhysicalOddLeakage.physicalOddCuts A orth
  let t := fun i => (mu i)^2
  let g := gap t
  let J r s := reserve half A (cut r) (cut s)
  let X r s := (g r)^2*(g s)^2*J r s
  let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne
  let z := densityCoordinates half A (cut 5)
  let B := 2*hs (MixedDefect.oddWords (k+3)) z z
  have j (r s : Fin 7) : J s r=J r s := reserveSwap half A (cut s) (cut r)
  have sym (r s : Fin 7) : X s r=X r s := by dsimp only [X]; rw [j r s]; grind only
  have pos (r s : Fin 7) : 0≤X r s := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)) (reserveNonnegative _ _ _ _)
  have all : sumOver labels (fun i => sumOver labels (X i))≤reserve half A t t := allCutSlots half A orth t sorted
  have slots := Std.le_trans (selectedSlots X sym pos) all
  have hk : K≤2*J 1 1 := ReserveMixedNorm.highestPairReserve half inv24 third h2 h24 h3 k A mu orth
  have hb := ReserveMixedNorm.spectralCutReserve half inv24 h2 h24 k A 5 orth
  change hs (MixedDefect.oddWords (k+3)) z z≤J 5 5 at hb
  have bnd : B≤2*J 5 5 := by unfold B; grind only
  have c1 (i : Fin 7) (l : PairLeakage A i) : K≤8*J 1 i := by
    have e := crossReserve half A orth 1 i l
    change J 1 1≤2*(Nat.cast (1+1):R)*J 1 i at e
    simp only [Semiring.natCast_add,Semiring.natCast_one] at e; grind only
  have c6 (i : Fin 7) (l : PairLeakage A i) : B≤24*J 5 i := by
    have e := crossReserve half A orth 5 i l
    change J 5 5≤2*(Nat.cast (5+1):R)*J 5 i at e
    have five' : (Nat.cast 5:R)=5 := by grind only
    simp only [Semiring.natCast_add,Semiring.natCast_one,five'] at e; grind only
  have mult (i j : Fin 7) (a b : R) (ord : a≤b) :
      (g i)^2*(g j)^2*a≤(g i)^2*(g j)^2*b :=
    OrderedRing.mul_le_mul_of_nonneg_left ord (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _))
  have q0 := mult 1 1 _ _ hk
  have q1 := mult 5 5 _ _ bnd
  have q2 := mult 1 0 _ _ (c1 0 one)
  have q3 := mult 1 2 _ _ (c1 2 three)
  have q4 := mult 5 0 _ _ (c6 0 one)
  have q5 := mult 5 2 _ _ (c6 2 three)
  have q6 := mult 5 4 _ _ (c6 4 five)
  have q7 := mult 5 6 _ _ (c6 6 seven)
  dsimp only [X] at slots
  have highFive := mult 1 4 _ _ (c1 4 five)
  have highSeven := mult 1 6 _ _ (c1 6 seven)
  let c := 6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2)
  let d := (g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)
  let e := (g 1)^2*((g 4)^2+(g 6)^2)
  let v := sharedSlots half A t
  have cleared : 6*v+(c+3*e)*K+d*B≤12*reserve half A t t := by
    dsimp only [v,sharedSlots,c,d,e]
    change 6*(2*((g 0)^2*(g 0)^2*J 0 0+(g 2)^2*(g 2)^2*J 2 2+
      2*((g 0)^2*(g 2)^2*J 0 2+(g 0)^2*(g 4)^2*J 0 4+(g 0)^2*(g 6)^2*J 0 6+
         (g 2)^2*(g 4)^2*J 2 4+(g 2)^2*(g 6)^2*J 2 6)))+_+_≤_
    grind only
  have unit := congrArg (fun z => z*(3*third)) h2
  have norm : 6*(half*third)=1 := by grind only
  have scaled := OrderedRing.mul_le_mul_of_nonneg_left cleared
    (OrderedRing.mul_nonneg (show 0≤half by grind only) (show 0≤third by grind only))
  change v+(half*third*c+half*(g 1)^2*((g 4)^2+(g 6)^2))*K+half*third*d*B≤2*reserve half A t t
  change half*third*(6*v+(c+3*e)*K+d*B)≤half*third*(12*reserve half A t t) at scaled
  have id (x : R) : 6*(half*third)*x=x := by rw [norm,Semiring.one_mul]
  have id3 (x : R) : 3*third*x=x := by rw [h3,Semiring.one_mul]
  have a := id v; have b := id (reserve half A t t); have m := id3 (half*e*K)
  dsimp only [e] at m scaled
  grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]
open UpperEndpoint UpperEndpointPrices
open UpperFrameGain (tail)
open UpperPhysicalInterior (spectrum)
open PhysicalDefectAssembly (frameDefects)

private theorem clearDen (a : F) {b : F} (pos : 0<b) : b*(a/b)=a := by
  have u := Field.mul_inv_cancel (show b≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

theorem chartOddHigh (half : F) (h2 : 2*half=1) (p : Inputs F) (c d wh ws : F)
    (cu : c≤p.ch) (dl : p.dl≤d) (dl0 : 0≤p.dl) (ch1 : p.ch≤1) :
    let w := tail (spectrum p.h p.k p.q) c d
    0≤(K p wh ws c d).odd ∧ (K p wh ws c d).odd*(H p).k2/2≤oddHigh half w := by
  have p1 := OrderedRing.mul_nonneg (show 0≤1-p.ch by grind only) (show 0≤1+p.ch-2*c by grind only)
  have p2 := OrderedRing.mul_nonneg dl0 (show 0≤2*d-p.dl by grind only)
  let a := (K p wh ws c d).odd
  have id : a=(1-p.ch)*(1+p.ch-2*c)+p.dl*(2*d-p.dl) := rfl
  have a0 : 0≤a := by grind only
  have lo := squareNonnegative (c-p.ch); have hi := squareNonnegative (d-p.dl)
  have sub : a≤(1-c)^2+d^2 := by grind only
  have h := OrderedRing.mul_le_mul_of_nonneg_left sub (OrderedRing.mul_nonneg (show 0≤half by grind only) (squareNonnegative p.k))
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have div := clearDen (a*(p.k*p.k)) (b:=2) (by grind only)
  have eg : a*(p.k*p.k)/2=half*p.k^2*a := by
    have h := congrArg (fun z => z*(a*p.k^2)) h2; grind only
  refine ⟨a0,?_⟩
  change a*(p.k*p.k)/2≤_; rw [eg]
  unfold oddHigh gap tail spectrum
  simp (config := {decide:=true}) only [↓reduceIte,Fin.isValue]
  grind only

/-- The complete checker highest coefficient and its odd tangent come from the same physical frame.
The still available shared slots and the shared mixed shift are recorded separately. -/
theorem chartHighestPaid (half inv24 third : F) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
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
    unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)+
      paid p c d*M.kappa+((P p).highQuad+(K p wh ws c d).odd*(H p).k2/2)*M.kappaOne+
      sharedSlots half A w≤frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let x := PackingPolynomial.physicalWeights half h2 k A
  let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
  let s := (P p).shift
  let t := p.w*(H p).delta
  let S := unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)
  let D := frameDefects half inv24 k A mu
  have sort : PauliMatchingPrices.SortedSpectrum w := by
    unfold w; rw [chart]; exact PhysicalEndpointPauli.chartSorted p c d h0 k0 q0 ordered (Std.le_trans cu cu1) (Std.le_trans dl0 dl)
  have charted := PhysicalEndpointPauli.chartPayment half inv24 third h2 h24 h3 k A mu orth p c d chart cl cu du dl dl0 cu1 ordered cornerOrder h0 k0 q0 f0 f1 u0 uc w0 wc
  change S+paid p c d*M.kappa+((P p).highQuad-(H p).anti)*M.kappaOne+
    (2*reserve half A w w-sixCoefficient half third w*betaSix half A)≤D at charted
  have raw := physicalSlots half inv24 third h2 h24 h3 k A mu orth sort
  change sharedSlots half A w+(leadingCoefficient half third w+oddHigh half w)*M.kappaOne+
    sixCoefficient half third w*betaSix half A≤2*reserve half A w w at raw
  have e := (PhysicalEndpointPauli.chartReserve p c d half third h2 h3).2.2.2.2.2
  rw [←chart] at e
  change leadingCoefficient half third w=(H p).anti at e
  rw [e] at raw
  have tan := (chartOddHigh half h2 p c d wh ws cu dl dl0 cu1).2
  rw [←chart] at tan
  have kg := physicalMomentOrder half h2 k A mu orth
  change 0≤M.cross ∧ _ ∧ M.cross≤M.kappaOne ∧ _ at kg
  have h := OrderedRing.mul_le_mul_of_nonneg_right tan (Std.le_trans kg.1 kg.2.2.1)
  change ((K p wh ws c d).odd*(H p).k2/2)*M.kappaOne≤oddHigh half w*M.kappaOne at h
  change S+paid p c d*M.kappa+((P p).highQuad+(K p wh ws c d).odd*(H p).k2/2)*M.kappaOne+sharedSlots half A w≤D
  grind only

end Field

end RankSeven.EndpointReserveSlots

#print axioms RankSeven.EndpointReserveSlots.physicalSlots
#print axioms RankSeven.EndpointReserveSlots.chartOddHigh
#print axioms RankSeven.EndpointReserveSlots.chartHighestPaid

