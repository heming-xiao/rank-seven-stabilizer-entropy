import Rank7PhysicalEndpointReserve
import Rank7UpperFrameTrace

namespace RankSeven.PhysicalEndpointPrice

open Lean.Grind Pauli ComplexScalar ExteriorCuts PackingDual PackingInterpolation
open ProjectedProbeOverlap (complementaryPair complementaryWeight weightedFourWedge)
open UpperFrameGain (tail weightedProbe)
open UpperPhysicalInterior (spectrum trueRay)
open UpperEndpoint UpperEndpointPrices UpperFrameTrace
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
open JointProbeGram (referencePair referenceShared)
open PhysicalDefectAssembly (frameDefects)
open PhysicalTailBlend (unshiftedDefects)
variable {R : Type} [CommRing R]

private theorem masked (s : Fin 7 → R) (c d : R) (i j : Fin 7) (hi : i=1∨i=2) :
    tail (UpperFrameGain.pairSpectrum s i) c d j=
      if j=0∨j=i then 1 else tail s c d j := by
  unfold tail UpperFrameGain.pairSpectrum
  by_cases h : j=5 <;> by_cases k : j=6 <;> by_cases p : j=0∨j=i <;> simp [h,k,p] <;> omega

private theorem wedgeId (s : Fin 7 → R) (c d : R) (i : Fin 7) (hi : i=1∨i=2) (w : Wedge7) :
    (if occupied w 0 && occupied w i then amplitude (tail (UpperFrameGain.pairSpectrum s i) c d) w else 0)=
      complementaryWeight 0 i (tail s c d) w := by
  rcases w with ⟨a,b,e,f,ab,be,ef⟩
  have nz : i≠0 := by omega
  have bn : b≠0 := by omega
  have en : e≠0 := by omega
  have fnm : f≠0 := by omega
  unfold occupied amplitude product4 complementaryWeight complementaryPair
  simp only [masked _ _ _ _ _ hi]
  by_cases a0 : a=0
  · subst a
    by_cases bi : b=i
    · have ei : e≠i := by omega
      have fi : f≠i := by omega
      simp [bi,ei,fi,en,fnm,nz,Ne.symm nz] <;> grind only
    · by_cases ei : e=i
      · have fi : f≠i := by omega
        simp [bi,ei,fi,bn,fnm,nz,Ne.symm nz] <;> grind only
      · by_cases fi : f=i <;> simp [bi,ei,fi,bn,en,fnm,nz,Ne.symm nz] <;> grind only
  · simp [a0,bn,en,fnm] <;> grind only

private def selected (i : Fin 7) (w : Wedge7) := (occupied w 0 && occupied w i) && SectorDefectAccounting.planeFlag w
private def q0123 : Wedge7 := ⟨0,1,2,3,by decide,by decide,by decide⟩
private def q0145 : Wedge7 := ⟨0,1,4,5,by decide,by decide,by decide⟩
private def q0246 : Wedge7 := ⟨0,2,4,6,by decide,by decide,by decide⟩

private theorem ref (s : Fin 7 → R) (c d : R) (i : Fin 7) :
    evaluate referenceWeight (fun w => if occupied w 0 && occupied w i then amplitude (tail (UpperFrameGain.pairSpectrum s i) c d) w else 0)=
    sumOver (wedges.filter (selected i)) (amplitude (tail (UpperFrameGain.pairSpectrum s i) c d)) := by
  let f := amplitude (tail (UpperFrameGain.pairSpectrum s i) c d)
  have eq (w : Wedge7) : (if occupied w 0 && occupied w i then f w else 0)*referenceWeight w=(if selected i w then f w else 0) := by
    unfold selected referenceWeight
    cases occupied w 0 && occupied w i <;> cases SectorDefectAccounting.planeFlag w <;> simp <;> grind only
  unfold evaluate
  change sumOver wedges (fun w => (if occupied w 0 && occupied w i then f w else 0)*referenceWeight w)=_
  rw [sumOverCongr _ eq]
  have filt (ls : List Wedge7) : sumOver ls (fun w => if selected i w then f w else 0)=sumOver (ls.filter (selected i)) f := by
    induction ls with
    | nil => rfl
    | cons a ls ih =>
      change (if selected i a then f a else 0)+sumOver ls _=_
      rw [List.filter_cons]
      cases take : selected i a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · rw [ih]; grind only
      · change f a+_=f a+_; rw [ih]; rfl
  exact filt wedges

theorem weightedChartProbes (s : Fin 7 → R) (x : Wedge7 → R) (c d : R) :
    let w := tail s c d
    let W j := weightedFourWedge 0 j w x
    weightedProbe s x 1 c d=W 1-referencePair w ∧
      weightedProbe s x 1 c d+weightedProbe s x 2 c d=W 1+W 2-referenceShared w := by
  let w := tail s c d
  let W j := weightedFourWedge 0 j w x
  have eq (i : Fin 7) (hi : i=1∨i=2) :
      weightedProbe s x i c d=W i-sumOver (wedges.filter (selected i)) (amplitude (tail (UpperFrameGain.pairSpectrum s i) c d)) := by
    unfold weightedProbe gain
    rw [ref]; apply congrArg (fun z => z-_)
    unfold evaluate W weightedFourWedge
    apply sumOverCongr; intro v; exact congrArg (fun y => y*x v) (wedgeId s c d i hi v)
  have hs := eq 1 (Or.inl rfl); have ht := eq 2 (Or.inr rfl)
  have f1 : wedges.filter (selected 1)=[q0123,q0145] := by decide
  have f2 : wedges.filter (selected 2)=[q0123,q0246] := by decide
  rw [f1] at hs; rw [f2] at ht
  simp (config:={decide:=true}) only [q0123,q0145,q0246,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    amplitude,product4,tail,UpperFrameGain.pairSpectrum,↓reduceIte,Semiring.one_mul,Semiring.mul_one,Semiring.add_zero] at hs ht
  change weightedProbe s x 1 c d=W 1-referencePair w ∧ weightedProbe s x 1 c d+weightedProbe s x 2 c d=W 1+W 2-referenceShared w
  simp (config:={decide:=true}) only [referencePair,referenceShared,w,tail,↓reduceIte]
  grind only

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

private theorem denominator (a : F) {b : F} (hp : 0<b) : b*(a/b)=a := by
  have h := Field.mul_inv_cancel (show b≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

private theorem positiveQuot {a b : F} (ap : 0<a) (bp : 0<b) : 0<a/b := by
  have t := denominator a bp
  by_cases h : 0<a/b
  · exact h
  · have z := OrderedRing.mul_le_mul_of_nonneg_left (show a/b≤0 by grind only) (Std.le_of_lt bp)
    grind only

private theorem nonnegQuot {a b : F} (ap : 0≤a) (bp : 0<b) : 0≤a/b := by
  have t := denominator a bp
  by_cases h : 0≤a/b
  · exact h
  · have z := OrderedRing.mul_pos bp (show 0< -(a/b) by grind only); grind only

/-- The literal replay price on the actual leading ray. Its two geometric premises are
the shared-anchor and highest-pair conversion of the same frame's signed-probe Grams. -/
theorem physicalPriceOnFrame (half inv24 third : F) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F) (mu : Fin 7 → F) (orth : OrthonormalFrame A)
    (p : Inputs F) (wh ws c d : F) (chart : (fun i => (mu i)^2)=tail (spectrum p.h p.k p.q) c d)
    (cl : p.cl≤c) (cu : c≤p.ch) (du : d≤p.dh) (dl : p.dl≤d) (dl0 : 0≤p.dl)
    (cu1 : p.ch≤1) (ordered : d≤c) (cornerOrder : p.dl≤p.cl) (h0 : 0≤p.h) (k0 : 0≤p.k) (q0 : 0≤p.q)
    (f0 : 0≤p.f) (f1 : p.f≤1) (u0 : 0≤p.u) (uc : 2*p.u≤3) (w0 : 0≤p.w) (wc : 4*p.w≤7)
    (sharedGeometry : let x := PackingPolynomial.physicalWeights half h2 k A
      (trueRay (sharedExcess x) (highExcess x) 0 0).peak≤12*(physicalPayment half h2 k A mu).kappa)
    (highGeometry : 2*highExcess (PackingPolynomial.physicalWeights half h2 k A)≤5*(physicalPayment half h2 k A mu).kappaOne)
    (traceOne traceShared : F) :
    let x := PackingPolynomial.physicalWeights half h2 k A
    let head := spectrum p.h p.k p.q
    let U i := weightedProbe head x i c d
    let ray := trueRay (sharedExcess x) (highExcess x) traceOne traceShared
    let K := UpperEndpointPrices.K p wh ws c d
    physicalPrice p wh ws c d ray+(P p).lambda*(U 1+U 2)+UpperPhysicalInterior.mu p*U 1≤
      invRate*(frameDefects half inv24 k A mu-unshiftedDefects half inv24 k A mu)+
        96*invRate*(K.one*traceOne+K.shared*traceShared) := by
  let x := PackingPolynomial.physicalWeights half h2 k A
  let head := spectrum p.h p.k p.q
  let U i := weightedProbe head x i c d
  let n := sharedExcess x
  let v := highExcess x
  let peak := (trueRay n v 0 0).peak
  let w := fun i => (mu i)^2
  let W i := weightedFourWedge 0 i w x
  let m := physicalPayment half h2 k A mu
  let s := (P p).shift
  let t := p.w*(H p).delta
  let g := (H p).g2
  let den := (H p).oddDen
  let odd := (K p wh ws c d).odd
  let S := g+paid p c d+odd*g/den
  let Q := (P p).highQuad+odd*(H p).k2/2
  let D := frameDefects half inv24 k A mu-unshiftedDefects half inv24 k A mu
  let extra := 96*invRate*((K p wh ws c d).one*traceOne+(K p wh ws c d).shared*traceShared)
  let j := invRate (R:=F)
  let l := invGeom (R:=F)
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have two : (0:F)<2 := by grind only
  have jr : 0<j := positiveQuot one (positiveQuot (by grind only) (by grind only))
  have lg : 0<l := positiveQuot one (positiveQuot (by grind only) two)
  have li : (5/2:F)*l=1 := denominator 1 (positiveQuot (by grind only) two)
  have h52 := denominator (5:F) two
  have r2 := congrArg (fun z => z*l) h52
  have r3 := congrArg (fun z : F => 2*z) li
  have gl : 5*l=2 := by grind only
  have oddN : 0≤odd := (EndpointReserveSlots.chartOddHigh half h2 p c d wh ws cu dl dl0 cu1).1
  have gN : 0≤g := by change 0≤(p.h*p.q)*(p.h*p.q); have := squareNonnegative (p.h*p.q); grind only
  have dd : den=p.h^2+3*p.q^2 := by change p.h*p.h+3*(p.q*p.q)=_; grind only
  have nnq := squareNonnegative p.q; have nnh := squareNonnegative p.h; have nnk := squareNonnegative p.k
  have oddSharedN : 0≤odd*g/den := by
    by_cases hp : 0<den
    · exact nonnegQuot (OrderedRing.mul_nonneg oddN gN) hp
    · have hh : p.h^2=0 := by grind only
      have z : g=0 := by change (p.h*p.q)*(p.h*p.q)=0; have b := congrArg (fun z => z*p.q^2) hh; grind only
      rw [z,Field.div_eq_mul_inv]; grind only
  have pbd := physicalShiftAndPayment p c d cl cu du dl dl0 cu1 ordered cornerOrder (OrderedRing.mul_nonneg h0 q0) f0 f1 u0 uc
  have pd : 0≤paid p c d := pbd.2.2.2.1
  have SN : 0≤S := by unfold S; grind only
  have headK : (H p).k2=p.k^2 := by change p.k*p.k=_; grind only
  have hp := nonnegQuot (show 0≤p.h*p.h+p.q*p.q by grind only) two
  have panti := OrderedRing.mul_nonneg nnk (show 0≤p.k^2+(p.h*p.h+p.q*p.q)/2 by grind only)
  have anti : 0≤(H p).anti := by change 0≤p.k*p.k*(p.k*p.k+(p.h*p.h+p.q*p.q)/2); grind only
  have hqw := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg w0 (show 0≤2-p.w by grind only)) (squareNonnegative (H p).delta)
  have highN : 0≤(P p).highQuad := by
    change 0≤12*p.w*(2-p.w)*((H p).delta*(H p).delta)+(H p).anti; grind only
  have od := nonnegQuot (OrderedRing.mul_nonneg oddN (show 0≤(H p).k2 by rw [headK]; exact nnk)) two
  have QN : 0≤Q := by unfold Q; grind only
  have pr := PhysicalEndpointReserve.chartPauliRemainder half inv24 third h2 h24 h3 k A mu orth p wh ws c d chart cl cu du dl dl0 cu1 ordered cornerOrder h0 k0 q0 f0 f1 u0 uc w0 wc
  have wedges := weightedChartProbes head x c d
  change U 1=weightedFourWedge 0 1 (tail head c d) x-referencePair (tail head c d) ∧
    U 1+U 2=weightedFourWedge 0 1 (tail head c d) x+weightedFourWedge 0 2 (tail head c d) x-referenceShared (tail head c d) at wedges
  change w=tail head c d at chart
  rw [←chart] at wedges
  change U 1=W 1-referencePair w ∧ U 1+U 2=W 1+W 2-referenceShared w at wedges
  change unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)+S*m.kappa+Q*m.kappaOne≤frameDefects half inv24 k A mu at pr
  rw [←wedges.1,←wedges.2] at pr
  have actual : 24*s*(U 1+U 2)+24*t*U 1+S*m.kappa+Q*m.kappaOne≤D := by unfold D; grind only
  change peak≤12*m.kappa at sharedGeometry
  change 2*v≤5*m.kappaOne at highGeometry
  let sPrice := (B p wh ws c d).physicalShared
  let qPrice := (B p wh ws c d).physicalHigh
  have a1 : 12*sPrice=S*j := by
    have id : sPrice=S*j/12 := by
      change ((g+(P p).sharedQuad+24*s*(H p).tax*(p.ch-p.dl-(c-d))+odd*g/den)*j)/12=_
      unfold S paid; apply congrArg (fun y => y*j/12); grind only
    rw [id]; exact denominator _ (by grind only)
  have a2 : qPrice=Q*j*l := rfl
  have spos : 0≤sPrice := by
    have n := OrderedRing.mul_nonneg SN (Std.le_of_lt jr); grind only
  have sBound := OrderedRing.mul_le_mul_of_nonneg_left sharedGeometry spos
  have unit := congrArg (fun z => z*m.kappa) a1
  have qBound := OrderedRing.mul_le_mul_of_nonneg_left highGeometry
    (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg QN (Std.le_of_lt jr)) (Std.le_of_lt lg))
  have geom := congrArg (fun z => z*(Q*j*m.kappaOne)) gl
  have scales := OrderedRing.mul_le_mul_of_nonneg_left actual (Std.le_of_lt jr)
  have chi : UpperPhysicalInterior.mu p=24*j*t := by
    change (H p).delta-((H p).delta-24*j*p.w*(H p).delta)=_; unfold t; grind only
  change sPrice*peak+qPrice*v+extra+(24*j*s)*(U 1+U 2)+UpperPhysicalInterior.mu p*U 1≤j*D+extra
  rw [chi,a2]; grind only

end Field

end RankSeven.PhysicalEndpointPrice

#print axioms RankSeven.PhysicalEndpointPrice.weightedChartProbes
#print axioms RankSeven.PhysicalEndpointPrice.physicalPriceOnFrame

