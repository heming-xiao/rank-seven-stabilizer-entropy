import Rank7PhysicalEndpointPrice
import Rank7LowerPhysicalGainScale
namespace RankSeven.LowerPhysicalPauliSlots
open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram PauliMatchingPrices WeightedProbeShift
open PhysicalTailBlend PauliReserveSlots EndpointReserveSlots LowerPhysicalGainScale
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalDefectAssembly (frameDefects)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sharedRetained (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (mu : Fin 7→R) (orth : OrthonormalFrame A) (w : Fin 7→R) :
    (gap w 0)^2*(gap w 2)^2*(physicalPayment half h2 k A mu).kappa≤sharedSlots half A w := by
  let h := gap w 0; let q := gap w 2
  let J (i j : Fin 7) := reserve half A (cut i) (cut j)
  let m := (physicalPayment half h2 k A mu).kappa
  have head := SharedTwoSlotReserve.physicalTwoSlots half h2 k A mu orth h q
  change h^2*q^2*m≤2*h^4*J 0 0+4*h^2*q^2*J 0 2+2*q^4*J 2 2 at head
  have pos (a b : Fin 7) : 0≤(gap w a)^2*(gap w b)^2*J a b :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)) (reserveNonnegative _ _ _ _)
  have a := pos 0 4; have b := pos 0 6; have c := pos 2 4; have d := pos 2 6
  change h^2*q^2*m≤2*(h^2*h^2*J 0 0+q^2*q^2*J 2 2+2*(h^2*q^2*J 0 2+h^2*(gap w 4)^2*J 0 4+
    h^2*(gap w 6)^2*J 0 6+q^2*(gap w 4)^2*J 2 4+q^2*(gap w 6)^2*J 2 6))
  dsimp only [h,q] at *; grind only

/-- Two unrestricted signed shifts on the actual sorted physical spectrum.
Retains the full required leading and shared reserves simultaneously. -/
theorem fullLeading (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R) (mu : Fin 7→R) (orth : OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) (s t f : R)
    (s0 : 0≤s) (t0 : 0≤t) (f0 : 0≤f) (f1 : f≤1)
    (sc : 2*s≤3*sharedGap (fun i => (mu i)^2)) (tc : 4*t≤7*leadingGap (fun i => (mu i)^2))
    (pos : 0<spectralPsi half third (fun i => (mu i)^2)) :
    let w := fun i => (mu i)^2
    let M := physicalPayment half h2 k A mu
    let x := PackingPolynomial.physicalWeights half h2 k A
    let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
    let g := sharedGap w; let d := leadingGap w
    let Q := quadraticPenalty half third w f
    unshiftedDefects half inv24 k A mu+24*s*(W 1+W 2-referenceShared w)+24*t*(W 1-referencePair w)+
      ((gap w 0)^2*(gap w 2)^2+12*s*(2*(g-(1-f)*(200/11)*tailGap w)-Q*s))*M.kappa+
      (12*t*(2*d-t)+leadingCoefficient half third w)*M.kappaOne≤frameDefects half inv24 k A mu := by
  let w := fun i => (mu i)^2
  let M := physicalPayment half h2 k A mu
  let x := PackingPolynomial.physicalWeights half h2 k A
  let W i := ProjectedProbeOverlap.weightedFourWedge 0 i w x
  let U := W 1+W 2-referenceShared w
  let V := W 1-referencePair w
  let g := sharedGap w; let d := leadingGap w; let e := tailGap w
  let Q := quadraticPenalty half third w f
  let E := emptyGap w
  let H := headReceipt half h2 k A mu s t
  let Res := 2*reserve half A w w-sixCoefficient half third w*betaSix half A
  let L := leadingCoefficient half third w
  let O := oddHigh half w
  let T := SixModeProbe.sixWedge half h2 A
  let D := unshiftedDefects half inv24 k A mu
  let P := frameDefects half inv24 k A mu
  have rate := UpperContractor.quotientEq (200:R) (show (0:R)<11 by have one := OrderedRing.zero_lt_one (R:=R); grind only)
  have receipt := PhysicalEndpointPauli.fullPenalty half inv24 third (200/11) h2 h24 h3 rate k A mu orth sort s t f s0 t0 f1 pos
  change D+H+24*t*g*M.cross+Res-24*s*((1-f)*e*(200/11)*M.kappa)+24*s*f*e*(3-T)-12*s^2*(Q-1)*M.kappa≤P at receipt
  have heq : H=24*s*(U+g*M.kappa+d*M.cross+E*M.emptyMass)+24*t*(V+d*M.kappaOne)-
      12*s^2*M.kappa-12*t^2*M.kappaOne-24*s*t*M.cross := rfl
  have slots := EndpointReserveSlots.physicalSlots half inv24 third h2 h24 h3 k A mu orth sort
  have sl : sharedSlots half A w+(L+O)*M.kappaOne≤Res := by change sharedSlots half A w+(L+O)*M.kappaOne+sixCoefficient half third w*betaSix half A≤2*reserve half A w w at slots; dsimp only [Res]; grind only
  have sh := sharedRetained half h2 k A mu orth w
  change (gap w 0)^2*(gap w 2)^2*M.kappa≤sharedSlots half A w at sh
  have kap := physicalMomentOrder half h2 k A mu orth
  change 0≤M.cross ∧ M.cross≤M.kappa ∧ M.cross≤M.kappaOne ∧ 0≤M.emptyMass at kap
  have cap := (SixPointRounding.physicalSixWedge half h2 k A orth)
  change T≤3 at cap
  obtain ⟨a,b,c,v,y,z,_⟩ := sort
  have gp : 0≤g := by change 0≤(w 0-w 1)*(w 2-w 3); apply OrderedRing.mul_nonneg <;> grind only
  have dp : 0≤d := by change 0≤(w 1-w 2)*(w 0-w 3); apply OrderedRing.mul_nonneg <;> grind only
  have ep : 0≤E := by change 0≤(w 1-w 5)*(w 2-w 4); apply OrderedRing.mul_nonneg <;> grind only
  have tp : 0≤e := by change 0≤w 4*(w 5-w 6); exact OrderedRing.mul_nonneg (squareNonnegative _) (by grind only)
  have cross := OrderedRing.mul_nonneg (PhysicalEndpointPauli.crossPayment s0 t0 gp dp sc tc) kap.1
  have emp := OrderedRing.mul_nonneg s0 (OrderedRing.mul_nonneg ep kap.2.2.2)
  have sixPay := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg s0 f0)
    (OrderedRing.mul_nonneg tp (show 0≤3-T by grind only))
  have odd : 0≤O := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (by grind only) (squareNonnegative _))
    (show 0≤(gap w 4)^2+(gap w 6)^2 by have := squareNonnegative (gap w 4); have := squareNonnegative (gap w 6); grind only)
  have high := OrderedRing.mul_nonneg odd (Std.le_trans kap.1 kap.2.2.1)
  change D+24*s*U+24*t*V+((gap w 0)^2*(gap w 2)^2+12*s*(2*(g-(1-f)*(200/11)*e)-Q*s))*M.kappa+
    (12*t*(2*d-t)+L)*M.kappaOne≤P
  rw [heq] at receipt
  grind only

end RankSeven.LowerPhysicalPauliSlots
#print axioms RankSeven.LowerPhysicalPauliSlots.fullLeading