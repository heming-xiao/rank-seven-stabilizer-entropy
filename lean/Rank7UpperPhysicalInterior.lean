import Rank7UpperFrameGain
import Rank7UpperRayGeometry

/-! The real upper corner implication for the same physical seven-frame.
The only exterior estimates used are the two signed corner bounds. -/
namespace RankSeven.UpperPhysicalInterior
open Lean.Grind Interval UpperEndpoint UpperEndpointPrices UpperInterior UpperFrameGain UpperContractor
open ExteriorCuts (Wedge7)
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def spectrum (h k q : R) (i : Fin 7) : R :=
  if i=0 then 1+(h+k+q) else if i=1 then 1+(k+q) else if i=2 then 1+q else 1

noncomputable abbrev mu (p : Inputs R) := (H p).delta-(P p).residual
noncomputable def cross (p : Inputs R) : R := 96*invRate*((1+p.q)*p.h/2)

def TailRectangle (box : UpperCorner.TailBox) : Prop :=
  0≤box.d.lo ∧ box.c.hi≤cppGrid.scale

def OrderedCorner (_p : Inputs R) (c d : R) : Prop := 0≤d ∧ d≤c ∧ c≤1

noncomputable def trueRay (n v t₁ tₛ : R) := rayFrom realArithmetic n v t₁ tₛ

/-- The two signed estimates required at each ordered corner of the upper
tie. The lower grid support weights do not enter either exterior estimate. -/
def ExteriorEstimates (p : Inputs R) (x : Wedge7→R) (n v : R) : Prop :=
  ∀ i j : Bool,OrderedCorner p (cAt p i) (dAt p j) →
    let c := cAt p i
    let d := dAt p j
    let F := corrected (spectrum p.h p.k p.q) x (P p).lambda (mu p) (cross p) c d
    let r := trueRay n v 0 0
    F≤splitBound p 0 0 c d r ∧ F≤singleBound p 0 0 c d r

private theorem rPrice (p : Inputs R) (wh ws c d : R) (r : RayData R) (v t₁ tₛ : R)
    (n : R) (ge : UpperRayGeometry.Geometry r) (nr : r.n=n) (vr : r.v=v)
    (high : r.traceOne≤t₁) (shared : r.traceShared≤tₛ)
    (hn : 0≤(K p wh ws c d).one) (sn : 0≤(K p wh ws c d).shared) :
    physicalPrice p wh ws c d r≤physicalPrice p wh ws c d (trueRay n v t₁ tₛ) := by
  let t := trueRay n v t₁ tₛ
  have peak : r.peak=t.peak := by rw [ge.2.1,nr,vr]; rfl
  have hv : r.v=t.v := vr
  have h := OrderedRing.mul_le_mul_of_nonneg_left high hn
  have s := OrderedRing.mul_le_mul_of_nonneg_left shared sn
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have a := UpperContractor.quotientEq (4242:R) (by grind only : (0:R)<25)
  have rate : 0≤(invRate (R:=R)) := by
    have d : (0:R)<4242/25 := by grind only
    have eq := UpperContractor.quotientEq (1:R) d
    by_cases pos : 0≤(invRate (R:=R))
    · exact pos
    · have bad := OrderedRing.mul_le_mul_of_nonneg_left (show (invRate (R:=R))≤0 by grind only) (Std.le_of_lt d)
      change (4242/25:R)*(1/(4242/25:R))≤(4242/25:R)*0 at bad; grind only
  have costs := OrderedRing.mul_le_mul_of_nonneg_left (show
      (K p wh ws c d).one*r.traceOne+(K p wh ws c d).shared*r.traceShared≤
      (K p wh ws c d).one*t₁+(K p wh ws c d).shared*tₛ by grind only)
    (show 0≤96*(invRate (R:=R)) by grind only)
  change (B p wh ws c d).physicalShared*r.peak+(B p wh ws c d).physicalHigh*r.v+_≤
    (B p wh ws c d).physicalShared*t.peak+(B p wh ws c d).physicalHigh*t.v+_
  have plus (x y z : R) (hxy : x≤y) : z+x≤z+y := by grind only
  rw [peak,hv]; exact plus _ _ _ costs

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem boundsAtActual (p : Inputs R) (wh ws c d : R) (r : RayData R) (n v : R)
    (ge : UpperRayGeometry.Geometry r) (nr : r.n=n) (vr : r.v=v) :
    splitBound p wh ws c d r=splitBound p 0 0 c d (trueRay n v 0 0) ∧
    singleBound p wh ws c d r=singleBound p 0 0 c d (trueRay n v 0 0) := by
  let t := trueRay n v 0 0
  have hm : r.m=t.m := by rw [ge.1,nr,vr]; rfl
  have hc : r.constant=t.constant := by rw [ge.2.2.1,nr,vr]; rfl
  have hj : r.improvement=t.improvement := by rw [ge.2.2.2.1,nr,vr,hm]; rfl
  have ht : r.tail=t.tail := by rw [ge.2.2.2.2,nr,vr]; rfl
  have hN : r.n=t.n := nr
  have hV : r.v=t.v := vr
  unfold splitBound singleBound; rw [hN,hV,hm,hc,hj,ht]; exact ⟨rfl,rfl⟩

def Witnesses (box : UpperCorner.TailBox) : Prop := ∀ j : Fin 6,∃ s∈UpperReplay.shifts,∃ rows,
  UpperCorner.margins box s=some rows ∧ UpperReplay.sectorPass rows j=true

private theorem orderedBox {box : UpperCorner.TailBox} {s : UpperCorner.Shifts} {rows}
    (pass : UpperCorner.margins box s=some rows) : box.d.hi≤box.c.lo := by
  rw [originalMargins] at pass; unfold preparedMargins at pass; split at pass <;> first | contradiction | omega

/-- A successful positive-excess branch gives an interior comparison for the
actual wedge polynomial and the genuine geometric and trace data. -/
theorem frameInterior {box : UpperCorner.TailBox} {h k q c d n v t₁ tₛ : R} (x : Wedge7→R)
    (inside : Inside cppGrid box h k q c d) (domain : TailRectangle box) (rows : Witnesses box)
    (h0 : 0≤h) (k0 : 0≤k) (q0 : 0≤q)
    (n0 : 0≤n) (v0 : 0≤v) (positive : 0<n+v) (nc : 2*n≤1) (vc : 3*v≤1)
    (highestTrace : v*(1-v)≤t₁) (sharedTrace : n*(1-n)≤tₛ)
    (exterior : ∀ f u w : R,ShiftValues f u w → ExteriorEstimates (realInputs box h k q f u w) x n v) :
    ∃ f u w wh ws : R,
      let p := realInputs box h k q f u w
      ShiftValues f u w ∧ WeightLimits p wh ws ∧
      corrected (spectrum h k q) x (P p).lambda (mu p) (cross p) c d <
        physicalPrice p wh ws c d (trueRay n v t₁ tₛ) := by
  obtain ⟨j,a,b,ha,hb,ab,nr,vr⟩ := UpperRayCones.cover n v n0 v0 positive
  let r := sectorRay j a b
  have ge := UpperRayGeometry.actualGeometry j a b ha hb
  obtain ⟨s,sm,rs,comp,pass⟩ := rows j
  obtain ⟨f,u,w,sv,hf,hu,hw⟩ := shiftEnclosed (R:=R) s sm
  obtain ⟨wh,ws,limits,accept⟩ := acceptedRealSector inside hf hu hw comp j pass
  let p := realInputs box h k q f u w
  let F := correctedPoly (spectrum h k q) x (P p).lambda (mu p) (cross p)
  obtain ⟨cl,ch⟩ := insideEndpoints.mp inside.cInside
  obtain ⟨dl,dh⟩ := insideEndpoints.mp inside.dInside
  have dpos : 0≤p.dl := lowerEndpointNonnegative (pointSound (R:=R) cppGrid box.d.lo) domain.1
  have order : p.dh≤p.cl := valueLe _ (orderedBox comp)
  have cunit : p.ch≤1 := by change value cppGrid box.c.hi≤1; rw [←scaleValue (R:=R) cppGrid]; exact valueLe _ domain.2
  change p.dl≤d at dl; change d≤p.dh at dh; change p.cl≤c at cl; change c≤p.ch at ch
  have Fcorner (i z : Bool) : F.eval (cAt p i) (dAt p z)≤splitBound p wh ws (cAt p i) (dAt p z) r ∧
      F.eval (cAt p i) (dAt p z)≤singleBound p wh ws (cAt p i) (dAt p z) r := by
    have ord : OrderedCorner p (cAt p i) (dAt p z) := by
      cases i <;> cases z <;> dsimp only [OrderedCorner,cAt,dAt] <;> exact ⟨by grind only,by grind only,by grind only⟩
    have e := exterior f u w sv i z ord
    obtain ⟨spl,sing⟩ := boundsAtActual p wh ws (cAt p i) (dAt p z) r n v ge nr vr
    rw [spl,sing]; change (correctedPoly _ _ _ _ _).eval _ _≤_ ∧ (correctedPoly _ _ _ _ _).eval _ _≤_
    rw [correctedPolyEval]; exact e
  have inter := rectangleOfCornerEstimates p wh ws j a b ha hb ab accept F Fcorner c d cl ch dl dh
  change (correctedPoly _ _ _ _ _).eval c d<_ at inter; rw [correctedPolyEval] at inter
  obtain ⟨hc,sc⟩ := supportTerms p wh ws c d limits (by grind only) dpos cl dl h0 k0 q0
  have low := UpperRayCones.traceBounds j a b ha hb (nr ▸ nc) (vr ▸ vc)
  change r.traceOne≤r.v*(1-r.v) ∧ r.traceShared≤r.n*(1-r.n) at low
  rw [nr,vr] at low
  have last := rPrice p wh ws c d r v t₁ tₛ n ge nr vr
    (Std.le_trans low.1 highestTrace) (Std.le_trans low.2 sharedTrace) hc sc
  exact ⟨f,u,w,wh,ws,sv,limits,Std.lt_of_lt_of_le inter last⟩

end RankSeven.UpperPhysicalInterior
#print axioms RankSeven.UpperPhysicalInterior.frameInterior
