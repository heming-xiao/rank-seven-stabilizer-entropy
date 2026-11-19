import Rank7UpperCornerRayBound
import Rank7UpperPairReplay
namespace RankSeven.UpperCertifiedExterior
open Lean.Grind Interval ExteriorCuts PackingDual UpperEndpoint UpperEndpointPrices UpperPrices UpperPhysicalInterior
open UpperFrameGain UpperFrameTrace UpperReplay UpperContractor UpperCornerRayBound
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem rate : (707:R)*(24*invRate)=100 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have a := UpperContractor.quotientEq (4242:R) (show (0:R)<25 by grind only)
  have b := UpperContractor.quotientEq (1:R) (show (0:R)<4242/25 by grind only)
  have ac := congrArg (fun z : R => z*invRate) a
  change 4242/25*invRate=1 at b
  grind only

private theorem choiceBounds {f u w : R} (sv : ShiftValues f u w) :
    f≤1 ∧ 0≤u ∧ 2*u≤3 ∧ 0≤w ∧ 4*w≤7 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have q4 (n : R) := UpperContractor.quotientEq n (show (0:R)<4 by grind only)
  have q2 (n : R) := UpperContractor.quotientEq n (show (0:R)<2 by grind only)
  obtain ⟨f0,u0,w0⟩ := sv
  have ff : f≤1 := by
    clear u0 w0
    have e:=q2 1; have j:=q4 3; have k:=q4 1
    clear q2 q4
    rcases f0 with h|h|h|h|h <;> rw [h] <;> grind only
  have uu : 0≤u ∧ 2*u≤3 := by rcases u0 with h|h|h|h <;> have j:=q4 5 <;> have k:=q4 3 <;> have e:=q2 3 <;> grind only
  have ww : 0≤w ∧ 4*w≤7 := by rcases w0 with h|h|h|h <;> have j:=q4 5 <;> have k:=q4 7 <;> have e:=q2 3 <;> grind only
  exact ⟨ff,uu.1,uu.2,ww.1,ww.2⟩

theorem physicalShiftCaps (p : Inputs R) (sv : ShiftValues p.f p.u p.w)
    (hn : 0≤p.h) (kn : 0≤p.k) (qn : 0≤p.q) (psi : 0<(H p).psi) (spread : p.dl≤p.ch) :
    (0≤(P p).lambda ∧ 707*(P p).lambda≤150*(p.h*p.q)) ∧
    (0≤mu p ∧ 707*mu p≤175*(p.k*(p.h+p.k+p.q))) ∧ 707*cross p=200*((1+p.q)*p.h) := by
  obtain ⟨f1,u0,uc,w0,wc⟩ := choiceBounds sv
  have g0 := OrderedRing.mul_nonneg hn qn
  have de := OrderedRing.mul_nonneg kn (show 0≤p.h+p.k+p.q by grind only)
  have sh := shiftAdmissible (f:=p.f) psi g0 (alphaPriceNonnegative f1) (show 0≤p.ch-p.dl by grind only) u0 uc
  rw [← shiftMatches p] at sh
  have rt := rate (R:=R)
  have sl := congrArg (fun z : R => z*(P p).shift) rt
  have yl := congrArg (fun z : R => z*p.w*(p.k*(p.h+p.k+p.q))) rt
  have yh := OrderedRing.mul_le_mul_of_nonneg_right wc de
  have yn := OrderedRing.mul_nonneg w0 de
  have lm : (P p).lambda=24*invRate*(P p).shift := rfl
  have ym : mu p=24*invRate*p.w*(p.k*(p.h+p.k+p.q)) := by
    change _-(_-24*invRate*p.w*(p.k*(p.h+p.k+p.q)))=_; grind only
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have h := UpperContractor.quotientEq ((1+p.q)*p.h) (show (0:R)<2 by grind only)
  have c := congrArg (fun z : R => z*((1+p.q)*p.h/2)) rt
  rw [lm,ym]; unfold cross
  grind only

theorem exteriorEstimates {box : UpperCorner.TailBox} {h k q c d : R}
    (res : Residual h k q c d) (headFloor : 1≤2*q) (inside : Inside cppGrid box h k q c d)
    (dom : TailRectangle box) (x : Wedge7→R) (nx : ∀w,0≤x w) (rows : RowsHold x)
    (n0 : 0≤sharedExcess x) (v0 : 0≤highExcess x) (f u w : R) (sv : ShiftValues f u w) :
    ExteriorEstimates (realInputs box h k q f u w) x (sharedExcess x) (highExcess x) := by
  let p := realInputs box h k q f u w
  obtain ⟨cl,ch⟩ := insideEndpoints.mp inside.cInside
  obtain ⟨dl,dh⟩ := insideEndpoints.mp inside.dInside
  change p.dl≤d at dl; change d≤p.dh at dh; change p.cl≤c at cl; change c≤p.ch at ch
  have dpos : 0≤p.dl := lowerEndpointNonnegative (pointSound (R:=R) cppGrid box.d.lo) dom.1
  have cunit : p.ch≤1 := by
    change value cppGrid box.c.hi≤1; rw [←scaleValue (R:=R) cppGrid]; exact valueLe _ dom.2
  have psi : 0<(H p).psi := by
    rw [reserveMatches]; exact (reserveBounds (h:=h) (q:=q) cl ch dh dl dpos cunit res.ordered).1
  obtain ⟨ls,ys,ac⟩ := physicalShiftCaps p sv res.hNonnegative res.kNonnegative res.qNonnegative psi
    (Std.le_trans dl (Std.le_trans res.ordered ch))
  intro i j cd
  exact signedRayBounds p x _ _ res.hNonnegative res.kNonnegative headFloor cd nx rows n0 v0 ls ys ac

end RankSeven.UpperCertifiedExterior
#print axioms RankSeven.UpperCertifiedExterior.physicalShiftCaps
#print axioms RankSeven.UpperCertifiedExterior.exteriorEstimates