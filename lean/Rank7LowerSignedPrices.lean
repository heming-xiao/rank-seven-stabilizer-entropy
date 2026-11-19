import Rank7LowerCorner
import Rank7LowerNormalizedSigned

namespace RankSeven.LowerSignedPrices
open Lean.Grind UpperEndpointPrices LowerCorner
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def mu (z y x w : R) : R := 24*invRate*w*(y*(z+y+x))
noncomputable def cross (z x : R) : R := 96*invRate*((1+x)*z/2)

private theorem rate : (707:R)*(24*invRate)=100 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have a := UpperContractor.quotientEq (4242:R) (show (0:R)<25 by grind only)
  have b := UpperContractor.quotientEq (1:R) (show (0:R)<4242/25 by grind only)
  have ac := congrArg (fun z : R => z*invRate) a
  change 4242/25*invRate=1 at b
  grind only

private theorem caps {f u w : R} (fs : f=0∨f=1/2∨f=1)
    (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4) :
    f≤1 ∧ 0≤u ∧ 2*u≤3 ∧ 0≤w ∧ 4*w≤7 := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have q4 (n : R) := UpperContractor.quotientEq n (show (0:R)<4 by grind only)
  have q2 (n : R) := UpperContractor.quotientEq n (show (0:R)<2 by grind only)
  have ff : f≤1 := by
    clear us ws; have e := q2 1; clear q2 q4
    rcases fs with h|h|h <;> rw [h] <;> grind only
  have uu : 0≤u ∧ 2*u≤3 := by rcases us with h|h|h|h <;> have j:=q4 5 <;> have k:=q4 3 <;> have e:=q2 3 <;> grind only
  have ww : 0≤w ∧ 4*w≤7 := by rcases ws with h|h|h|h <;> have j:=q4 5 <;> have k:=q4 7 <;> have e:=q2 3 <;> grind only
  exact ⟨ff,uu.1,uu.2,ww.1,ww.2⟩

private theorem invBound (N f : R) (np : 0<N) : 0≤N/(N+72*(f*f)) ∧ N/(N+72*(f*f))≤1 := by
  have sq := squareNonnegative f
  have dp : 0<N+72*(f*f) := by grind only
  have div := UpperContractor.quotientEq N dp
  constructor
  · apply UpperContractor.cancelLe dp; rw [Semiring.mul_zero,div]; exact Std.le_of_lt np
  · apply UpperContractor.cancelLe dp; rw [Semiring.mul_one,div]; grind only

private theorem normPos (z x : R) (xh : 1≤2*x) : 0<z*z+x*x := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have xp : 0<x := by grind only
  have xs := OrderedRing.mul_pos xp xp
  have zs := squareNonnegative z
  grind only

private theorem shiftBound (g tax b N f u : R) (gn : 0≤g) (tn : 0≤tax) (br : 1≤b)
    (np : 0<N) (un : 0≤u) (uc : 2*u≤3) :
    let s := u*(UpperPrices.positivePart (g-tax*(1-1/b))*(N/(N+72*(f*f))))
    0≤s ∧ 2*s≤3*g := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have bp : 0<b := by grind only
  have inv := UpperContractor.quotientEq (1:R) bp
  have invle : 1/b≤1 := by apply UpperContractor.cancelLe bp; rw [inv,Semiring.mul_one]; exact br
  have loss := OrderedRing.mul_nonneg tn (show 0≤1-1/b by grind only)
  let G := UpperPrices.positivePart (g-tax*(1-1/b))
  have pp : 0≤G ∧ G≤g := by dsimp [G,UpperPrices.positivePart]; split <;> grind only
  have ip := invBound N f np
  have ui := OrderedRing.mul_nonneg un pp.1
  have pay := OrderedRing.mul_nonneg ui ip.1
  have limit := OrderedRing.mul_le_mul_of_nonneg_left ip.2 ui
  have cap := OrderedRing.mul_le_mul_of_nonneg_right uc pp.1
  change 0≤u*(G*(N/(N+72*(f*f)))) ∧ 2*(u*(G*(N/(N+72*(f*f)))))≤3*g
  grind only

theorem realCaps (z y x b f u w wa wb : R)
    (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (b1 : 1≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4) :
    let p := realPrices z y x b f u w wa wb
    (0≤p.lambda ∧ 707*p.lambda≤150*(z*x)) ∧
    (0≤mu z y x w ∧ 707*mu z y x w≤175*(y*(z+y+x))) ∧
    707*cross z x=200*((1+x)*z) := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  obtain ⟨f1,u0,uc,w0,wc⟩ := caps fs us ws
  have x0 : 0≤x := by grind only
  have ds := OrderedRing.mul_nonneg y0 (show 0≤z+y+x by grind only)
  have tax := UpperPrices.alphaPriceNonnegative f1
  have sh := shiftBound (z*x) (UpperPrices.alphaPrice f) b (z*z+x*x) f u (OrderedRing.mul_nonneg z0 x0) tax b1 (normPos z x xh) u0 uc
  let s := u*(UpperPrices.positivePart (z*x-(1-f)*(200/11)*(1-1/b))*((z*z+x*x)/((z*z+x*x)+72*(f*f))))
  change 0≤s ∧ 2*s≤3*(z*x) at sh
  have rt := rate (R:=R)
  have sl := congrArg (fun z : R => z*s) rt
  have yl := congrArg (fun t : R => t*w*(y*(z+y+x))) rt
  have yh := OrderedRing.mul_le_mul_of_nonneg_right wc ds
  have yn := OrderedRing.mul_nonneg w0 ds
  have h := UpperContractor.quotientEq ((1+x)*z) (show (0:R)<2 by grind only)
  have c := congrArg (fun t : R => t*((1+x)*z/2)) rt
  change (0≤24*invRate*s ∧ 707*(24*invRate*s)≤150*(z*x)) ∧
    (0≤24*invRate*w*(y*(z+y+x)) ∧ 707*(24*invRate*w*(y*(z+y+x)))≤175*(y*(z+y+x))) ∧
    707*(96*invRate*((1+x)*z/2))=200*((1+x)*z)
  grind only

end RankSeven.LowerSignedPrices
#print axioms RankSeven.LowerSignedPrices.realCaps