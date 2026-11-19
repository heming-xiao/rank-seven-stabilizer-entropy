import Rank7UpperCornerShiftHull
import Rank7UpperCornerCompletion
namespace RankSeven.UpperCornerRayBound
open Lean.Grind ExteriorCuts PackingDual UpperEndpoint UpperEndpointPrices UpperPhysicalInterior UpperFrameGain UpperFrameTrace UpperInterior
open UpperCornerColumns UpperCornerSignedIdentity UpperCornerShiftHull UpperCornerCompletion
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem tailChoice (n v : R) : ∃ b : Bool,(if b then n else 2*v)=2*(trueRay n v 0 0).tail := by
  change ∃ b : Bool,(if b then n else 2*v)=2*UpperWeighted.larger v (n/2)
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have eq := UpperContractor.quotientEq n (show (0:R)<2 by grind only)
  unfold UpperWeighted.larger; split
  · exact ⟨false,rfl⟩
  · exact ⟨true,eq.symm⟩

private theorem middleChoice (n v : R) : ∃ b : Bool,(if b then v else 2*n)=2*(trueRay n v 0 0).m := by
  change ∃ b : Bool,(if b then v else 2*n)=2*UpperWeighted.larger n (v/2)
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have eq := UpperContractor.quotientEq v (show (0:R)<2 by grind only)
  unfold UpperWeighted.larger; split
  · exact ⟨false,rfl⟩
  · exact ⟨true,eq.symm⟩

private theorem floorChoice (n v : R) : ∃ f : Fin 3,
    (match f.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v)=2*(trueRay n v 0 0).constant := by
  change ∃ f : Fin 3,_=2*UpperWeighted.larger (UpperWeighted.larger ((5/2:R)*n) (2*v)) (2*n+v)
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have eq := congrArg (fun z : R => z*n) (UpperContractor.quotientEq (5:R) (show (0:R)<2 by grind only))
  have either (a b : R) : UpperWeighted.larger a b=a ∨ UpperWeighted.larger a b=b := by
    unfold UpperWeighted.larger; split <;> simp
  rcases either (UpperWeighted.larger ((5/2:R)*n) (2*v)) (2*n+v) with left|right
  · rw [left]
    rcases either ((5/2:R)*n) (2*v) with left|right
    · rw [left]; refine ⟨0,?_⟩; change 5*n=2*((5/2:R)*n); grind only
    · rw [right]; refine ⟨1,?_⟩; change 4*v=2*(2*v); grind only
  · rw [right]; refine ⟨2,?_⟩; change 4*n+2*v=2*(2*n+v); grind only

private theorem tiny (p : Inputs R) : mu p=24*invRate*p.w*(p.k*(p.h+p.k+p.q)) := by
  change _-(_-24*invRate*p.w*(p.k*(p.h+p.k+p.q)))=_; grind only

theorem signedRayBounds (p : Inputs R) (x : Wedge7→R) (c d : R)
    (hn : 0≤p.h) (kn : 0≤p.k) (qn : 1≤2*p.q) (cd : OrderedCorner p c d)
    (nx : ∀w,0≤x w) (rows : RowsHold x) (n0 : 0≤sharedExcess x) (v0 : 0≤highExcess x)
    (ls : 0≤(P p).lambda ∧ 707*(P p).lambda≤150*(p.h*p.q))
    (ys : 0≤mu p ∧ 707*mu p≤175*(p.k*(p.h+p.k+p.q)))
    (ac : 707*cross p=200*((1+p.q)*p.h)) :
    let F := corrected (spectrum p.h p.k p.q) x (P p).lambda (mu p) (cross p) c d
    let r := trueRay (sharedExcess x) (highExcess x) 0 0
    F≤splitBound p 0 0 c d r ∧ F≤singleBound p 0 0 c d r := by
  let n := sharedExcess x
  let v := highExcess x
  let t := missingTriple x
  let r := trueRay n v 0 0
  let F := corrected (spectrum p.h p.k p.q) x (P p).lambda (mu p) (cross p) c d
  let g := p.h*p.q
  let delta := p.k*(p.h+p.k+p.q)
  let l := (P p).lambda
  let y := mu p
  let C := (p.h+p.k+p.q)*(p.k+p.q)*p.q-l*((p.k+p.q)+p.q)-y*p.q
  let J := 2*n+v-3*r.m
  let base := c*d*(g-l)*n+(delta-y)*(d*d*v-(1-d)*(c-d)*r.tail)-c*d*(p.h+2*p.k+3*p.q)*r.m-d^4*r.constant
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have qpos : 0≤p.q := by grind only
  have gpos : 0≤p.h*p.q := OrderedRing.mul_nonneg hn qpos
  have dpos : 0≤p.k*(p.h+p.k+p.q) := OrderedRing.mul_nonneg kn (by grind only)
  have cp : 0≤C := completionPriceNonnegative hn kn qpos (by dsimp [l]; grind only) (by dsimp [y]; grind only)
  have residual : (P p).residual=delta-y := by change (P p).residual=(H p).delta-((H p).delta-(P p).residual); grind only
  have comp : (P p).completion=C := by
    have e := tiny p
    change UpperPrices.positivePart ((p.h+p.k+p.q)*(p.k+p.q)*p.q-l*((p.k+p.q)+p.q)-
      (24*invRate*p.w*(p.k*(p.h+p.k+p.q)))*p.q)=C
    rw [← e]; change UpperPrices.positivePart C=C
    simp [UpperPrices.positivePart,cp]
  obtain ⟨bt,ht⟩ := tailChoice n v
  obtain ⟨bm,hm⟩ := middleChoice n v
  obtain ⟨z,hz⟩ := floorChoice n v
  change (if bt then n else 2*v)=2*r.tail at ht
  change (if bm then v else 2*n)=2*r.m at hm
  change (match z.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v)=2*r.constant at hz
  have get (layout : Layout) := fullShifts layout p.h p.k p.q c d l y (cross p) x hn kn qn cd nx rows n0 v0 ls ys ac
  have split0 := get ⟨false,bt,bm,z,false⟩
  change 2*F≤c*d*(2*g-2*p.h-6*p.q-5-2*l)*n+
    (delta-y)*(2*d*d*v-(1-d)*(c-d)*(if bt then n else 2*v))-2*p.k*c*d*v at split0
  rw [ht] at split0
  have fifth := UpperContractor.quotientEq (5:R) (by grind only : (0:R)<2)
  have head : 2*(5/2:R)=5 := fifth
  have equalSplit : 2*splitBound p 0 0 c d r=c*d*(2*g-2*p.h-6*p.q-5-2*l)*n+
      (delta-y)*(2*d*d*v-(1-d)*(c-d)*(2*r.tail))-2*p.k*c*d*v := by
    change 2*(c*d*((g-p.h-3*p.q-5/2)-l)*n+(P p).residual*(d*d*v-(1-d)*(c-d)*r.tail)-c*d*p.k*v)=_
    rw [residual]
    have m := congrArg (fun w : R => c*d*w*n) head; grind only
  have sing (charge : Bool) : 2*F≤2*base-2*c*C*t-d^3*p.q*(if charge then 2*(J-t) else 0) := by
    have raw := get ⟨true,bt,bm,z,charge⟩
    change 2*F≤c*d*(2*g-2*l)*n+(delta-y)*(2*d*d*v-(1-d)*(c-d)*(if bt then n else 2*v))-
      (c*d*(p.h+2*p.k+3*p.q)*(if bm then v else 2*n)+d^4*(match z.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v)+
      d^3*p.q*(if charge then 4*n+2*v-3*(if bm then v else 2*n)-2*t else 0)+2*c*C*t) at raw
    rw [ht,hm,hz] at raw
    cases charge <;> dsimp only [Bool.false_eq_true,↓reduceIte,base,J] at * <;> grind only
  have low := sing false
  have high := sing true
  have tn := (sharedTraceCaps x nx rows n0).1
  let a := d^3*p.q
  let b := c*C
  let price := smaller a b
  have cn : 0≤c := Std.le_trans cd.1 cd.2.1
  have bn : 0≤b := OrderedRing.mul_nonneg cn cp
  have dn := cd.1
  have an : 0≤a := by
    have cube := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg dn dn) dn
    exact OrderedRing.mul_nonneg (show 0≤d^3 by grind only) qpos
  have pp : price≤a ∧ price≤b ∧ 0≤price := by dsimp [price,smaller]; split <;> grind only
  have jp : (0≤J → r.improvement=J) ∧ (J≤0 → r.improvement=0) := by
    change (0≤J → UpperPrices.positivePart J=J) ∧ (J≤0 → UpperPrices.positivePart J=0)
    unfold UpperPrices.positivePart; split <;> grind only
  have final := minimumCompletion (F:=F) (base:=base) (x:=t) (a:=a) (b:=b) (J:=J) (price:=price)
    tn bn ⟨pp.1,pp.2.1⟩ pp.2.2 jp
    (by change F≤base-c*C*t; change 2*F≤2*base-2*c*C*t-d^3*p.q*0 at low; grind only)
    (by change F≤base-c*C*t-d^3*p.q*(J-t); change 2*F≤2*base-2*c*C*t-d^3*p.q*(2*(J-t)) at high; grind only)
  have equalSingle : singleBound p 0 0 c d r=base-price*r.improvement := by
    change c*d*(g-l)*n+(P p).residual*(d*d*v-(1-d)*(c-d)*r.tail)-c*d*(p.h+2*p.k+3*p.q)*r.m-
      (d*d*(d*d))*r.constant-smaller (d*d*d*p.q) (c*(P p).completion)*r.improvement=_
    rw [residual,comp,show d*d*d*p.q=a by dsimp [a]; grind only]
    dsimp only [base,price,b]; grind only
  change F≤splitBound p 0 0 c d r ∧ F≤singleBound p 0 0 c d r
  rw [← equalSplit] at split0
  rw [equalSingle]
  exact ⟨by grind only,final⟩

end RankSeven.UpperCornerRayBound
#print axioms RankSeven.UpperCornerRayBound.signedRayBounds