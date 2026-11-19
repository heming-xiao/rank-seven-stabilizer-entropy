import Rank7UpperCornerShiftHull
import Rank7UpperCornerCompletion
namespace RankSeven.LowerNormalizedSigned
open Lean.Grind ExteriorCuts PackingDual UpperEndpoint UpperEndpointPrices UpperPhysicalInterior UpperFrameGain UpperFrameTrace UpperInterior
open UpperCornerColumns UpperCornerSignedIdentity UpperCornerShiftHull UpperCornerCompletion
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LT R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem positiveParts (J : R) : (0≤J → UpperPrices.positivePart J=J) ∧
    (J≤0 → UpperPrices.positivePart J=0) := by unfold UpperPrices.positivePart; split <;> grind only

private theorem halve (F B : R) (e : 2*F≤2*B) : F≤B := by grind only
private theorem lowHalf (F B c C t e : R) (bound : 2*F≤2*B-2*c*C*t-e*0) : F≤B-c*C*t := by grind only
private theorem highHalf (F B c C t e J : R) (bound : 2*F≤2*B-2*c*C*t-e*(2*(J-t))) :
    F≤B-c*C*t-e*(J-t) := by grind only

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

def splitPrice (h k q c d l y : R) (r : RayData R) : R :=
  c*d*(h*q-h-3*q-5/2-l)*r.n+(k*(h+k+q)-y)*(d*d*r.v-(1-d)*(c-d)*r.tail)-c*d*k*r.v

noncomputable def single (h k q c d l y : R) (r : RayData R) : R :=
  let C := (h+k+q)*(k+q)*q-l*((k+q)+q)-y*q
  c*d*(h*q-l)*r.n+(k*(h+k+q)-y)*(d*d*r.v-(1-d)*(c-d)*r.tail)-c*d*(h+2*k+3*q)*r.m-d^4*r.constant-
    smaller (d^3*q) (c*C)*r.improvement

theorem normalizedBounds (h k q lambda mu a : R) (x : Wedge7→R) (c d : R)
    (hn : 0≤h) (kn : 0≤k) (qn : 1≤2*q) (cd : 0≤d ∧ d≤c ∧ c≤1)
    (nx : ∀w,0≤x w) (rows : RowsHold x) (n0 : 0≤sharedExcess x) (v0 : 0≤highExcess x)
    (ls : 0≤lambda ∧ 707*lambda≤150*(h*q))
    (ys : 0≤mu ∧ 707*mu≤175*(k*(h+k+q)))
    (ac : 707*a=200*((1+q)*h)) :
    let F := corrected (spectrum h k q) x lambda (mu) a c d
    let r := trueRay (sharedExcess x) (highExcess x) 0 0
    F≤splitPrice h k q c d lambda mu r ∧ F≤single h k q c d lambda mu r := by
  let n := sharedExcess x
  let v := highExcess x
  let t := missingTriple x
  let r := trueRay n v 0 0
  let F := corrected (spectrum h k q) x lambda (mu) a c d
  let g := h*q
  let delta := k*(h+k+q)
  let l := lambda
  let y := mu
  let C := (h+k+q)*(k+q)*q-l*((k+q)+q)-y*q
  let J := 2*n+v-3*r.m
  let base := c*d*(g-l)*n+(delta-y)*(d*d*v-(1-d)*(c-d)*r.tail)-c*d*(h+2*k+3*q)*r.m-d^4*r.constant
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have qpos : 0≤q := by grind only
  have gpos : 0≤h*q := OrderedRing.mul_nonneg hn qpos
  have dpos : 0≤k*(h+k+q) := OrderedRing.mul_nonneg kn (by grind only)
  have cp : 0≤C := completionPriceNonnegative hn kn qpos (by dsimp [l]; grind only) (by dsimp [y]; grind only)
  obtain ⟨bt,ht⟩ := tailChoice n v
  obtain ⟨bm,hm⟩ := middleChoice n v
  obtain ⟨z,hz⟩ := floorChoice n v
  change (if bt then n else 2*v)=2*r.tail at ht
  change (if bm then v else 2*n)=2*r.m at hm
  change (match z.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v)=2*r.constant at hz
  have get (layout : Layout) := fullShifts layout h k q c d l y a x hn kn qn cd nx rows n0 v0 ls ys ac
  have split0 := get ⟨false,bt,bm,z,false⟩
  change 2*F≤c*d*(2*g-2*h-6*q-5-2*l)*n+
    (delta-y)*(2*d*d*v-(1-d)*(c-d)*(if bt then n else 2*v))-2*k*c*d*v at split0
  rw [ht] at split0
  have fifth := UpperContractor.quotientEq (5:R) (by grind only : (0:R)<2)
  have head : 2*(5/2:R)=5 := fifth
  have equalSplit : 2*splitPrice h k q c d lambda mu r=c*d*(2*g-2*h-6*q-5-2*l)*n+
      (delta-y)*(2*d*d*v-(1-d)*(c-d)*(2*r.tail))-2*k*c*d*v := by
    change 2*(c*d*((g-h-3*q-5/2)-l)*n+(delta-y)*(d*d*v-(1-d)*(c-d)*r.tail)-c*d*k*v)=_
    have m := congrArg (fun w : R => c*d*w*n) head; grind only
  have sing (charge : Bool) : 2*F≤2*base-2*c*C*t-d^3*q*(if charge then 2*(J-t) else 0) := by
    have raw := get ⟨true,bt,bm,z,charge⟩
    change 2*F≤c*d*(2*g-2*l)*n+(delta-y)*(2*d*d*v-(1-d)*(c-d)*(if bt then n else 2*v))-
      (c*d*(h+2*k+3*q)*(if bm then v else 2*n)+d^4*(match z.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v)+
      d^3*q*(if charge then 4*n+2*v-3*(if bm then v else 2*n)-2*t else 0)+2*c*C*t) at raw
    rw [ht,hm,hz] at raw
    cases charge <;> dsimp only [Bool.false_eq_true,↓reduceIte,base,J] at * <;> grind only
  have low := sing false
  have high := sing true
  have tn := (sharedTraceCaps x nx rows n0).1
  let a := d^3*q
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
    exact positiveParts J
  have final := minimumCompletion (F:=F) (base:=base) (x:=t) (a:=a) (b:=b) (J:=J) (price:=price)
    tn bn ⟨pp.1,pp.2.1⟩ pp.2.2 jp
    (lowHalf _ _ _ _ _ _ low)
    (highHalf _ _ _ _ _ _ _ high)
  have equalSingle : single h k q c d lambda mu r=base-price*r.improvement := rfl
  change F≤splitPrice h k q c d lambda mu r ∧ F≤single h k q c d lambda mu r
  rw [← equalSplit] at split0
  rw [equalSingle]
  exact ⟨halve _ _ split0,final⟩

end RankSeven.LowerNormalizedSigned
#print axioms RankSeven.LowerNormalizedSigned.normalizedBounds