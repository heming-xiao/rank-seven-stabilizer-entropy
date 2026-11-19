import Rank7LowerSmallHeadData
import Rank7RealLowerPhysicalPrice
namespace RankSeven.RealLowerSmallHead
open Pauli ExteriorCuts PackingDual PackingInterpolation UpperFrameGain LowerSmallHeadData
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
noncomputable section

def productHead (e f g : Bool) (x y r z : ℝ) : ℝ :=
  let b:=x+2*y+r
  (if e then b+x+y+z else b)*(if f then b+x+y else b)*(if g then b+x else b)*b

theorem headExpansion (e f g : Bool) (x y r z : ℝ) :
    productHead e f g x y r z=sumOver tags (fun j =>
      ((cf (e.toNat+2*f.toNat+4*g.toNat) j : Nat) : ℝ)*mon x y r z j) := by
  cases e <;> cases f <;> cases g
  · change (x+2*y+r)*(x+2*y+r)*(x+2*y+r)*(x+2*y+r)=1*(r^4)+(8*(y*r^3)+(24*(y^2*r^2)+(32*(y^3*r)+(16*(y^4)+(4*(x*r^3)+(24*(x*y*r^2)+(48*(x*y^2*r)+(32*(x*y^3)+(6*(x^2*r^2)+(24*(x^2*y*r)+(24*(x^2*y^2)+(4*(x^3*r)+(8*(x^3*y)+(1*(x^4)+(0*(r^3*z)+(0*(y*r^2*z)+(0*(y^2*r*z)+(0*(y^3*z)+(0*(x*r^2*z)+(0*(x*y*r*z)+(0*(x*y^2*z)+(0*(x^2*r*z)+(0*(x^2*y*z)+(0*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change (x+2*y+r)*(x+2*y+r)*((x+2*y+r)+x)*(x+2*y+r)=1*(r^4)+(8*(y*r^3)+(24*(y^2*r^2)+(32*(y^3*r)+(16*(y^4)+(5*(x*r^3)+(30*(x*y*r^2)+(60*(x*y^2*r)+(40*(x*y^3)+(9*(x^2*r^2)+(36*(x^2*y*r)+(36*(x^2*y^2)+(7*(x^3*r)+(14*(x^3*y)+(2*(x^4)+(0*(r^3*z)+(0*(y*r^2*z)+(0*(y^2*r*z)+(0*(y^3*z)+(0*(x*r^2*z)+(0*(x*y*r*z)+(0*(x*y^2*z)+(0*(x^2*r*z)+(0*(x^2*y*z)+(0*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change (x+2*y+r)*((x+2*y+r)+x+y)*(x+2*y+r)*(x+2*y+r)=1*(r^4)+(9*(y*r^3)+(30*(y^2*r^2)+(44*(y^3*r)+(24*(y^4)+(5*(x*r^3)+(33*(x*y*r^2)+(72*(x*y^2*r)+(52*(x*y^3)+(9*(x^2*r^2)+(39*(x^2*y*r)+(42*(x^2*y^2)+(7*(x^3*r)+(15*(x^3*y)+(2*(x^4)+(0*(r^3*z)+(0*(y*r^2*z)+(0*(y^2*r*z)+(0*(y^3*z)+(0*(x*r^2*z)+(0*(x*y*r*z)+(0*(x*y^2*z)+(0*(x^2*r*z)+(0*(x^2*y*z)+(0*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change (x+2*y+r)*((x+2*y+r)+x+y)*((x+2*y+r)+x)*(x+2*y+r)=1*(r^4)+(9*(y*r^3)+(30*(y^2*r^2)+(44*(y^3*r)+(24*(y^4)+(6*(x*r^3)+(40*(x*y*r^2)+(88*(x*y^2*r)+(64*(x*y^3)+(13*(x^2*r^2)+(57*(x^2*y*r)+(62*(x^2*y^2)+(12*(x^3*r)+(26*(x^3*y)+(4*(x^4)+(0*(r^3*z)+(0*(y*r^2*z)+(0*(y^2*r*z)+(0*(y^3*z)+(0*(x*r^2*z)+(0*(x*y*r*z)+(0*(x*y^2*z)+(0*(x^2*r*z)+(0*(x^2*y*z)+(0*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change ((x+2*y+r)+x+y+z)*(x+2*y+r)*(x+2*y+r)*(x+2*y+r)=1*(r^4)+(9*(y*r^3)+(30*(y^2*r^2)+(44*(y^3*r)+(24*(y^4)+(5*(x*r^3)+(33*(x*y*r^2)+(72*(x*y^2*r)+(52*(x*y^3)+(9*(x^2*r^2)+(39*(x^2*y*r)+(42*(x^2*y^2)+(7*(x^3*r)+(15*(x^3*y)+(2*(x^4)+(1*(r^3*z)+(6*(y*r^2*z)+(12*(y^2*r*z)+(8*(y^3*z)+(3*(x*r^2*z)+(12*(x*y*r*z)+(12*(x*y^2*z)+(3*(x^2*r*z)+(6*(x^2*y*z)+(1*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change ((x+2*y+r)+x+y+z)*(x+2*y+r)*((x+2*y+r)+x)*(x+2*y+r)=1*(r^4)+(9*(y*r^3)+(30*(y^2*r^2)+(44*(y^3*r)+(24*(y^4)+(6*(x*r^3)+(40*(x*y*r^2)+(88*(x*y^2*r)+(64*(x*y^3)+(13*(x^2*r^2)+(57*(x^2*y*r)+(62*(x^2*y^2)+(12*(x^3*r)+(26*(x^3*y)+(4*(x^4)+(1*(r^3*z)+(6*(y*r^2*z)+(12*(y^2*r*z)+(8*(y^3*z)+(4*(x*r^2*z)+(16*(x*y*r*z)+(16*(x*y^2*z)+(5*(x^2*r*z)+(10*(x^2*y*z)+(2*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change ((x+2*y+r)+x+y+z)*((x+2*y+r)+x+y)*(x+2*y+r)*(x+2*y+r)=1*(r^4)+(10*(y*r^3)+(37*(y^2*r^2)+(60*(y^3*r)+(36*(y^4)+(6*(x*r^3)+(44*(x*y*r^2)+(106*(x*y^2*r)+(84*(x*y^3)+(13*(x^2*r^2)+(62*(x^2*y*r)+(73*(x^2*y^2)+(12*(x^3*r)+(28*(x^3*y)+(4*(x^4)+(1*(r^3*z)+(7*(y*r^2*z)+(16*(y^2*r*z)+(12*(y^3*z)+(4*(x*r^2*z)+(18*(x*y*r*z)+(20*(x*y^2*z)+(5*(x^2*r*z)+(11*(x^2*y*z)+(2*(x^3*z)+(0)))))))))))))))))))))))))
    ring
  · change ((x+2*y+r)+x+y+z)*((x+2*y+r)+x+y)*((x+2*y+r)+x)*(x+2*y+r)=1*(r^4)+(10*(y*r^3)+(37*(y^2*r^2)+(60*(y^3*r)+(36*(y^4)+(7*(x*r^3)+(52*(x*y*r^2)+(127*(x*y^2*r)+(102*(x*y^3)+(18*(x^2*r^2)+(88*(x^2*y*r)+(106*(x^2*y^2)+(20*(x^3*r)+(48*(x^3*y)+(8*(x^4)+(1*(r^3*z)+(7*(y*r^2*z)+(16*(y^2*r*z)+(12*(y^3*z)+(5*(x*r^2*z)+(23*(x*y*r*z)+(26*(x*y^2*z)+(8*(x^2*r*z)+(18*(x^2*y*z)+(4*(x^3*z)+(0)))))))))))))))))))))))))
    ring

private theorem factorOnce (w : Wedge7) (i : Fin 7) (a : ℝ) :
    amplitude (fun t => if t=i then a else 1) w=(if occupied w i then a else 1) := by
  have h1:=w.ij; have h2:=w.jk; have h3:=w.km
  unfold amplitude product4 occupied
  by_cases t : w.i=i <;> by_cases u : w.j=i <;> by_cases v : w.k=i <;> by_cases s : w.m=i
  all_goals first | omega | simp [t,u,v,s]

private theorem factorMul (s t : Fin 7→ℝ) (w : Wedge7) :
    amplitude (fun i => s i*t i) w=amplitude s w*amplitude t w := by
  unfold amplitude product4; ring

theorem headAmplitude (x y r z : ℝ) (unit : x+2*y+r=1) (w : Wedge7) :
    amplitude (tail (UpperPhysicalInterior.spectrum z y x) 1 1) w=
      productHead (occupied w 0) (occupied w 1) (occupied w 2) x y r z := by
  have factor : tail (UpperPhysicalInterior.spectrum z y x) 1 1 =
      fun i => ((if i=0 then 1+(z+y+x) else 1)*(if i=1 then 1+(y+x) else 1))*(if i=2 then 1+x else 1) := by
    funext i; fin_cases i <;> simp [tail,UpperPhysicalInterior.spectrum]
  rw [factor,factorMul,factorMul,factorOnce,factorOnce,factorOnce]
  unfold productHead; rw [unit]
  cases occupied w 0 <;> cases occupied w 1 <;> cases occupied w 2 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

theorem monNonnegative (x y r z : ℝ) (hx : 0≤x) (hy : 0≤y) (hr : 0≤r) (hz : 0≤z) (j : Nat) :
    0≤mon x y r z j := by
  unfold mon; split <;> positivity

end
end RankSeven.RealLowerSmallHead
#print axioms RankSeven.RealLowerSmallHead.headExpansion
#print axioms RankSeven.RealLowerSmallHead.headAmplitude