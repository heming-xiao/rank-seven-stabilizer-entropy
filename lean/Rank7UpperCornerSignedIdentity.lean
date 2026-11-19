import Rank7UpperCornerWedgeWeights
namespace RankSeven.UpperCornerSignedIdentity
open Lean.Grind Pauli UpperCornerExpansion UpperCornerFactors UpperCornerColumns UpperCornerPolynomial UpperCornerFrameProducts UpperCornerWedgeWeights ExteriorCuts PackingDual PackingInterpolation
attribute [local instance] Ring.intCast
variable {R : Type} [CommRing R]

def tail2 (r : Branch) (n v : R) := if r.halfTail then n else 2*v
def middle2 (r : Branch) (n v : R) := if r.halfMiddle then v else 2*n
def floor2 (r : Branch) (n v : R) := match r.floor.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v
def extra2 (r : Branch) (n v x : R) := if r.charge then 4*n+2*v-3*middle2 r n v-2*x else 0

def twiceBound (r : Branch) (h k q c d lambda mu n v x : R) :=
  let X := h+k+q
  let Y := k+q
  let g := h*q
  let delta := k*X
  let C := X*Y*q-lambda*(Y+q)-mu*q
  let tailLoss := (1-d)*(c-d)
  let head := if r.single then 2*g else 2*g-2*h-6*q-5
  c*d*(head-2*lambda)*n+(delta-mu)*(2*d*d*v-tailLoss*tail2 r n v)-
  (if r.single then c*d*(h+2*k+3*q)*middle2 r n v+d^4*floor2 r n v+d^3*q*extra2 r n v x+2*c*C*x
   else 2*k*c*d*v)

private theorem castTail (r : Branch) (n v : Int) :
    Int.cast (R:=R) (tail2 r n v)=tail2 r (Int.cast n) (Int.cast v) := by
  unfold tail2; split <;> first | rfl | (rw [Ring.intCast_mul]; grind)
private theorem castMiddle (r : Branch) (n v : Int) :
    Int.cast (R:=R) (middle2 r n v)=middle2 r (Int.cast n) (Int.cast v) := by
  unfold middle2; split <;> first | rfl | (rw [Ring.intCast_mul]; grind)
private theorem castFloor (r : Branch) (n v : Int) :
    Int.cast (R:=R) (floor2 r n v)=floor2 r (Int.cast n) (Int.cast v) := by
  rcases r.floor with ⟨i,t⟩; have lim : i=0∨i=1∨i=2 := by omega
  unfold floor2; split <;> simp_all only [Ring.intCast_add,Ring.intCast_mul] <;> grind
private theorem castExtra (r : Branch) (n v x : Int) :
    Int.cast (R:=R) (extra2 r n v x)=extra2 r (Int.cast n) (Int.cast v) (Int.cast x) := by
  cases e : r.charge <;> simp only [extra2,e,Bool.false_eq_true,ite_false,ite_true,Ring.intCast_add,Ring.intCast_sub,Ring.intCast_mul,castMiddle] <;> grind

private def raw (r : Branch) (p : Nat→R) (n v x : R) :=
  let l := Int.cast (R:=R) r.l
  let y := Int.cast (R:=R) r.y
  (-2)*(707-l)*p 34*n-2*(707-y)*p 45*v+(707-y)*p 46*tail2 r n v+
    (if r.single then 707*p 48*middle2 r n v+707*p 49*floor2 r n v+707*p 50*extra2 r n v x+
      (1414*p 51-2*l*p 52-2*y*p 53)*x else (1414*p 43+4242*p 44+3535*p 41)*n+1414*p 47*v)

private theorem structurally (r : Branch) (p : Nat→R) (w : Wedge7) :
    sumOver (terms r w) (fun t => Int.cast t.1*p t.2)=
      1414*p (ground w).1.1 -2*Int.cast r.l*(Int.cast (high w)*p (ground w).1.2+Int.cast (second w)*p (ground w).2.1)-
      2*Int.cast r.y*(Int.cast (high w)*p (ground w).2.2)+400*p 42*Int.cast (enter w)+raw r p (Int.cast (shared w)) (Int.cast (high w)) (Int.cast (missing w)) := by
  let n := shared w; let v := high w; let x := missing w
  let b := tail2 r n v; let m := middle2 r n v; let z := floor2 r n v; let j := extra2 r n v x
  have eq : terms r w=
      [(1414,(ground w).1.1),(-2*r.l*v,(ground w).1.2),(-2*r.l*second w,(ground w).2.1),(-2*r.y*v,(ground w).2.2),
       (400*enter w,42),(-2*(707-r.l)*n,34),(-2*(707-r.y)*v,45),((707-r.y)*b,46)]++
      (if r.single then [(707*m,48),(707*z,49),(707*j,50),(1414*x,51),(-2*r.l*x,52),(-2*r.y*x,53)]
        else [(1414*n,43),(4242*n,44),(3535*n,41),(1414*v,47)]) := rfl
  rw [eq]; dsimp only [b,m,z,j,n,v,x]
  cases choice : r.single <;> simp only [raw,choice,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,castTail,castMiddle,castFloor,castExtra,Ring.intCast_sub,Ring.intCast_mul,Ring.intCast_neg] <;> grind only

theorem physicalPrice (r : Branch) (h k q c d lambda mu cross : R) (w : Wedge7)
    (l : 707*lambda=Int.cast r.l*(h*q)) (y : 707*mu=Int.cast r.y*(k*(h+k+q))) (a : 707*cross=200*((1+q)*h)) :
    let n := Int.cast (R:=R) (shared w)
    let v := Int.cast (R:=R) (high w)
    let x := Int.cast (R:=R) (missing w)
    price r (vector h k q c d) w =
      22624*(amplitude (source h k q c d) w-lambda*(pairVal h k q c d 1 w+pairVal h k q c d 2 w)-
        mu*pairVal h k q c d 1 w+cross*Int.cast (enter w)*d*(1-c))-11312*twiceBound r h k q c d lambda mu n v x := by
  let p := fun j => eval (vector h k q c d) (pattern j)
  obtain ⟨P,Q,S,T⟩ := physicalTerms h k q c d w
  change p (ground w).1.1=_ at P
  change Int.cast (high w)*p (ground w).1.2=_ at Q
  change Int.cast (second w)*p (ground w).2.1=_ at S
  change Int.cast (high w)*p (ground w).2.2=_ at T
  change sumOver (terms r w) (fun pr => Int.cast pr.1*p pr.2)=_
  rw [structurally,P,Q,S,T]
  have p34 : p 34=16*(c*d*h*q) := by rw [show p 34=_ from scaledProduct h k q c d 34]; change 16*(c*d*h*q)=_; grind only
  have p41 : p 41=16*(c*d*1*1) := by rw [show p 41=_ from scaledProduct h k q c d 41]; change 16*(1*1*c*d)=_; grind only
  have p42 : p 42=16*((1+q)*h*d*(1-c)) := by rw [show p 42=_ from scaledProduct h k q c d 42]; change 16*(d*(1+q)*h*(1-c))=_; grind only
  have p43 : p 43=16*(c*d*1*h) := by rw [show p 43=_ from scaledProduct h k q c d 43]; change 16*(1*c*d*h)=_; grind only
  have p44 : p 44=16*(c*d*1*q) := by rw [show p 44=_ from scaledProduct h k q c d 44]; change 16*(1*c*d*q)=_; grind only
  have p45 : p 45=16*(k*(h+k+q)*d*d) := by rw [show p 45=_ from scaledProduct h k q c d 45]; change 16*((h+k+q)*d*d*k)=_; grind only
  have p46 : p 46=16*(k*(h+k+q)*(1-d)*(c-d)) := by rw [show p 46=_ from scaledProduct h k q c d 46]; change 16*((h+k+q)*(1-d)*(c-d)*k)=_; grind only
  have p47 : p 47=16*(k*1*c*d) := by rw [show p 47=_ from scaledProduct h k q c d 47]; change 16*(1*c*d*k)=_; grind only
  have p48 : p 48=16*(1*c*d*(h+2*k+3*q)) := by rw [show p 48=_ from scaledProduct h k q c d 48]; change 16*((h+2*k+3*q)*1*c*d)=_; grind only
  have p49 : p 49=16*(d*d*d*d) := by rw [show p 49=_ from scaledProduct h k q c d 49]; change 16*(d*d*d*d)=_; grind only
  have p50 : p 50=16*(d*d*d*q) := by rw [show p 50=_ from scaledProduct h k q c d 50]; change 16*(d*d*d*q)=_; grind only
  have p51 : p 51=16*(c*(h+k+q)*(k+q)*q) := by rw [show p 51=_ from scaledProduct h k q c d 51]; change 16*((h+k+q)*(k+q)*c*q)=_; grind only
  have p52 : p 52=16*(c*h*q*(k+q+q)) := by rw [show p 52=_ from scaledProduct h k q c d 52]; change 16*((k+q+q)*c*h*q)=_; grind only
  have p53 : p 53=16*(c*k*(h+k+q)*q) := by rw [show p 53=_ from scaledProduct h k q c d 53]; change 16*((h+k+q)*c*k*q)=_; grind only
  let n := Int.cast (R:=R) (shared w); let v := Int.cast (R:=R) (high w); let x := Int.cast (R:=R) (missing w)
  let U := pairVal h k q c d 1 w+pairVal h k q c d 2 w
  let V := pairVal h k q c d 1 w
  let L := -32*U+32*c*d*n-(if r.single then 32*c*(k+q+q)*x else 0)
  let M := -32*V+32*d*d*v-16*(1-d)*(c-d)*tail2 r n v-(if r.single then 32*c*q*x else 0)
  let T := 32*Int.cast (R:=R) (enter w)*d*(1-c)
  have clearEq (u v : R) (eq : v-u=(707*lambda-Int.cast r.l*(h*q))*L+
      (707*mu-Int.cast r.y*(k*(h+k+q)))*M+(707*cross-200*((1+q)*h))*T) : u=v := by
    rw [l,y,a] at eq; grind only
  apply clearEq
  clear clearEq l y a P Q S
  cases choice : r.single <;> simp only [raw,twiceBound,L,M,T,U,V,x,n,v,choice,Bool.false_eq_true,ite_false,ite_true,p42,p34,p43,p44,p41,p45,p46,p47,p48,p49,p50,p51,p52,p53] <;> grind only
end RankSeven.UpperCornerSignedIdentity
#print axioms RankSeven.UpperCornerSignedIdentity.physicalPrice