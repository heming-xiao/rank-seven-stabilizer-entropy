import Rank7HighestPhysicalConcentration

namespace RankSeven.HighestExteriorStability

open Lean.Grind Pauli ComplexScalar SymmetricDefect
open PauliPairContraction (normSum)
open HighestCodeLocalization (innerProduct)
variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- Quadratic data restricted to a four-component decomposition of a two-form. -/
structure Form (R : Type) where
  q0 : R
  q1 : R
  q2 : R
  q3 : R
  q01 : R
  q02 : R
  q03 : R
  q12 : R
  q13 : R
  q23 : R

def value (q : Form R) (a b c d : R) := q.q0*a^2+q.q1*b^2+q.q2*c^2+q.q3*d^2+
  2*(q.q01*a*b+q.q02*a*c+q.q03*a*d+q.q12*b*c+q.q13*b*d+q.q23*c*d)

def diagonal (n0 n1 n2 n3 a b c d : R) := n0*a^2+n1*b^2+n2*c^2+n3*d^2

theorem compressionStability (q : Form R) (n0 n1 n2 n3 e : R)
    (nonneg : ∀a b c d,0≤value q a b c d)
    (upper : ∀a b c d,2*value q a b c d≤5*diagonal n0 n1 n2 n3 a b c d)
    (first : value q 1 2 0 0≤2*diagonal n0 n1 n2 n3 1 2 0 0)
    (second : value q 1 0 2 0≤2*diagonal n0 n1 n2 n3 1 0 2 0)
    (mass : n0+n1+n2+n3=1) (lastNonnegative : 0≤n3)
    (single : n1+n2≤2*e) (last : n3≤e^2) (en : 0≤e) :
    2*(value q 1 1 1 1-2)≤13*e+e^2 := by
  let S := q.q03+q.q13+q.q23
  have pos := nonneg 0 1 (-1) 0
  have tail := upper 0 0 0 1
  have plus := upper (4*S) (4*S) (4*S) 5
  have minus := nonneg (4*S) (4*S) (4*S) (-5)
  have firstBound : value q 1 1 1 0≤2*(n0+n1+n2)+2*(n1+n2) := by
    simp only [value,diagonal] at first second pos ⊢; grind only
  have nsum := OrderedRing.mul_nonneg lastNonnegative (squareNonnegative S)
  have combined : 16*S^2≤25*n3 := by
    have eq : value q (4*S) (4*S) (4*S) 5-value q (4*S) (4*S) (4*S) (-5)=80*S^2 := by
      unfold value S; grind only
    have d : diagonal n0 n1 n2 n3 (4*S) (4*S) (4*S) 5=16*S^2*(1-n3)+25*n3 := by
      unfold diagonal; grind only
    rw [d] at plus
    grind only
  have cross : 4*S≤5*e := by
    by_cases ok : 4*S≤5*e
    · exact ok
    · have bad := OrderedRing.mul_pos (show 0<4*S-5*e by grind only) (show 0<4*S+5*e by grind only)
      grind only
  have id : value q 1 1 1 1=value q 1 1 1 0+q.q3+2*S := by unfold value S; grind only
  have q3 : 2*q.q3≤5*n3 := by unfold value diagonal at tail; grind only
  rw [id]; grind only

theorem physicalHighestRate {e v kappa : R} (small : 20*e≤1) (paid : 6137*e≤2000*kappa)
    (en : 0≤e) (stability : 2*v≤13*e+e^2) :
    2*v≤5*kappa := by
  have q := OrderedRing.mul_le_mul_of_nonneg_right small en
  grind only

def output (z : α→Fin 4→ComplexScalar R) (a b c d : R) (i : α) :=
  ofReal a*z i 0+ofReal b*z i 1+ofReal c*z i 2+ofReal d*z i 3

def columnForm (xs : List α) (scale : R) (z : α→Fin 4→ComplexScalar R) : Form R :=
  let n i := scale*sumOver xs (fun t => normSq (z t i))
  let e i j := scale*sumOver xs (fun t => (star (z t i)*z t j).re)
  ⟨n 0,n 1,n 2,n 3,e 0 1,e 0 2,e 0 3,e 1 2,e 1 3,e 2 3⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem columnValue (xs : List α) (scale : R) (z : α→Fin 4→ComplexScalar R) (a b c d : R) :
    value (columnForm xs scale z) a b c d=scale*normSum xs (output z a b c d) := by
  induction xs with
  | nil =>
    change value ⟨scale*0,scale*0,scale*0,scale*0,scale*0,scale*0,scale*0,scale*0,scale*0,scale*0⟩ a b c d=scale*0
    unfold value; grind only
  | cons i is ih =>
    let u (j : Fin 4) := z i j
    let G := columnForm is scale z
    let f (j : Fin 4) := normSq (u j)
    let g (j k : Fin 4) := (star (u j)*u k).re
    let v : Form R := ⟨f 0,f 1,f 2,f 3,g 0 1,g 0 2,g 0 3,g 1 2,g 1 3,g 2 3⟩
    have add : value (columnForm (i::is) scale z) a b c d=scale*value v a b c d+value G a b c d := by
      simp only [G,v,value,columnForm,sumOver,List.map_cons,List.sum_cons,f,g,u]; grind only
    have point : value v a b c d=normSq (output z a b c d i) := by
      simp only [v,value,f,g,u,output,normSq,re_add,im_add,re_mul,im_mul,re_star,im_star,re_ofReal,im_ofReal]
      grind only
    change value (columnForm (i::is) scale z) a b c d=scale*(normSq (output z a b c d i)+normSum is (output z a b c d))
    rw [add,point]; change scale*normSq (output z a b c d i)+value (columnForm is scale z) a b c d=_
    rw [ih]; grind only

theorem componentStability (xs : List α) (scale : R) (sn : 0≤scale) (z : α→Fin 4→ComplexScalar R) (n0 n1 n2 n3 e : R)
    (bound : ∀a b c d,2*(scale*normSum xs (output z a b c d))≤5*diagonal n0 n1 n2 n3 a b c d)
    (first : scale*normSum xs (output z 1 2 0 0)≤2*diagonal n0 n1 n2 n3 1 2 0 0)
    (second : scale*normSum xs (output z 1 0 2 0)≤2*diagonal n0 n1 n2 n3 1 0 2 0)
    (mass : n0+n1+n2+n3=1) (lastNonnegative : 0≤n3)
    (single : n1+n2≤2*e) (last : n3≤e^2) (en : 0≤e) :
    2*(scale*normSum xs (output z 1 1 1 1)-2)≤13*e+e^2 := by
  let q := columnForm xs scale z
  have v (a b c d : R) : value q a b c d=scale*normSum xs (output z a b c d) := columnValue _ _ _ _ _ _ _
  have pos (a b c d : R) : 0≤value q a b c d := by
    rw [v]; exact OrderedRing.mul_nonneg sn (Compression.sumOverNonnegative _ _ (fun i _ => normSq_nonnegative _))
  rw [←v]; exact compressionStability q n0 n1 n2 n3 e pos (fun a b c d => by rw [v]; exact bound _ _ _ _)
    (by rw [v]; exact first) (by rw [v]; exact second) mass lastNonnegative single last en

end RankSeven.HighestExteriorStability

#print axioms RankSeven.HighestExteriorStability.compressionStability
#print axioms RankSeven.HighestExteriorStability.componentStability
#print axioms RankSeven.HighestExteriorStability.physicalHighestRate

