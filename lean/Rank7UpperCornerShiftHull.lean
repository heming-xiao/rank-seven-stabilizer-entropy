import Rank7UpperCornerAccounting
namespace RankSeven.UpperCornerShiftHull
open Lean.Grind Pauli ExteriorCuts PackingDual UpperCornerColumns UpperCornerAccounting UpperCornerSignedIdentity UpperFrameTrace UpperFrameGain UpperPhysicalInterior
attribute [local instance] Ring.intCast
structure Layout where
  single : Bool
  halfTail : Bool
  halfMiddle : Bool
  floor : Fin 3
  charge : Bool

def Layout.branch (a : Layout) (l y : Bool) : Branch :=
  ⟨a.single,l,y,a.halfTail,if a.single then a.halfMiddle else false,if a.single then a.floor else 0,if a.single then a.charge else false⟩
def Layout.index (a : Layout) (l y : Bool) : Nat :=
  let b := (l.toNat*2+y.toNat)*2+a.halfTail.toNat
  if a.single then 8+((b*2+a.halfMiddle.toNat)*3+a.floor.val)*2+a.charge.toNat else b
private theorem table : ∀si bt mt : Bool,∀z : Fin 3,∀j l y : Bool,
    let a : Layout := ⟨si,bt,mt,z,j⟩
    a.index l y<104 ∧ tag (a.index l y)=a.branch l y := by decide

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem slope (x : Wedge7→R) (h k q c d l y a n v z : R) (r : Layout) (ls ys : Bool) :
    let F := corrected (spectrum h k q) x
    let sp := spectrum h k q
    let U := weightedProbe sp x 1 c d+weightedProbe sp x 2 c d
    let V := weightedProbe sp x 1 c d
    let b := tail2 (r.branch false false) n v
    let sg := -2*U+2*c*d*n-(if r.single then 2*c*(k+q+q)*z else 0)
    let hg := -2*V+2*d*d*v-(1-d)*(c-d)*b-(if r.single then 2*c*q*z else 0)
    2*F l y a c d-twiceBound (r.branch ls ys) h k q c d l y n v z=
      2*F 0 0 a c d-twiceBound (r.branch false false) h k q c d 0 0 n v z+l*sg+y*hg := by
  dsimp only
  cases g : r.single <;> simp only [corrected,twiceBound,tail2,middle2,floor2,extra2,Layout.branch,g,Bool.false_eq_true,ite_false,ite_true] <;> grind only

theorem fullShifts (r : Layout) (h k q c d l y a : R) (x : Wedge7→R)
    (hn : 0≤h) (kn : 0≤k) (qn : 1≤2*q) (cd : 0≤d ∧ d≤c ∧ c≤1)
    (nx : ∀w,0≤x w) (rows : RowsHold x) (n0 : 0≤sharedExcess x) (v0 : 0≤highExcess x)
    (ls : 0≤l ∧ 707*l≤150*(h*q)) (ys : 0≤y ∧ 707*y≤175*(k*(h+k+q))) (ac : 707*a=200*((1+q)*h)) :
    2*corrected (spectrum h k q) x l y a c d≤
      twiceBound (r.branch false false) h k q c d l y (sharedExcess x) (highExcess x) (missingTriple x) := by
  classical
  let n := sharedExcess x; let v := highExcess x; let z := missingTriple x
  let sp := spectrum h k q
  let U := weightedProbe sp x 1 c d+weightedProbe sp x 2 c d
  let V := weightedProbe sp x 1 c d
  let b := tail2 (r.branch false false) n v
  let G := -2*U+2*c*d*n-(if r.single then 2*c*(k+q+q)*z else 0)
  let H := -2*V+2*d*d*v-(1-d)*(c-d)*b-(if r.single then 2*c*q*z else 0)
  let li := decide (0≤G)
  let yi := decide (0≤H)
  let L : R := if li then (150*(h*q))/707 else 0
  let Y : R := if yi then (175*(k*(h+k+q)))/707 else 0
  let T := r.branch li yi
  have pp : (0:R)<707 := by have := OrderedRing.zero_lt_one (R:=R); grind only
  have lq := UpperContractor.quotientEq (150*(h*q)) pp
  have yq := UpperContractor.quotientEq (175*(k*(h+k+q))) pp
  have lc : 707*L=Int.cast (R:=R) T.l*(h*q) := by
    dsimp only [L,T,Branch.l,Layout.branch]; cases e : li <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> grind
  have yc : 707*Y=Int.cast (R:=R) T.y*(k*(h+k+q)) := by
    dsimp only [Y,T,Branch.y,Layout.branch]; cases e : yi <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> grind
  have vertex := table r.single r.halfTail r.halfMiddle r.floor r.charge li yi
  change r.index li yi<104 ∧ tag (r.index li yi)=T at vertex
  have pay := discreteBound (r.index li yi) vertex.1 h k q c d L Y a x hn kn qn cd nx rows n0 v0 (vertex.2.symm ▸ lc) (vertex.2.symm ▸ yc) ac
  rw [vertex.2] at pay
  have useL : l*G≤L*G := by
    by_cases s : 0≤G
    · have order : l≤L := by apply UpperContractor.cancelLe pp; dsimp [L,li]; simp [s]; exact Std.le_trans ls.2 (Std.le_of_eq lq.symm)
      exact OrderedRing.mul_le_mul_of_nonneg_right order s
    · have o := OrderedRing.mul_le_mul_of_nonneg_left (show G≤0 by grind only) ls.1
      dsimp only [L,li]; simp [s]; grind only
  have useY : y*H≤Y*H := by
    by_cases s : 0≤H
    · have order : y≤Y := by apply UpperContractor.cancelLe pp; dsimp [Y,yi]; simp [s]; exact Std.le_trans ys.2 (Std.le_of_eq yq.symm)
      exact OrderedRing.mul_le_mul_of_nonneg_right order s
    · have o := OrderedRing.mul_le_mul_of_nonneg_left (show H≤0 by grind only) ys.1
      dsimp only [Y,yi]; simp [s]; grind only
  let F := corrected sp x
  let B (l y : R) := twiceBound (r.branch false false) h k q c d l y n v z
  let init := 2*F 0 0 a c d-B 0 0
  have low : 2*F l y a c d-B l y=init+l*G+y*H := slope x h k q c d l y a n v z r false false
  have high : 2*F L Y a c d-twiceBound T h k q c d L Y n v z=init+L*G+Y*H := slope x h k q c d L Y a n v z r li yi
  change 2*F L Y a c d≤twiceBound T h k q c d L Y n v z at pay
  change 2*F l y a c d≤B l y
  grind only
end RankSeven.UpperCornerShiftHull
#print axioms RankSeven.UpperCornerShiftHull.fullShifts
