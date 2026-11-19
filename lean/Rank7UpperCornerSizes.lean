import Rank7UpperCornerColumns
namespace RankSeven.UpperCornerSizes
set_option maxRecDepth 8192
open Lean.Grind Pauli UpperCornerDual UpperSignedData UpperCornerExpansion UpperCornerFactors UpperCornerColumns ExteriorCuts
private abbrev bounded (x : Int) (n : Nat) := x.natAbs≤n
private theorem add {x y : Int} {a b : Nat} (u : bounded x a) (v : bounded y b) : bounded (x+y) (a+b) :=
  Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add u v)
private theorem sub {x y : Int} {a b : Nat} (u : bounded x a) (v : bounded y b) : bounded (x-y) (a+b) :=
  Nat.le_trans (Int.natAbs_sub_le _ _) (Nat.add_le_add u v)
private theorem mul {x y : Int} {a b : Nat} (u : bounded x a) (v : bounded y b) : bounded (x*y) (a*b) := by
  unfold bounded; rw [Int.natAbs_mul]; exact Nat.mul_le_mul u v
private theorem neg {x : Int} {a : Nat} (h : bounded x a) : bounded (-x) a := by simpa only [bounded,Int.natAbs_neg] using h
private theorem val (n : Int) : bounded n n.natAbs := Nat.le_refl _
private theorem enlarge {x : Int} {b n : Nat} (h : bounded x n) (k : n≤b) : bounded x b := Nat.le_trans h k

private theorem atArray {α : Type} (a : Array α) (p : α→Bool) (d : α) (pd : p d=true) (ok : a.toList.all p=true) (i : Nat) :
    p (a[i]?.getD d)=true := by
  cases eq : a[i]? with
  | none => exact pd
  | some x =>
    have h : x∈a.toList := by simpa using (Array.mem_of_getElem? eq)
    exact List.all_eq_true.mp ok x h

set_option maxRecDepth 6000 in
private theorem table : precomputed.toList.all (fun a => a.toList.all (fun v => decide (v.natAbs≤648)))=true := by decide
private theorem fastBound (i : Nat) (m : Key) : bounded (fast i m) 648 := by
  have a := atArray precomputed _ #[] (by decide) table i
  exact _root_.of_decide_eq_true (atArray _ _ 0 (by decide) a (index m))

set_option maxRecDepth 6000 in
private theorem limits : selection.toList.all (fun a => a.toList.all (fun p => decide (p.1<286 ∧ p.2≤33936)))=true := by decide
theorem selectionLimits (j : Nat) (m : Key) : (sel j m).1<286 ∧ (sel j m).2≤33936 := by
  have a := atArray selection _ #[] (by decide) limits j
  exact _root_.of_decide_eq_true (atArray _ _ (0,0) (by decide) a (index m))

set_option maxRecDepth 6000 in
private theorem objectives : allData.toList.all (fun a => a.val.coeff.toList.all (fun c => decide (c.natAbs≤23245)))=true := by decide
private theorem objBound (j : Nat) (w : Wedge7) : bounded ((objective j).cost w) 23245 := by
  have b := atArray allData _ ⟨obj0,ok0⟩ (by decide) objectives j
  exact _root_.of_decide_eq_true (atArray _ _ (0:Int) (by decide) b (slot w))

private theorem slopesBound (r : Branch) (f : Nat→Int) (hf : ∀i,bounded (f i) 648)
    (n v x : Int) (hn : bounded n 2) (hv : bounded v 1) (hx : bounded x 1) :
    bounded (slopes r f n v x) 1000000000 := by
  have hl : bounded r.l 150 := by unfold Branch.l; split <;> decide
  have hy : bounded r.y 175 := by unfold Branch.y; split <;> decide
  let b := if r.halfTail then n else 2*v
  let m := if r.halfMiddle then v else 2*n
  let z := match r.floor.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v
  let e := if r.charge then 4*n+2*v-3*m-2*x else 0
  have hb : bounded b 2 := by unfold b; split; exact hn; exact mul (val 2) hv
  have hm : bounded m 4 := by unfold m; split; exact enlarge hv (by decide); exact mul (val 2) hn
  have hz : bounded z 12 := by unfold z; split <;> first | exact enlarge (mul (val 5) hn) (by decide) | exact enlarge (mul (val 4) hv) (by decide) | exact enlarge (add (mul (val 4) hn) (mul (val 2) hv)) (by decide)
  have he : bounded e 24 := by unfold e; split; exact sub (sub (add (mul (val 4) hn) (mul (val 2) hv)) (mul (val 3) hm)) (mul (val 2) hx); decide
  let core := -2*(707-r.l)*f 34*n-2*(707-r.y)*f 45*v+(707-r.y)*f 46*b
  have hc : bounded core 10000000 := enlarge (add (sub (mul (mul (mul (val (-2)) (sub (val 707) hl)) (hf 34)) hn) (mul (mul (mul (val 2) (sub (val 707) hy)) (hf 45)) hv)) (mul (mul (sub (val 707) hy) (hf 46)) hb)) (by decide)
  change bounded (if r.single then core+707*f 48*m+707*f 49*z+707*f 50*e+(1414*f 51-2*r.l*f 52-2*r.y*f 53)*x else core+(1414*f 43+4242*f 44+3535*f 41)*n+1414*f 47*v) _
  split
  · exact enlarge (add (add (add (add hc (mul (mul (val 707) (hf 48)) hm)) (mul (mul (val 707) (hf 49)) hz)) (mul (mul (val 707) (hf 50)) he)) (mul (sub (sub (mul (val 1414) (hf 51)) (mul (mul (val 2) hl) (hf 52))) (mul (mul (val 2) hy) (hf 53))) hx)) (by decide)
  · exact enlarge (add (add hc (mul (add (add (mul (val 1414) (hf 43)) (mul (val 4242) (hf 44))) (mul (val 3535) (hf 41))) hn)) (mul (mul (val 1414) (hf 47)) hv)) (by decide)

theorem digitRange (j : Nat) (m : Key) (w : Wedge7) :
    -UpperPackedCoordinates.base <term (tag j) m w-(sel j m).2*(objective (sel j m).1).cost w ∧
      term (tag j) m w-(sel j m).2*(objective (sel j m).1).cost w <UpperPackedCoordinates.base := by
  let r := tag j
  have hi : bounded (high w) 1 := by unfold high; split <;> decide
  have se : bounded (second w) 1 := by unfold second; split <;> decide
  have mi : bounded (missing w) 1 := by unfold missing; split <;> decide
  have en : bounded (enter w) 1 := by unfold enter; split <;> decide
  have sf := add hi se
  have featB (l : Fin 4) : bounded (feature l m w) 648 := by
    unfold feature; split <;> first | exact fastBound _ _ | exact mul hi (fastBound _ _) | exact mul se (fastBound _ _)
  have hl : bounded r.l 150 := by unfold Branch.l; split <;> decide
  have hy : bounded r.y 175 := by unfold Branch.y; split <;> decide
  have tr : bounded (term r m w) 2000000000 := enlarge (add (add (sub (sub (mul (val 1414) (featB 0)) (mul (mul (val 2) hl) (add (featB 1) (featB 2)))) (mul (mul (val 2) hy) (featB 3))) (mul (mul (val 400) (fastBound 42 m)) en)) (slopesBound _ _ (fun i => fastBound i m) _ _ _ sf hi mi)) (by decide)
  have num : bounded ((sel j m).2:Int) 33936 := (selectionLimits j m).2
  have diff := sub tr (mul num (objBound (sel j m).1 w))
  let result := term r m w-(sel j m).2*(objective (sel j m).1).cost w
  change result.natAbs≤2000000000+33936*23245 at diff
  have lo := Int.le_natAbs (a:=-result)
  rw [Int.natAbs_neg] at lo
  have high := Int.le_natAbs (a:=result)
  change -UpperPackedCoordinates.base<result ∧ result<UpperPackedCoordinates.base; unfold UpperPackedCoordinates.base; omega
end RankSeven.UpperCornerSizes
#print axioms RankSeven.UpperCornerSizes.digitRange