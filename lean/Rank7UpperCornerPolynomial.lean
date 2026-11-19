import Rank7UpperCornerFactorsReal
import Rank7UpperCornerColumns
namespace RankSeven.UpperCornerPolynomial
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation UpperCornerExpansion UpperCornerFactors UpperCornerColumns
attribute [local instance] Ring.intCast
abbrev Term := Int×Nat
def terms (r : Branch) (w : Wedge7) : List Term :=
  let shape := ground w
  let n := shared w
  let v := high w
  let x := missing w
  let b := if r.halfTail then n else 2*v
  let m := if r.halfMiddle then v else 2*n
  let z := match r.floor.val with | 0 => 5*n | 1 => 4*v | _ => 4*n+2*v
  let j := if r.charge then 4*n+2*v-3*m-2*x else 0
  [(1414,shape.1.1),(-2*r.l*v,shape.1.2),(-2*r.l*second w,shape.2.1),(-2*r.y*v,shape.2.2),
    (400*enter w,42),(-2*(707-r.l)*n,34),(-2*(707-r.y)*v,45),((707-r.y)*b,46)]++
  (if r.single then [(707*m,48),(707*z,49),(707*j,50),(1414*x,51),(-2*r.l*x,52),(-2*r.y*x,53)]
   else [(1414*n,43),(4242*n,44),(3535*n,41),(1414*v,47)])
private theorem sumAppend {C α : Type} [CommRing C] (a b : List α) (f : α→C) :
    sumOver (a++b) f=sumOver a f+sumOver b f := by
  induction a with
  | nil => change sumOver b f=0+sumOver b f; grind only
  | cons h a ih => change f h+sumOver (a++b) f=(f h+sumOver a f)+sumOver b f; rw [ih]; grind only
theorem polynomialCoeff (r : Branch) (w : Wedge7) (m : Key) :
    sumOver (terms r w) (fun pr => pr.1*fast pr.2 m)=term r m w := by
  have f : feature 0 m w=fast (ground w).1.1 m := rfl
  have g : feature 1 m w=high w*fast (ground w).1.2 m := rfl
  have h : feature 2 m w=second w*fast (ground w).2.1 m := rfl
  have j : feature 3 m w=high w*fast (ground w).2.2 m := rfl
  cases chosen : r.single <;> simp only [terms,term,slopes,f,g,h,j,chosen,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> grind only
private theorem shapesOk : wedges.all (fun w => let s := ground w; decide (s.1.1<54 ∧ s.1.2<54 ∧ s.2.1<54 ∧ s.2.2<54))=true := by decide
theorem termInRange (r : Branch) (w : Wedge7) (p : Term) (hp : p∈terms r w) : p.2<54 := by
  have hw := _root_.of_decide_eq_true (List.all_eq_true.mp shapesOk w (memWedges w))
  change (ground w).1.1<54 ∧ (ground w).1.2<54 ∧ (ground w).2.1<54 ∧ (ground w).2.2<54 at hw
  unfold terms at hp
  cases chosen : r.single <;> simp only [chosen,Bool.false_eq_true,ite_false,ite_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  all_goals rcases hp with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> first | decide | exact hw.1 | exact hw.2.1 | exact hw.2.2.1 | exact hw.2.2.2
  · rcases h with rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> first | decide | exact hw.1 | exact hw.2.1 | exact hw.2.2.1 | exact hw.2.2.2
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide

variable {R : Type} [CommRing R]
def price (r : Branch) (v : Var→R) (w : Wedge7) := sumOver (terms r w) (fun term => Int.cast term.1*eval v (pattern term.2))
private theorem castSum {α : Type} (xs : List α) (f : α→Int) :
    Int.cast (R:=R) (sumOver xs f)=sumOver xs (fun i => Int.cast (f i)) := by
  induction xs with
  | nil => exact Ring.intCast_zero
  | cons a as ih => change Int.cast (f a+sumOver as f)=_; rw [Ring.intCast_add,ih]; rfl

theorem priceExpansion (r : Branch) (v : Var→R) (w : Wedge7) :
    price r v w=sumOver keys (fun m => Int.cast (term r m w)*mon v m) := by
  unfold price
  have each (pr : Term) (hp : pr∈terms r w) : Int.cast pr.1*eval v (pattern pr.2)=
      sumOver keys (fun m => Int.cast (pr.1*fast pr.2 m)*mon v m) := by
    rw [realExpansion v pr.2 (termInRange r w pr hp),sumOverMulLeft]
    apply sumOverCongr; intro m; rw [Ring.intCast_mul]; grind only
  rw [AnticommutingDefect.sumCongrMem _ _ _ each,sumOverSwap]
  apply sumOverCongr; intro m
  rw [←polynomialCoeff,castSum,sumOverMulRight]

private theorem inc (r : Branch) (v : Var→R) (x : Wedge7→R) :
    evaluate x (price r v)=sumOver keys (fun m => mon v m*UpperCornerDual.val x (term r m)) := by
  unfold evaluate UpperCornerDual.val
  simp only [priceExpansion,sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap]; apply sumOverCongr; intro m; apply sumOverCongr; intro w; grind only

theorem gainExpansion (r : Branch) (v : Var→R) (x : Wedge7→R) :
    gain x (price r v)=sumOver keys (fun m => mon v m*gain x (fun w => Int.cast (term r m w))) := by
  unfold gain; rw [inc,inc,←Compression.sumOverSub]; apply sumOverCongr; intro m
  change mon v m*UpperCornerDual.val x (term r m)-mon v m*UpperCornerDual.val referenceWeight (term r m)=
    mon v m*(UpperCornerDual.val x (term r m)-UpperCornerDual.val referenceWeight (term r m)); grind only
end RankSeven.UpperCornerPolynomial
#print axioms RankSeven.UpperCornerPolynomial.gainExpansion