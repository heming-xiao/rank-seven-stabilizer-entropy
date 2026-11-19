import Rank7UpperCornerExpansion
namespace RankSeven.UpperPackedCoordinates
open Lean.Grind Pauli
def base : Int := 1000000000000000000000000
def pack {α : Type} (xs : List α) (f : α→Int) : Int := match xs with
  | [] => 0
  | i::is => f i+base*pack is f
theorem packAdd {α : Type} (xs : List α) (f g : α→Int) :
    pack xs (fun i => f i+g i)=pack xs f+pack xs g := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change f i+g i+base*pack xs (fun i => f i+g i)=(f i+base*pack xs f)+(g i+base*pack xs g); rw [ih]; grind only
theorem packScale {α : Type} (xs : List α) (n : Int) (f : α→Int) : pack xs (fun i => n*f i)=n*pack xs f := by
  induction xs with
  | nil => change 0=n*0; grind only
  | cons i xs ih => change n*f i+base*pack xs (fun i => n*f i)=n*(f i+base*pack xs f); rw [ih]; grind only
theorem inject {α : Type} (xs : List α) (f g : α→Int)
    (bounded : ∀i∈xs,-base<f i-g i ∧ f i-g i<base) (equal : pack xs f=pack xs g) :
    ∀i∈xs,f i=g i := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have bound := bounded a List.mem_cons_self
    change f a+base*pack as f=g a+base*pack as g at equal
    have suffix : pack as f=pack as g := by unfold base at equal bound; omega
    have head : f a=g a := by rw [suffix] at equal; omega
    have tail := ih (fun i hi => bounded i (List.mem_cons_of_mem a hi)) suffix
    intro i hi; cases List.mem_cons.mp hi with
    | inl h => exact h ▸ head
    | inr h => exact tail i h
end RankSeven.UpperPackedCoordinates
#print axioms RankSeven.UpperPackedCoordinates.inject