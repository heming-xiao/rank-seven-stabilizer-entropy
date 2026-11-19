import Rank7UpperCornerPolynomial
namespace RankSeven.UpperCornerFrameProducts
open Lean.Grind Pauli UpperCornerExpansion UpperCornerFactors UpperCornerColumns UpperCornerPolynomial ExteriorCuts PackingDual UpperFrameGain UpperPhysicalInterior
attribute [local instance] Ring.intCast
variable {R : Type} [CommRing R]
def vector (h k q c d : R) (i : Var) : R :=
  match i.val with | 0 => h | 1 => k | 2 => 2*q-1 | 3 => 1-c | 4 => c-d | _ => d
def physicalAtom (h k q c d : R) : Atom→R
  | .h => h | .k => k | .q => q | .b => 1 | .c => c | .d => d | .t => 1-c | .e => c-d
  | .X => h+k+q | .Y => k+q | .YQ => k+q+q | .L => h+2*k+3*q | .bd => 1-d
  | .alpha => 1+(h+k+q) | .beta => 1+(k+q) | .gamma => 1+q

theorem scaledAtom (h k q c d : R) (a : Atom) :
    linear (vector h k q c d) a.form=2*physicalAtom h k q c d a := by
  cases a
  · change Int.cast (R:=R) (2:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (0:Int)*(1-c)+(Int.cast (R:=R) (0:Int)*(c-d)+(Int.cast (R:=R) (0:Int)*(d)+(0))))))=2*physicalAtom h k q c d .h; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (0:Int)*(1-c)+(Int.cast (R:=R) (0:Int)*(c-d)+(Int.cast (R:=R) (0:Int)*(d)+(0))))))=2*physicalAtom h k q c d .k; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (1:Int)*(1-c)+(Int.cast (R:=R) (1:Int)*(c-d)+(Int.cast (R:=R) (1:Int)*(d)+(0))))))=2*physicalAtom h k q c d .q; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (2:Int)*(1-c)+(Int.cast (R:=R) (2:Int)*(c-d)+(Int.cast (R:=R) (2:Int)*(d)+(0))))))=2*physicalAtom h k q c d .b; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (0:Int)*(1-c)+(Int.cast (R:=R) (2:Int)*(c-d)+(Int.cast (R:=R) (2:Int)*(d)+(0))))))=2*physicalAtom h k q c d .c; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (0:Int)*(1-c)+(Int.cast (R:=R) (0:Int)*(c-d)+(Int.cast (R:=R) (2:Int)*(d)+(0))))))=2*physicalAtom h k q c d .d; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (2:Int)*(1-c)+(Int.cast (R:=R) (0:Int)*(c-d)+(Int.cast (R:=R) (0:Int)*(d)+(0))))))=2*physicalAtom h k q c d .t; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (0:Int)*(1-c)+(Int.cast (R:=R) (2:Int)*(c-d)+(Int.cast (R:=R) (0:Int)*(d)+(0))))))=2*physicalAtom h k q c d .e; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (2:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (1:Int)*(1-c)+(Int.cast (R:=R) (1:Int)*(c-d)+(Int.cast (R:=R) (1:Int)*(d)+(0))))))=2*physicalAtom h k q c d .X; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (1:Int)*(1-c)+(Int.cast (R:=R) (1:Int)*(c-d)+(Int.cast (R:=R) (1:Int)*(d)+(0))))))=2*physicalAtom h k q c d .Y; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (2:Int)*(2*q-1)+(Int.cast (R:=R) (2:Int)*(1-c)+(Int.cast (R:=R) (2:Int)*(c-d)+(Int.cast (R:=R) (2:Int)*(d)+(0))))))=2*physicalAtom h k q c d .YQ; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (2:Int)*(h)+(Int.cast (R:=R) (4:Int)*(k)+(Int.cast (R:=R) (3:Int)*(2*q-1)+(Int.cast (R:=R) (3:Int)*(1-c)+(Int.cast (R:=R) (3:Int)*(c-d)+(Int.cast (R:=R) (3:Int)*(d)+(0))))))=2*physicalAtom h k q c d .L; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (0:Int)*(2*q-1)+(Int.cast (R:=R) (2:Int)*(1-c)+(Int.cast (R:=R) (2:Int)*(c-d)+(Int.cast (R:=R) (0:Int)*(d)+(0))))))=2*physicalAtom h k q c d .bd; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (2:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (3:Int)*(1-c)+(Int.cast (R:=R) (3:Int)*(c-d)+(Int.cast (R:=R) (3:Int)*(d)+(0))))))=2*physicalAtom h k q c d .alpha; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (2:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (3:Int)*(1-c)+(Int.cast (R:=R) (3:Int)*(c-d)+(Int.cast (R:=R) (3:Int)*(d)+(0))))))=2*physicalAtom h k q c d .beta; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
  · change Int.cast (R:=R) (0:Int)*(h)+(Int.cast (R:=R) (0:Int)*(k)+(Int.cast (R:=R) (1:Int)*(2*q-1)+(Int.cast (R:=R) (3:Int)*(1-c)+(Int.cast (R:=R) (3:Int)*(c-d)+(Int.cast (R:=R) (3:Int)*(d)+(0))))))=2*physicalAtom h k q c d .gamma; dsimp only [physicalAtom]; grind only [Ring.intCast_ofNat]
def fourProduct {C : Type} [CommRing C] (f : Atom→C) (p : Four Atom) := f p.1.1*f p.1.2*f p.2.1*f p.2.2
theorem scaledProduct (h k q c d : R) (j : Nat) :
    eval (vector h k q c d) (pattern j)=16*fourProduct (physicalAtom h k q c d) (shape j) := by
  unfold eval pattern fourProduct; dsimp only; simp only [scaledAtom]; grind only

def weightAt (i : Fin 7) : Atom := match i.val with | 0 => .alpha | 1 => .beta | 2 => .gamma | 5 => .c | 6 => .d | _ => .b
def weightWith (firstAtom secondAtom : Atom) (j i : Fin 7) : Atom := if i=0 then firstAtom else if i=j then secondAtom else weightAt i
def wedgeAtoms (weight : Fin 7→Atom) (w : Wedge7) : Four Atom := ((weight w.i,weight w.j),weight w.k,weight w.m)
private def listOf {α : Type} (p : Four α) := [p.1.1,p.1.2,p.2.1,p.2.2]
private def test (w : Wedge7) :=
  let sh := ground w
  decide ((listOf (shape sh.1.1)).Perm (listOf (wedgeAtoms weightAt w))) &&
  (!(occupied w 0 && occupied w 1) || decide ((listOf (shape sh.1.2)).Perm (listOf (wedgeAtoms (weightWith .h .q 1) w)) ∧
    (listOf (shape sh.2.2)).Perm (listOf (wedgeAtoms (weightWith .k .X 1) w)))) &&
  (!(occupied w 0 && occupied w 2) || decide ((listOf (shape sh.2.1)).Perm (listOf (wedgeAtoms (weightWith .h .q 2) w))))
private theorem shapes : wedges.all test=true := by decide
private theorem permProd {C : Type} [CommRing C] (l : Atom→C) {a b : List Atom} (p : a.Perm b) :
    (a.map l).prod=(b.map l).prod := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,List.prod_cons]; rw [ih]
  | swap => simp only [List.map_cons,List.prod_cons]; grind only
  | trans _ _ h₁ h₂ => exact h₁.trans h₂
private theorem sameProd (f : Atom→R) {s u : Four Atom} (h : (listOf s).Perm (listOf u)) :
    fourProduct f s=fourProduct f u := by
  have e := permProd f h
  change f s.1.1*(f s.1.2*(f s.2.1*(f s.2.2*1)))=f u.1.1*(f u.1.2*(f u.2.1*(f u.2.2*1))) at e
  unfold fourProduct; grind only

theorem physicalWedgeProducts (w : Wedge7) (f : Atom→R) :
    let g := ground w
    fourProduct f (shape g.1.1)=amplitude (fun i => f (weightAt i)) w ∧
    ((occupied w 0 && occupied w 1)=true →
      fourProduct f (shape g.1.2)=amplitude (fun i => f (weightWith .h .q 1 i)) w ∧
      fourProduct f (shape g.2.2)=amplitude (fun i => f (weightWith .k .X 1 i)) w) ∧
    ((occupied w 0 && occupied w 2)=true →
      fourProduct f (shape g.2.1)=amplitude (fun i => f (weightWith .h .q 2 i)) w) := by
  have checked := List.all_eq_true.mp shapes w (memWedges w)
  unfold test at checked
  have second := Bool.and_eq_true_iff.mp checked
  have first := Bool.and_eq_true_iff.mp second.1
  refine ⟨sameProd f (_root_.of_decide_eq_true first.1),?_,?_⟩
  · intro h
    have z := first.2; simp only [h,Bool.not_true,Bool.false_or] at z
    obtain ⟨a,b⟩ := _root_.of_decide_eq_true z
    exact ⟨sameProd f a,sameProd f b⟩
  · intro h
    have z := second.2; simp only [h,Bool.not_true,Bool.false_or] at z
    exact sameProd f (_root_.of_decide_eq_true z)
end RankSeven.UpperCornerFrameProducts
#print axioms RankSeven.UpperCornerFrameProducts.physicalWedgeProducts
#print axioms RankSeven.UpperCornerFrameProducts.scaledProduct