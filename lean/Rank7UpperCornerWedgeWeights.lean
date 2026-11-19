import Rank7UpperCornerFrameProducts
namespace RankSeven.UpperCornerWedgeWeights
open Lean.Grind Pauli UpperCornerExpansion UpperCornerFactors UpperCornerColumns UpperCornerPolynomial UpperCornerFrameProducts ExteriorCuts PackingDual UpperFrameGain UpperPhysicalInterior
attribute [local instance] Ring.intCast
variable {R : Type} [CommRing R]
def source (h k q c d : R) : Fin 7→R := tail (fun i => if i=0 then 1+(h+k+q) else if i=1 then 1+(k+q) else if i=2 then 1+q else 1) c d
def strip (h k q c d : R) (j : Fin 7) (i : Fin 7) := if i=0∨i=j then 1 else source h k q c d i

theorem site (h k q c d : R) : (fun i => physicalAtom h k q c d (weightAt i))=source h k q c d := by
  funext i
  have cs : ∀t : Fin 7,t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6 := by decide
  rcases cs i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem singleFactor (w : Wedge7) (i : Fin 7) (x : R) :
    amplitude (fun t => if t=i then x else 1) w=(if occupied w i then x else 1) := by
  have e1 := w.ij; have e2 := w.jk; have e3 := w.km
  unfold amplitude product4 occupied
  by_cases ai : w.i=i <;> by_cases aj : w.j=i <;> by_cases ak : w.k=i <;> by_cases am : w.m=i
  all_goals first | omega | simp [ai,aj,ak,am] <;> grind only
private theorem multFactor (s t : Fin 7→R) (w : Wedge7) :
    amplitude (fun i => s i*t i) w=amplitude s w*amplitude t w := by unfold amplitude product4; grind only
theorem pairProduct (h k q c d : R) (aa bb : Atom) (j : Fin 7) (hj : j≠0)
    (w : Wedge7) (present : (occupied w 0 && occupied w j)=true) :
    amplitude (fun i => physicalAtom h k q c d (weightWith aa bb j i)) w =
      (physicalAtom h k q c d aa*physicalAtom h k q c d bb)*amplitude (strip h k q c d j) w := by
  let F := physicalAtom h k q c d
  have eq : (fun i => F (weightWith aa bb j i))=(fun i => (strip h k q c d j i*(if i=0 then F aa else 1))*(if i=j then F bb else 1)) := by
    funext i
    have e := congrFun (site h k q c d) i
    by_cases p : i=0 <;> by_cases z : i=j
    all_goals first | omega | simp [weightWith,strip,p,z,F] at * <;> grind only
  change amplitude (fun i => F (weightWith aa bb j i)) w=_
  rw [eq,multFactor,multFactor,singleFactor,singleFactor,(Bool.and_eq_true_iff.mp present).1,(Bool.and_eq_true_iff.mp present).2]
  simp only [ite_true]; dsimp only [F]; grind only

def pairVal (h k q c d : R) (j : Fin 7) (w : Wedge7) := if occupied w 0 && occupied w j then amplitude (strip h k q c d j) w else 0

theorem physicalTerms (h k q c d : R) (w : Wedge7) :
    let p := fun j => eval (vector h k q c d) (pattern j)
    let s := ground w
    p s.1.1=16*amplitude (source h k q c d) w ∧
    Int.cast (high w)*p s.1.2=16*h*q*pairVal h k q c d 1 w ∧
    Int.cast (second w)*p s.2.1=16*h*q*pairVal h k q c d 2 w ∧
    Int.cast (high w)*p s.2.2=16*k*(h+k+q)*pairVal h k q c d 1 w := by
  dsimp only
  obtain ⟨e,first,other⟩ := physicalWedgeProducts w (physicalAtom h k q c d)
  simp only [scaledProduct,e,site]
  refine ⟨True.intro,?_,?_,?_⟩
  · by_cases present : (occupied w 0 && occupied w 1)=true
    · rw [(first present).1,pairProduct h k q c d .h .q 1 (by decide) w present]
      simp [high,pairVal,present,physicalAtom]; grind only
    · simp [high,pairVal,present]; grind only
  · by_cases present : (occupied w 0 && occupied w 2)=true
    · rw [other present,pairProduct h k q c d .h .q 2 (by decide) w present]
      simp [second,pairVal,present,physicalAtom]; grind only
    · simp [second,pairVal,present]; grind only
  · by_cases present : (occupied w 0 && occupied w 1)=true
    · rw [(first present).2,pairProduct h k q c d .k .X 1 (by decide) w present]
      simp [high,pairVal,present,physicalAtom]; grind only
    · simp [high,pairVal,present]; grind only
end RankSeven.UpperCornerWedgeWeights
#print axioms RankSeven.UpperCornerWedgeWeights.physicalTerms
