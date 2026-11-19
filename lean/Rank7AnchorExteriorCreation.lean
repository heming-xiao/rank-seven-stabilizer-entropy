import Rank7AnchorSteinerTest

namespace RankSeven.AnchorExteriorCreation
open Lean.Grind Pauli ComplexScalar AnchorSteinerTest
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

def raise (y : I→C) : (L : List I) → (Basis L.length→C) → (Basis L.length→C)
  | [],_,_ => 0
  | _::L,v,(false,z) => raise y L (fun w=>v (false,w)) z
  | i::L,v,(true,z) => y i*v (false,z)-raise y L (fun w=>v (true,w)) z

def lower (y : I→C) : (L : List I) → (Basis L.length→C) → (Basis L.length→C)
  | [],_,_ => 0
  | i::L,v,(false,z) => star (y i)*v (true,z)+lower y L (fun w=>v (false,w)) z
  | _::L,v,(true,z) => -lower y L (fun w=>v (true,w)) z

def gram {d : Nat} (f g : Basis d→C) := sumOver (qubitIndices d) fun z=>star (f z)*g z
private theorem sumBits {V : Type} [CommRing V] {d : Nat} (f : Basis (d+1)→V) :
    sumOver (qubitIndices (d+1)) f = sumOver (qubitIndices d) (fun z=>f (false,z))+
      sumOver (qubitIndices d) (fun z=>f (true,z)) := by
  change Bool × Basis d → V at f
  change sumOver (productIndices [false,true] (qubitIndices d)) f=_
  have app (xs ys : List V) : (xs++ys).sum=xs.sum+ys.sum := by
    induction xs with
    | nil => change ys.sum=0+ys.sum; grind only
    | cons v xs ih => change v+(xs++ys).sum=v+xs.sum+ys.sum; rw [ih]; grind only
  simp [sumOver,productIndices,List.map_append,app,List.map_map,Function.comp_def]

private theorem gramBits {d : Nat} (f g : Basis (d+1)→C) :
    gram f g=gram (fun z=>f (false,z)) (fun z=>g (false,z))+gram (fun z=>f (true,z)) (fun z=>g (true,z)) := sumBits _

private theorem leftAdd {d : Nat} (f g v : Basis d→C) :
    gram (fun z=>f z+g z) v=gram f v+gram g v := by
  unfold gram; rw [←sumOverAdd]; apply sumOverCongr; intro z; rw [star_add]; grind only
private theorem rightAdd {d : Nat} (f g v : Basis d→C) :
    gram v (fun z=>f z+g z)=gram v f+gram v g := by
  unfold gram; rw [←sumOverAdd]; apply sumOverCongr; intro z; grind only
private theorem leftScale {d : Nat} (c : C) (f v : Basis d→C) :
    gram (fun z=>c*f z) v=star c*gram f v := by
  unfold gram; rw [sumOverMulLeft]; apply sumOverCongr; intro z; rw [star_mul]; grind only
private theorem rightScale {d : Nat} (c : C) (f v : Basis d→C) :
    gram v (fun z=>c*f z)=c*gram v f := by
  unfold gram; rw [sumOverMulLeft]; apply sumOverCongr; intro z; grind only
private theorem starNeg (z : C) : star (-z) = -star z := by apply ComplexScalar.ext <;> simp <;> grind only
private theorem leftNeg {d : Nat} (f v : Basis d→C) : gram (fun z=> -f z) v= -gram f v := by
  have e (z:Basis d) : -f z=(-1)*f z := by grind only
  rw [show (fun z=> -f z)=fun z=>(-1)*f z from funext e,leftScale,starNeg]
  have one : star (1:C)=1 := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [one]; grind only
private theorem rightNeg {d : Nat} (f v : Basis d→C) : gram v (fun z=> -f z)= -gram v f := by
  have e (z:Basis d) : -f z=(-1)*f z := by grind only
  rw [show (fun z=> -f z)=fun z=>(-1)*f z from funext e,rightScale]; grind only
private theorem leftSub {d : Nat} (f g v : Basis d→C) :
    gram (fun z=>f z-g z) v=gram f v-gram g v := by
  have e (z:Basis d) : f z-g z=f z+-g z := by grind only
  rw [show (fun z=> f z-g z)=fun z=>f z+-g z from funext e,leftAdd,leftNeg]; grind only
private theorem rightSub {d : Nat} (f g v : Basis d→C) :
    gram v (fun z=>f z-g z)=gram v f-gram v g := by
  have e (z:Basis d) : f z-g z=f z+-g z := by grind only
  rw [show (fun z=> f z-g z)=fun z=>f z+-g z from funext e,rightAdd,rightNeg]; grind only

theorem adjoint (y : I→C) (L : List I) (f g : Basis L.length→C) :
    gram (raise y L f) g=gram f (lower y L g) ∧ gram (lower y L f) g=gram f (raise y L g) := by
  induction L with
  | nil =>
    have zero : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
    change (star 0*g ()+0=star (f ())*0+0) ∧ (star 0*g ()+0=star (f ())*0+0)
    rw [zero]; grind only
  | cons i L ih =>
    rw [gramBits (raise y (i::L) f) g,gramBits f (lower y (i::L) g),
        gramBits (lower y (i::L) f) g,gramBits f (raise y (i::L) g)]
    simp only [raise,lower,leftSub,rightSub,leftAdd,rightAdd,leftNeg,rightNeg,leftScale,rightScale,star_star]
    have e:=ih (fun z=>f (false,z)) (fun z=>g (false,z))
    have h:=ih (fun z=>f (true,z)) (fun z=>g (true,z))
    grind only

theorem carGram (y : I→C) (L : List I) (f g : Basis L.length→C) :
    gram (raise y L f) (raise y L g)+gram (lower y L f) (lower y L g)=
      ofReal (sumOver L (fun i=>normSq (y i)))*gram f g := by
  induction L with
  | nil =>
    have zero : ofReal (0:R)=(0:C) := rfl
    change (star 0*0+0)+(star 0*0+0)=ofReal 0*(star (f ())*g ()+0)
    rw [zero]; grind only
  | cons i L ih =>
    rw [gramBits (raise y (i::L) f) (raise y (i::L) g),gramBits (lower y (i::L) f) (lower y (i::L) g),gramBits f g]
    simp only [raise,lower,leftSub,rightSub,leftAdd,rightAdd,leftNeg,rightNeg,leftScale,rightScale,star_star]
    have e:=ih (fun z=>f (false,z)) (fun z=>g (false,z))
    have h:=ih (fun z=>f (true,z)) (fun z=>g (true,z))
    have c:=adjoint y L (fun z=>f (false,z)) (fun z=>g (true,z))
    have d:=adjoint y L (fun z=>f (true,z)) (fun z=>g (false,z))
    have prod:=star_mul_self (y i)
    have emb : ofReal (sumOver (i::L) (fun j=>normSq (y j)))=
      ofReal (normSq (y i))+ofReal (sumOver L (fun j=>normSq (y j))) := by
      apply ComplexScalar.ext <;> simp [sumOver]; grind only
    rw [emb]; grind only

end RankSeven.AnchorExteriorCreation
#print axioms RankSeven.AnchorExteriorCreation.carGram
