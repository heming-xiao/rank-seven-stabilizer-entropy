import Rank7AnchorExteriorHomogeneous

namespace RankSeven.AnchorMixedCAR
open Lean.Grind Pauli ComplexScalar AnchorExteriorCreation
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

def dot (L : List I) (x y : I→C) := sumOver L fun i=>star (x i)*y i

theorem linearRaise (y : I→C) (L : List I) (a b : C) (f g : Basis L.length→C) (z : Basis L.length) :
    raise y L (fun w=>a*f w+b*g w) z=a*raise y L f z+b*raise y L g z := by
  induction L with
  | nil => change 0=a*0+b*0; grind only
  | cons i L ih =>
    rcases z with ⟨t,z⟩; cases t <;> simp only [raise,ih] <;> grind only

theorem linearLower (y : I→C) (L : List I) (a b : C) (f g : Basis L.length→C) (z : Basis L.length) :
    lower y L (fun w=>a*f w+b*g w) z=a*lower y L f z+b*lower y L g z := by
  induction L with
  | nil => change 0=a*0+b*0; grind only
  | cons i L ih =>
    rcases z with ⟨t,z⟩; cases t <;> simp only [lower,ih] <;> grind only

theorem zeroLower (y : I→C) (L : List I) : lower y L (fun _=>0) = fun _=>0 := by
  funext z; induction L with
  | nil => rfl
  | cons _ L ih => rcases z with ⟨b,z⟩; cases b <;> simp only [lower,ih] <;> grind only

theorem negRaise (y : I→C) (L : List I) (f : Basis L.length→C) (z : Basis L.length) :
    raise y L (fun w=> -f w) z= -raise y L f z := by
  have e : (fun w=> -f w) = (fun w=>(-1)*f w+0*f w) := by funext w; grind only
  rw [e,linearRaise]; grind only

theorem negLower (y : I→C) (L : List I) (f : Basis L.length→C) (z : Basis L.length) :
    lower y L (fun w=> -f w) z= -lower y L f z := by
  have e : (fun w=> -f w) = (fun w=>(-1)*f w+0*f w) := by funext w; grind only
  rw [e,linearLower]; grind only

private theorem loSub (y : I→C) (L : List I) (a : C) (f g : Basis L.length→C) (z : Basis L.length) :
    lower y L (fun w=>a*f w-g w) z=a*lower y L f z-lower y L g z := by
  have e : (fun w=>a*f w-g w)=(fun w=>a*f w+(-1)*g w) := by funext w; grind only
  rw [e,linearLower]; grind only

private theorem loAdd (y : I→C) (L : List I) (a : C) (f g : Basis L.length→C) (z : Basis L.length) :
    lower y L (fun w=>a*f w+g w) z=a*lower y L f z+lower y L g z := by
  have e : (fun w=>a*f w+g w)=(fun w=>a*f w+1*g w) := by funext w; grind only
  rw [e,linearLower]; grind only

private theorem upAdd (y : I→C) (L : List I) (a : C) (f g : Basis L.length→C) (z : Basis L.length) :
    raise y L (fun w=>a*f w+g w) z=a*raise y L f z+raise y L g z := by
  have e : (fun w=>a*f w+g w)=(fun w=>a*f w+1*g w) := by funext w; grind only
  rw [e,linearRaise]; grind only

/-- Mixed canonical anticommutation, including distinct arbitrary complex modes. -/
theorem lowerRaise (x y : I→C) (L : List I) (f : Basis L.length→C) (z : Basis L.length) :
    lower x L (raise y L f) z+raise y L (lower x L f) z=dot L x y*f z := by
  induction L with
  | nil => change 0+0=0*f z; grind only
  | cons i L ih =>
    rcases z with ⟨b,z⟩
    have h (b : Bool) := ih (fun w=>f (b,w)) z
    have d : dot (i::L) x y=star (x i)*y i+dot L x y := rfl
    cases b <;> simp only [lower,raise,loSub,upAdd,negRaise,d] <;>
      first | (have eq:=h false; grind only) | (have eq:=h true; grind only)

theorem lowerLower (x y : I→C) (L : List I) (f : Basis L.length→C) (z : Basis L.length) :
    lower x L (lower y L f) z= -lower y L (lower x L f) z := by
  induction L with
  | nil => change 0= -0; grind only
  | cons i L ih =>
    rcases z with ⟨b,z⟩
    have h (b : Bool) := ih (fun w=>f (b,w)) z
    cases b <;> simp only [lower,loAdd,negLower] <;>
      first | (have eq:=h false; grind only) | (have eq:=h true; grind only)

theorem push (x y : I→C) (L : List I) (f : Basis L.length→C) :
    lower x L (raise y L f)=fun z=>dot L x y*f z-raise y L (lower x L f) z := by
  funext z; have h:=lowerRaise x y L f z; grind only

def three (L : List I) (a b c : I→C) (f : Basis L.length→C) := lower c L (lower b L (lower a L f))
def two (L : List I) (a b : I→C) (f : Basis L.length→C) := lower b L (lower a L f)

/-- Annihilator of the two-form obtained by contracting a∧b∧c with y.
The annihilator is antilinear in that two-form, yielding dot(a,y), etc. -/
def contracted (L : List I) (y a b c : I→C) (f : Basis L.length→C) (z:Basis L.length) :=
    dot L a y*two L b c f z-dot L b y*two L a c f z+dot L c y*two L a b f z

theorem triplePush (L : List I) (y a b c : I→C) (f : Basis L.length→C) (z : Basis L.length) :
    three L a b c (raise y L f) z = contracted L y a b c f z-raise y L (three L a b c f) z := by
  unfold three contracted two
  rw [push a y L f,funext (loSub b L (dot L a y) f (raise y L (lower a L f)))]
  rw [loSub,push b y L (lower a L f),loSub]
  have h:=lowerRaise c y L (lower b L (lower a L f)) z; grind only

theorem twoLower (L : List I) (y a b : I→C) (f : Basis L.length→C) (z : Basis L.length) :
    lower y L (two L a b f) z=two L a b (lower y L f) z := by
  unfold two; rw [lowerLower y b,show lower y L (lower a L f)=(fun w=> -lower a L (lower y L f) w) from funext (lowerLower y a L f),negLower]; grind only

theorem threeLower (L : List I) (y a b c : I→C) (f : Basis L.length→C) (z : Basis L.length) :
    lower y L (three L a b c f) z= -three L a b c (lower y L f) z := by
  change lower y L (lower c L (two L a b f)) z=_
  rw [lowerLower y c,show lower y L (two L a b f)=two L a b (lower y L f) from funext (twoLower L y a b f)]; rfl

theorem contractedLower (L : List I) (y a b c : I→C) (f : Basis L.length→C) (z : Basis L.length) :
    lower y L (contracted L y a b c f) z = contracted L y a b c (lower y L f) z := by
  have simpForm (h : Basis L.length→C) (w : Basis L.length) : contracted L y a b c h w =
      dot L c y*two L a b h w +(-1)*(dot L b y*two L a c h w+(-dot L a y)*two L b c h w) := by
    unfold contracted; grind only
  rw [funext (simpForm f),simpForm (lower y L f) z,linearLower,linearLower]; simp only [twoLower]

end RankSeven.AnchorMixedCAR
#print axioms RankSeven.AnchorMixedCAR.triplePush
#print axioms RankSeven.AnchorMixedCAR.contractedLower
