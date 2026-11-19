import Rank7AnchorMixedCAR

namespace RankSeven.AnchorTripleEnergy
open Lean.Grind Pauli ComplexScalar AnchorSteinerTest AnchorExteriorCreation AnchorMixedCAR
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

private theorem reSum {J : Type} (B : List J) (f : J→C) :
    (sumOver B f).re=sumOver B (fun i=>(f i).re) := by
  induction B with
  | nil => rfl
  | cons i B ih => change (f i+sumOver B f).re=(f i).re+sumOver B (fun i=>(f i).re); rw [re_add,ih]
theorem reGram {d : Nat} (f : Basis d→C) : (gram f f).re = mass (qubitIndices d) f := by
  unfold gram mass; rw [reSum]; simp only [re_star_mul_self]

private theorem sumZero {V J : Type} [CommRing V] (B : List J) : sumOver B (fun _=>(0:V))=0 := by
  induction B with
  | nil => rfl
  | cons i B ih => change 0+sumOver B _=0; rw [ih]; grind only

private theorem gramZero {d : Nat} (f : Basis d→C) :
    gram (fun _=>0) f=0 ∧ gram f (fun _=>0)=0 := by
  have z : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
  unfold gram; simp only [z,Semiring.zero_mul,Semiring.mul_zero,sumZero,true_and]

private theorem gramDiff {d : Nat} (f g : Basis d→C) :
    gram (fun z=>f z-g z) (fun z=>f z-g z)=gram f f+gram g g-gram f g-gram g f := by
  unfold gram; rw [←sumOverAdd,←Compression.sumOverSub,←Compression.sumOverSub]
  apply sumOverCongr; intro z
  have e : star (f z-g z)= star (f z)-star (g z) := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [e]; grind only

theorem threeVacant (L : List I) (y a b c : I→C) (f : Basis L.length→C) (vac : lower y L f=fun _=>0) :
    lower y L (three L a b c f)=fun _=>0 := by
  funext z; rw [threeLower,vac]; unfold three; simp only [zeroLower]; grind only

theorem contractedVacant (L : List I) (y a b c : I→C) (f : Basis L.length→C) (vac : lower y L f=fun _=>0) :
    lower y L (contracted L y a b c f)=fun _=>0 := by
  funext z; rw [contractedLower,vac]; unfold contracted two; simp only [zeroLower]; grind only

/-- Exact site-triple identity on the y-vacant sector. Includes arbitrary complex
modes a,b,c,y and unnormalized f; no positivity, orthogonality or distinct-site condition. -/
theorem tripleEnergy (L : List I) (y a b c : I→C) (f : Basis L.length→C) (vac : lower y L f=fun _=>0) :
    mass (qubitIndices L.length) (contracted L y a b c f) =
    mass (qubitIndices L.length) (three L a b c (raise y L f)) -
      sumOver L (fun i=>normSq (y i))*mass (qubitIndices L.length) (three L a b c f) := by
  let v:=contracted L y a b c f
  let w:=three L a b c f
  have vz : lower y L v=fun _=>0 := contractedVacant L y a b c f vac
  have wz : lower y L w=fun _=>0 := threeVacant L y a b c f vac
  have left := (adjoint y L w v).1
  have right := (adjoint y L v w).2
  rw [vz,(gramZero w).2] at left
  rw [vz,(gramZero w).1] at right
  have car:=carGram y L w w
  rw [wz,(gramZero (fun _=>0)).1] at car
  have eq : three L a b c (raise y L f)=fun z=>v z-raise y L w z := funext (triplePush L y a b c f)
  have d := gramDiff v (raise y L w)
  rw [←eq,left,←right] at d
  have en:=congrArg ComplexScalar.re car
  have res:=congrArg ComplexScalar.re d
  simp only [re_add,re_sub,re_zero,re_mul,re_ofReal,im_ofReal,reGram] at en res
  change mass _ v = _-_ * mass _ w; grind only

end RankSeven.AnchorTripleEnergy
#print axioms RankSeven.AnchorTripleEnergy.tripleEnergy
