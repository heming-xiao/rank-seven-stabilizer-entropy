import Rank7PhysicalC2Synthesis
import Rank7PhysicalTwoHoleOccupancy

/-! Adjoint occupation bound for actual Pauli columns of the two-hole
free-mode synthesis. All scalar products here use ordered ambient triples. -/
namespace RankSeven.PhysicalC2Adjoint
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel
open PhysicalCutCapacities (Triple triples)
open PhysicalTwoHoleOccupancy (raise3 twoOccupied gram3 modeGram)
variable {R C I J U W : Type} [CommRing R] [CommRing C]

def synth (is : List I) (ps : List J) (G : I → J → U → ComplexScalar R)
    (c : I → J → ComplexScalar R) (u : U) := sumOver is (fun i => sumOver ps (fun p => c i p *G i p u))
def readout (us : List U) (G : I → J → U → ComplexScalar R) (F : U → ComplexScalar R)
    (i : I) (p : J) := sumOver us (fun u => star (G i p u)*F u)
private theorem realSum (xs : List U) (f : U → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun u => (f u).re) := by
  induction xs with
  | nil => rfl
  | cons a as ih => change (f a+sumOver as f).re=(f a).re+_; rw [re_add,ih]; rfl
theorem finiteAdjoint (is : List I) (ps : List J) (us : List U) (G : I → J → U → ComplexScalar R)
    (c : I → J → ComplexScalar R) (F : U → ComplexScalar R) :
    sumOver us (fun u => star (synth is ps G c u)*F u)=
    sumOver is (fun i => sumOver ps (fun p => star (c i p)*readout us G F i p)) := by
  unfold synth readout; simp only [ComplexExterior.starSumOver,star_mul,sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap]; apply sumOverCongr; intro i; rw [sumOverSwap]
  apply sumOverCongr; intro p; apply sumOverCongr; intro u; grind only

def twoColumn {n} (half : R) (x y : Basis n → ComplexScalar R) (p : Word n) (a b : Basis n) :=
  sumOver (qubitIndices n) (fun c => y c* sumOver (qubitIndices n)
    (fun t => x t*WedgeSquareIntertwiner.wedgeSquareColumn half p ((a,b),(c,t))))
def column {n} (half : R) (r : I → Basis n → ComplexScalar R) (x y : Basis n → ComplexScalar R)
    (i : I) (p : Word n) (u : Triple (Basis n)) := raise3 (r i) (twoColumn half x y p) u.1.1 u.1.2 u.2
theorem twoExpansion {n} (half : R) (x y : Basis n → ComplexScalar R) (f : Word n → ComplexScalar R) (a b : Basis n) :
    twoOccupied half x y f a b=sumOver (MixedDefect.oddWords n) (fun p => f p*twoColumn half x y p a b) := by
  unfold twoOccupied PhysicalTwoHoleOccupancy.lower3 PhysicalTwoHoleOccupancy.anchored PhysicalUniformOccupation.oneHole
    PhysicalUniformOccupation.wave twoColumn
  simp only [sumOverMulLeft]
  conv => lhs; arg 2; intro c; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro p; apply sumOverCongr; intro c; apply sumOverCongr; intro t
  unfold PhysicalCutCapacities.extend; grind only

theorem c2Expansion {n} (half : R) (is : List I) (r : I → Basis n → ComplexScalar R)
    (x y : Basis n → ComplexScalar R) (f : I → Word n → ComplexScalar R) (u : Triple (Basis n)) :
    sumOver is (fun i => raise3 (r i) (twoOccupied half x y (f i)) u.1.1 u.1.2 u.2)=
    synth is (MixedDefect.oddWords n) (column half r x y) f u := by
  unfold synth; apply sumOverCongr; intro i; unfold column raise3
  simp only [twoExpansion,sumOverMulLeft]
  rw [←Compression.sumOverSub,←sumOverAdd]
  apply sumOverCongr; intro p; grind only

private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
theorem gramReadout {n} (half : R) (r : I → Basis n → ComplexScalar R) (x y : Basis n → ComplexScalar R)
    (f : Basis n → Basis n → Basis n → ComplexScalar R) (i : I) (p : Word n) :
    readout (triples (qubitIndices n)) (column half r x y) (fun u => f u.1.1 u.1.2 u.2) i p=
    gram3 (qubitIndices n) (raise3 (r i) (twoColumn half x y p)) f := by
  simp only [readout,triples,productSum,column,gram3,PhysicalTwoHoleOccupancy.sum3]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
/-- Over an ordered ring the adjoint bound follows by expanding
the squared norm of S S†F−K F. This avoids spectral decomposition. -/
theorem adjointNorm (is : List I) (ps : List J) (us : List U) (G : I → J → U → ComplexScalar R)
    (K : R) (hk : 0<K)
    (op : ∀c,sumOver us (fun u => normSq (synth is ps G c u))≤K*sumOver is (fun i => sumOver ps (fun p => normSq (c i p))))
    (F : U → ComplexScalar R) :
    sumOver is (fun i => sumOver ps (fun p => normSq (readout us G F i p)))≤K*sumOver us (fun u => normSq (F u)) := by
  let c := readout us G F
  let w := synth is ps G c
  let z := sumOver is (fun i => sumOver ps (fun p => normSq (c i p)))
  let d := sumOver us (fun u => normSq (F u))
  have adj := congrArg ComplexScalar.re (finiteAdjoint is ps us G c F)
  change (sumOver us (fun u => star (w u)*F u)).re=(sumOver is (fun i => sumOver ps (fun p => star (c i p)*c i p))).re at adj
  simp only [realSum,re_star_mul_self] at adj
  change sumOver us (fun u => (star (w u)*F u).re)=z at adj
  have dif (u) : normSq (w u-ofReal K*F u) =normSq (w u)+K^2*normSq (F u)- (2*K)*(star (w u)*F u).re := by
    simp only [normSq,re_sub,im_sub,re_mul,im_mul,re_ofReal,im_ofReal,re_star,im_star]; grind only
  have pos := Compression.sumOverNonnegative us (fun u => normSq (w u-ofReal K*F u)) (fun _ _ => normSq_nonnegative _)
  rw [sumOverCongr _ dif,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,adj] at pos
  have bound := op c
  change sumOver us (fun u => normSq (w u))≤K*z at bound
  change 0≤sumOver us (fun u => normSq (w u))+K^2*d-2*K*z at pos
  change z≤K*d
  by_cases e : z≤K*d
  · exact e
  · have falsePos := OrderedRing.mul_pos hk (show 0<z-K*d by grind only); grind only

set_option maxHeartbeats 1500000 in
theorem actualC2Norm [DecidableEq I] {n} (half : R) (unit : 2*half=1)
    (is : List I) (nd : is.Nodup) (r : I → Basis n → ComplexScalar R)
    (orth : ∀i j,modeGram (qubitIndices n) (r i) (r j)=if i=j then 1 else 0)
    (x y : Basis n → ComplexScalar R) (hx : modeGram (qubitIndices n) x x=1)
    (hy : modeGram (qubitIndices n) y y=1) (ry : ∀i,modeGram (qubitIndices n) (r i) y=0)
    (f : I → Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun u => normSq (synth is (MixedDefect.oddWords n) (column half r x y) f u))≤
    36*half^n * sumOver is (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq (f i p))) := by
  let A := fun t i => star (r i t)
  let v := fun t => star (y t)
  have orthA (i j) : sumOver (qubitIndices n) (fun a => star (A a i)*A a j)=if i=j then 1 else 0 := by
    have d : (if j=i then (1:ComplexScalar R) else 0)=(if i=j then 1 else 0) := by
      by_cases h : i=j
      · subst j; rfl
      · simp [h,Ne.symm h]
    rw [←d,←orth j i]; unfold modeGram; apply sumOverCongr; intro a; simp only [A,star_star]; exact CommSemiring.mul_comm _ _
  have yv : sumOver (qubitIndices n) (fun a => star (v a)*v a)=1 := by
    rw [←hy]; unfold modeGram; apply sumOverCongr; intro a; simp only [v,star_star]; exact CommSemiring.mul_comm _ _
  have yr (i) : sumOver (qubitIndices n) (fun a => star (v a)*A a i)=0 := by
    rw [←ry i]; unfold modeGram; apply sumOverCongr; intro a; simp only [v,A,star_star]; exact CommSemiring.mul_comm _ _
  have bound := PhysicalC2Synthesis.physicalC2Norm half unit is nd A orthA x v hx yv yr f
  have row (u : Triple (Basis n)) : PhysicalC2Synthesis.physicalC2 half is A x (fun t => star (v t)) f u=
      synth is (MixedDefect.oddWords n) (column half r x y) f u := by
    rw [←c2Expansion]; unfold PhysicalC2Synthesis.physicalC2; apply sumOverCongr; intro i
    simp only [v,star_star]
    rfl
  simpa only [row] using bound

theorem actualC2AdjointNorm [DecidableEq I] {n} (half : R) (unit : 2*half=1)
    (is : List I) (nd : is.Nodup) (r : I → Basis n → ComplexScalar R)
    (orth : ∀i j,modeGram (qubitIndices n) (r i) (r j)=if i=j then 1 else 0)
    (x y : Basis n → ComplexScalar R) (hx : modeGram (qubitIndices n) x x=1)
    (hy : modeGram (qubitIndices n) y y=1) (ry : ∀i,modeGram (qubitIndices n) (r i) y=0)
    (F : Basis n → Basis n → Basis n → ComplexScalar R) :
    sumOver is (fun i => sumOver (MixedDefect.oddWords n) (fun p =>
      normSq (gram3 (qubitIndices n) (raise3 (r i) (twoColumn half x y p)) F)))≤
    36*half^n * sumOver (triples (qubitIndices n)) (fun u => normSq (F u.1.1 u.1.2 u.2)) := by
  have hp (k : Nat) : 0<half^k := by
    induction k with
    | zero => simp [Semiring.pow_zero]; grind
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind)
  have pos : 0<36*half^n := OrderedRing.mul_pos (by grind) (hp n)
  simpa only [gramReadout] using adjointNorm is (MixedDefect.oddWords n) (triples (qubitIndices n)) (column half r x y) _
    pos (actualC2Norm half unit is nd r orth x y hx hy ry) (fun u => F u.1.1 u.1.2 u.2)

end Order
end RankSeven.PhysicalC2Adjoint
#print axioms RankSeven.PhysicalC2Adjoint.actualC2Norm
#print axioms RankSeven.PhysicalC2Adjoint.actualC2AdjointNorm
