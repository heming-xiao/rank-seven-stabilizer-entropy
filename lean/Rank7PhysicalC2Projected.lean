import Rank7PhysicalC2Adjoint

/-! Free-mode projection for the two-hole occupation bound. The free
covectors are P e_i where P=1−|x⟩⟨x|−|y⟩⟨y| on the ambient cube. -/
namespace RankSeven.PhysicalC2Projected
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel
open PhysicalCutCapacities (Triple triples)
open PhysicalTwoHoleOccupancy (modeGram gram3 raise3 twoOccupied)
open PhysicalC2Adjoint (synth readout column twoColumn)
open PhysicalOccupationBound (source physicalSource slice)
variable {R I J : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
def delta [DecidableEq I] (i t : I) : ComplexScalar R := if i=t then 1 else 0
def free [DecidableEq I] (x y : I → ComplexScalar R) (i t : I) :=
  delta i t - x t*star (x i) - y t*star (y i)
def dot (is : List I) (x f : I → ComplexScalar R) := sumOver is (fun i => x i*f i)
def remove (is : List I) (x f : I → ComplexScalar R) (t : I) := f t-star (x t)*dot is x f
def project (is : List I) (x y f : I → ComplexScalar R) (t : I) :=
  f t-star (x t)*dot is x f-star (y t)*dot is y f
private theorem starSub (a b : ComplexScalar R) : star (a-b)=star a-star b := by apply ComplexScalar.ext <;> simp <;> grind only
private theorem starDelta [DecidableEq I] (i t : I) : star (delta (R:=R) i t)=delta i t := by
  by_cases h : i=t <;> simp [h,delta] <;> exact star_ofReal _
private theorem pick [DecidableEq I] (is : List I) (nd : is.Nodup) (all : ∀i,i∈is)
    (t : I) (f : I → ComplexScalar R) :sumOver is (fun i => delta t i*f i)=f t := by
  refine (sumOverCongr is (g:=fun i => if t=i then f i else 0) (fun i => ?_)).trans (ExteriorPauliBase.sumOnIndex is t f nd (all t))
  by_cases h : t=i <;> simp [delta,h,Semiring.one_mul,Semiring.zero_mul]
private theorem symmetric [DecidableEq I] (i t : I) : delta (R:=R) i t=delta t i := by
  by_cases h : i=t
  · subst i; rfl
  · simp [delta,h,Ne.symm h]
theorem coefficientProjection [DecidableEq I] (is : List I) (nd : is.Nodup) (all : ∀i,i∈is)
    (x y f : I → ComplexScalar R) (t : I) :
    sumOver is (fun i => star (free x y i t)*f i)=project is x y f t := by
  have row (i) : star (free x y i t)*f i=
      delta t i*f i-star (x t)*(x i*f i)-star (y t)*(y i*f i) := by
    simp only [free,starSub,star_mul,star_star,starDelta,symmetric i t]; grind only
  rw [sumOverCongr _ row]; simp only [Compression.sumOverSub,pick is nd all,←sumOverMulLeft,dot,project]
theorem freeOrthogonal [DecidableEq I] (is : List I) (nd : is.Nodup) (all : ∀i,i∈is)
    (x y : I → ComplexScalar R) (xy : modeGram is x y=0) (hy : modeGram is y y=1) (i : I) :
    sumOver is (fun t => y t*star (free x y i t))=0 := by
  have row (t) : y t*star (free x y i t)=delta i t*y t-(star (x t)*y t)*x i-(star (y t)*y t)*y i := by
    simp only [free,starSub,star_mul,star_star,starDelta]; grind only
  unfold modeGram at xy hy
  rw [sumOverCongr _ row]; simp only [Compression.sumOverSub,pick is nd all,←sumOverMulRight,xy,hy,Semiring.zero_mul,Semiring.one_mul]; grind only

private theorem realSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun t => (f t).re) := by
  induction xs with
  | nil => rfl
  | cons a as ih => change (f a+sumOver as f).re=(f a).re+_; rw [re_add,ih]; rfl
theorem singleEnergy (is : List I) (x f : I → ComplexScalar R) (hx : modeGram is x x=1) :
    sumOver is (fun t => normSq (remove is x f t))=sumOver is (fun t => normSq (f t))-normSq (dot is x f) := by
  let z := dot is x f
  have orth : sumOver is (fun t => star (remove is x f t)*remove is x f t)=
      sumOver is (fun t => star (f t)*f t)-star z*z := by
    have row (t) : star (remove is x f t)*remove is x f t=
        star (f t)*f t-star (x t*f t)*z -star z*(x t*f t)+(star (x t)*x t)*(star z*z) := by
      unfold remove; change star (f t-star (x t)*z)*(f t-star (x t)*z)=_
      simp only [starSub,star_mul,star_star]; grind only
    unfold modeGram at hx
    rw [sumOverCongr _ row]; simp only [sumOverAdd,Compression.sumOverSub,←sumOverMulRight,←sumOverMulLeft,
      ←ComplexExterior.starSumOver,hx]
    change _-star z*z-star z*z+1*(star z*z)=_; grind only
  simpa only [realSum,re_sub,re_star_mul_self] using congrArg ComplexScalar.re orth

theorem composeProjection (is : List I) (x y f : I → ComplexScalar R) (xy : modeGram is x y=0) :
    remove is y (remove is x f)=project is x y f := by
  have row (t) : y t*remove is x f t=y t*f t-(star (x t)*y t)*dot is x f := by unfold remove; grind only
  have elim : dot is y (remove is x f)=dot is y f := by
    unfold dot; rw [sumOverCongr is row,Compression.sumOverSub,←sumOverMulRight]
    change _- modeGram is x y*_=_
    rw [xy,Semiring.zero_mul]; grind only
  funext t; change remove is x f t-star (y t)*dot is y (remove is x f)=_; rw [elim]; rfl

private theorem baseOrtho [DecidableEq I] (is : List I) (nd : is.Nodup) (all : ∀i,i∈is) (i j : I) :
    sumOver is (fun t => star (delta (R:=R) i t)*delta j t)=if i=j then 1 else 0 := by
  rw [sumOverCongr is (g:=fun t => delta i t*delta j t) (by intro t; rw [starDelta]),
    pick is nd all i (delta j),symmetric j i]; rfl
private theorem sliceSum {n} (half : R) (x : Basis n → ComplexScalar R) (is : List I)
    (A : I → ComplexScalar R) (f : I → Word n → ComplexScalar R) (u : Triple (Basis n)) :
    slice half x (fun p => sumOver is (fun i => A i*f i p)) u=sumOver is (fun i => A i*slice half x (f i) u) := by
  unfold slice PhysicalUniformOccupation.wave; simp only [sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro t; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro i; apply sumOverCongr; intro t; apply sumOverCongr; intro p; grind only

theorem absorb {n} (half : R) (x y : Basis n → ComplexScalar R) (f : Basis n → Word n → ComplexScalar R) :
    physicalSource half (qubitIndices n) (fun t i => star (free x y i t)) x f=
    physicalSource half (qubitIndices n) (fun t i => delta i t) x
      (fun i p => project (qubitIndices n) x y (fun j => f j p) i) := by
  have nd := HyperplaneIncidence.normalsNodup n
  have all := @qubitIndicesComplete n
  funext u; unfold physicalSource source PhysicalOccupationBound.atom
  simp only [symmetric _ u.1.1,pick _ nd all]
  simp only [←coefficientProjection _ nd all]; symm; exact sliceSum _ _ _ _ _ _
private theorem gramSwap (is : List I) (x y : I → ComplexScalar R) : modeGram is y x=star (modeGram is x y) := by
  unfold modeGram; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro i; rw [star_mul,star_star]; exact CommSemiring.mul_comm _ _
theorem freeParseval [DecidableEq I] (is : List I) (nd : is.Nodup) (all : ∀i,i∈is) (x y : I → ComplexScalar R)
    (hx : modeGram is x x=1) (hy : modeGram is y y=1) (xy : modeGram is x y=0) (t u : I) :
    sumOver is (fun i => star (free x y i t)*free x y i u)=free x y t u := by
  have yx : modeGram is y x=0 := by rw [gramSwap,xy]; exact star_ofReal _
  have row (v : I → ComplexScalar R) (i : I) : v i*free x y i u=
    delta u i*v i-((star (x i)*v i)*x u+(star (y i)*v i)*y u) := by
    unfold free; rw [symmetric i u]; grind only
  have dots (v : I → ComplexScalar R) : dot is v (fun i => free x y i u)=v u-(modeGram is x v*x u+modeGram is y v*y u) := by
    unfold dot; rw [sumOverCongr is (row v),Compression.sumOverSub,sumOverAdd,pick _ nd all,←sumOverMulRight,←sumOverMulRight]; rfl
  rw [coefficientProjection _ nd all]; unfold project; rw [dots,dots,hx,hy,xy,yx]; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
theorem projectionEnergy (is : List I) (x y f : I → ComplexScalar R) (hx : modeGram is x x=1) (hy : modeGram is y y=1)
    (xy : modeGram is x y=0) : sumOver is (fun t => normSq (project is x y f t))≤sumOver is (fun t => normSq (f t)) := by
  rw [←composeProjection is x y f xy,singleEnergy is y _ hy,singleEnergy is x f hx]
  have p := normSq_nonnegative (dot is x f)
  have q := normSq_nonnegative (dot is y (remove is x f)); grind only
private theorem sumLe (xs : List J) (f g : J → R) (h : ∀i,f i≤g i) : sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i js ih => change f i+sumOver js f≤g i+sumOver js g; have := h i; grind only
theorem physicalProjectedNorm {n} (half : R) (unit : 2*half=1) (x y : Basis n → ComplexScalar R)
    (hx : modeGram (qubitIndices n) x x=1) (hy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (f : Basis n → Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun u => normSq (synth (qubitIndices n) (MixedDefect.oddWords n) (column half (free x y) x y) f u))≤
    36*half^n * sumOver (qubitIndices n) (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq (f i p))) := by
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  let d : Basis n → Basis n → ComplexScalar R := fun t i => delta i t
  let A := fun t i => star (free x y i t)
  let v := fun t => star (y t)
  let g := fun i p => project L x y (fun j => f j p) i
  have nd := HyperplaneIncidence.normalsNodup n
  have all := @qubitIndicesComplete n
  have nv : sumOver L (fun t => star (v t)*v t)=1 := by
    rw [←hy]; unfold modeGram; apply sumOverCongr; intro t; simp only [v,star_star]; exact CommSemiring.mul_comm _ _
  have orthA (i) : sumOver L (fun t => star (v t)*A t i)=0 := by
    simp only [A,v,star_star]; exact freeOrthogonal L nd all x y xy hy i
  have raw := PhysicalDoubleHoleNorm.physicalSecondContraction half unit L nd d (baseOrtho L nd all) x v hx nv g
  have eq : physicalSource half L A x f=physicalSource half L d x g := absorb half x y f
  rw [←eq] at raw
  have row (u : Triple (Basis n)) :
      PhysicalDoubleHoleNorm.contraction L v (SingleCreationCAR.merged (physicalSource half L A x f)) u=
      synth L P (column half (free x y) x y) f u := by
    rw [PhysicalC2Synthesis.physicalC2Identity half L A x v orthA,←PhysicalC2Adjoint.c2Expansion]
    unfold PhysicalC2Synthesis.physicalC2; apply sumOverCongr; intro i; simp only [v,star_star]; rfl
  rw [sumOverCongr _ (fun u => congrArg normSq (row u))] at raw
  have ens : sumOver L (fun i => sumOver P (fun p => normSq (g i p)))≤sumOver L (fun i => sumOver P (fun p => normSq (f i p))) := by
    conv => lhs; rw [sumOverSwap]
    conv => rhs; rw [sumOverSwap]
    apply sumLe; intro p; exact projectionEnergy L x y (fun i => f i p) hx hy xy
  have hp (k : Nat) : 0<half^k := by
    induction k with
    | zero => simp [Semiring.pow_zero]; grind
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind)
  have pos : 0≤36*half^n := Std.le_of_lt (OrderedRing.mul_pos (by grind) (hp n))
  exact Std.le_trans raw (OrderedRing.mul_le_mul_of_nonneg_left ens pos)

/-- The complement block bound with the canonical projected columns and
arbitrary ambient output, without completing the two modes to a basis. -/
theorem physicalProjectedAdjoint {n} (half : R) (unit : 2*half=1) (x y : Basis n → ComplexScalar R)
    (hx : modeGram (qubitIndices n) x x=1) (hy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (F : Basis n → Basis n → Basis n → ComplexScalar R) :
    sumOver (qubitIndices n) (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq
      (gram3 (qubitIndices n) (raise3 (free x y i) (twoColumn half x y p)) F)))≤
    36*half^n * sumOver (triples (qubitIndices n)) (fun u => normSq (F u.1.1 u.1.2 u.2)) := by
  have hp (k : Nat) : 0<half^k := by
    induction k with
    | zero => simp [Semiring.pow_zero]; grind
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind)
  have pos : 0<36*half^n := OrderedRing.mul_pos (by grind) (hp n)
  simpa only [PhysicalC2Adjoint.gramReadout] using PhysicalC2Adjoint.adjointNorm (qubitIndices n) (MixedDefect.oddWords n)
    (triples (qubitIndices n)) (column half (free x y) x y) _ pos (physicalProjectedNorm half unit x y hx hy xy)
    (fun u => F u.1.1 u.1.2 u.2)
end Order
end RankSeven.PhysicalC2Projected
#print axioms RankSeven.PhysicalC2Projected.freeParseval
#print axioms RankSeven.PhysicalC2Projected.physicalProjectedAdjoint
