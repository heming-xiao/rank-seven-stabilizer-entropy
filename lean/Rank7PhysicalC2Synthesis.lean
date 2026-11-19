import Rank7PhysicalDoubleHoleNorm

/-! Wedge multiplication by each free mode after the physical two-hole
contraction. Both contracted mode arguments in twoHole are covectors. -/
namespace RankSeven.PhysicalC2Synthesis
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
open PhysicalCutCapacities (Triple triples)
open PhysicalOccupationBound (tail insert atom source slice physicalSource)
open PhysicalDoubleHoleNorm (contraction)
open SingleCreationCAR (merged)
open PhysicalUniformOccupation (wave)
variable {R C α I : Type} [CommRing R] [CommRing C]
def wedge3 (v : α → ComplexScalar R) (E : α → α → ComplexScalar R) (r : Triple α) :=
  v r.1.1*E r.1.2 r.2-v r.1.2*E r.1.1 r.2+v r.2*E r.1.1 r.1.2
def twoHole {n} (half : R) (x y : Basis n → ComplexScalar R) (f : Word n → ComplexScalar R)
    (a b : Basis n) := sumOver (qubitIndices n) (fun c => y c * sumOver (qubitIndices n)
      (fun t => x t * wave half f ((a,b),(c,t))))
def physicalC2 {n} (half : R) (ys : List I) (A : Basis n → I → ComplexScalar R) (x y : Basis n → ComplexScalar R)
    (f : I → Word n → ComplexScalar R) (r : Triple (Basis n)) :=
  sumOver ys (fun i => wedge3 (fun t => A t i) (twoHole half x y (f i)) r)

private theorem mergeAt (Z : Four α → ComplexScalar R) (t a b c : α) :
    merged Z ((t,a),(b,c))=Z ((t,a),(b,c))-Z ((a,t),(b,c))-Z ((b,a),(t,c))-Z ((c,a),(b,t)) := by
  change Z ((t,a),(b,c))+(-Z ((a,t),(b,c))+(-Z ((b,a),(t,c))+(-Z ((c,a),(b,t))+0)))=_
  grind only
private theorem negativeSum {B : Type} (xs : List B) (F : B → ComplexScalar R) :
    sumOver xs (fun i => -F i)= -sumOver xs F := by
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem signedSite {n} (half : R) (x : Basis n → ComplexScalar R) (f : Word n → ComplexScalar R)
    (a b c : Basis n) :
    slice half x f ((b,a),c)= -slice half x f ((a,b),c) ∧
    slice half x f ((b,c),a)=slice half x f ((a,b),c) := by
  let p : Permutation := ((0,2),(1,3))
  let q : Permutation := ((0,2),(3,1))
  have hp : p∈permutations := by decide
  have hq : q∈permutations := by decide
  have sp : oddPermutation p=true := by decide
  have sq : oddPermutation q=false := by decide
  have sign (t : Basis n) := FiveFrameContractions.waveReorder half f (insert t ((a,b),c)) p hp
  have cyc (t : Basis n) := FiveFrameContractions.waveReorder half f (insert t ((a,b),c)) q hq
  simp only [sp,sq,signed,ite_true,Bool.false_eq_true,ite_false] at sign cyc
  change ∀t,wave half f (insert t ((b,a),c))= -wave half f (insert t ((a,b),c)) at sign
  change ∀t,wave half f (insert t ((b,c),a))=wave half f (insert t ((a,b),c)) at cyc
  unfold slice; simp only [sign,cyc,Ring.mul_neg,negativeSum]; exact ⟨True.intro,True.intro⟩
private theorem orderTwo {n} (half : R) (x y : Basis n → ComplexScalar R) (f : Word n → ComplexScalar R)
    (a b : Basis n) :
    sumOver (qubitIndices n) (fun t => y t*slice half x f ((t,a),b))= -twoHole half x y f a b := by
  let p : Permutation := ((3,2),(0,1))
  have hp : p∈permutations := by decide
  have sg : oddPermutation p=true := by decide
  have h (t c : Basis n) := FiveFrameContractions.waveReorder half f ((a,b),(t,c)) p hp
  simp only [sg,signed,ite_true] at h
  change ∀ t c,wave half f (insert c ((t,a),b))= -wave half f ((a,b),(t,c)) at h
  unfold slice twoHole; simp only [h,Ring.mul_neg,negativeSum]
private theorem mergeSource (ys : List I) (A : α → I → ComplexScalar R)
    (Y : I → Triple α → ComplexScalar R) (a b c d : α) :
    merged (source ys A Y) ((a,b),(c,d))=sumOver ys (fun i => merged (atom A i (Y i)) ((a,b),(c,d))) := by
  simp only [mergeAt,source,Compression.sumOverSub]

theorem physicalC2Identity {n} (half : R) (ys : List I) (A : Basis n → I → ComplexScalar R)
    (x y : Basis n → ComplexScalar R) (orthY : ∀i,sumOver (qubitIndices n) (fun a => star (y a)*A a i)=0)
    (f : I → Word n → ComplexScalar R) (r : Triple (Basis n)) :
    contraction (qubitIndices n) y (merged (physicalSource half ys A x f)) r=
    physicalC2 half ys A x (fun t => star (y t)) f r := by
  rcases r with ⟨⟨a,b⟩,c⟩
  unfold contraction physicalSource PhysicalOccupationBound.insert physicalC2
  simp only [mergeSource,sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro i
  let s := slice half x (f i)
  let v := fun t => A t i
  let z := fun t => star (y t)
  have point (t : Basis n) : z t*merged (atom A i s) ((t,a),(b,c))=
      (z t*v t)*s ((a,b),c)-v a*(z t*s ((t,b),c))+v b*(z t*s ((t,a),c))-v c*(z t*s ((t,a),b)) := by
    rw [mergeAt]; change z t*(v t*s ((a,b),c)-v a*s ((t,b),c)-v b*s ((a,t),c)-v c*s ((a,b),t))=_
    rw [show s ((a,t),c)= -s ((t,a),c) from (signedSite half x (f i) t a c).1,
      show s ((a,b),t)=s ((t,a),b) from (signedSite half x (f i) t a b).2]; grind only
  rw [show sumOver (qubitIndices n) (fun t => star (y t)*merged (atom A i (slice half x (f i))) ((t,a),(b,c)))=_
    from sumOverCongr _ point]
  simp only [Compression.sumOverSub,sumOverAdd,←sumOverMulRight,←sumOverMulLeft]
  change sumOver (qubitIndices n) (fun t => star (y t)*A t i)*s ((a,b),c)
    -v a*sumOver _ (fun t => z t*slice half x (f i) ((t,b),c))
    +v b*sumOver _ (fun t => z t*slice half x (f i) ((t,a),c))
    -v c*sumOver _ (fun t => z t*slice half x (f i) ((t,a),b))=_
  rw [orthY,orderTwo,orderTwo,orderTwo]; unfold wedge3; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
/-- The ordered triple norm is 3! times the exterior norm. The coefficient
36/d equals 3! times (3/2)(4/d) on physical odd-Pauli synthesis columns. -/
theorem physicalC2Norm [DecidableEq I] {n} (half : R) (unit : 2*half=1)
    (ys : List I) (nd : ys.Nodup) (A : Basis n → I → ComplexScalar R)
    (orth : ∀i j,sumOver (qubitIndices n) (fun a => star (A a i)*A a j)=if i=j then 1 else 0)
    (x y : Basis n → ComplexScalar R) (hx : sumOver (qubitIndices n) (fun a => star (x a)*x a)=1)
    (hy : sumOver (qubitIndices n) (fun a => star (y a)*y a)=1)
    (orthY : ∀i,sumOver (qubitIndices n) (fun a => star (y a)*A a i)=0)
    (f : I → Word n → ComplexScalar R) :
    sumOver (triples (qubitIndices n)) (fun r => normSq (physicalC2 half ys A x (fun t => star (y t)) f r))≤
    36*half^n * sumOver ys (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq (f i p))) := by
  simpa only [physicalC2Identity half ys A x y orthY] using
    PhysicalDoubleHoleNorm.physicalSecondContraction half unit ys nd A orth x y hx hy f
end Order
end RankSeven.PhysicalC2Synthesis
#print axioms RankSeven.PhysicalC2Synthesis.physicalC2Identity
#print axioms RankSeven.PhysicalC2Synthesis.physicalC2Norm
