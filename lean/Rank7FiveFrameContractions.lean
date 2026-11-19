import Rank7FiveShuffleCAR
import Rank7PhysicalHopping
import Rank7PhysicalCompressedSwap
import Rank7PhysicalUniformOccupation

/-! Polarized zero-, one- and two-exchange matrix elements on physical frame slots. -/
namespace RankSeven.FiveFrameContractions
open Lean.Grind Pauli ComplexScalar
open FiveShuffleCAR (Five indices act ident firstSwap secondSwap merge)
open PhysicalCutCapacities (Triple triples)
variable {R α I J : Type} [CommRing R]

private theorem productSum {A B C : Type} [CommRing C] (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]

private theorem fiveSum {C : Type} [CommRing C] (xs : List α) (F : Five α → C) :
    sumOver (indices xs) F = sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun c => sumOver xs (fun d =>
      sumOver xs (fun e => F ((a,b),(c,d),e)))))) := by unfold indices; simp only [productSum]

def slotPair (A : α → I → ComplexScalar R) (i j : I) (Y : Triple α → ComplexScalar R) (u : Five α) :=
  A u.1.1 i*A u.1.2 j*Y u.2
def modeDot (xs : List α) (A : α → I → ComplexScalar R) (i j : I) :=
  sumOver xs (fun a => star (A a i)*A a j)
def cutOne (xs : List α) (A : α → I → ComplexScalar R) (i : I) (Y : Triple α → ComplexScalar R) (d e : α) :=
  sumOver xs (fun c => star (A c i)*Y ((c,d),e))
def cutTwo (xs : List α) (A : α → I → ComplexScalar R) (i j : I) (Y : Triple α → ComplexScalar R) (e : α) :=
  sumOver xs (fun c => sumOver xs (fun d => (star (A c i)*star (A d j))*Y ((c,d),e)))
def pairing {B : Type} (xs : List B) (F G : B → ComplexScalar R) := sumOver xs (fun u => star (F u)*G u)

theorem zeroEntry (xs : List α) (A : α → I → ComplexScalar R) (i j k l : I) (Y W : Triple α → ComplexScalar R) :
    pairing (indices xs) (slotPair A i j Y) (slotPair A k l W) =
      modeDot xs A i k * modeDot xs A j l * pairing (triples xs) Y W := by
  unfold pairing modeDot; rw [fiveSum]; unfold triples
  simp only [slotPair,star_mul,productSum,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; arg 2; intro d; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; arg 2; intro d; rw [sumOverSwap]
  conv => lhs; arg 2; intro c; arg 2; intro d; arg 2; intro e; rw [sumOverSwap]
  apply sumOverCongr; intro c; apply sumOverCongr; intro d; apply sumOverCongr; intro e; apply sumOverCongr; intro b; apply sumOverCongr; intro a
  grind only

theorem oneEntry (xs : List α) (A : α → I → ComplexScalar R) (i j k l : I) (Y W : Triple α → ComplexScalar R) :
    pairing (indices xs) (slotPair A i j Y) (fun u => slotPair A k l W (act firstSwap u)) =
      modeDot xs A i k * sumOver xs (fun d => sumOver xs (fun e => star (cutOne xs A l Y d e)*cutOne xs A j W d e)) := by
  unfold pairing modeDot cutOne; rw [fiveSum]
  simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro a; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  conv => lhs; arg 2; intro d; arg 2; intro a; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro d; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; arg 2; intro d; rw [sumOverSwap]
  conv => lhs; arg 2; intro d; arg 2; intro e; rw [sumOverSwap]
  conv => lhs; arg 2; intro d; arg 2; intro e; arg 2; intro b; rw [sumOverSwap]
  apply sumOverCongr; intro d; apply sumOverCongr; intro e; apply sumOverCongr; intro b; apply sumOverCongr; intro c; apply sumOverCongr; intro a
  change star (A a i*A b j*Y ((c,d),e))*(A a k*A c l*W ((b,d),e))=_
  simp only [star_mul]; grind only

theorem twoEntry (xs : List α) (A : α → I → ComplexScalar R) (i j k l : I) (Y W : Triple α → ComplexScalar R) :
    pairing (indices xs) (slotPair A i j Y) (fun u => slotPair A k l W (act secondSwap u)) =
      sumOver xs (fun e => star (cutTwo xs A k l Y e)*cutTwo xs A i j W e) := by
  unfold pairing cutTwo; rw [fiveSum]
  simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [sumOverSwap]
  conv => lhs; arg 2; intro a; arg 2; intro b; rw [sumOverSwap]
  conv => lhs; arg 2; intro a; rw [sumOverSwap]
  conv => lhs; rw [sumOverSwap]
  apply sumOverCongr; intro e; apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro c; apply sumOverCongr; intro d
  change star (A a i*A b j*Y ((c,d),e))*(A c k*A d l*W ((a,b),e))=_
  simp only [star_mul]; grind only

def source (ys : List I) (A : α → I → ComplexScalar R) (Y : I → I → Triple α → ComplexScalar R) (u : Five α) :=
  sumOver (productIndices ys ys) (fun e => slotPair A e.1 e.2 (Y e.1 e.2) u)

private theorem pairingExpand {E T : Type} (es : List E) (xs : List T) (F H : E → T → ComplexScalar R) :
    pairing xs (fun t => sumOver es (fun i => F i t)) (fun t => sumOver es (fun j => H j t)) =
      sumOver es (fun i => sumOver es (fun j => pairing xs (F i) (H j))) := by
  unfold pairing; simp only [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft]
  conv => rhs; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro j; rw [sumOverSwap]

private theorem collapse {T : Type} [DecidableEq T] (ys : List T) (nd : ys.Nodup) (i : T) (hi : i∈ys) (F : T → ComplexScalar R) :
    sumOver ys (fun k => (if i=k then 1 else 0)*F k)=F i := by
  refine (sumOverCongr ys (g:=fun k => if i=k then F k else 0) (fun k => ?_)).trans
    (ExteriorPauliBase.sumOnIndex ys i F nd hi)
  by_cases e : i=k <;> simp [e,Semiring.one_mul,Semiring.zero_mul]

private theorem sumCongr {E C : Type} [CommRing C] (es : List E) {f g : E → C} (h : ∀i∈es, f i=g i) :
    sumOver es f=sumOver es g := congrArg List.sum (List.map_congr_left h)

theorem sourceZero [DecidableEq I] (xs : List α) (ys : List I) (nd : ys.Nodup)
    (A : α → I → ComplexScalar R) (orth : ∀ i j,modeDot xs A i j=if i=j then 1 else 0)
    (Y : I → I → Triple α → ComplexScalar R) :
    pairing (indices xs) (source ys A Y) (source ys A Y)=
      sumOver ys (fun i => sumOver ys (fun j => pairing (triples xs) (Y i j) (Y i j))) := by
  unfold source; rw [pairingExpand]; simp only [productSum,zeroEntry,orth]
  apply sumCongr; intro i hi; apply sumCongr; intro j hj
  have eq (k l : I) : (if i=k then (1:ComplexScalar R) else 0)*(if j=l then 1 else 0)*pairing (triples xs) (Y i j) (Y k l)=
      (if i=k then 1 else 0)*((if j=l then 1 else 0)*pairing (triples xs) (Y i j) (Y k l)) := by grind only
  simp only [eq,←sumOverMulLeft]
  rw [collapse ys nd i hi,collapse ys nd j hj]

theorem sourceOne [DecidableEq I] (xs : List α) (ys : List I) (nd : ys.Nodup)
    (A : α → I → ComplexScalar R) (orth : ∀ i j,modeDot xs A i j=if i=j then 1 else 0)
    (Y : I → I → Triple α → ComplexScalar R) :
    pairing (indices xs) (source ys A Y) (fun u => source ys A Y (act firstSwap u))=
      sumOver ys (fun i => sumOver ys (fun j => sumOver ys (fun l => sumOver xs (fun d => sumOver xs (fun e =>
        star (cutOne xs A l (Y i j) d e)*cutOne xs A j (Y i l) d e))))) := by
  unfold source; rw [pairingExpand]; simp only [productSum,oneEntry,orth]
  apply sumCongr; intro i hi; apply sumOverCongr; intro j
  let h (k l : I) := sumOver xs (fun d => sumOver xs (fun e =>
    star (cutOne xs A l (Y i j) d e)*cutOne xs A j (Y k l) d e))
  refine (sumOverCongr ys (fun k => (sumOverMulLeft ys (h k) (if i=k then 1 else 0)).symm)).trans ?_
  exact collapse ys nd i hi (fun k => sumOver ys (h k))

theorem sourceTwo (xs : List α) (ys : List I)
    (A : α → I → ComplexScalar R) (Y : I → I → Triple α → ComplexScalar R) :
    pairing (indices xs) (source ys A Y) (fun u => source ys A Y (act secondSwap u))=
      sumOver (productIndices ys ys) (fun b => sumOver (productIndices ys ys) (fun c => sumOver xs (fun e =>
        star (cutTwo xs A c.1 c.2 (Y b.1 b.2) e)*cutTwo xs A b.1 b.2 (Y c.1 c.2) e))) := by
  unfold source; rw [pairingExpand]; simp only [twoEntry]

open PhysicalUniformOccupation (wave)
open PhysicalCutCapacities (leg)
open GenericExteriorKernel (position reorder)
attribute [local instance] Ring.intCast

def anchored {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (x : Fin 7)
    (c : Word n → ComplexScalar R) (u : Triple (Basis n)) :=
  sumOver (qubitIndices n) (fun t => star (A t x)*wave half c ((t,u.1.1),(u.1.2,u.2)))
def modeEdge {n} (A : Basis n → Fin 7 → ComplexScalar R) (x i : Fin 7) (p : PhysicalPairExchange.Edge n) :=
  star (A p.1 x)*star (A p.2 i)

theorem anchoredCutOne {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (x i : Fin 7)
    (c : Word n → ComplexScalar R) (d e : Basis n) :
    cutOne (qubitIndices n) A i (anchored half A x c) d e =
      PhysicalHopping.contract (modeEdge A x i) (wave half c) (d,e) := by
  unfold cutOne anchored PhysicalHopping.contract PhysicalHopping.edges modeEdge
  rw [productSum]; simp only [sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; grind only

theorem anchoredCutTwo {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (x i j : Fin 7)
    (c : Word n → ComplexScalar R) (e : Basis n) :
    cutTwo (qubitIndices n) A i j (anchored half A x c) e =
    sumOver (MixedDefect.oddWords n) (fun p => c p*leg half A ((x,i),j) e p) := by
  let xs := qubitIndices n
  let os := MixedDefect.oddWords n
  change sumOver xs (fun v => sumOver xs (fun w => (star (A v i)*star (A w j))*
    sumOver xs (fun t => star (A t x)*sumOver os (fun p => c p*WedgeSquareIntertwiner.wedgeSquareColumn half p ((t,v),w,e))))) =
    sumOver os (fun p => c p*sumOver (triples xs) (fun a => star (PhysicalCutCapacities.tensorThree A a ((x,i),j))*
      WedgeSquareIntertwiner.wedgeSquareColumn half p (PhysicalCutCapacities.extend a e)))
  unfold triples; simp only [productSum,sumOverMulLeft]
  conv => lhs; arg 2; intro v; arg 2; intro w; rw [sumOverSwap]
  conv => lhs; arg 2; intro v; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro p
  conv => lhs; arg 2; intro v; rw [sumOverSwap]
  rw [sumOverSwap]; apply sumOverCongr; intro t; apply sumOverCongr; intro v; apply sumOverCongr; intro w
  unfold PhysicalCutCapacities.tensorThree PhysicalCutCapacities.extend; simp only [star_mul]; grind only

private theorem starModeUnit {n} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (x : Fin 7) :
    sumOver (qubitIndices n) (fun t => star (star (A t x))*star (A t x))=1 := by
  simp only [star_star]
  rw [sumOverCongr _ (fun t => CommSemiring.mul_comm (A t x) (star (A t x))),orth,ite_eq_left rfl]

theorem waveReorder {n} (half : R) (c : Word n → ComplexScalar R) (u : Four (Basis n))
    (p : ExteriorPauliBase.Permutation) (hp : p∈ExteriorPauliBase.permutations) :
    wave half c (reorder u p)=GenericExteriorKernel.signed (ExteriorPauliBase.oddPermutation p) (wave half c u) := by
  unfold wave WedgeSquareIntertwiner.wedgeSquareColumn WedgeSquareIntertwiner.alternatingWord
  simp only [AlternatingTrace.alternatingRow _ p hp]
  unfold GenericExteriorKernel.signed FourCopySectors.coefficient
  cases ExteriorPauliBase.oddPermutation p <;> simp only [Bool.false_eq_true,ite_false,ite_true,Ring.intCast_one,Ring.intCast_neg,Semiring.one_mul]
  · rfl
  have neg (p : Word n) (z : ComplexScalar R) : c p*(ofReal half^(n+2)*(-1*z))=(-1)*(c p*(ofReal half^(n+2)*z)) := by grind only
  rw [sumOverCongr _ (fun q => neg q _),←sumOverMulLeft]
  change (-1)*wave half c u= -wave half c u; grind only

theorem anchoredLast {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (x : Fin 7) (c : Word n → ComplexScalar R)
    (u : Triple (Basis n)) :
    anchored half A x c u= -PhysicalUniformOccupation.oneHole (fun t => star (A t x)) (wave half c) u := by
  let p : ExteriorPauliBase.Permutation := ((3,0),(1,2))
  have hp : p∈ExteriorPauliBase.permutations := by decide
  have sign : ExteriorPauliBase.oddPermutation p=true := by decide
  have row (t) : star (A t x)*wave half c ((t,u.1.1),(u.1.2,u.2))=
      (-1)*(star (A t x)*wave half c (PhysicalCutCapacities.extend u t)) := by
    have h := waveReorder half c (PhysicalCutCapacities.extend u t) p hp
    rw [sign] at h; change wave half c ((t,u.1.1),(u.1.2,u.2))= -wave half c (PhysicalCutCapacities.extend u t) at h
    rw [h]; grind only
  unfold anchored PhysicalUniformOccupation.oneHole; rw [sumOverCongr _ row,←sumOverMulLeft]; grind only

private theorem reSum {B : Type} (xs : List B) (f : B → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=(f i).re+_; rw [re_add,ih]; rfl

/-- The one-exchange term for arbitrary Pauli-frame sources is an explicit
square for each first source index. -/
theorem physicalOneExchange {n} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (x : Fin 7) (ys : List (Fin 7)) (nd : ys.Nodup)
    (c : Fin 7 → Fin 7 → Word n → ComplexScalar R) :
    let Y := fun i j => anchored half A x (c i j)
    let Z := source ys A Y
    pairing (indices (qubitIndices n)) Z (fun u => Z (act firstSwap u)) =
      sumOver ys (fun i => sumOver (PhysicalHopping.edges n) (fun r => ofReal (normSq (sumOver ys (fun j =>
        PhysicalHopping.contract (fun p => star (modeEdge A x j p)) (wave half (c i j)) r))))) := by
  intro Y Z
  rw [show pairing (indices (qubitIndices n)) Z (fun u => Z (act firstSwap u))=_ from sourceOne _ ys nd A orth Y]
  apply sumOverCongr; intro i
  change sumOver ys (fun j => sumOver ys (fun l => sumOver (qubitIndices n) (fun d => sumOver (qubitIndices n) (fun e =>
    star (cutOne _ A l (anchored half A x (c i j)) d e)*cutOne _ A j (anchored half A x (c i l)) d e))))=_
  simp only [anchoredCutOne]; rw [sumOverSwap]
  refine Eq.trans ?_ (PhysicalHopping.physicalHoppingSquare half ys (modeEdge A x) (c i))
  apply sumOverCongr; intro l; apply sumOverCongr; intro j
  exact (productSum (C:=ComplexScalar R) (qubitIndices n) (qubitIndices n) (fun r =>
    star (PhysicalHopping.contract (modeEdge A x l) (wave half (c i j)) r)*PhysicalHopping.contract (modeEdge A x j) (wave half (c i l)) r)).symm

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumLe {E : Type} (xs : List E) (f g : E → R) (h : ∀ i∈xs, f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i is ih =>
    have a := h i List.mem_cons_self
    have b := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    change f i+sumOver is f ≤ g i+sumOver is g; grind only

theorem physicalZeroExchange {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (x : Fin 7) (ys : List (Fin 7)) (nd : ys.Nodup)
    (c : Fin 7 → Fin 7 → Word n → ComplexScalar R) :
    let Z := source ys A (fun i j => anchored half A x (c i j))
    sumOver (indices (qubitIndices n)) (fun u => normSq (Z u)) ≤
      (36*half^n)*sumOver ys (fun i => sumOver ys (fun j => sumOver (MixedDefect.oddWords n) (fun p => normSq (c i j p)))) := by
  intro Z
  have eq := congrArg ComplexScalar.re (sourceZero (qubitIndices n) ys nd A orth (fun i j => anchored half A x (c i j)))
  simp only [pairing,reSum,re_star_mul_self] at eq
  change sumOver _ (fun u => normSq (Z u))=_ at eq; rw [eq,sumOverMulLeft]
  apply sumLe; intro i _; rw [sumOverMulLeft]; apply sumLe; intro j _
  have one := PhysicalUniformOccupation.physicalOneHoleBound half unit (fun t => star (A t x)) (starModeUnit A orth x) (c i j)
  have neg (v : ComplexScalar R) : normSq (-v)=normSq v := by simp [normSq]; grind only
  simpa only [anchoredLast,neg] using one
end Order

end RankSeven.FiveFrameContractions
#print axioms RankSeven.FiveFrameContractions.physicalZeroExchange
#print axioms RankSeven.FiveFrameContractions.physicalOneExchange
#print axioms RankSeven.FiveFrameContractions.sourceOne
