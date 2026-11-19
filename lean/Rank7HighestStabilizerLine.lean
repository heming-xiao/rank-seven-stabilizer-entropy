import Rank7HighestAnchorReduction

namespace RankSeven.HighestStabilizerLine

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestCosetFourier HighestExteriorOccupation
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
open HeavyPauliGroup StabilizerCharacterBasis
variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem entryLE (xs : List α) (f : α→R) (hn : ∀i,0≤f i) (i : α) (hi : i∈xs) : f i≤sumOver xs f := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    change f i≤f a+sumOver xs f
    rcases List.mem_cons.mp hi with rfl|hi
    · have s := Compression.sumOverNonnegative xs f (fun j _ => hn j); grind only
    · have s := ih hi; have p := hn a; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem columnIP (xs : List α) (P : Mx α R) (p : Projection xs P) (i j : α) :
    innerProduct xs (fun a => P a i) (fun a => P a j)=P i j := by
  have eq : matMul xs (dagger P) P=P := by rw [p.herm,p.square]
  exact congrFun (congrFun eq i) j

theorem projectionMinors (half : R) (h2 : 2*half=1) (xs : List α) (full : ∀i,i∈xs)
    (P : Mx α R) (p : Projection xs P) (tr : trace xs P=1) (i j a b : α) :
    P a i*P b j=P a j*P b i := by
  let col i := fun a => P a i
  let es := productIndices xs xs
  let mass i j := HighestExteriorOccupation.measure half xs (exterior (col i) (col j))
  let u i := (P i i).re
  have diag (i : α) : normSum xs (col i)=u i := by
    have h := columnIP xs P p i i; rw [selfProduct] at h
    exact congrArg ComplexScalar.re h
  have loc (i j : α) : mass i j=u i*u j-normSq (P i j) := by
    unfold mass; rw [exteriorMass half h2,diag,diag,columnIP xs P p]
  have norm : sumOver xs u=1 := by
    have h := congrArg ComplexScalar.re tr
    simpa only [trace,(realSum _ _).1,re_one,u] using h
  have byrow (j : α) : sumOver xs (fun i => normSq (P i j))=u j := diag j
  have total : sumOver xs (fun i => sumOver xs (mass i))=0 := by
    change sumOver xs (fun i => sumOver xs (fun j => mass i j))=0
    simp only [loc,Compression.sumOverSub,←sumOverMulLeft,norm]
    rw [sumOverSwap xs xs,sumOverCongr xs byrow]
    simp only [Semiring.mul_one]; grind only
  have hn : 0<half := by have := OrderedRing.zero_lt_one (R:=R); grind only
  have mn (i j : α) : 0≤mass i j := OrderedRing.mul_nonneg (Std.le_of_lt hn)
    (Compression.sumOverNonnegative _ _ (fun t _ => normSq_nonnegative _))
  have k0 := entryLE xs (fun i => sumOver xs (mass i)) (fun t => Compression.sumOverNonnegative xs _ (fun r _ => mn t r)) i (full i)
  have k1 := entryLE xs (mass i) (mn i) j (full j)
  have mz : mass i j=0 := by have := mn i j; grind only
  let v := exterior (col i) (col j)
  change half*normSum es v=0 at mz
  have nz : normSum es v=0 := by
    have s := Compression.sumOverNonnegative es (fun t => normSq (v t)) (fun t _ => normSq_nonnegative _)
    change 0≤normSum es v at s
    by_cases ok : normSum es v=0
    · exact ok
    · have no := OrderedRing.mul_pos hn (show 0<normSum es v by grind only); grind only
  have at0 := entryLE es (fun t => normSq (v t)) (fun _ => normSq_nonnegative _) (a,b) (HyperplaneInduction.pairMember (full _) (full _))
  change normSq (v (a,b))≤normSum es v at at0
  have real := squareNonnegative (v (a,b)).re
  have imag := squareNonnegative (v (a,b)).im
  change (v (a,b)).re^2+(v (a,b)).im^2≤normSum es v at at0
  have zr (t : R) (ht : t^2≤0) : t=0 := by
    by_cases e : t=0
    · exact e
    · by_cases h : 0<t
      · have bad := OrderedRing.mul_pos h h; grind only
      · have m : 0< -t := by grind only
        have bad := OrderedRing.mul_pos m m; grind only
  have vz : v (a,b)=0 := by apply ComplexScalar.ext <;> first
    | simpa only [re_zero] using zr (v (a,b)).re (by grind only)
    | simpa only [im_zero] using zr (v (a,b)).im (by grind only)
  change P a i*P b j-P a j*P b i=0 at vz
  grind only

private theorem sumZero {S : Type} [CommRing S] (ls : List α) : sumOver ls (fun _ => (0:S))=0 := by
  induction ls with | nil => rfl | cons i is ih => change 0+sumOver is _=0; rw [ih]; grind only

theorem projectedExteriorZero (half : R) (h2 : 2*half=1) (xs : List α) (full : ∀i,i∈xs) (P : Mx α R) (p : Projection xs P)
    (tr : trace xs P=1) (x y : α→ComplexScalar R) : exterior (image xs P x) (image xs P y)=fun _ => 0 := by
  funext e
  rcases e with ⟨a,b⟩
  unfold exterior image
  simp only [sumOverMulRight,sumOverMulLeft]
  conv => lhs; arg 1; rw [sumOverSwap xs xs]
  rw [←Compression.sumOverSub]
  have row (i : α) : sumOver xs (fun j => P a i*x i*(P b j*y j))-sumOver xs (fun j => P a j*y j*(P b i*x i))=0 := by
    rw [←Compression.sumOverSub]
    have eq (j : α) : P a i*x i*(P b j*y j)-P a j*y j*(P b i*x i)=0 := by
      have k := projectionMinors half h2 xs full P p tr i j a b
      grind only
    rw [sumOverCongr _ eq]
    exact sumZero _
  rw [sumOverCongr _ row]
  exact sumZero _

theorem pivot (half : R) (h2 : 2*half=1) (xs : List α) (full : ∀i,i∈xs)
    (P : Mx α R) (p : Projection xs P) (tr : trace xs P=1) :
    ∃k∈xs,0<(P k k).re ∧ P k k=ofReal (P k k).re ∧
      ∀(x : α→ComplexScalar R) (a : α),ofReal (P k k).re*image xs P x a=P a k*image xs P x k := by
  classical
  have one : sumOver xs (fun i => (P i i).re)=1 := by
    simpa only [trace,(realSum _ _).1,re_one] using congrArg ComplexScalar.re tr
  have ex : ∃k∈xs,0<(P k k).re := by
    apply Classical.byContradiction; intro no
    have nn (i : α) (hi : i∈xs) : 0≤ -(P i i).re := by
      have bad : ¬0<(P i i).re := fun h => no ⟨i,hi,h⟩
      grind only
    have t := Compression.sumOverNonnegative _ _ nn
    have neg := sumOverMulLeft xs (fun i => (P i i).re) (-1)
    simp only [Ring.neg_mul,Semiring.one_mul] at neg
    rw [←neg,one] at t; have := OrderedRing.zero_lt_one (R:=R); grind only
  obtain ⟨k,hk,positive⟩ := ex
  have diag := columnIP xs P p k k
  rw [selfProduct] at diag
  have val : P k k=ofReal (P k k).re := by rw [←diag,re_ofReal]
  refine ⟨k,hk,positive,val,?_⟩
  intro x a; rw [←val]; unfold image; simp only [sumOverMulLeft]
  apply sumOverCongr; intro j; have id := projectionMinors half h2 xs full P p tr j k a k
  grind only

theorem characterPivot {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (c : Word n) :
    let B := block half L c
    ∃k∈qubitIndices n, 0<(B k k).re ∧ B k k=ofReal (B k k).re ∧
      ∀(x : Basis n→ComplexScalar R) (a : Basis n), ofReal (B k k).re*image (qubitIndices n) B x a=B a k*image (qubitIndices n) B x k :=
  pivot half h2 _ qubitIndicesComplete _ (PhysicalProjectionAngles.lineProjection half h2 L c) (blockTrace half h2 L c)

end RankSeven.HighestStabilizerLine

#print axioms RankSeven.HighestStabilizerLine.projectionMinors
#print axioms RankSeven.HighestStabilizerLine.projectedExteriorZero
#print axioms RankSeven.HighestStabilizerLine.characterPivot

