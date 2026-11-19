import Rank7HighestScaledSlater
import Rank7HighestAnchorPauliTrace

namespace RankSeven.HighestCharacterChart

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCharacterBasis StabilizerCosetTransform CharacterFourOrbits StabilizerPopulationRounding
open HighestCodeLocalization HighestExteriorOccupation HighestCosetFourier
open HighestStabilizerLine AnchorMixedCAR
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
variable {R I : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local notation "C" => ComplexScalar R

def analysis {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (x : Basis n→C) (b : Line T) :=
  image (qubitIndices n) (block half F c) (act (wordAdd c b.val) x) i

theorem columnProduct {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G)
    (c : Word n) (i : Basis n) (x z : Basis n→C) :
    star (image (qubitIndices n) (block half F c) x i)*image (qubitIndices n) (block half F c) z i=
      block half F c i i*innerProduct (qubitIndices n) x (image (qubitIndices n) (block half F c) z) := by
  let B:=block half F c
  let xs:=qubitIndices n
  have herm (j : Basis n) : star (B i j)=B j i:=congrFun (congrFun (blockHerm (R:=R) half F c) j) i
  have m (j k : Basis n) : B j i*B i k=B j k*B i i:=
    projectionMinors half h2 xs qubitIndicesComplete B (PhysicalProjectionAngles.lineProjection half h2 F c) (blockTrace half h2 F c) i k j i
  change star (sumOver xs (fun j=>B i j*x j))*(sumOver xs (fun k=>B i k*z k))=
    B i i*sumOver xs (fun j=>star (x j)*sumOver xs (fun k=>B j k*z k))
  rw [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft]
  apply sumOverCongr; intro j
  rw [star_mul,herm,sumOverMulLeft,sumOverMulLeft,sumOverMulLeft]; apply sumOverCongr; intro k
  have e:=m j k; grind only

theorem columnPrice {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G)
    (c : Word n) (i : Basis n) (x : Basis n→C) :
    normSq (image (qubitIndices n) (block half F c) x i)=(block half F c i i).re*pop half F c x := by
  have eq:=congrArg ComplexScalar.re (columnProduct half h2 F c i x x)
  have herm:=congrFun (congrFun (blockHerm (R:=R) half F c) i) i
  change star (block half F c i i)=block half F c i i at herm
  have eqi:=congrArg ComplexScalar.im herm; rw [im_star] at eqi
  have zero : (block half F c i i).im=0:=by grind only
  rw [re_star_mul_self,re_mul,zero] at eq
  change _=(block half F c i i).re*(innerProduct _ x (image _ _ x)).re
  grind only

theorem chartNorm {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (x : Basis n→C) :
    normSum T.reps.attach (analysis half F T c i x)=(block half F c i i).re*normSum (qubitIndices n) x := by
  have e (r : Line T) : normSq (analysis half F T c i x r)=(block half F c i i).re*pop half F r.val x := by
    unfold analysis; rw [columnPrice half h2,HighestCodeTransport.actPopulation half h2,←wordAddAssoc,wordAddSelf,wordAddComm (unitWord n),wordAddZero]
  unfold normSum; rw [sumOverCongr _ e,←sumOverMulLeft,lineSum T (fun a=>pop half F a x),popTotal half h2]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem analysisLinear {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (x z : Basis n→C) (b : C) :
    analysis half F T c i (fun j=>x j+b*z j)=fun r=>analysis half F T c i x r+b*analysis half F T c i z r := by
  funext r; unfold analysis
  let p:=wordAdd c r.val
  have e : act p (fun j=>x j+b*z j)=fun j=>act p x j+b*act p z j := by funext j; rw [actAdd,actScale]
  change image _ _ (act p _) _ = _; rw [e]
  unfold image; rw [sumOverMulLeft,←sumOverAdd]; apply sumOverCongr; intro j; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem polar (L : List I) (x z : I→C) (b : C) :
    normSum L (fun j=>x j+b*z j)=normSum L x+normSq b*normSum L z+2*(b*dot L x z).re := by
  induction L with
  | nil => change 0=0+normSq b*0+2*(b*0).re; simp only [Semiring.mul_zero,re_zero]; grind only
  | cons j L ih =>
    change normSq (x j+b*z j)+normSum L _=normSq (x j)+normSum L x+normSq b*(normSq (z j)+normSum L z)+2*(b*(star (x j)*z j+dot L x z)).re
    rw [ih]; simp only [normSq,re_mul,im_mul,re_add,im_add,re_star,im_star]; grind only

theorem chartGram {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (x z : Basis n→C) :
    dot T.reps.attach (analysis half F T c i x) (analysis half F T c i z)=
      ofReal (block half F c i i).re*dot (qubitIndices n) x z := by
  let φ:= analysis half F T c i
  let A:=dot T.reps.attach (φ x) (φ z)
  let B:=dot (qubitIndices n) x z
  let h:=(block half F c i i).re
  have e (b : C) : (b*A).re=h*(b*B).re := by
    have n0:=chartNorm half h2 F T c i (fun j=>x j+b*z j)
    rw [analysisLinear,polar,polar,chartNorm half h2,chartNorm half h2] at n0
    change _+_+2*(b*A).re=h*(_+_+2*(b*B).re) at n0
    grind only
  have r:=e 1; rw [Semiring.one_mul,Semiring.one_mul] at r
  have m:=e imaginaryUnit
  change A=ofReal h*B
  apply ComplexScalar.ext
  · rw [re_mul,re_ofReal,im_ofReal]; grind only
  · simp only [re_mul,im_mul,re_ofReal,im_ofReal] at m ⊢
    change 0*A.re-1*A.im=h*(0*B.re-1*B.im) at m
    grind only

open UpperPairLoss (rest)
open UpperPairCap (walls)
open ExteriorCuts (Wedge7)
open AnchorVacantScore (sites)
open HighestFivePairMinors (pairs coefficient)
open PhysicalCompressionEffect (OrthonormalFrame)
open HighestAnchorPauliTrace (headFrame wordExpectation)
open PackingPolynomial (physicalWeights)

def tail {n} (A : Basis n→Fin 7→C) (j : Fin 5) (i : Basis n) := A i (rest j)

theorem physicalCoordinateCap {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G)
    (T : Transversal G) [DecidableEq (Line T)] (a : Line T) (c : Word n) (i : Basis n)
    (pos : 0<(block half F c i i).re) (A : Basis n→Fin 7→C) (orth : OrthonormalFrame A) (v : Basis n→C) :
    let φ:=analysis half F T c i
    sumOver (sites a T.reps.attach) (fun t=>sumOver pairs (fun p=>normSq (coefficient (φ v) (fun j=>φ (tail A j)) t p)))≤
      2*(block half F c i i).re^3*normSum (qubitIndices n) v := by
  let φ:=analysis half F T c i
  let h:=(block half F c i i).re
  have orth' (u v : Fin 5) : dot (qubitIndices n) (tail A u) (tail A v)=if u=v then 1 else 0 := by
    have inj : rest u=rest v ↔ u=v:=by revert u v; decide
    have eq:=orth (rest u) (rest v)
    simp only [inj] at eq; exact eq
  have norm (j : Fin 5) : dot T.reps.attach (φ (tail A j)) (φ (tail A j))=ofReal h := by
    simp only [φ,chartGram half h2,orth',ite_true,Semiring.mul_one]; rfl
  have apart (j k : Fin 5) (ne : j≠k) : dot T.reps.attach (φ (tail A j)) (φ (tail A k))=0 := by
    simp only [φ,chartGram half h2,orth',ne,ite_false,Semiring.mul_zero]
  have b:=HighestScaledSlater.anchoredScaledFive a T.reps.attach (linesNodup T) (φ v) (fun j=>φ (tail A j)) h pos norm apart
  let price:=sumOver (sites a T.reps.attach) (fun t=>sumOver pairs (fun p=>normSq (coefficient (φ v) (fun j=>φ (tail A j)) t p)))
  change price ≤ 2*h^2*normSum T.reps.attach (φ v) at b
  have vn : normSum T.reps.attach (φ v)=h*normSum (qubitIndices n) v:=chartNorm half h2 F T c i v
  rw [vn] at b
  change price≤2*h^3*normSum (qubitIndices n) v; grind only

def wallPair (w : Wedge7) : Fin 5×Fin 5 := (Fin.ofNat 5 (w.k.val-2),Fin.ofNat 5 (w.m.val-2))

theorem wallTable : walls.map wallPair=pairs := by decide

private theorem sumLE {B : Type} (xs : List B) (f g : B→R) (le : ∀w∈xs,f w≤g w) : sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons i xs ih =>
    have a:=le i List.mem_cons_self; have b:=ih (fun w hw=>le w (List.mem_cons_of_mem i hw))
    change f i+sumOver xs f≤g i+sumOver xs g; grind only

/-- The sole remaining local physical inequality is the word average on a single
anchored exterior test. Everything on its right uses actual physical Pauli coordinates. -/
def wallDomination {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G)
    (a : Line T) (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (v : Basis n→C) : Prop :=
  let s t:=block half F c t i
  let h:=(block half F c i i).re
  let φ:=analysis half F T c i
  ∀w∈walls, h^2*half^n*sumOver (words n) (fun p=>(wordExpectation (headFrame A s v) p w).re) ≤
    4*sumOver (sites a T.reps.attach) (fun t=>normSq (coefficient (φ v) (fun j=>φ (tail A j)) t (wallPair w)))

theorem wordPrice {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    [DecidableEq (Line T)] (a : Line T) (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (orth : OrthonormalFrame A)
    (pos : 0<(block half F c i i).re) (v : Basis n→C) (one : wallDomination half F T a c i A v) :
    let s t:=block half F c t i
    half^n*sumOver walls (fun w=>sumOver (words n) (fun p=>(wordExpectation (headFrame A s v) p w).re))≤
      8*((block half F c i i).re*normSum (qubitIndices n) v) := by
  let s t:=block half F c t i
  let h:=(block half F c i i).re
  let φ:=analysis half F T c i
  let cost w:=sumOver (words n) (fun p=>(wordExpectation (headFrame A s v) p w).re)
  let wt t p:=normSq (coefficient (φ v) (fun j=>φ (tail A j)) t p)
  let B:=sites a T.reps.attach
  have b:=sumLE walls (fun w=>h^2*half^n*cost w) (fun w=>4*sumOver B (fun t=>wt t (wallPair w))) one
  rw [←sumOverMulLeft,←sumOverMulLeft,sumOverSwap walls B] at b
  have tbl (t) : sumOver walls (fun w=>wt t (wallPair w))=sumOver pairs (wt t) := by
    rw [←wallTable]; simp only [sumOver,List.map_map,Function.comp_def]
  rw [sumOverCongr B tbl] at b
  have cap:=physicalCoordinateCap half h2 F T a c i pos A orth v
  let total:=sumOver B (fun t=>sumOver pairs (wt t))
  let m:=normSum (qubitIndices n) v
  change total≤2*h^3*m at cap
  change h^2*half^n*sumOver walls cost≤4*total at b
  change half^n*sumOver walls cost≤8*(h*m)
  have hh : 0<h*h := OrderedRing.mul_pos pos pos
  apply Classical.byContradiction; intro neg
  have strict : 8*(h*m)<half^n*sumOver walls cost:=by grind only
  have bad:=OrderedRing.mul_lt_mul_of_pos_left strict hh; grind only

section Field
variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K] [OrderedRing K]

theorem physicalHighestFromWall (half : K) (h2 : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar K) (mu : Fin 7→K) (orth : OrthonormalFrame A)
    (anchor : ∀{G : MaximalFamily (k+3)} (F : Lift G) (c : Word (k+3)) (i : Basis (k+3)),
      0<(block half F c i i).re → ∀v : Basis (k+3)→ComplexScalar K,
      innerProduct (qubitIndices (k+3)) (fun t=>block half F c t i) v=0 →
      ∃(T : Transversal G) (a : Line T),wallDomination half F T a c i A v) :
    2*UpperFrameTrace.highExcess (physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne := by
  classical
  apply HighestAnchorPauliTrace.physicalHighestFromWords half h2 k A mu orth
  intro G F c i hi v
  dsimp only; intro hv
  obtain ⟨T,a,one⟩:=anchor F c i hi v hv
  exact wordPrice half h2 F T a c i A orth hi v one
end Field

end RankSeven.HighestCharacterChart

#print axioms RankSeven.HighestCharacterChart.columnProduct
#print axioms RankSeven.HighestCharacterChart.chartNorm
#print axioms RankSeven.HighestCharacterChart.chartGram
#print axioms RankSeven.HighestCharacterChart.physicalCoordinateCap
#print axioms RankSeven.HighestCharacterChart.wordPrice
#print axioms RankSeven.HighestCharacterChart.physicalHighestFromWall

