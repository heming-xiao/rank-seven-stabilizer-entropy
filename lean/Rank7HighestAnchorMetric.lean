import Rank7HighestAnchorVectors

namespace RankSeven.HighestAnchorMetric

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestCodeLocalization HighestExteriorOccupation HighestExteriorComponents
open HighestStabilizerLine HighestAnchorVectors HighestTailTransfer HighestCosetFourier FiniteProjectionAngles SlaterUnionBound
open HeavyPauliGroup StabilizerCharacterBasis
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem column (xs : List α) (P : Mx α R) (pr : Projection xs P) (v : α→ComplexScalar R) (i : α) :
    innerProduct xs (fun a => P a i) v=image xs P v i := by
  unfold innerProduct image; apply sumOverCongr; intro a
  have eq : star (P a i)=P i a := congrFun (congrFun pr.herm i) a
  rw [eq]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem orthogonalPartner [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (P : Mx α R)
    (pr : Projection xs P) (v : α→ComplexScalar R) (i : α) :
    innerProduct xs (fun a => P a i) (image xs (compl P) v)=0 := by
  rw [column xs P pr,imageComp]; change image xs (matMul xs P (compl P)) v i=0
  unfold compl; rw [subRight,idRight xs nd full,pr.square]
  unfold image subM
  have eq (a : α) : (P i a-P i a)*v a=0 := by grind only
  rw [sumOverCongr _ eq]
  have zz (ls : List α) : sumOver ls (fun _ => (0:ComplexScalar R))=0 := by
    induction ls with | nil => rfl | cons j js ih => change 0+sumOver js _=0; rw [ih]; grind only
  exact zz _

theorem removeParallel [DecidableEq α] (half : R) (h2 : 2*half=1) (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs)
    (P : Mx α R) (pr : Projection xs P) (tr : trace xs P=1) (v : α→ComplexScalar R) (i : α) :
    exterior (fun a => P a i) v=exterior (fun a => P a i) (image xs (compl P) v) := by
  have rem (j : α) : image xs (compl P) v j=v j-image xs P v j := by
    let V (j : α) (_ : Unit) := v j
    change matMul xs (compl P) V j ()=_
    unfold compl; rw [subLeft,idLeft xs nd full]; rfl
  funext t; rcases t with ⟨a,b⟩
  have kill : P a i*image xs P v b=image xs P v a*P b i := by
    unfold image; rw [sumOverMulLeft,sumOverMulRight]; apply sumOverCongr; intro j
    have eq := projectionMinors half h2 xs full P pr tr i j a b; grind only
  unfold exterior; simp only [rem]; grind only

theorem characterWedgeMass {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (c : Word n)
    (i : Basis n) (v : Basis n→ComplexScalar R) :
    let xs := qubitIndices n
    let P := block half L c
    let s a := P a i
    let y := image xs (compl P) v
    exterior s v=exterior s y ∧ innerProduct xs s y=0 ∧ normSum xs s=(P i i).re ∧
      HighestExteriorOccupation.measure half xs (exterior s v)=(P i i).re*normSum xs y := by
  let xs := qubitIndices n
  let P := block half L c
  let s a := P a i
  let y := image xs (compl P) v
  have pr := PhysicalProjectionAngles.lineProjection half h2 L c
  have tr := blockTrace half h2 L c
  have eq := removeParallel half h2 xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete P pr tr v i
  have orth := orthogonalPartner xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete P pr v i
  have col : innerProduct xs s s=P i i := by
    have g : matMul xs (dagger P) P=P := by rw [pr.herm,pr.square]
    exact congrFun (congrFun g i) i
  rw [selfProduct] at col
  have ns : normSum xs s=(P i i).re := congrArg ComplexScalar.re col
  refine ⟨eq,orth,ns,?_⟩
  rw [eq,exteriorMass half h2,orth,ns]
  simp only [normSq,re_zero,im_zero]; grind only

theorem lineBoundFromOrthogonal {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R)
    {G : MaximalFamily n} (L : Lift G) (c : Word n)
    (score : ∀(i : Basis n),0<(block half L c i i).re → ∀(v : Basis n→ComplexScalar R),
      let xs := qubitIndices n
      let s a := block half L c a i
      innerProduct xs s v=0 → normSum (rows n) (transfer half A (exterior s v))≤
        2*(3*(4*half^n))*((block half L c i i).re*normSum xs v)) : HighestAnchorVectors.lineBound half A L c := by
  intro i pos v
  let xs := qubitIndices n
  let P := block half L c
  let s a := P a i
  let y := image xs (compl P) v
  have met := characterWedgeMass half h2 L c i v
  have eq : exterior s v=exterior s y := met.1
  have h := score i pos y met.2.1
  change normSum (rows n) (transfer half A (exterior s v))≤2*(3*(4*half^n))*HighestExteriorOccupation.measure half xs (exterior s v)
  rw [met.2.2.2,eq]; exact h

end RankSeven.HighestAnchorMetric

#print axioms RankSeven.HighestAnchorMetric.characterWedgeMass
#print axioms RankSeven.HighestAnchorMetric.lineBoundFromOrthogonal

