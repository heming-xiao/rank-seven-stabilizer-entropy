import Rank7HighestChartMinorTrace

namespace RankSeven.HighestChartSelection

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCharacterBasis StabilizerCosetTransform CharacterFourOrbits StabilizerPairedCharacters
open HighestCharacterChart HighestChartAction HighestChartMinorTrace PhysicalAntiQuartic AnchorSteiner
variable {R J : Type} [CommRing R]
local notation "C" => ComplexScalar R

private theorem cocNorm {n} (p q : Word n) : normSq (cocycle (imaginaryUnit (R:=R)) p q)=1 := by
  induction p with
  | empty => cases q; change normSq (1:C)=1; unfold normSq; rw [re_one,im_one]; grind only
  | cons a p ih => cases q with | cons b q =>
      rw [cocycle,normSq_mul,ih]; cases a <;> cases b <;> simp only [axisCocycle,normSq,imaginaryUnit,re_one,im_one,re_neg,im_neg] <;> grind only

private theorem cocFour {n} (p q : Word n) : (cocycle (imaginaryUnit (R:=R)) p q)^4=1 := by
  rw [cocyclePhaseBits _ imaginaryUnit_sq]
  have e:=imaginaryUnit_fourth (R:=R)
  cases negativeProduct p q <;> cases anti p q <;> simp [phase] <;> grind only

theorem stable {n} {G : MaximalFamily n} (T : Transversal G) (g : Word n) (hg : g∈G.labels) (b : Line T) :
    shift T g b=b := by
  apply Subtype.ext; apply StabilizerSmallCodes.repClass _ _ _ b.property
  change wordAdd (wordAdd b.val g) b.val∈G.labels
  rwa [wordAddComm b.val g,wordAddCancel]

theorem stableStep {n} {G : MaximalFamily n} (F : Lift G) (T : Transversal G) (c g : Word n) (hg : g∈G.labels) (b : Line T) :
    star (step (R:=R) F T c g b)=phase (F.sign g)*chi b.val g := by
  let u:=wordAdd c b.val
  unfold step; rw [stable T g hg b]; dsimp only; rw [wordAddCancel]
  change star (cocycle imaginaryUnit g u*star (cocycle imaginaryUnit u g)*(phase (F.sign g)*chi c g))=_
  rw [cocycleSwap (imaginaryUnit (R:=R)) g u]
  have norm:=star_mul_self (cocycle (imaginaryUnit (R:=R)) u g)
  rw [cocNorm] at norm
  have z : ofReal (1:R)=(1:C):=rfl
  rw [z] at norm
  have mult : chi g u*cocycle imaginaryUnit u g*star (cocycle imaginaryUnit u g)=(chi g u:C):=by grind only
  rw [mult]; unfold u
  rw [show (chi g (wordAdd c b.val):C)=chi (wordAdd c b.val) g from by unfold chi;rw [antiSymm],StabilizerOddSector.charAddLeft]
  unfold chi
  cases anti c g <;> cases anti b.val g <;> cases F.sign g <;>
    apply ComplexScalar.ext <;> simp [phase] <;> grind only

theorem rowEigen {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c g : Word n) (hg : g∈G.labels)
    (i : Basis n) (b : Line T) (x : Basis n→C) :
    analysis half F T c i (act g x) b=(phase (F.sign g)*chi b.val g)*analysis half F T c i x b := by
  rw [analysisAction,stable T g hg,stableStep F T c g hg]

theorem phaseRow {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c g p : Word n) (hg : g∈G.labels)
    (i : Basis n) (b : Line T) (x : Basis n→C) :
    cocycle imaginaryUnit g p*analysis half F T c i (act (wordAdd p g) x) b=
    (phase (F.sign g)*chi b.val g)*analysis half F T c i (act p x) b := by
  have eq:=rowEigen half F T c g hg i b (act p x)
  have m (j : Basis n) := actProduct (R:=R) g p x j
  rw [wordAddComm g p] at m
  rw [funext m] at eq
  rw [analysisVector] at eq
  unfold HighestCodeLocalization.innerProduct at eq
  rw [←eq,analysisVector]; unfold HighestCodeLocalization.innerProduct
  rw [sumOverMulLeft]; apply sumOverCongr; intro j; grind only

private theorem rowMul {I K : Type} (U : I→K→C) (z : I→C) (r : Four I) (x : Four K) :
    blade (fun b j=>z b*U b j) r x=fourProduct z r*blade U r x := by
  unfold blade
  rw [AlternatingTrace.alternatingRight _ (FourCopySectors.tensorEquivariant _) r,
    AlternatingTrace.alternatingRight _ (FourCopySectors.tensorEquivariant _) r]
  unfold FourCopySectors.act; rw [sumOverMulLeft]; apply sumOverCongr; intro σ
  unfold tensorFour tensor fourProduct; grind only

def parity {n} {G : MaximalFamily n} {T : Transversal G} (r : Four (Line T)) (g : Word n) :=
  ((anti r.1.1.val g ^^ anti r.1.2.val g) ^^ anti r.2.1.val g) ^^ anti r.2.2.val g

theorem translatedBlade {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c g p : Word n) (hg : g∈G.labels)
    (i : Basis n) (A : Basis n→J→C) (r : Four (Line T)) (x : Four J) :
    blade (moved half F T c i A (wordAdd p g)) r x=phase (parity r g)*blade (moved half F T c i A p) r x := by
  let U (p : Word n):=moved half F T c i A p
  let u:=cocycle (imaginaryUnit (R:=R)) g p
  let η (b : Line T) : C:=phase (F.sign g)*chi b.val g
  let z (p : Word n):=blade (U p) r x
  have m : (fun b j=>u*U (wordAdd p g) b j)=(fun b j=>η b*U p b j):=by
    funext b j; exact phaseRow half F T c g p hg i b (fun t=>A t j)
  have prod:=congrArg (fun M=>blade M r x) m
  change blade (fun b j=>u*U (wordAdd p g) b j) r x=blade (fun b j=>η b*U p b j) r x at prod
  rw [rowMul (U (wordAdd p g)) (fun _=>u),rowMul (U p) η] at prod
  have unit : fourProduct (fun _ : Line T=>u) r=1:=by
    have e:=cocFour (R:=R) g p; change u^4=1 at e; unfold fourProduct; grind only
  have amp : fourProduct η r=phase (parity r g) := by
    unfold fourProduct η parity chi
    cases F.sign g <;> cases anti r.1.1.val g <;> cases anti r.1.2.val g <;> cases anti r.2.1.val g <;> cases anti r.2.2.val g <;>
      simp [phase] <;> grind only
  rw [unit,Semiring.one_mul,amp] at prod; exact prod

def affine {n} {G : MaximalFamily n} {T : Transversal G} (r : Four (Line T)) := plane r.1.1 r.1.2 r.2.1 r.2.2

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem offPlane {n} {G : MaximalFamily n} (half : R) (F : Lift G) (T : Transversal G) (c : Word n)
    (i : Basis n) (A : Basis n→J→C) (r : Four (Line T)) (x : Four J) (off : ¬affine r) :
    sumOver (words n) (fun p=>blade (moved half F T c i A p) r x)=0 := by
  let f (p : Word n):=blade (moved half F T c i A p) r x
  have ex : ∃g∈G.labels, parity r g=true:=by
    apply Classical.byContradiction; intro no; apply off
    apply (AnchorCharacterSupport.parityCriterion ..).mpr; intro g hg
    cases e:parity r g with
    | false => exact e
    | true => exact False.elim (no ⟨g,hg,e⟩)
  obtain ⟨g,hg,odd⟩:=ex
  have row (p : Word n) : f (wordAdd p g)=(-1)*f p:=by unfold f; rw [translatedBlade half F T c g p hg,odd]; rfl
  have eq:=AntiPairIncidence.sumShift g f
  rw [sumOverCongr _ row,←sumOverMulLeft] at eq
  have a:=congrArg ComplexScalar.re eq; have b:=congrArg ComplexScalar.im eq
  apply ComplexScalar.ext <;> simp at a b ⊢ <;> grind only

omit [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem shiftAffine {n} {G : MaximalFamily n} (T : Transversal G) (p : Word n) (r : Four (Line T)) :
    affine (fourMap (shift T p) r) ↔ affine r := by
  have same (b : Line T) (g : Word n) (hg : g∈G.labels) :
      anti (shift T p b).val g=(anti b.val g ^^ anti p g) := by
    have h:=(G.criterion _).mp (represents T (wordAdd b.val p)).2 g hg
    rw [antiAddLeft,antiAddLeft] at h
    change anti (representative T (wordAdd b.val p)) g=_
    cases x:anti b.val g <;> cases y:anti p g <;> cases z:anti (representative T (wordAdd b.val p)) g <;> simp_all
  have eq (g : Word n) (hg : g∈G.labels) : parity (fourMap (shift T p) r) g=parity r g:=by
    unfold parity fourMap; simp only [same _ g hg]
    cases anti r.1.1.val g <;> cases anti r.1.2.val g <;> cases anti r.2.1.val g <;> cases anti r.2.2.val g <;> cases anti p g <;> rfl
  unfold affine; rw [AnchorCharacterSupport.parityCriterion,AnchorCharacterSupport.parityCriterion]
  change (∀g∈G.labels, parity (fourMap (shift T p) r) g=false)↔(∀g∈G.labels,parity r g=false)
  exact ⟨fun h g hg=>(eq g hg).symm.trans (h g hg),fun h g hg=>(eq g hg).trans (h g hg)⟩

noncomputable def masked {n} {G : MaximalFamily n} {T : Transversal G} (D : Four (Line T)→C) (r : Four (Line T)) : C :=
  @ite C (affine r) (Classical.propDecidable _) (D r) 0

/-- The complete physical word average may be evaluated with the affine-plane
restriction on both exterior coefficients, in the original unnormalized chart. -/
theorem planeTrace {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (w : ExteriorCuts.Wedge7) :
    let h:=(block half F c i i).re
    let D:=fun r=>blade (columns half F T c i A) r (FrameExteriorSector.sourceTuple w)
    sumOver (words n) (fun p=>sumOver (fourIndices T.reps.attach)
      (fun r=>(star (masked D r)*(fourProduct (fun u=>star (step F T c p u)) r*masked D (fourMap (shift T p) r))).re))=
      24*h^4*sumOver (words n) (fun p=>(HighestAnchorPauliTrace.wordExpectation A p w).re) := by
  classical
  let B:=fourIndices T.reps.attach
  let x:=FrameExteriorSector.sourceTuple w
  let D r:=blade (columns half F T c i A) r x
  let V:=masked D
  let phase4 (p : Word n) (r : Four (Line T)):=fourProduct (fun u=>star (step (R:=R) F T c p u)) r
  let m (p : Word n):=fourMap (shift T p)
  let row (f : Four (Line T)→C) (p : Word n) (r : Four (Line T)):=(star (f r)*(phase4 p r*f (m p r))).re
  have same (r : Four (Line T)) : sumOver (words n) (fun p=>row V p r)=sumOver (words n) (fun p=>row D p r) := by
    by_cases yes:affine r
    · apply sumOverCongr; intro p; have other:affine (m p r):=(shiftAffine T p r).mpr yes
      simp only [row,V,masked,yes,other,ite_true]
    · have eq : sumOver (words n) (fun p=>phase4 p r*D (m p r))=0:=by
        have e:=offPlane half F T c i A r x yes; simp only [movedBlade] at e; exact e
      have en:=congrArg ComplexScalar.re (congrArg (fun q=>star (D r)*q) eq)
      change (star (D r)*sumOver (words n) _).re=(star (D r)*0).re at en
      rw [sumOverMulLeft,(HighestCosetFourier.realSum _ _).1,Semiring.mul_zero,re_zero] at en
      have z : V r=0:=by simp only [V,masked,yes,ite_false]
      have same0 (p : Word n) : row V p r=0:=by unfold row; rw [z]; simp; grind only
      change sumOver (words n) (fun p=>row D p r)=0 at en
      rw [en,sumOverCongr _ same0]
      generalize words n=ps; induction ps with
      | nil => rfl
      | cons p ps ih => change 0+sumOver ps _=0; rw [ih]; grind only
  let h:=(block half F c i i).re
  change sumOver (words n) (fun p=>sumOver B (row V p))=24*h^4*_
  rw [sumOverSwap,sumOverCongr B same,sumOverSwap B (words n),sumOverMulLeft (words n) _ (24*h^4)]
  apply sumOverCongr; intro p; exact wordOrbitTrace half h2 F T c i A p w

end RankSeven.HighestChartSelection

#print axioms RankSeven.HighestChartSelection.stableStep
#print axioms RankSeven.HighestChartSelection.translatedBlade
#print axioms RankSeven.HighestChartSelection.offPlane
#print axioms RankSeven.HighestChartSelection.shiftAffine
#print axioms RankSeven.HighestChartSelection.planeTrace

