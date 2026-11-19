import Rank7HighestTransferBound

namespace RankSeven.HighestAnchorReduction

open Lean.Grind Pauli ComplexScalar HighestCodeLocalization HighestExteriorOccupation HighestExteriorComponents
open FiniteProjectionAngles SlaterUnionBound HighestTailTransfer HighestTransferBound HighestExteriorStability
open HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open PhysicalCompressionEffect (OrthonormalFrame)
open PauliPairContraction (normSum)
open WeightedProbeShift (physicalPayment)
open PackingPolynomial (physicalWeights link)
open UpperFrameTrace (highExcess)
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

def anchorTests {n : Nat} (half : F) (A : Basis n→Fin 7→ComplexScalar F)
    {G : MaximalFamily n} (L : Lift G) (c d : Word n) : Prop :=
  let xs := qubitIndices n
  let v := component (HighestExteriorComponents.split half L c d) xs (fun t => A t 0) (fun t => A t 1)
  let m i := HighestExteriorOccupation.measure half xs (v i)
  let z t i := transfer half A (v i) t
  let q := 3*(4*half^n)
  normSum (rows n) (output z 1 2 0 0)≤2*q*diagonal (m 0) (m 1) (m 2) (m 3) 1 2 0 0 ∧
  normSum (rows n) (output z 1 0 2 0)≤2*q*diagonal (m 0) (m 1) (m 2) (m 3) 1 0 2 0

theorem forCode (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (orth : OrthonormalFrame A) {G : MaximalFamily (k+3)} (L : Lift G) (c d : Word (k+3)) (dif : ¬equiv G c d)
    (tests : anchorTests half A L c d) :
    let xs := qubitIndices (k+3)
    let Q := PhysicalProjectionAngles.code half L c d
    let e := 1-half*(energy xs Q (fun t => A t 0)+energy xs Q (fun t => A t 1))
    2*highExcess (physicalWeights half h2 k A)≤13*e+e^2 := by
  let n := k+3
  let xs := qubitIndices n
  let Q := PhysicalProjectionAngles.code half L c d
  let e := 1-half*(energy xs Q (fun t => A t 0)+energy xs Q (fun t => A t 1))
  let v := component (HighestExteriorComponents.split half L c d) xs (fun t => A t 0) (fun t => A t 1)
  let m i := HighestExteriorOccupation.measure half xs (v i)
  let z t i := transfer half A (v i) t
  let q := 3*(4*half^n)
  let s := q⁻¹
  let D := diagonal (m 0) (m 1) (m 2) (m 3)
  have hn : 0<half := by have := OrderedRing.zero_lt_one (R:=F); grind only
  have pow (r : Nat) : 0<half^r := by
    induction r with | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one | succ r ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih hn
  have qp : 0<q := by unfold q; have := pow n; grind only
  have inv : q*s=1 := Field.mul_inv_cancel (show q≠0 by grind only)
  have sn : 0≤s := by
    by_cases ok : 0≤s
    · exact ok
    · have bad := OrderedRing.mul_pos qp (show 0< -s by grind only)
      grind only
  have inequality (x y b : F) (e : x≤b*q*y) : s*x≤b*y := by
    have pr := OrderedRing.mul_le_mul_of_nonneg_left e sn
    have id : s*(b*q*y)=b*y := by grind only
    rwa [id] at pr
  have bnd (a b c' d' : F) : 2*(s*normSum (rows n) (output z a b c' d'))≤5*D a b c' d' := by
    have bound := componentUpper half h2 A orth L c d dif a b c' d'
    change 2*normSum (rows n) (output z a b c' d')≤5*q*D a b c' d' at bound
    have h := inequality _ _ _ bound; grind only
  change normSum (rows n) (output z 1 2 0 0)≤2*q*D 1 2 0 0 ∧ normSum (rows n) (output z 1 0 2 0)≤2*q*D 1 0 2 0 at tests
  have src := physicalSourceMass half h2 L c d dif A orth
  change m 0+m 1+m 2+m 3=1 ∧ 0≤m 3 ∧ m 1+m 2≤2*e ∧ m 3≤e^2 ∧ 0≤e at src
  obtain ⟨all,nn,single,last,en⟩ := src
  have paid := componentStability (rows n) s sn z (m 0) (m 1) (m 2) (m 3) e bnd
    (inequality _ _ _ tests.1) (inequality _ _ _ tests.2) all nn single last en
  have linkEq := componentTransfer half h2 k A L c d
  change normSum (rows n) (output z 1 1 1 1)=q*link (physicalWeights half h2 k A) 0 1 at linkEq
  rw [linkEq] at paid
  change 2*(link (physicalWeights half h2 k A) 0 1-2)≤13*e+e^2
  grind only

theorem physicalHighest (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A)
    (anchors : ∀{G : MaximalFamily (k+3)} (L : Lift G) (c d : Word (k+3)), ¬equiv G c d → anchorTests half A L c d) :
    2*highExcess (physicalWeights half h2 k A)≤5*(physicalPayment half h2 k A mu).kappaOne := by
  let K := (physicalPayment half h2 k A mu).kappaOne
  by_cases large : 2≤15*K
  · exact HighestAnchorSelection.largeGram half h2 k A mu orth large
  · obtain ⟨G,L,c,d,dif,unit,near,price⟩ := HighestPhysicalConcentration.physicalStabilizerPlane half h2 k A mu orth (by change 15*K≤2; grind only)
    let xs := qubitIndices (k+3)
    let Q := PhysicalProjectionAngles.code half L c d
    let E := energy xs Q (fun t => A t 0)+energy xs Q (fun t => A t 1)
    let e := 1-half*E
    change E≤2 at unit; change 19<10*E at near; change 6137*(2-E)≤4000*K at price
    have eq : 2*e=2-E := by unfold e; grind only
    have paid := forCode half h2 k A orth L c d dif (anchors L c d dif)
    exact physicalHighestRate (e:=e) (kappa:=K) (by grind only) (by grind only) (by grind only) paid

theorem counterexampleRequiresAnchor (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7→F) (orth : OrthonormalFrame A)
    (bad : 5*(physicalPayment half h2 k A mu).kappaOne<2*highExcess (physicalWeights half h2 k A)) :
    ∃G : MaximalFamily (k+3),∃L : Lift G,∃c d : Word (k+3), ¬equiv G c d ∧ ¬anchorTests half A L c d ∧
      let xs := qubitIndices (k+3)
      let Q := PhysicalProjectionAngles.code half L c d
      let E := energy xs Q (fun t => A t 0)+energy xs Q (fun t => A t 1)
      19<10*E ∧ 6137*(2-E)≤4000*(physicalPayment half h2 k A mu).kappaOne := by
  let K := (physicalPayment half h2 k A mu).kappaOne
  have sm : 15*K≤2 := by
    by_cases h : 2≤15*K
    · have impossible := HighestAnchorSelection.largeGram half h2 k A mu orth h; grind only
    · grind only
  obtain ⟨G,L,c,d,dif,unit,near,price⟩ := HighestPhysicalConcentration.physicalStabilizerPlane half h2 k A mu orth sm
  refine ⟨G,L,c,d,dif,?_,near,price⟩
  intro ok
  let xs := qubitIndices (k+3)
  let Q := PhysicalProjectionAngles.code half L c d
  let E := energy xs Q (fun t => A t 0)+energy xs Q (fun t => A t 1)
  let e := 1-half*E
  change E≤2 at unit; change 19<10*E at near; change 6137*(2-E)≤4000*K at price
  have eq : 2*e=2-E := by unfold e; grind only
  have s := forCode half h2 k A orth L c d dif ok
  have bound := physicalHighestRate (e:=e) (kappa:=K) (by grind only) (by grind only) (by grind only) s
  grind only

end RankSeven.HighestAnchorReduction

#print axioms RankSeven.HighestAnchorReduction.forCode
#print axioms RankSeven.HighestAnchorReduction.physicalHighest
#print axioms RankSeven.HighestAnchorReduction.counterexampleRequiresAnchor

