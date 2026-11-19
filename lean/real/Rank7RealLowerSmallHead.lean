import Rank7LowerSmallHeadOff
import Rank7LowerSmallHeadFirst
import Rank7LowerSmallHeadBoth
import Rank7LowerSmallHeadMixed
import Rank7RealLowerSmallHeadFactors
import Rank7RealLowerSmallHeadDual
import Rank7LowerPhysicalGainScale
import Rank7PhysicalComparison
namespace RankSeven.RealLowerSmallHead
open Pauli ExteriorCuts PackingDual PackingInterpolation UpperFrameGain LowerSmallHeadData
open PhysicalCompressionEffect (OrthonormalFrame physicalEntries)
open PhysicalDefectAssembly (PairedDefectBound)
open PackingPolynomial (physicalWeights)
noncomputable section

theorem cornerGain (k : Corner) (a : Wedge7→ℝ) (an : ∀w,0≤a w) (rows : RowsHold a)
    (z y x r : ℝ) (hz : 0≤z) (hy : 0≤y) (hx : 0≤x) (hr : 0≤r) (unit : x+2*y+r=1) :
    gain a (fun w=>amplitude (tail (UpperPhysicalInterior.spectrum z y x) 1 1) w * (tailPrice k w:ℝ))≤0 := by
  have expansion (w : Wedge7) :
      amplitude (tail (UpperPhysicalInterior.spectrum z y x) 1 1) w*(tailPrice k w:ℝ)=
      sumOver tags (fun j=>mon x y r z j * (cost k j w:ℝ)) := by
    rw [headAmplitude _ _ _ _ unit,headExpansion,sumOverMulRight]
    apply sumOverCongr; intro j; unfold cost mask; push_cast; ring
  rw [show (fun w=>amplitude (tail (UpperPhysicalInterior.spectrum z y x) 1 1) w*(tailPrice k w:ℝ))=
    fun w=>sumOver tags (fun j=>mon x y r z j * (cost k j w:ℝ)) from funext expansion]
  apply gainSumNonpos tags (fun j w=>(cost k j w:ℝ)) (mon x y r z) a (fun j _ => monNonnegative _ _ _ _ hx hy hr hz j)
  intro j hj
  have cert : ∃p:Plan,p.ok (cost k j)=true := by
    cases k with
    | off => exact offPlans j hj
    | first => exact firstPlans j hj
    | both => exact bothPlans j hj
    | mixed => exact mixedPlans j hj
  obtain ⟨p,ok⟩:=cert; exact planSound p _ ok a an rows

def tailWeight (c d : ℝ) : Corner→ℝ
  | .off => (1-c)*(1-d)
  | .first => c-d
  | .both => c*d
  | .mixed => (1-c)*d

/-- The ordered-tail simplex has a nonnegative decomposition even when the second-only
corner has positive gain. The mixed price sums both one-tail corners. -/
theorem exteriorNonpositive (a : Wedge7→ℝ) (an : ∀w,0≤a w) (rows : RowsHold a)
    (z y x c d : ℝ) (hz : 0≤z) (hy : 0≤y) (hx : 0≤x) (head : x+2*y≤1)
    (hd : 0≤d) (hdc : d≤c) (hc : c≤1) :
    gain a (amplitude (tail (UpperPhysicalInterior.spectrum z y x) c d))≤0 := by
  let s:=UpperPhysicalInterior.spectrum z y x
  let S : List Corner := [.off,.first,.both,.mixed]
  let f (k : Corner) (w : Wedge7) := amplitude (tail s 1 1) w * (tailPrice k w:ℝ)
  have expansion (w : Wedge7) : amplitude (tail s c d) w=sumOver S (fun k=>tailWeight c d k*f k w) := by
    rw [distinctTailFactors]
    change _=tailWeight c d .off*f .off w+(tailWeight c d .first*f .first w+
      (tailWeight c d .both*f .both w+(tailWeight c d .mixed*f .mixed w+0)))
    simp only [f,tailWeight,tailPrice]
    cases occupied w 5 <;> cases occupied w 6 <;> norm_num <;> ring
  change gain a (amplitude (tail s c d))≤0
  rw [funext expansion]
  apply gainSumNonpos S f (tailWeight c d) a
  · intro k _
    cases k with
    | off => exact mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr (hdc.trans hc))
    | first => exact sub_nonneg.mpr hdc
    | both => exact mul_nonneg (hd.trans hdc) hd
    | mixed => exact mul_nonneg (sub_nonneg.mpr hc) hd
  · intro k _; exact cornerGain k a an rows z y x (1-(x+2*y)) hz hy hx (sub_nonneg.mpr head) (by ring)

theorem physicalOldSmallHead (half inv24 : ℝ) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar ℝ) (mu : Fin 7→ℝ) (orth : OrthonormalFrame A)
    (z y x b c : ℝ) (hz : 0≤z) (hy : 0≤y) (hx : 0≤x) (head : x+2*y≤1)
    (cb : 1≤c ∧ c≤b) (chart : (fun i=>(mu i)^2)=LowerPhysicalGainScale.rawSpectrum z y x b c) :
    PairedDefectBound half inv24 h2 k A mu := by
  let a:=physicalWeights half h2 k A
  let s:=UpperPhysicalInterior.spectrum z y x
  have bp : 0<b := by linarith only [cb.1,cb.2]
  have rows:=PackingPolynomial.physicalRows half h2 k A orth
  have ng:=exteriorNonpositive a rows.1 rows.2 z y x (c/b) (1/b) hz hy hx head
    (by positivity) ((div_le_div_iff_of_pos_right bp).mpr cb.1) ((div_le_one bp).mpr cb.2)
  have form : LowerPhysicalGainScale.rawSpectrum z y x b c=fun i=>b*tail s (c/b) (1/b) i := by
    funext i; unfold LowerPhysicalGainScale.rawSpectrum tail
    by_cases v : i=5 <;> by_cases t : i=6 <;> simp [v,t,s,ne_of_gt bp] <;> field_simp
  have g:=physicalGain half h2 k A mu (fun i=>b*s i) c 1 (fun i=>congrFun chart i)
  rw [gainPolyEval] at g
  change SectorDefectAccounting.exteriorGain (amplitude mu) (physicalEntries half h2 k A)=
    gain a (amplitude (LowerPhysicalGainScale.rawSpectrum z y x b c)) at g
  rw [form,LowerPhysicalGainScale.rawGainScale] at g
  have GN:=mul_nonpos_of_nonneg_of_nonpos (show 0≤b^4 by positivity) ng
  have loss:=SectorDefectAccounting.physicalLossNonnegative half h2 k A orth (amplitude mu)
  apply PhysicalComparison.compareOfCompression half inv24 h2 h24 k A mu orth
  linarith only [g,GN,loss]

/-- Strict cap exits are empty on the replay contractor's residual. The small-head
exit is paid, and the shared-tail equality x=b−1 is excluded by the lower slabs. -/
theorem residualOld {P : Prop} (z y x b : ℝ) (res : LowerContractor.Residual z y x b)
    (b0 : 0<b) (bcap : b≤4/3) (old : LowerLeaves.OldCondition z y x b)
    (small : x+2*y≤1 → P) :
    P ∨ 5*z*x=z+2*y+3*x ∨ 96*y≤1 ∨ 3*b*x=2 ∨ z=(b-1)*(1+x+y) := by
  rcases old with h|h|h|h|h|h|h|h
  · exact Or.inr (Or.inl (le_antisymm (by linarith only [h]) res.headWeight))
  · exfalso; linarith only [h,res.deltaCap]
  · exact False.elim ((not_lt_of_ge res.productCap) h)
  · exact Or.inl (small h)
  · exact Or.inr (Or.inr (Or.inl h))
  · right; right; right; left
    have hb := (le_div_iff₀ b0).mp h
    nlinarith only [hb,res.tail]
  · exfalso; linarith only [h,res.xHead,bcap]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (le_antisymm h res.zShared))))

end
end RankSeven.RealLowerSmallHead
#print axioms RankSeven.RealLowerSmallHead.cornerGain
#print axioms RankSeven.RealLowerSmallHead.exteriorNonpositive
#print axioms RankSeven.RealLowerSmallHead.physicalOldSmallHead
#print axioms RankSeven.RealLowerSmallHead.residualOld