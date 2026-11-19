import Rank7LowerSmallHeadData
import Rank7RealLowerPhysicalPrice
namespace RankSeven.RealLowerSmallHead
open Pauli ExteriorCuts PackingDual PackingInterpolation LowerSmallHeadData
noncomputable section
private theorem refEval (c : Wedge7→Nat) :
    evaluate (referenceWeight : Wedge7→ℝ) (fun w => (c w:ℝ))=refN c := by
  unfold evaluate refN
  generalize wedges=ws
  induction ws with
  | nil => simp [sumOver]
  | cons w ws ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    change (c w:ℝ)*referenceWeight w+sumOver ws _=_
    rw [ih]; cases b : SectorDefectAccounting.planeFlag w <;> simp [referenceWeight,b]

theorem planSound (p : Plan) (c : Wedge7→Nat) (ok : p.ok c=true)
    (a : Wedge7→ℝ) (ha : ∀w,0≤a w) (rows : RowsHold a) :
    gain a (fun w => (c w : ℝ))≤0 := by
  simp only [Plan.ok,Bool.and_eq_true_iff,decide_eq_true_eq] at ok
  have dual := weakDual a ha rows (fun w=>p.denom*c w) p.prices (p.denom*refN c)
    ⟨ok.1.1.2,ok.1.2,ok.2⟩
  have scale : score a (fun w => p.denom*c w)=(p.denom : ℝ)*evaluate a (fun w => (c w:ℝ)) := by
    unfold score evaluate; rw [sumOverMulLeft]; apply sumOverCongr; intro w
    change ((p.denom*c w:Nat):ℝ)*a w=_; push_cast; ring
  rw [scale] at dual
  change _≤((p.denom*refN c:Nat):ℝ) at dual
  push_cast at dual
  have pos : (0:ℝ)<p.denom := by exact_mod_cast ok.1.1.1
  unfold gain; rw [refEval]
  exact sub_nonpos.mpr ((mul_le_mul_iff_right₀ pos).mp dual)

private theorem zeroSum {α : Type} (S : List α) : sumOver S (fun _ => (0:ℝ))=0 := by
  induction S with
  | nil => rfl
  | cons j js ih => change 0+sumOver js (fun _ => (0:ℝ))=0; rw [ih,zero_add]

private theorem linearEval {α : Type} (S : List α) (f : α→Wedge7→ℝ) (b : α→ℝ) (a : Wedge7→ℝ) :
    evaluate a (fun w => sumOver S (fun j=>b j*f j w))=sumOver S (fun j=>b j*evaluate a (f j)) := by
  induction S with
  | nil => unfold evaluate; rw [show (fun w => sumOver ([] : List α) (fun j=>b j*f j w)*a w)=fun _ => (0:ℝ) by funext; change 0*_=0; ring]; exact zeroSum wedges
  | cons j js ih =>
    have step (w : Wedge7) : sumOver (j::js) (fun i=>b i*f i w)*a w=b j*(f j w*a w)+sumOver js (fun i=>b i*f i w)*a w := by
      change (b j*f j w+sumOver js (fun i=>b i*f i w))*a w=_; ring
    change sumOver wedges _=b j*evaluate a (f j)+sumOver js _
    rw [sumOverCongr wedges step,sumOverAdd,←sumOverMulLeft,←ih]; rfl

theorem linearGain {α : Type} (S : List α) (f : α→Wedge7→ℝ) (b : α→ℝ) (a : Wedge7→ℝ) :
    gain a (fun w => sumOver S (fun j=>b j*f j w))=sumOver S (fun j=>b j*gain a (f j)) := by
  unfold gain; rw [linearEval,linearEval,←Compression.sumOverSub]; apply sumOverCongr; intro j; ring

theorem gainSumNonpos {α : Type} (S : List α) (f : α→Wedge7→ℝ) (b : α→ℝ) (a : Wedge7→ℝ)
    (bn : ∀j∈S,0≤b j) (gn : ∀j∈S,gain a (f j)≤0) :
    gain a (fun w => sumOver S (fun j=>b j*f j w))≤0 := by
  rw [linearGain]; convert UpperOddCut.sumLe S (f:=fun j=>b j*gain a (f j)) (g:=fun _=>0) (fun j hj=>mul_nonpos_of_nonneg_of_nonpos (bn j hj) (gn j hj)) using 1
  exact (zeroSum S).symm

end
end RankSeven.RealLowerSmallHead
#print axioms RankSeven.RealLowerSmallHead.planSound
#print axioms RankSeven.RealLowerSmallHead.gainSumNonpos