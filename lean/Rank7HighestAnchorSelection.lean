import Rank7PhysicalEndpointPrice
import Rank7UpperPairCap

namespace RankSeven.HighestAnchorSelection

open Lean.Grind Pauli ComplexScalar JointProbePayment JointProbeGram WeightedProbeShift
open MixedDefect (oddWords)
open PhysicalCompressionEffect (OrthonormalFrame)
open PackingPolynomial (physicalWeights link)
open UpperFrameTrace (highExcess)
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]

theorem largeGram (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (large : 2≤15*(physicalPayment half h2 k A mu).kappaOne) :
    2*highExcess (physicalWeights half h2 k A)≤5*(physicalPayment half h2 k A mu).kappaOne := by
  have cap := UpperPairCap.physicalPairCap half h2 k A orth
  unfold highExcess; grind only

private theorem denom (a : F) {d : F} (pos : 0<d) : d*(a/d)=a := by
  have ok := Field.mul_inv_cancel (show d≠0 by grind only)
  rw [Field.div_eq_mul_inv]; grind only

/-- The rational threshold dominates the trigonometric cutoff after squaring, with
strict slack certified by a square centered at 379/408. -/
theorem threshold (P kappa : F) (P1 : P≤1) (top : 1-kappa≤P) (small : 15*kappa≤2) :
    let t := (83-60*P)/36
    1<2*t ∧ t<P ∧ 4*P*(1-P)<(2*t-1)^2 ∧ 5*P+3*t<8*(1-kappa) := by
  let t := (83-60*P)/36
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have eq : 36*t=83-60*P := denom _ (by grind only)
  have square := squareNonnegative (408*P-379)
  have eq2 := congrArg (fun z => (2*z-36)^2) eq
  change 1<2*t ∧ t<P ∧ 4*P*(1-P)<(2*t-1)^2 ∧ 5*P+3*t<8*(1-kappa)
  grind only

private theorem maximum {α : Type} (f : α→F) (xs : List α) (a : α) :
    ∃p,p∈a::xs ∧ ∀q∈a::xs,f q≤f p := by
  induction xs generalizing a with
  | nil => exact ⟨a,by simp,fun q h => (List.mem_singleton.mp h) ▸ Std.le_refl _⟩
  | cons b bs ih =>
    obtain ⟨p,mem,top⟩ := ih b
    by_cases good : f a≤f p
    · refine ⟨p,List.mem_cons_of_mem _ mem,?_⟩
      intro q h; rcases List.mem_cons.mp h with rfl|h; exact good; exact top q h
    · refine ⟨a,List.mem_cons_self,?_⟩
      intro q h; rcases List.mem_cons.mp h with rfl|h; exact Std.le_refl _
      have e := top q h; grind only

private theorem averageLe (half : F) (h2 : 2*half=1) {n : Nat} (f g : Word n→F)
    (le : ∀p∈oddWords n,f p≤g p) : oddAverage half f≤oddAverage half g := by
  have h := Compression.sumOverNonnegative (oddWords n) (fun p => g p-f p) (fun p hp => by have := le p hp; grind only)
  rw [Compression.sumOverSub] at h
  have pp (n : Nat) : 0≤half^n := by
    induction n with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  apply OrderedRing.mul_le_mul_of_nonneg_left (by grind only) (show 0≤2*half^n by have := pp n; grind only)

omit [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F] in
private theorem avgAdd {n : Nat} (half : F) (f g : Word n→F) :
    oddAverage half (fun p => f p+g p)=oddAverage half f+oddAverage half g := by unfold oddAverage; rw [sumOverAdd]; grind only
omit [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F] in
private theorem avgSub {n : Nat} (half : F) (f g : Word n→F) :
    oddAverage half (fun p => f p-g p)=oddAverage half f-oddAverage half g := by unfold oddAverage; rw [Compression.sumOverSub]; grind only
omit [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F] in
private theorem avgMul {n : Nat} (half c : F) (f : Word n→F) :
    oddAverage half (fun p => c*f p)=c*oddAverage half f := by unfold oddAverage; rw [←sumOverMulLeft]; grind only

noncomputable local instance : DecidableRel ((·<·) : F→F→Prop) := fun _ _ => Classical.propDecidable _

/-- For every small highest-pair Gram, one actual maximizing odd word and a rational
threshold capture more than five eighths of the normalized pair weight. -/
theorem physicalHeavyAnchor (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    let f (p : Word (k+3)) := pairWeight A p 0 1
    ∃p∈oddWords (k+3), ∃t:F,
      (∀q∈oddWords (k+3), f q≤f p) ∧ 36*t=83-60*f p ∧ 1<2*t ∧ t<f p ∧
      4*f p*(1-f p)<(2*t-1)^2 ∧ 5<8*oddAverage half (fun q => if t<f q then f q else 0) := by
  classical
  let n := k+3
  let os := oddWords n
  let f (p : Word n) := pairWeight A p 0 1
  let κ := (physicalPayment half h2 k A mu).kappaOne
  have av : oddAverage half f=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have one : (0:F)<1 := OrderedRing.zero_lt_one
  have ex : ∃p∈os,∀q∈os,f q≤f p := by
    cases ho : os with
    | nil =>
      have z : oddAverage half f=0 := by change 2*half^n*sumOver os f=0; rw [ho]; change _*0=0; grind only
      grind only
    | cons a as => exact maximum f as a
  obtain ⟨p,hp,top⟩ := ex
  let P := f p
  let t := (83-60*P)/36
  let keep (v : Word n) := if t<f v then f v else 0
  let H := oddAverage half keep
  let sq := oddAverage half (fun i => (f i)^2)
  have f0 (v : Word n) : 0≤f v := normSq_nonnegative _
  have P1 : P≤1 := by
    have lim := leadingTriangle A orth p hp
    have b := normSq_nonnegative (pairAmplitude A p 0 2)
    have c := normSq_nonnegative (pairAmplitude A p 1 2)
    change 0≤pairWeight A p 0 2 at b; change 0≤pairWeight A p 1 2 at c
    change P+pairWeight A p 0 2+pairWeight A p 1 2≤1 at lim; grind only
  have ident : κ=1-sq := by
    change oddAverage half (fun i => f i*(1-f i))=_
    have eq (i : Word n) : f i*(1-f i)=f i-(f i)^2 := by grind only
    simp only [eq,avgSub,av]; rfl
  have avgTop := averageLe half h2 (fun v => (f v)^2) (fun v => P*f v) (fun v hv => by
    have h := OrderedRing.mul_le_mul_of_nonneg_right (top v hv) (f0 v); change f v*f v≤P*f v at h; grind only)
  rw [avgMul,av] at avgTop
  change sq≤P*1 at avgTop
  have cap : 1-κ≤P := by grind only
  have cut := threshold P κ P1 cap small
  change 1<2*t ∧ t<P ∧ 4*P*(1-P)<(2*t-1)^2 ∧ 5*P+3*t<8*(1-κ) at cut
  have cmp (v : Word n) (hv : v∈os) : (f v)^2≤t*f v+(P-t)*keep v := by
    by_cases h : t<f v
    · have ho := OrderedRing.mul_le_mul_of_nonneg_right (top v hv) (f0 v)
      change f v*f v≤P*f v at ho; unfold keep; simp only [h,ite_true]; grind only
    · have ho := OrderedRing.mul_le_mul_of_nonneg_right (show f v≤t by grind only) (f0 v)
      unfold keep; simp only [h,ite_false]; grind only
  have e := averageLe half h2 _ _ cmp
  rw [avgAdd,avgMul,avgMul,av] at e
  change sq≤t*1+(P-t)*H at e
  have mass : 5<8*H := by
    by_cases good : 5<8*H
    · exact good
    · have v := OrderedRing.mul_nonneg (show 0≤P-t by grind only) (show 0≤5-8*H by grind only); grind only
  exact ⟨p,hp,t,top,denom _ (by grind only),cut.1,cut.2.1,cut.2.2.1,mass⟩

end RankSeven.HighestAnchorSelection

#print axioms RankSeven.HighestAnchorSelection.largeGram
#print axioms RankSeven.HighestAnchorSelection.threshold
#print axioms RankSeven.HighestAnchorSelection.physicalHeavyAnchor

