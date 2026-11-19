import Rank7LowerSignedExterior
namespace RankSeven.LowerPhysicalGainScale
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation UpperFrameGain UpperPhysicalInterior LowerSignedExterior
variable {R : Type} [CommRing R]

def rawProbe (s : Fin 7→R) (weights : Wedge7→R) (j : Fin 7) : R :=
  gain weights (fun w => if occupied w 0 && occupied w j then amplitude (pairSpectrum s j) w else 0)



private theorem mulAmp (s t : Fin 7→R) (w : Wedge7) :
    amplitude (fun i => s i*t i) w=amplitude s w*amplitude t w := by
  unfold amplitude product4; grind only

private theorem scaleEval (weights f : Wedge7→R) (k : R) : evaluate weights (fun w => k*f w)=k*evaluate weights f := by
  unfold evaluate; rw [sumOverMulLeft]; apply sumOverCongr; intro w; grind only
private theorem scaleGain (weights f : Wedge7→R) (k : R) : gain weights (fun w => k*f w)=k*gain weights f := by
  unfold gain; rw [scaleEval,scaleEval]; grind only

private def degree (j i : Fin 7) : Nat := if i=0∨i=j then 0 else 1
private theorem degrees : wedges.all (fun w => [1,2].all (fun j =>
    !(occupied w 0 && occupied w j) || decide (degree j w.i+degree j w.j+degree j w.k+degree j w.m=2)))=true := by decide

theorem rawProbeScale (s : Fin 7→R) (weights : Wedge7→R) (b : R) (j : Fin 7) (hi : j=1 ∨ j=2) :
    rawProbe (fun i => b*s i) weights j=b^2*rawProbe s weights j := by
  have pm : pairSpectrum (fun i => b*s i) j=(fun i => (b^degree j i)*pairSpectrum s j i) := by
    funext i; by_cases test : i=0∨i=j <;> simp [pairSpectrum,degree,test] <;> grind only
  have jm : j∈([1,2] : List (Fin 7)) := by rcases hi with h|h <;> simp [h]
  have factor (w : Wedge7) (good : (occupied w 0 && occupied w j)=true) : amplitude (fun i => b^degree j i) w=b^2 := by
    have v := List.all_eq_true.mp (List.all_eq_true.mp degrees w (memWedges w)) j jm
    simp only [good,Bool.not_true,Bool.false_or,decide_eq_true_eq] at v
    unfold amplitude product4; rw [← Semiring.pow_add,← Semiring.pow_add,← Semiring.pow_add,v]
  unfold rawProbe; rw [← scaleGain,pm]
  apply congrArg (gain weights); funext w
  by_cases good : (occupied w 0 && occupied w j)=true
  · simp only [good,↓reduceIte,mulAmp,factor w good]
  · simp [good] <;> grind only

theorem rawGainScale (s : Fin 7→R) (weights : Wedge7→R) (b : R) :
    gain weights (amplitude (fun i => b*s i))=b^4*gain weights (amplitude s) := by
  rw [← scaleGain]; apply congrArg (gain weights); funext w; unfold amplitude product4; grind only

private theorem strip (s : Fin 7→R) (j : Fin 7) (good : j=1 ∨ j=2) (c d : R) :
    pairSpectrum (tail s c d) j=tail (pairSpectrum s j) c d := by
  funext i; rcases good with rfl|rfl <;> unfold tail pairSpectrum <;> split <;> split <;> first | rfl | (simp_all <;> omega)

variable {S : Type} [Field S] [LE S] [LT S] [Std.IsLinearOrder S] [Std.LawfulOrderLT S] [OrderedRing S]

def rawSpectrum (z y x b c : S) : Fin 7→S := tail (fun i => b*spectrum z y x i) c 1

/-- Restores the literal quartic gain, two degree-two weighted probe differences,
and the physical crossing for the ordered spectrum (α,β,γ,b,b,c,1). -/
theorem physicalNumerator (z y x b c w : S) (p : LowerCorner.Prices S) (weights : Wedge7→S) (bp : 0<b) :
    let s := rawSpectrum z y x b c
    let U := rawProbe s weights
    (b*b)*gainAt z y x b c w p weights=
      gain weights (amplitude s)-(b*b*p.lambda)*(U 1+U 2)-
      (b*b*LowerSignedPrices.mu z y x w)*U 1+
      LowerSignedPrices.cross z x*(b*b)*(b-c)*weights entering := by
  let h := spectrum z y x
  let s := tail h (c/b) (1/b)
  let m := LowerSignedPrices.mu z y x w
  let a := LowerSignedPrices.cross z x
  have cx := UpperContractor.quotientEq c bp
  have dx := UpperContractor.quotientEq (1:S) bp
  have form : rawSpectrum z y x b c=fun i => b*s i := by
    funext i; unfold rawSpectrum; dsimp only [s,h,tail]
    by_cases cc : i=5 <;> by_cases dd : i=6 <;> simp [cc,dd,cx,dx]
  have u (i : Fin 7) (hi : i=1∨i=2) :
      rawProbe (fun j => b*s j) weights i=b^2*weightedProbe h weights i (c/b) (1/b) := by
    rw [rawProbeScale _ _ _ _ hi]; unfold rawProbe weightedProbe; rw [show pairSpectrum s i=tail (pairSpectrum h i) (c/b) (1/b) from strip h i hi _ _]
  change b*b*(b*b*(gain weights (amplitude s)-p.lambda*(weightedProbe h weights 1 (c/b) (1/b)+weightedProbe h weights 2 (c/b) (1/b))-
    m*weightedProbe h weights 1 (c/b) (1/b)+a*weights entering*(1/b)*(1-c/b)))=_
  rw [form,rawGainScale,u 1 (Or.inl rfl),u 2 (Or.inr rfl)]
  have sc : b*b*((1/b)*(1-c/b))=b-c := by
    rw [show b*b*((1/b)*(1-c/b))=(b*(1/b))*(b-b*(c/b)) by grind only,cx,dx]; grind only
  have fee := congrArg (fun t : S => a*(b*b)*t*weights entering) sc
  dsimp only [a,m] at *; grind only

end RankSeven.LowerPhysicalGainScale
#print axioms RankSeven.LowerPhysicalGainScale.physicalNumerator