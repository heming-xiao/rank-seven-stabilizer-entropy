import Rank7UpperInterior
import Rank7PackingPolynomial

/-! The exterior quantity being interpolated uses a fixed physical frame,
including both weighted probe differences and the entering-wedge allowance. -/
namespace RankSeven.UpperFrameGain
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation Interval
variable {R : Type} [CommRing R]

def tail (s : Fin 7→R) (c d : R) (i : Fin 7) : R := if i=5 then c else if i=6 then d else s i

private theorem once (w : Wedge7) (i : Fin 7) (x : R) :
    amplitude (fun t => if t=i then x else 1) w=(if occupied w i then x else 1) := by
  have e1 := w.ij; have e2 := w.jk; have e3 := w.km
  unfold amplitude product4 occupied
  by_cases ai : w.i=i <;> by_cases aj : w.j=i <;> by_cases ak : w.k=i <;> by_cases am : w.m=i
  all_goals first | omega | simp [ai,aj,ak,am] <;> grind only

private theorem ampMul (s t : Fin 7→R) (w : Wedge7) :
    amplitude (fun i => s i*t i) w=amplitude s w*amplitude t w := by unfold amplitude product4; grind only

theorem distinctTailFactors (s : Fin 7→R) (w : Wedge7) (c d : R) :
    amplitude (tail s c d) w=amplitude (tail s 1 1) w*(if occupied w 5 then c else 1)*(if occupied w 6 then d else 1) := by
  have factor : tail s c d=(fun i => (tail s 1 1 i*(if i=5 then c else 1))*(if i=6 then d else 1)) := by
    funext i; unfold tail; by_cases hc : i=5 <;> by_cases hd : i=6
    all_goals first | omega | simp [hc,hd] <;> grind only
  rw [factor,ampMul,ampMul,once,once]

def wedgePolynomial (s : Fin 7→R) (w : Wedge7) : Bilinear R :=
  let a := amplitude (tail s 1 1) w
  if occupied w 5 then (if occupied w 6 then ⟨0,0,0,a⟩ else ⟨0,a,0,0⟩)
  else (if occupied w 6 then ⟨0,0,a,0⟩ else ⟨a,0,0,0⟩)

theorem wedgePolynomialEval (s : Fin 7→R) (w : Wedge7) (c d : R) :
    (wedgePolynomial s w).eval c d=amplitude (tail s c d) w := by
  rw [distinctTailFactors]; unfold wedgePolynomial; cases occupied w 5 <;> cases occupied w 6 <;> simp [Bilinear.eval] <;> grind only

def combine (a : R) (F G : Bilinear R) : Bilinear R :=
  ⟨a*F.constant+G.constant,a*F.first+G.first,a*F.second+G.second,a*F.interaction+G.interaction⟩
private theorem combineEval (a : R) (F G : Bilinear R) (c d : R) :
    (combine a F G).eval c d=a*F.eval c d+G.eval c d := by unfold combine Bilinear.eval; grind only

def sumWedges (s : Fin 7→R) (x : Wedge7→R) : List Wedge7→Bilinear R
  | [] => ⟨0,0,0,0⟩
  | w::ws => combine (x w) (wedgePolynomial s w) (sumWedges s x ws)

theorem sumWedgesEval (s : Fin 7→R) (x : Wedge7→R) (ws : List Wedge7) (c d : R) :
    (sumWedges s x ws).eval c d=sumOver ws (fun w => amplitude (tail s c d) w*x w) := by
  induction ws with
  | nil => change 0+0*c+0*d+0*c*d=0; grind only
  | cons w ws ih =>
    change (combine _ _ _).eval c d=amplitude (tail s c d) w*x w+sumOver ws _
    rw [combineEval,wedgePolynomialEval,ih]; grind only

def gainPoly (s : Fin 7→R) (x : Wedge7→R) := sumWedges s (fun w => x w-referenceWeight w) wedges

theorem gainPolyEval (s : Fin 7→R) (x : Wedge7→R) (c d : R) :
    (gainPoly s x).eval c d=gain x (amplitude (tail s c d)) := by
  rw [gainPoly,sumWedgesEval]; unfold gain evaluate
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro w; grind only

def pairSpectrum (s : Fin 7→R) (i : Fin 7) (j : Fin 7) := if j=0∨j=i then 1 else s j
def weightedProbe (s : Fin 7→R) (x : Wedge7→R) (i : Fin 7) (c d : R) :=
  gain x (fun w => if occupied w 0 && occupied w i then amplitude (tail (pairSpectrum s i) c d) w else 0)

def probePoly (s : Fin 7→R) (x : Wedge7→R) (i : Fin 7) :=
  sumWedges (pairSpectrum s i) (fun w => if occupied w 0 && occupied w i then x w-referenceWeight w else 0) wedges

theorem probePolyEval (s : Fin 7→R) (x : Wedge7→R) (i : Fin 7) (c d : R) :
    (probePoly s x i).eval c d=weightedProbe s x i c d := by
  rw [probePoly,sumWedgesEval]; unfold weightedProbe gain evaluate
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro w; split <;> grind only

def entering : Wedge7 := ⟨1,2,3,4,by decide,by decide,by decide⟩

/-- Input c,d are the last two probabilities and s contains the other five.
The crossing coefficient is 96 γ h/(2 A), in the normalized price units. -/
def corrected (s : Fin 7→R) (x : Wedge7→R) (lambda mu cross c d : R) :=
  gain x (amplitude (tail s c d))-lambda*(weightedProbe s x 1 c d+weightedProbe s x 2 c d)
    -mu*weightedProbe s x 1 c d+cross*x entering*d*(1-c)

def correctedPoly (s : Fin 7→R) (x : Wedge7→R) (lambda mu cross : R) : Bilinear R :=
  let v := cross*x entering
  combine 1 (gainPoly s x) (combine (-lambda-mu) (probePoly s x 1)
    (combine (-lambda) (probePoly s x 2) ⟨0,0,v,-v⟩))

theorem correctedPolyEval (s : Fin 7→R) (x : Wedge7→R) (lambda mu cross c d : R) :
    (correctedPoly s x lambda mu cross).eval c d=corrected s x lambda mu cross c d := by
  rw [correctedPoly,combineEval,combineEval,combineEval,gainPolyEval,probePolyEval,probePolyEval]
  unfold corrected Bilinear.eval; grind only

/-- Substitution into the actual normalized physical exterior gain. -/
theorem physicalGain (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (mu s : Fin 7→R) (c d : R) (weights : ∀i,(mu i)^2=tail s c d i) :
    SectorDefectAccounting.exteriorGain (amplitude mu) (PhysicalCompressionEffect.physicalEntries half unit k A)=
    (gainPoly s (PackingPolynomial.physicalWeights half unit k A)).eval c d := by
  rw [gainPolyEval,PackingPolynomial.physicalExteriorExpansion,←PackingPolynomial.spectralGainExpansion]
  have same : PackingPolynomial.suffix (PackingPolynomial.forwardGap (fun i => (mu i)^2))=tail s c d := by
    funext i; rw [PackingPolynomial.suffixForwardGap,weights]
  rw [same]

end RankSeven.UpperFrameGain
#print axioms RankSeven.UpperFrameGain.correctedPolyEval
#print axioms RankSeven.UpperFrameGain.physicalGain
