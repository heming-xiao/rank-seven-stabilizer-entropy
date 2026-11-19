import Rank7UpperCornerSignedIdentity
import Rank7UpperSignedCornerGain
namespace RankSeven.UpperCornerAccounting
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation UpperCornerExpansion UpperCornerFactors UpperCornerColumns UpperCornerPolynomial UpperCornerFrameProducts UpperCornerWedgeWeights UpperCornerSignedIdentity UpperFrameTrace UpperFrameGain
attribute [local instance] Ring.intCast
variable {R : Type} [CommRing R]
private theorem addEval (x f g : Wedge7→R) : evaluate x (fun w => f w+g w)=evaluate x f+evaluate x g := by
  unfold evaluate; rw [←sumOverAdd]; apply sumOverCongr; intro w; grind only
private theorem subEval (x f g : Wedge7→R) : evaluate x (fun w => f w-g w)=evaluate x f-evaluate x g := by
  unfold evaluate; rw [←Compression.sumOverSub]; apply sumOverCongr; intro w; grind only
private theorem scaleEval (x f : Wedge7→R) (a : R) : evaluate x (fun w => a*f w)=a*evaluate x f := by
  unfold evaluate; rw [sumOverMulLeft]; apply sumOverCongr; intro w; grind only
private theorem addG (x f g : Wedge7→R) : gain x (fun w => f w+g w)=gain x f+gain x g := by unfold gain; rw [addEval,addEval]; grind only
private theorem subG (x f g : Wedge7→R) : gain x (fun w => f w-g w)=gain x f-gain x g := by unfold gain; rw [subEval,subEval]; grind only
private theorem scaleG (x f : Wedge7→R) (a : R) : gain x (fun w => a*f w)=a*gain x f := by unfold gain; rw [scaleEval,scaleEval]; grind only
private theorem zeroG (x : Wedge7→R) : gain x (fun _ => 0)=0 := by
  have e := scaleG x (fun _ => (0:R)) 0; simp only [Semiring.zero_mul] at e; exact e
private theorem gainTail (x f g : Wedge7→R) (r : Branch) : gain x (fun w => tail2 r (f w) (g w))=tail2 r (gain x f) (gain x g) := by unfold tail2; split <;> simp only [scaleG]
private theorem gainMiddle (x f g : Wedge7→R) (r : Branch) : gain x (fun w => middle2 r (f w) (g w))=middle2 r (gain x f) (gain x g) := by unfold middle2; split <;> simp only [scaleG]
private theorem gainFloor (x f g : Wedge7→R) (r : Branch) : gain x (fun w => floor2 r (f w) (g w))=floor2 r (gain x f) (gain x g) := by
  have cs : ∀i : Fin 3,i=0∨i=1∨i=2 := by decide
  rcases cs r.floor with e|e|e <;> simp only [floor2,e] <;> first | exact scaleG _ _ _ | (change gain x (fun w => 4*f w+2*g w)=_; rw [addG,scaleG,scaleG])
private theorem gainExtra (x f g z : Wedge7→R) (r : Branch) : gain x (fun w => extra2 r (f w) (g w) (z w))=extra2 r (gain x f) (gain x g) (gain x z) := by
  cases e : r.charge <;> simp only [extra2,e,Bool.false_eq_true,ite_false,ite_true,zeroG,subG,addG,scaleG,gainMiddle]
theorem gainTwice (x N V Z : Wedge7→R) (r : Branch) (h k q c d l y : R) :
    gain x (fun w => twiceBound r h k q c d l y (N w) (V w) (Z w))=
      twiceBound r h k q c d l y (gain x N) (gain x V) (gain x Z) := by
  cases e : r.single <;> simp only [twiceBound,e,Bool.false_eq_true,ite_false,ite_true,subG,addG,scaleG,gainTail,gainMiddle,gainFloor,gainExtra]

private theorem pairEval (x : Wedge7→R) (i : Fin 7) :
    evaluate x (fun w => Int.cast (R:=R) (if occupied w 0 && occupied w i then (1:Int) else 0))=PackingPolynomial.link x 0 i := by
  apply sumOverCongr; intro w; by_cases h : (occupied w 0 && occupied w i)=true <;> simp [h] <;> grind only
private theorem highG (x : Wedge7→R) : gain x (fun w => Int.cast (high w))=UpperFrameTrace.highExcess x := by
  unfold gain high UpperFrameTrace.highExcess; rw [pairEval,pairEval,PackingPolynomial.referenceLink _ _ (by decide : (0:Fin 7)≠1)]
private theorem sharedG (x : Wedge7→R) : gain x (fun w => Int.cast (shared w))=UpperFrameTrace.sharedExcess x := by
  unfold shared; simp only [Ring.intCast_add,addG,highG]
  unfold gain second UpperFrameTrace.highExcess UpperFrameTrace.sharedExcess
  rw [pairEval,pairEval,PackingPolynomial.referenceLink _ _ (by decide : (0:Fin 7)≠2)]; grind only
private theorem missingG (x : Wedge7→R) : gain x (fun w => Int.cast (missing w))=missingTriple x := by
  let keep (w : Wedge7) := (Row.triple 0 1 2).covers w
  have seen (w : Wedge7) : (Int.cast (R:=R) (missing w))=(if keep w then -1 else 0) := by
    unfold missing keep Row.covers; by_cases yes : ((occupied w 0 && occupied w 1) && occupied w 2)=true <;> simp [yes] <;> grind
  have e (y : Wedge7→R) : evaluate y (fun w => Int.cast (missing w))= -rowMass y (.triple 0 1 2) := by
    have f (w : Wedge7) : Int.cast (missing w)*y w=(-1)*(if keep w then y w else 0) := by rw [seen]; cases keep w <;> simp <;> grind only
    unfold evaluate; rw [sumOverCongr wedges f,←sumOverMulLeft]; change (-1)*rowMass _ _=_; grind only
  have ref : rowMass (referenceWeight (R:=R)) (.triple 0 1 2)=1 := by
    let a : Wedge7 := ⟨0,1,2,3,by decide,by decide,by decide⟩
    have tab : wedges.all (fun w => ((keep w && SectorDefectAccounting.planeFlag w)==(w==a)))=true := by decide
    have term (w : Wedge7) : (if keep w then referenceWeight (R:=R) w else 0)=(if a=w then 1 else 0) := by
      have eq := beq_iff_eq.mp (List.all_eq_true.mp tab w (memWedges w))
      have same : (if keep w then referenceWeight (R:=R) w else 0)=(if keep w && SectorDefectAccounting.planeFlag w then 1 else 0) := by
        unfold referenceWeight; cases keep w <;> cases SectorDefectAccounting.planeFlag w <;> rfl
      rw [same,eq]; by_cases wa : w=a
      · subst w; simp
      · have aw : a≠w := Ne.symm wa; simp [wa,aw]
    change sumOver wedges (fun w => if keep w then referenceWeight w else 0)=_
    rw [sumOverCongr wedges term,ExteriorPauliBase.sumOnIndex wedges a (fun _ => 1) wedgesNodup (memWedges a)]
  unfold gain missingTriple; rw [e,e,ref]; grind only
private theorem enterG (x : Wedge7→R) : gain x (fun w => Int.cast (enter w))=x entering := by
  have f (y : Wedge7→R) (w : Wedge7) : Int.cast (enter w)*y w=(if entering=w then y w else 0) := by
    unfold enter; by_cases eq : entering=w
    · subst w; simp; grind
    · have rev := Ne.symm eq; simp [eq,rev]; grind
  have e (y : Wedge7→R) : evaluate y (fun w => Int.cast (enter w))=y entering := by
    unfold evaluate; rw [sumOverCongr wedges (f y),ExteriorPauliBase.sumOnIndex wedges entering y wedgesNodup (memWedges _)]
  have z : referenceWeight (R:=R) entering=0 := by
    change (if SectorDefectAccounting.planeFlag entering then 1 else 0)=0; rw [show SectorDefectAccounting.planeFlag entering=false by decide]; rfl
  unfold gain; rw [e,e,z]; grind only
section Physical
variable {S : Type} [Field S] [LE S] [LT S] [Std.IsLinearOrder S] [Std.LawfulOrderLT S] [OrderedRing S]
omit [LE S] [LT S] [Std.IsLinearOrder S] [Std.LawfulOrderLT S] [OrderedRing S] in
private theorem stripProbe (h k q c d : S) (j : Fin 7) (good : j=1∨j=2) :
    strip h k q c d j=tail (UpperFrameGain.pairSpectrum (UpperPhysicalInterior.spectrum h k q) j) c d := by
  funext a; have cases7 : ∀v : Fin 7,v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6 := by decide
  rcases good with rfl|rfl <;> rcases cases7 a with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

omit [LE S] [LT S] [Std.IsLinearOrder S] [Std.LawfulOrderLT S] [OrderedRing S] in
theorem physicalSignedGain (r : Branch) (h k q c d l y a : S) (x : Wedge7→S)
    (lc : 707*l=Int.cast r.l*(h*q)) (yc : 707*y=Int.cast r.y*(k*(h+k+q))) (ac : 707*a=200*((1+q)*h)) :
    gain x (price r (vector h k q c d))=22624*corrected (UpperPhysicalInterior.spectrum h k q) x l y a c d-
      11312*twiceBound r h k q c d l y (sharedExcess x) (highExcess x) (missingTriple x) := by
  let sp := UpperPhysicalInterior.spectrum h k q
  have info := funext (fun w => physicalPrice r h k q c d l y a w lc yc ac)
  rw [info]
  have crossEq (w : Wedge7) : a*Int.cast (enter w)*d*(1-c)=(a*d*(1-c))*Int.cast (enter w) := by grind only
  simp only [crossEq,subG,addG,scaleG,gainTwice,sharedG,highG,missingG,enterG]
  have one (j : Fin 7) (good : j=1∨j=2) : gain x (pairVal h k q c d j)=weightedProbe sp x j c d := by
    unfold pairVal weightedProbe; rw [stripProbe h k q c d j good]
  rw [one 1 (Or.inl rfl),one 2 (Or.inr rfl)]
  change 22624*(gain x (amplitude (tail sp c d))-l*(weightedProbe sp x 1 c d+weightedProbe sp x 2 c d)-y*weightedProbe sp x 1 c d+
    a*d*(1-c)*x entering)-_ = 22624*(gain x (amplitude (tail sp c d))-l*(weightedProbe sp x 1 c d+weightedProbe sp x 2 c d)-y*weightedProbe sp x 1 c d+
    a*x entering*d*(1-c))-_
  grind only

theorem discreteBound (j : Nat) (hj : j<104) (h k q c d l y a : S) (x : Wedge7→S)
    (hn : 0≤h) (kn : 0≤k) (qn : 1≤2*q) (cd : 0≤d ∧ d≤c ∧ c≤1)
    (nx : ∀w,0≤x w) (rows : RowsHold x) (n0 : 0≤sharedExcess x) (v0 : 0≤highExcess x)
    (lc : 707*l=Int.cast (tag j).l*(h*q)) (yc : 707*y=Int.cast (tag j).y*(k*(h+k+q))) (ac : 707*a=200*((1+q)*h)) :
    2*corrected (UpperPhysicalInterior.spectrum h k q) x l y a c d≤
      twiceBound (tag j) h k q c d l y (sharedExcess x) (highExcess x) (missingTriple x) := by
  have vn (i : Var) : 0≤vector h k q c d i := by
    have cases6 : ∀i : Var,i=0∨i=1∨i=2∨i=3∨i=4∨i=5 := by decide
    rcases cases6 i with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals dsimp [vector]; grind only
  have paid := UpperSignedCornerGain.signedPolynomial j hj (vector h k q c d) vn x nx rows n0 v0
  rw [physicalSignedGain (tag j) h k q c d l y a x lc yc ac] at paid
  grind only

end Physical
end RankSeven.UpperCornerAccounting
#print axioms RankSeven.UpperCornerAccounting.physicalSignedGain
#print axioms RankSeven.UpperCornerAccounting.discreteBound
