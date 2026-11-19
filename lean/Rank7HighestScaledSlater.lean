import Rank7HighestFivePairMinors

namespace RankSeven.HighestScaledSlater

open Lean.Grind Pauli ComplexScalar AnchorExteriorCreation AnchorMixedCAR AnchorTripleEnergy
open HighestTailReplacement HighestSlaterCoordinates HighestFivePairMinors
variable {R I J : Type} [CommRing R]
local notation "C" => ComplexScalar R

def weighted (h : R) : (d : Nat)→(Basis d→C)→R
  | 0,f => normSq (f ())
  | d+1,f => weighted h d (fun z=>f (false,z))+h*weighted h d (fun z=>f (true,z))

private theorem gramAdd {d : Nat} (f g h t : Basis d→C) :
    gram (fun z=>f z+g z) (fun z=>h z+t z)=gram f h+gram f t+gram g h+gram g t := by
  unfold gram; rw [←sumOverAdd,←sumOverAdd,←sumOverAdd]; apply sumOverCongr; intro z; rw [star_add]; grind only

private theorem gramZero {d : Nat} (f : Basis d→C) : gram f (fun _=>0)=0 ∧ gram (fun _=>0) f=0 := by
  have h : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
  unfold gram; simp only [h,Semiring.zero_mul,Semiring.mul_zero,and_self]
  generalize qubitIndices d=B
  induction B with
  | nil => rfl
  | cons i B ih => change 0+sumOver B _=0; rw [ih]; grind only

private theorem gramScale {d : Nat} (h : C) (f g : Basis d→C) :
    gram f (fun z=>h*g z)=h*gram f g := by
  unfold gram; rw [sumOverMulLeft]; apply sumOverCongr; intro z; grind only

theorem commonNormEnergy (L : List I) (Y : J→I→C) (js : List J) (nd : js.Nodup) (h : R)
    (norm : ∀j∈js, dot L (Y j) (Y j)=ofReal h)
    (apart : ∀i∈js,∀j∈js,i≠j → dot L (Y i) (Y j)=0)
    (f : Basis js.length→C) : energy (synth L Y js f)=weighted h js.length f := by
  induction js with
  | nil =>
    have g:=synthGram L Y [] List.nodup_nil (by simp) (by simp) f f
    have gg : gram f f=star (f ())*f () := by change _+0=_; grind only
    rw [gg] at g
    have e:=congrArg ComplexScalar.re g
    rw [reGram,re_star_mul_self] at e; exact e
  | cons i js ih =>
    obtain ⟨absent,nd'⟩:=List.nodup_cons.mp nd
    have tail:=ih nd' (fun j hj=>norm j (List.mem_cons_of_mem i hj))
        (fun j hj k hk=>apart j (List.mem_cons_of_mem i hj) k (List.mem_cons_of_mem i hk))
    have away : ∀j∈js,coordinate L Y (Y i) j=0 := by
      intro j hj; unfold coordinate
      rw [apart i (by simp) j (List.mem_cons_of_mem i hj) (fun eq=>absent (eq ▸ hj))]
      apply ComplexScalar.ext <;> simp <;> grind only
    have vacant (g : Basis js.length→C) : lower (Y i) L (synth L Y js g)=fun _=>0 := by
      rw [lowerSynth,lowerOff _ _ away,synthZero]
    let f0:=synth L Y js (fun w=>f (false,w))
    let f1:=synth L Y js (fun w=>f (true,w))
    have e1:gram (raise (Y i) L f1) f0=0:=by rw [(adjoint ..).1,vacant,(gramZero _).1]
    have e2:gram f0 (raise (Y i) L f1)=0:=by rw [←(adjoint ..).2,vacant,(gramZero _).2]
    have p:=push (Y i) (Y i) L f1; rw [vacant,raiseZero,norm i (by simp)] at p
    have p' : lower (Y i) L (raise (Y i) L f1)=fun z=>ofReal h*f1 z := p.trans (by funext z; grind only)
    have e3 : gram (raise (Y i) L f1) (raise (Y i) L f1)=ofReal h*gram f1 f1:=by rw [(adjoint ..).1,p',gramScale]
    have g := gramAdd f0 (raise (Y i) L f1) f0 (raise (Y i) L f1)
    rw [e1,e2,e3] at g
    have eq:=congrArg ComplexScalar.re g
    simp only [reGram,re_add,re_zero,re_mul,re_ofReal,im_ofReal] at eq
    have x:=tail (fun w=>f (false,w)); have z:=tail (fun w=>f (true,w))
    change energy f0=_ at x; change energy f1=_ at z
    change energy (fun z=>f0 z+raise (Y i) L f1 z)=_
    change energy (fun z=>f0 z+raise (Y i) L f1 z)=energy f0+0+0+(h*energy f1-0*_) at eq
    rw [eq,x,z]; change _= _+h*_; grind only

private theorem zeroNorm : normSq (0:C)=0:=by simp only [normSq,re_zero,im_zero]; grind only
private theorem negNorm (z : C) : normSq (-z)=normSq z:=by simp only [normSq,re_neg,im_neg]; grind only

private theorem weightedZero (h : R) (d : Nat) : weighted h d (fun _=>0)=0 := by
  induction d with
  | zero => exact zeroNorm
  | succ d ih => change weighted h d (fun _=>0)+h*weighted h d (fun _=>0)=0; rw [ih]; grind only

theorem weightedFilled (h : R) (d : Nat) : weighted h d (filled d)=h^d := by
  induction d with
  | zero =>
    change normSq (1:C)=h^0; simp only [normSq,re_one,im_one,Semiring.pow_zero]; grind only
  | succ d ih => change weighted h d (fun _=>0)+h*weighted h d (filled d)=h^(d+1); rw [weightedZero,ih,Semiring.pow_succ]; grind only

theorem weightedHoles (h : R) (m : Fin 5×Fin 5→C) :
    weighted h 5 (holeTable m)=h^3*sumOver pairs (fun p=>normSq (m p)) := by
  simp only [weighted,holeTable,zeroNorm,negNorm,pairs,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  grind only

theorem scaledSlater (L : List I) (Y : Fin 5→I→C) (h : R)
    (norm : ∀j, dot L (Y j) (Y j)=ofReal h)
    (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0) :
    energy (synth L Y five (filled five.length))=h^5 :=
  (commonNormEnergy L Y five (by decide) h (fun j _=>norm j) (fun i _ j _=>apart i j) _).trans (weightedFilled h 5)

theorem scaledPairMinors (L : List I) (y a b c : I→C) (Y : Fin 5→I→C) (h : R)
    (norm : ∀j, dot L (Y j) (Y j)=ofReal h)
    (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0) :
    energy (contracted L y a b c (synth L Y five (filled five.length)))=
      h^3*sumOver pairs (fun p=>normSq (minor L y a b c Y p)) := by
  rw [contractedSynth]
  exact (commonNormEnergy L Y five (by decide) h (fun j _=>norm j) (fun i _ j _=>apart i j) _).trans
    ((congrArg (weighted h 5) (pullCoordinates L y a b c Y)).trans (weightedHoles h _))

open HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits AnchorOccupation
open AnchorVacantScore (sites)

theorem siteMinor [DecidableEq I] (L : List I) (nd : L.Nodup) (y : I→C) (Y : Fin 5→I→C)
    (t : I×I×I) (ht : t∈AnchorScoreEnumeration.tripleList L) (p : Fin 5×Fin 5) :
    minor L y (mode t.1) (mode t.2.1) (mode t.2.2) Y p=coefficient y Y t p := by
  obtain ⟨hi,hj,hk⟩:=tripleMembers L t ht
  unfold minor coefficient
  simp only [dotMode L nd _ hi,dotMode L nd _ hj,dotMode L nd _ hk]

private theorem sumAt {K : Type} (xs : List K) {f g : K→R} (eq : ∀j∈xs,f j=g j) :
    sumOver xs f=sumOver xs g:=congrArg List.sum (List.map_congr_left eq)

theorem siteEnergy [DecidableEq I] (L : List I) (nd : L.Nodup) (y : I→C) (Y : Fin 5→I→C) (h : R)
    (norm : ∀j,dot L (Y j) (Y j)=ofReal h) (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0)
    (t : I×I×I) (ht : t∈AnchorScoreEnumeration.tripleList L) :
    energy (contracted L y (mode t.1) (mode t.2.1) (mode t.2.2) (synth L Y five (filled five.length)))=
      h^3*sumOver pairs (fun p=>normSq (coefficient y Y t p)) :=
  (scaledPairMinors L y _ _ _ Y h norm apart).trans (congrArg (fun x=>h^3*x)
    (sumOverCongr pairs (fun p=>congrArg normSq (siteMinor L nd y Y t ht p))))

theorem anchoredTrace {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)]
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C) (Y : Fin 5→Line T→C) (h : R)
    (norm : ∀j,dot L (Y j) (Y j)=ofReal h) (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0) :
    sumOver (sites a L) (fun t=>energy (contracted L y (mode t.1) (mode t.2.1) (mode t.2.2) (synth L Y five (filled five.length))))=
    h^3*sumOver (sites a L) (fun t=>sumOver pairs (fun p=>normSq (coefficient y Y t p))) := by
  rw [sumOverMulLeft (sites a L) _ (h^3)]
  exact sumAt _ (fun t ht=>siteEnergy L nd y Y h norm apart t (List.mem_filter.mp ht).1)

theorem anchoredScaledFive {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)]
    [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (a : Line T) (L : List (Line T)) (nd : L.Nodup) (y : Line T→C) (Y : Fin 5→Line T→C) (h : R)
    (pos : 0<h) (norm : ∀j,dot L (Y j) (Y j)=ofReal h) (apart : ∀i j,i≠j → dot L (Y i) (Y j)=0) :
    sumOver (sites a L) (fun t=>sumOver pairs (fun p=>normSq (coefficient y Y t p))) ≤ 2*h^2*modeMass L y := by
  let f:=synth L Y five (filled five.length)
  have cp : cap L 5 f := synthCap L Y five _
  have score:=AnchorAllFock.anchoredPairContractions a L nd y f cp
  let val:=sumOver (sites a L) (fun t=>sumOver pairs (fun p=>normSq (coefficient y Y t p)))
  let cost:=sumOver (sites a L) (fun t=>energy (contracted L y (mode t.1) (mode t.2.1) (mode t.2.2) f))
  change cost≤2*modeMass L y*energy f at score
  have ee : energy f=h^5:=scaledSlater L Y h norm apart
  have tr : cost=h^3*val:=anchoredTrace a L nd y Y h norm apart
  have bound : h^3*val ≤ 2*modeMass L y*h^5:=tr ▸ (ee ▸ score)
  have p2:=OrderedRing.mul_pos pos pos; have p3:=OrderedRing.mul_pos p2 pos
  have p : 0<h^3:=by grind only
  change val≤2*h^2*modeMass L y
  apply Classical.byContradiction; intro neg
  have bad : 2*h^2*modeMass L y<val:=by grind only
  have falseIneq:=OrderedRing.mul_lt_mul_of_pos_left bad p
  grind only

end RankSeven.HighestScaledSlater

#print axioms RankSeven.HighestScaledSlater.commonNormEnergy
#print axioms RankSeven.HighestScaledSlater.scaledSlater
#print axioms RankSeven.HighestScaledSlater.scaledPairMinors
#print axioms RankSeven.HighestScaledSlater.anchoredTrace
#print axioms RankSeven.HighestScaledSlater.anchoredScaledFive

