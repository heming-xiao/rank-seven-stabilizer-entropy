import Rank7HighestAnchorSelection

namespace RankSeven.HighestAnchorCommutation

open Lean.Grind Pauli ComplexScalar ThreeLegFourier HeadPauliFourier PauliEdgeBlocks
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalPairedReduction (dagger)
open JointProbePayment (pairWeight pairAmplitude)
open HighestAnchorSelection WeightedProbeShift
open StabilizerCharacterBasis (act)
open PhysicalAntiQuartic (cocycle axisCocycle)
open MixedDefect (oddWords)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- If two unit vectors each have a large overlap with a third, the three-by-three
Gram determinant excludes a weak overlap between them. -/
theorem overlapHalf (H : Fin 3→Fin 3→ComplexScalar R) (gram : SlaterUnionBound.Gram H)
    (herm : dagger H=H) (diag : ∀i,H i i=1) (P Q T : R)
    (first : normSq (H 0 1)=P) (second : normSq (H 1 2)=Q) (side : normSq (H 0 2)=T)
    (pHead : 1≤2*P) (qHead : 1≤2*Q) (close : 4*P*(1-P)<(2*Q-1)^2) : 1<2*T := by
  let a := H 0 1; let b := H 1 2; let c := H 0 2
  let x := a*b*star c
  have symm (i j : Fin 3) : star (H i j)=H j i := congrFun (congrFun herm j) i
  have det := determinantGramNonnegative gram
  rw [determinantThree] at det
  have id : detThree H=1-ofReal P-ofReal Q-ofReal T+x+star x := by
    unfold detThree
    rw [diag,diag,diag,←symm 1 2,←symm 0 1,←symm 0 2]
    change 1*(1*1-b*star b)-a*(star a*1-b*star c)+c*(star a*star b-1*star c)=_
    rw [←first,←second,←side]
    change _=1-ofReal (normSq a)-ofReal (normSq b)-ofReal (normSq c)+x+star x
    unfold x; simp only [star_mul,star_star,←star_mul_self]; grind only
  rw [id] at det; simp only [re_add,re_sub,re_ofReal,re_star,re_one] at det
  have norm : normSq x=P*Q*T := by
    change normSq (a*b*star c)=_; rw [normSq_mul,normSq_mul,normSq_star]; change normSq (H 0 1)*normSq (H 1 2)*normSq (H 0 2)=_; rw [first,second,side]
  have sq := squareNonnegative x.im
  change x.re^2+x.im^2=P*Q*T at norm
  have t0 : 0≤T := side ▸ normSq_nonnegative _
  have pos : 0≤P+Q+T-1 := by grind only
  have up : P+Q+T-1≤2*x.re := by grind only
  have v := OrderedRing.mul_nonneg (show 0≤2*x.re-(P+Q+T-1) by grind only) (show 0≤2*x.re+(P+Q+T-1) by grind only)
  have dd : (P+Q+T-1)^2≤4*P*Q*T := by grind only
  by_cases done : 1<2*T
  · exact done
  · have t : 0≤1-2*T := by grind only
    have h := OrderedRing.mul_nonneg (show 0≤2*P-1 by grind only) (show 0≤2*Q-1 by grind only)
    have eq := OrderedRing.mul_nonneg t (show 0≤2*((2*P-1)*(2*Q-1))+(1-2*T) by grind only)
    grind only

private def ip {α : Type} (xs : List α) (x y : α→ComplexScalar R) := sumOver xs (fun a => star (x a)*y a)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem ipStar {α} (xs : List α) (x y : α→ComplexScalar R) : star (ip xs x y)=ip xs y x := by
  unfold ip; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro a; simp only [star_mul,star_star]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem cocycleNorm {n : Nat} (p q : Word n) : normSq (cocycle (imaginaryUnit (R:=R)) p q)=1 := by
  induction p with
  | empty => cases q; change normSq (1:ComplexScalar R)=1; unfold normSq; rw [re_one,im_one]; grind only
  | cons a p ih =>
    cases q with
    | cons b q =>
      rw [cocycle,normSq_mul,ih]; cases a <;> cases b <;>
        simp only [axisCocycle,normSq,imaginaryUnit,re_one,im_one,re_neg,im_neg] <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem actAdjoint {n : Nat} (p : Word n) (x y : Basis n → ComplexScalar R) :
    ip (qubitIndices n) (act p x) y=ip (qubitIndices n) x (act p y) := by
  let xs := qubitIndices n
  let P := wordEntry (imaginaryUnit (R:=R)) p
  change sumOver xs (fun i => star (sumOver xs (fun j => P i j*x j))*y i)=sumOver xs (fun j => star (x j)*sumOver xs (fun i => P j i*y i))
  simp only [ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft,star_mul]
  rw [sumOverSwap]; apply sumOverCongr; intro j; apply sumOverCongr; intro i
  change star (wordEntry imaginaryUnit p i j)*star (x j)*y i=star (x j)*(wordEntry imaginaryUnit p j i*y i)
  rw [ComplexPauliMoment.wordHermitian]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem legStar {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) (t : Basis n) :
    UpperPairPfaffian.pauliLeg A p t 0=star (act p (fun i => A i 0) t) := by
  unfold UpperPairPfaffian.pauliLeg act; rw [ComplexExterior.starSumOver]
  apply sumOverCongr; intro i; rw [star_mul,ComplexPauliMoment.wordHermitian]; grind only

/-- Two heavy odd probes have a product label heavy in the single physical head column. -/
theorem heavyDifference {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (u v : Word n)
    (pu : 1≤2*pairWeight A u 0 1) (pv : 1≤2*pairWeight A v 0 1)
    (close : 4*pairWeight A u 0 1*(1-pairWeight A u 0 1)<(2*pairWeight A v 0 1-1)^2) :
    1<2*(head (localH A (wordAdd u v)))^2 := by
  let xs := qubitIndices n
  let x a := A a 0
  let y a := A a 1
  let z a := star (y a)
  let a (v : Word n) := act v x
  let cols (j : Fin 3) := if j=0 then a u else if j=1 then z else a v
  let B i j := cols j i
  let G := matMul xs (dagger B) B
  have entry (i j : Fin 3) : G i j=ip xs (cols i) (cols j) := rfl
  have gram : SlaterUnionBound.Gram G := ⟨Basis n,xs,B,rfl⟩
  have herm : dagger G=G := by funext i j; change star (ip xs (cols j) (cols i))=_; exact ipStar _ _ _
  have xn : ip xs x x=1 := by change sumOver _ (fun t => star (A t 0)*A t 0)=1; rw [orth]; rfl
  have yn : ip xs y y=1 := by change sumOver _ (fun t => star (A t 1)*A t 1)=1; rw [orth]; rfl
  have an (p : Word n) : ip xs (a p) (a p)=1 := by
    change ip xs (act p x) (act p x)=1; rw [actAdjoint]
    have sq : act p (act p x)=x := funext (StabilizerCharacterBasis.actSquare p x)
    rw [sq,xn]
  have zn : ip xs z z=1 := by
    rw [←yn]; unfold ip; apply sumOverCongr; intro i; unfold z; rw [star_star]; grind only
  have diag (i : Fin 3) : G i i=1 := by
    have all : i=0∨i=1∨i=2 := by omega
    rw [entry]; rcases all with h|h|h <;> subst i
    · exact an u
    · exact zn
    · exact an v
  have pairEq (p : Word n) : ip xs (a p) z=UpperPairPfaffian.pair A p 0 1 := by
    rw [←UpperPairPfaffian.pairFromLeg]; unfold ip
    apply sumOverCongr; intro t; rw [legStar]; change star (a p t)*star (y t)=star (y t)*star (a p t); grind only
  have first : normSq (G 0 1)=pairWeight A u 0 1 := by
    change normSq (ip xs (a u) z)=_; rw [pairEq]; exact normSq_star _
  have second : normSq (G 1 2)=pairWeight A v 0 1 := by
    change normSq (ip xs z (a v))=_; rw [←ipStar,pairEq,normSq_star]; exact normSq_star _
  let q := wordAdd u v
  let J := localH A q
  have expect : ip xs x (act q x)=J 0 0 := rfl
  have diff : ip xs (a u) (a v)=cocycle imaginaryUnit u v*J 0 0 := by
    change ip xs (act u x) (act v x)=_; rw [actAdjoint,←expect]
    unfold ip; rw [sumOverMulLeft]; apply sumOverCongr; intro i
    rw [StabilizerCharacterBasis.actProduct]; grind only
  have jHerm : dagger J=J := PhysicalOddLeakage.compressionHerm (firstThree A) q
  have im := congrArg ComplexScalar.im (congrFun (congrFun jHerm 0) 0)
  change (star (J 0 0)).im=(J 0 0).im at im; rw [im_star] at im
  have rr : normSq (J 0 0)=(head J)^2 := by
    have zi : (J 0 0).im=0 := by grind only
    unfold normSq head; rw [zi]; grind only
  have side : normSq (G 0 2)=(head J)^2 := by
    change normSq (ip xs (a u) (a v))=_; rw [diff,normSq_mul,cocycleNorm,rr,Semiring.one_mul]
  exact overlapHalf G gram herm diag _ _ _ first second side pu pv close

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]
noncomputable local instance : DecidableRel ((·<·) : F→F→Prop) := fun _ _ => Classical.propDecidable _

/-- More than five eighths of the physical weight lies in one translate of the
maximal commuting Pauli family for the first source vector. -/
theorem physicalHeavyCoset (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    let f (v : Word (k+3)) := pairWeight A v 0 1
    ∃p∈oddWords (k+3),∃t:F, ∃G : HeavyPauliGroup.MaximalFamily (k+3),
      (∀q∈oddWords (k+3), t<f q → wordAdd p q∈G.labels) ∧
      5<8*JointProbeGram.oddAverage half (fun q => if t<f q then f q else 0) := by
  classical
  obtain ⟨p,hp,t,_top,_,pos,strict,slack,mass⟩ := physicalHeavyAnchor half h2 k A mu orth small
  let f (v : Word (k+3)) := pairWeight A v 0 1
  change t<f p at strict
  change 4*f p*(1-f p)<(2*t-1)^2 at slack
  obtain ⟨G,properties⟩ := HeavyPauliGroup.physicalFamily half h2 k A mu orth
  refine ⟨p,hp,t,G,?_,mass⟩
  intro q hq heavy
  change t<f q at heavy
  have grow := OrderedRing.mul_nonneg (show 0≤2*f q-1-(2*t-1) by grind only) (show 0≤2*f q-1+(2*t-1) by grind only)
  have a := heavyDifference A orth p q (show 1≤2*f p by grind only) (show 1≤2*f q by grind only)
    (show 4*f p*(1-f p)<(2*f q-1)^2 by grind only)
  exact properties.1 _ a

end Field

end RankSeven.HighestAnchorCommutation

#print axioms RankSeven.HighestAnchorCommutation.overlapHalf
#print axioms RankSeven.HighestAnchorCommutation.heavyDifference
#print axioms RankSeven.HighestAnchorCommutation.physicalHeavyCoset

