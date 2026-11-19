import Rank7HighestTripleCounting

namespace RankSeven.HighestAnchorCoefficient

open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
open HeavyPauliGroup StabilizerCosetTransform CharacterFourOrbits AnchorSteiner
open HighestCharacterChart HighestChartAction HighestChartMinorTrace HighestChartSelection HighestChartOrbitPrice
open HighestFivePairMinors (coefficient)
variable {R I : Type} [CommRing R]
attribute [local instance] Ring.intCast
local notation "C" => ComplexScalar R

def det3 (v f g : I→C) (i j k : I) :=
  v i*(f j*g k-f k*g j)-v j*(f i*g k-f k*g i)+v k*(f i*g j-f j*g i)

theorem laplace {K : Type} (U : I→K→C) (i j k l : I) (a b c d : K) :
    let s:=fun t=>U t a
    let v:=fun t=>U t b
    let f:=fun t=>U t c
    let g:=fun t=>U t d
    blade U ((i,j),(k,l)) ((a,b),(c,d))=
      s i*det3 v f g j k l-s j*det3 v f g i k l+s k*det3 v f g i j l-s l*det3 v f g i j k := by
  let r:Four I:=((i,j),(k,l))
  let x:Four K:=((a,b),(c,d))
  let sign (p:Permutation):C:=Int.cast (FourCopySectors.coefficient .antisymmetric p)
  let term (p:Permutation):=sign p*tensorFour U (reorder r p) x
  change sumOver permutations term=_
  have pp : permutations=[((0,1),(2,3)),((0,1),(3,2)),((0,2),(1,3)),((0,2),(3,1)),((0,3),(1,2)),((0,3),(2,1)),((1,0),(2,3)),((1,0),(3,2)),((1,2),(0,3)),((1,2),(3,0)),((1,3),(0,2)),((1,3),(2,0)),((2,0),(1,3)),((2,0),(3,1)),((2,1),(0,3)),((2,1),(3,0)),((2,3),(0,1)),((2,3),(1,0)),((3,0),(1,2)),((3,0),(2,1)),((3,1),(0,2)),((3,1),(2,0)),((3,2),(0,1)),((3,2),(1,0))]:=by decide
  rw [pp]
  unfold sumOver; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  let t (i₁ i₂ i₃ i₄ : I):=U i₁ a*U i₂ b*U i₃ c*U i₄ d
  have spell (p:Permutation) : term p=sign p*t (position r p.1.1) (position r p.1.2) (position r p.2.1) (position r p.2.2):=by
    unfold term tensorFour tensor reorder x t; grind only
  simp only [spell]
  have signEq (p : Permutation) : sign p=if oddPermutation p then -1 else 1:=by
    unfold sign FourCopySectors.coefficient; cases oddPermutation p <;> simp <;> grind
  simp only [signEq]
  change (1)*t i j k l+((-1)*t i j l k+((-1)*t i k j l+((1)*t i k l j+((1)*t i l j k+((-1)*t i l k j+((-1)*t j i k l+((1)*t j i l k+((1)*t j k i l+((-1)*t j k l i+((-1)*t j l i k+((1)*t j l k i+((1)*t k i j l+((-1)*t k i l j+((-1)*t k j i l+((1)*t k j l i+((1)*t k l i j+((-1)*t k l j i+((-1)*t l i j k+((1)*t l i k j+((1)*t l j i k+((-1)*t l j k i+((-1)*t l k i j+((1)*t l k j i+(0))))))))))))))))))))))))=_
  unfold t det3; grind only

private theorem phaseMod (z : C) : normSq (-z)=normSq z:=by simp only [normSq,re_neg,im_neg]; grind only
private theorem zeroMod : normSq (0:C)=0:=by simp only [normSq,re_zero,im_zero]; grind only

def expand4 (a b c d u v x y : C) := a*u-b*v+c*x-d*y

/-- Expansion in the one-coordinate anchor column leaves one minor when the
anchor occurs once. Repeated anchor rows make the original determinant zero. -/
private theorem swap1 (v f g : I→C) (i j k : I) : det3 v f g i j k= -det3 v f g j i k:=by unfold det3; grind only
private theorem swap2 (v f g : I→C) (i j k : I) : det3 v f g i j k= -det3 v f g i k j:=by unfold det3; grind only
private theorem cyc (v f g : I→C) (i j k : I) : det3 v f g i j k=det3 v f g k i j:=by unfold det3; grind only

theorem deltaBound [DecidableEq I] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (a : I) (z : C) (v f g : I→C) (i j k l : I) :
    let δ (t : I):=if t=a then z else 0
    let d:=det3 v f g
    normSq (expand4 (δ i) (δ j) (δ k) (δ l) (d j k l) (d i k l) (d i j l) (d i j k))≤
      normSq z*((if i=a then normSq (d j k l) else 0)+(if j=a then normSq (d i k l) else 0)+
        (if k=a then normSq (d i j l) else 0)+(if l=a then normSq (d i j k) else 0)) := by
  let d:=det3 v f g
  have d1 (i j : I) : d i i j=0:=by unfold d det3; grind only
  have d2 (i j : I) : d i j i=0:=by unfold d det3; grind only
  have d3 (i j : I) : d j i i=0:=by unfold d det3; grind only
  dsimp only
  change normSq (expand4 _ _ _ _ (d j k l) (d i k l) (d i j l) (d i j k))≤normSq z*
      ((if i=a then normSq (d j k l) else 0)+(if j=a then normSq (d i k l) else 0)+
       (if k=a then normSq (d i j l) else 0)+(if l=a then normSq (d i j k) else 0))
  have rhs : 0≤normSq z*((if i=a then normSq (d j k l) else 0)+(if j=a then normSq (d i k l) else 0)+
       (if k=a then normSq (d i j l) else 0)+(if l=a then normSq (d i j k) else 0)) := by
    apply OrderedRing.mul_nonneg (normSq_nonnegative _)
    have each (q : Prop) [Decidable q] (u : C) : 0≤if q then normSq u else 0:=by split; exact normSq_nonnegative _; exact Std.le_refl _
    have e0:=each (i=a) (d j k l); have e1:=each (j=a) (d i k l); have e2:=each (k=a) (d i j l); have e3:=each (l=a) (d i j k)
    grind only
  by_cases h₀:i=a <;> by_cases h₁:j=a <;> by_cases h₂:k=a <;> by_cases h₃:l=a <;>
    subst_vars <;> simp_all [expand4] <;>
    simp only [normSq,re_sub,im_sub,re_add,im_add,re_zero,im_zero,re_mul,im_mul] at rhs ⊢ <;> first | grind only | grind only [swap1,swap2,cyc,re_neg,im_neg]

def punctures [DecidableEq I] (a : I) (f : I→I→I→R) (r : Four I) :=
  (if r.1.1=a then f r.1.2 r.2.1 r.2.2 else 0)+(if r.1.2=a then f r.1.1 r.2.1 r.2.2 else 0)+
  (if r.2.1=a then f r.1.1 r.1.2 r.2.2 else 0)+(if r.2.2=a then f r.1.1 r.1.2 r.2.1 else 0)

private theorem moveFirst {n} {G : MaximalFamily n} {T : Transversal G} (a b c d : Line T) :
    plane a b c d ↔ plane b a c d := by unfold plane; rw [PauliEdgeBlocks.wordAddComm a.val b.val]

theorem maskedHoles {n} {G : MaximalFamily n} {T : Transversal G} [DecidableEq (Line T)] (a : Line T)
    (q : Line T→Line T→Line T→R) (u v f g : Line T) :
    @ite R (affine ((u,v),(f,g))) (Classical.propDecidable _) (punctures a q ((u,v),(f,g))) 0=
      punctures a (fun b c d=>if hit a b c d then q b c d else 0) ((u,v),(f,g)) := by
  classical
  let on:=affine ((u,v),(f,g))
  have e0 : u=a → (on ↔ plane a v f g):=by intro e; subst u; rfl
  have e1 : v=a → (on ↔ plane a u f g):=by intro e; subst v; exact moveFirst .. 
  have e2 : f=a → (on ↔ plane a u v g):=by intro e; subst f; exact (swapAnchorTriple ..).trans (moveFirst ..)
  have e3 : g=a → (on ↔ plane a u v f):=by intro e; subst g; exact (swapTail ..).trans ((swapAnchorTriple ..).trans (moveFirst ..))
  have gate (b c d t : Line T) (eq : t=a→(on ↔ plane a b c d)) :
      (if on then (if t=a then q b c d else 0) else 0)=(if t=a then (if hit a b c d then q b c d else 0) else 0) := by
    by_cases ht:t=a
    · have b':(hit a b c d=true) ↔ on:=
        (Iff.of_eq (@decide_eq_true_eq (plane a b c d) (Classical.propDecidable _))).trans (eq ht).symm
      by_cases h:on <;> simp [ht,b',h]
    · simp [ht]
  have add (x y z w : R) : (if on then x+y+z+w else 0)=
      (if on then x else 0)+(if on then y else 0)+(if on then z else 0)+(if on then w else 0):=by
    by_cases h:on <;> simp [h] <;> grind only
  change (if on then _ else 0)=_
  unfold punctures; rw [add,gate _ _ _ _ e0,gate _ _ _ _ e1,gate _ _ _ _ e2,gate _ _ _ _ e3]
  
open StabilizerCharacterBasis (block Lift)
open HighestAnchorPauliTrace (headFrame)
open UpperPairCap (walls)
open FrameExteriorSector (sourceTuple)
open UpperPairLoss (rest)
open HighestTripleCounting (price)
open AnchorSteinerTest (mass)

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem markedRow {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    [DecidableEq (Line T)] (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (v : Basis n→C)
    (w : ExteriorCuts.Wedge7) (hw : w∈walls) (r : Four (Line T)) :
    let φ:=analysis half F T c i
    let s t:=block half F c t i
    let h:=(s i).re
    let a:=anchor T c
    let D t:=blade (columns half F T c i (headFrame A s v)) t (sourceTuple w)
    normSq (masked D r)≤h^2*punctures a (price a (φ v) (fun j=>φ (tail A j)) (wallPair w)) r := by
  classical
  let φ:=analysis half F T c i
  let s t:=block half F c t i
  let h:=(s i).re
  let a:=anchor T c
  let H:=headFrame A s v
  let U:=columns half F T c i H
  let p:=wallPair w
  let y:=φ v
  let Y j:=φ (tail A j)
  let f:=Y p.1
  let g:=Y p.2
  let z:=φ s a
  let D t:=blade U t (sourceTuple w)
  let q (j k l : Line T):=normSq (det3 y f g j k l)
  have wall : ∀w∈walls,w.i=0 ∧ w.j=1 ∧ rest (wallPair w).1=w.k ∧ rest (wallPair w).2=w.m:=by decide
  obtain ⟨w0,w1,w2,w3⟩:=wall w hw
  have hn : normSq z=h^2:=anchorNorm half h2 F T c i
  have non (j : Fin 5) : rest j≠0 ∧ rest j≠1:=by revert j; decide
  have first (t : Line T) : U t w.i=(if t=a then z else 0):=by
    rw [w0]; change φ s t=_
    by_cases eq:t=a
    · subst t; simp [z]
    · rw [ite_eq_right eq]; exact anchorOff half h2 F T c i t eq
  have second (t : Line T) : U t w.j=y t:=by rw [w1]; rfl
  have third (t : Line T) : U t w.k=f t:=by
    rw [←w2]; unfold U columns H headFrame; simp only [(non _).1,(non _).2,ite_false]; rfl
  have fourth (t : Line T) : U t w.m=g t:=by
    rw [←w3]; unfold U columns H headFrame; simp only [(non _).1,(non _).2,ite_false]; rfl
  obtain ⟨⟨p₀,p₁⟩,p₂,p₃⟩:=r
  let r:Four (Line T):=((p₀,p₁),(p₂,p₃))
  have dec : D r=expand4 (if p₀=a then z else 0) (if p₁=a then z else 0) (if p₂=a then z else 0) (if p₃=a then z else 0)
      (det3 y f g p₁ p₂ p₃) (det3 y f g p₀ p₂ p₃) (det3 y f g p₀ p₁ p₃) (det3 y f g p₀ p₁ p₂) := by
    have m:=laplace U p₀ p₁ p₂ p₃ w.i w.j w.k w.m
    simp only [first,second,third,fourth] at m; exact m
  have bound : normSq (D r)≤h^2*punctures a q r := by
    rw [dec,←hn]; exact deltaBound a z y f g p₀ p₁ p₂ p₃
  have qeq (x t u : Line T) : det3 y f g x t u=coefficient y Y (x,t,u) p:=by unfold det3 coefficient f g; grind only
  have m : (if affine r then punctures a q r else 0)=punctures a (price a y Y p) r:=by
    have eq:=maskedHoles a q p₀ p₁ p₂ p₃
    refine eq.trans ?_
    apply congrArg (fun Q=>punctures a Q r)
    funext x t u; unfold price q; rw [qeq]
  change normSq (masked D r)≤h^2*punctures a (price a y Y p) r
  rw [←m]
  by_cases aff:affine r
  · simp only [aff,masked,ite_true]; exact bound
  · simp only [aff,masked,ite_false,zeroMod,Semiring.mul_zero]; exact Std.le_refl _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem punctureSum [DecidableEq I] (L : List I) (nd : L.Nodup) (a : I) (mem : a∈L) (f : I→I→I→R) :
    sumOver (fourIndices L) (punctures a f)=4*sumOver L (fun i=>sumOver L (fun j=>sumOver L (f i j))) := by
  have four (Q : Four I→R) : sumOver (fourIndices L) Q=
      sumOver L (fun i=>sumOver L (fun j=>sumOver L (fun k=>sumOver L (fun l=>Q ((i,j),(k,l)))))) := by
    unfold fourIndices; simp only [HighestTailTransfer.sumPairs]
  have zz (xs : List I) : sumOver xs (fun _=>(0:R))=0:=by
    induction xs with | nil => rfl | cons j xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
  have zero:=zz L
  have gate (p : Prop) [Decidable p] (u : I→R) : sumOver L (fun b=>if p then u b else 0)=(if p then sumOver L u else 0):=by
    by_cases h:p <;> simp only [h,ite_true,ite_false,zero]
  have sel (z : R) : sumOver L (fun b=>if b=a then z else 0)=z:=by
    have e (b:I) : (if b=a then z else 0)=(if a=b then z else 0):=by
      by_cases h:b=a; subst b; rfl; simp only [h,Ne.symm h,ite_false]
    rw [sumOverCongr L e]; exact ExteriorPauliBase.sumOnIndex L a (fun _=>z) nd mem
  rw [four]; simp only [punctures,sumOverAdd,gate,sel]; grind only

theorem maskMass {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    [DecidableEq (Line T)] (c : Word n) (i : Basis n) (A : Basis n→Fin 7→C) (v : Basis n→C)
    (w : ExteriorCuts.Wedge7) (hw : w∈walls) :
    let φ:=analysis half F T c i
    let h:=(block half F c i i).re
    let H:=headFrame A (fun t=>block half F c t i) v
    let D r:=blade (columns half F T c i H) r (sourceTuple w)
    mass (fourIndices T.reps.attach) (masked D) ≤ 24*h^2*
      sumOver (AnchorVacantScore.sites (anchor T c) T.reps.attach)
        (fun t=>normSq (coefficient (φ v) (fun j=>φ (tail A j)) t (wallPair w))) := by
  classical
  let a:=anchor T c
  let φ:=analysis half F T c i
  let h:=(block half F c i i).re
  let H:=headFrame A (fun t=>block half F c t i) v
  let D r:=blade (columns half F T c i H) r (sourceTuple w)
  let y:=φ v
  let Y j:=φ (tail A j)
  let p:=wallPair w
  let q:=price a y Y p
  let B:=fourIndices T.reps.attach
  let f r:=normSq (masked D r)
  have row (r) : 0≤h^2*punctures a q r-f r:=by have eq:=markedRow half h2 F T c i A v w hw r; change f r≤h^2*punctures a q r at eq; grind only
  have eq:=Compression.sumOverNonnegative B _ (fun r _=>row r)
  rw [Compression.sumOverSub,←sumOverMulLeft] at eq
  have loc : sumOver B (punctures a q)=4*sumOver T.reps.attach (fun i=>sumOver T.reps.attach (fun j=>sumOver T.reps.attach (q i j))) :=
    punctureSum _ (linesNodup T) a (List.mem_attach _ a) q
  rw [loc,HighestTripleCounting.anchoredTriples a T.reps.attach y Y p] at eq
  change sumOver B f≤24*h^2*sumOver _ (fun t=>normSq (coefficient y Y t p)); grind only

theorem physicalWallDomination {n} {G : MaximalFamily n} (half : R) (h2 : 2*half=1) (F : Lift G) (T : Transversal G)
    (c : Word n) (i : Basis n) (pos : 0<(block half F c i i).re) (A : Basis n→Fin 7→C) (v : Basis n→C) :
    wallDomination half F T (anchor T c) c i A v := by
  classical
  intro w hw
  let h:=(block half F c i i).re
  let H:=headFrame A (fun t=>block half F c t i) v
  let D r:=blade (columns half F T c i H) r (sourceTuple w)
  let m:=mass (fourIndices T.reps.attach) (masked D)
  let W:=sumOver (words n) (fun p=>(HighestAnchorPauliTrace.wordExpectation H p w).re)
  let φ:=analysis half F T c i
  let B:=sumOver (AnchorVacantScore.sites (anchor T c) T.reps.attach)
      (fun t=>normSq (coefficient (φ v) (fun j=>φ (tail A j)) t (wallPair w)))
  have physical:=physicalOrbitPrice half h2 F T c i A v w hw
  have massBound:=maskMass half h2 F T c i A v w hw
  change 24*h^4*half^n*W≤4*m at physical
  change m≤24*h^2*B at massBound
  change h^2*half^n*W≤4*B
  have hh : 0<h*h:=OrderedRing.mul_pos pos pos
  have pp : 0<24*(h*h):=by grind only
  apply Classical.byContradiction; intro neg
  have bad : 4*B<h^2*half^n*W:=by grind only
  have fail:=OrderedRing.mul_lt_mul_of_pos_left bad pp; grind only

section Field

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K] [OrderedRing K]

/-- The highest probe geometry payment on every original complex orthonormal
seven-frame, with its exact factor five and no stabilizer-line or orbit premise. -/
theorem physicalHighest (half : K) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar K)
    (mu : Fin 7→K) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    2*UpperFrameTrace.highExcess (PackingPolynomial.physicalWeights half h2 k A)≤5*(WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne := by
  apply physicalHighestFromWall half h2 k A mu orth
  intro G F c i pos v _
  obtain ⟨T⟩:=transversalExists G
  exact ⟨T,anchor T c,physicalWallDomination half h2 F T c i pos A v⟩

end Field

end RankSeven.HighestAnchorCoefficient

#print axioms RankSeven.HighestAnchorCoefficient.laplace
#print axioms RankSeven.HighestAnchorCoefficient.deltaBound
#print axioms RankSeven.HighestAnchorCoefficient.markedRow
#print axioms RankSeven.HighestAnchorCoefficient.maskMass
#print axioms RankSeven.HighestAnchorCoefficient.physicalWallDomination
#print axioms RankSeven.HighestAnchorCoefficient.physicalHighest

