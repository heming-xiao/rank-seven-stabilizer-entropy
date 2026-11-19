import Rank7FiveFaceTest

/-! Reduction of each physical omitted-pair row to the full two-hole
Gram estimate on an orthonormal three-volume. -/
namespace RankSeven.FiveFaceCapacity
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel FiveFaceTest
open PhysicalCutCapacities (Triple triples columnCoef)
open PhysicalTwoHoleOccupancy (gram3 gram2 raise3 lower3 modeGram Alt3)
open PhysicalTwoHoleAdjointTransport (col1 col2 singleCol coord)
variable {R I : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
private theorem minusSum (xs : List I) (f : I → ComplexScalar R) : sumOver xs (fun i => -f i)= -sumOver xs f := by
  have z := sumOverMulLeft xs f (-1); simp only [Ring.neg_mul,Semiring.one_mul] at z; exact z.symm
private theorem gramMinus (L : List I) (E G : I→I→ComplexScalar R) :
    gram2 L E (fun a b => -G a b)= -gram2 L E G := by
  simp only [gram2,PhysicalTwoHoleOccupancy.sum2,Ring.mul_neg,minusSum]
private theorem squareSix (z : ComplexScalar R) : normSq (6*z)=36*normSq z := by
  change normSq (ofReal 6*z)=_; rw [normSq_mul,normSq_ofReal]; grind only
private theorem signSquare (z : ComplexScalar R) : normSq (-z)=normSq z := by simp [normSq]; grind only
private theorem singletonNorm {n} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (i j : Fin 7)
    (empty : ∀a b,lower3 (qubitIndices n) (dual (form A j)) (volume A) a b=0) (p : Word n) :
    normSq (gram3 (qubitIndices n) (singleCol half (dual (form A i)) (dual (form A j)) p) (volume A))=
    36*normSq (columnCoef half A ((3,4),(2,i)) p) := by
  let L := qubitIndices n
  let F := volume A
  have alt : Alt3 F := tripleAlternating _ _ _
  unfold singleCol; rw [PhysicalTwoHoleOccupancy.subtractLeft,
    PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt,PhysicalTwoHoleOccupancy.zeroGramRight L empty]
  rw [show ∀ z : ComplexScalar R,z-3*0=z from fun z => by grind only,←gramSwap3,normSq_star]
  change normSq (gram3 L (triple (form A 2) (form A 3) (form A 4)) (col1 half (dual (form A i)) p))=_
  rw [oneExtract,squareSix]

def choosing (j : Fin 3) : Fin 7 := ⟨j.val+2,by omega⟩
def others (j : Fin 3) : Fin 7×Fin 7 := [(3,4),(2,4),(2,3)].getD j.val (0,0)
private theorem threeCases (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by revert j; decide
private theorem doubleNorm {n} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (p : Word n) (j : Fin 3) :
    normSq (gram3 (qubitIndices n) (raise3 (dual (form A (choosing j))) (col2 half (dual (form A 0)) (dual (form A 1)) p)) (volume A))=
    36*normSq (columnCoef half A (others j,(1,0)) p) := by
  let L := qubitIndices n
  let F := volume A
  let E := col2 half (dual (form A 0)) (dual (form A 1)) p
  have alt : Alt3 F := tripleAlternating _ _ _
  have vals (j : Fin 3) : lower3 L (dual (form A (choosing j))) F=(fun a b => if j=1 then -(pair (form A (others j).1) (form A (others j).2) a b) else pair (form A (others j).1) (form A (others j).2) a b) := by
    funext a b; rw [volumeLower _ orth]; rcases threeCases j with rfl|rfl|rfl <;>
      simp only [show choosing 0=2 from rfl,show choosing 1=3 from rfl,show choosing 2=4 from rfl,
        show others 0=(3,4) from rfl,show others 1=(2,4) from rfl,show others 2=(2,3) from rfl,
        Fin.reduceEq,ite_true,ite_false] <;> grind only
  rw [PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt,vals j]
  have value : gram2 L E (pair (form A (others j).1) (form A (others j).2))= star (2*columnCoef half A (others j,(1,0)) p) := by
    rw [←gramSwap2,twoExtract]
  have three : star (2:ComplexScalar R)=2 := star_ofReal (2:R)
  by_cases h : j=1
  · simp only [ite_eq_left h,gramMinus,Ring.mul_neg,signSquare]; rw [value,star_mul,three]
    rw [show ∀z : ComplexScalar R,3*(2*z)=6*z from fun _ => by grind only,squareSix,normSq_star]
  · simp only [ite_eq_right h]; rw [value,star_mul,three]
    rw [show ∀z : ComplexScalar R,3*(2*z)=6*z from fun _ => by grind only,squareSix,normSq_star]

private theorem coordLower {n} (F : Basis n→Basis n→Basis n→ComplexScalar R) (z a b) :
    lower3 (qubitIndices n) (coord z) F a b=F a b z := by
  unfold lower3
  rw [←ExteriorPauliBase.sumOnIndex (qubitIndices n) z (F a b) (HyperplaneIncidence.normalsNodup n) (qubitIndicesComplete _)]
  apply sumOverCongr; intro t; unfold coord; by_cases h : z=t <;> simp [h,Ne.symm,Semiring.one_mul,Semiring.zero_mul] <;> grind
theorem canonicalCombination {n} (h : Basis n→ComplexScalar R) (E : Basis n→Basis n→ComplexScalar R)
    (F : Basis n→Basis n→Basis n→ComplexScalar R) (alt : Alt3 F) :
    gram3 (qubitIndices n) (raise3 h E) F=sumOver (qubitIndices n) (fun z => h z*gram3 (qubitIndices n) (raise3 (coord z) E) F) := by
  let L := qubitIndices n
  simp only [PhysicalTwoHoleOccupancy.creationAdjointLeft _ _ _ _ alt]
  have ce (z : Basis n) : lower3 (qubitIndices n) (coord z) F=(fun a b => F a b z) := by funext a b; exact coordLower F z a b
  simp only [ce]; unfold gram2 PhysicalTwoHoleOccupancy.sum2 lower3; simp only [sumOverMulLeft]
  conv => rhs; rw [sumOverSwap]; arg 2; intro a; rw [sumOverSwap]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro t; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
private theorem freeBessel {n} (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (E : Basis n→Basis n→ComplexScalar R) (F : Basis n→Basis n→Basis n→ComplexScalar R) (alt : Alt3 F) :
    sumOver (List.finRange 3) (fun j => normSq (gram3 (qubitIndices n) (raise3 (dual (form A (choosing j))) E) F))≤
    sumOver (qubitIndices n) (fun z => normSq (gram3 (qubitIndices n) (raise3 (coord z) E) F)) := by
  let L := qubitIndices n
  let B := fun t j => A t (choosing j)
  have sep : ∀(i j : Fin 3),choosing i=choosing j→i=j := by decide
  have or (i j) : sumOver L (fun t => star (B t i)*B t j)=if i=j then 1 else 0 := by
    change sumOver L (fun t => star (A t (choosing i))*A t (choosing j))=_
    rw [orth]; by_cases e : i=j
    · subst j; simp
    · rw [ite_eq_right (fun z => e (sep _ _ z)),ite_eq_right e]
  have bound := PhysicalCutCapacities.frameBessel (List.finRange 3) L (List.nodup_finRange 3) (fun _ => List.mem_finRange _) B or
    (fun z => gram3 L (raise3 (coord z) E) F)
  simp only [canonicalCombination (dual _) E F alt]; exact bound

/-- The joint two-hole Gram bound, in full ordered triple coordinates. -/
def TwoHoleUpper (half : R) (n : Nat) : Prop := ∀(x y : Basis n→ComplexScalar R),
  modeGram (qubitIndices n) x x=1 → modeGram (qubitIndices n) y y=1 → modeGram (qubitIndices n) x y=0 →
  ∀F : Basis n→Basis n→Basis n→ComplexScalar R,Alt3 F →
  (∀a b,lower3 (qubitIndices n) x F a b=0) → (∀a b,lower3 (qubitIndices n) y F a b=0) →
  sumOver (MixedDefect.oddWords n) (fun p => normSq (gram3 (qubitIndices n) (singleCol half x y p) F))+
  sumOver (MixedDefect.oddWords n) (fun p => normSq (gram3 (qubitIndices n) (singleCol half y x p) F))+
  sumOver (qubitIndices n) (fun i => sumOver (MixedDefect.oddWords n) (fun p => normSq
    (gram3 (qubitIndices n) (raise3 (PhysicalC2Projected.free x y i) (col2 half x y p)) F)))≤
  36*half^n*sumOver (triples (qubitIndices n)) (fun u => normSq (F u.1.1 u.1.2 u.2))

def faces : List (Four (Fin 7)) := [((3,4),(2,0)),((3,4),(2,1)),((3,4),(1,0)),((2,4),(1,0)),((2,3),(1,0))]
private theorem sumLe {J} (js : List J) (f g : J→R) (h : ∀i,f i≤g i) : sumOver js f≤sumOver js g := by
  induction js with
  | nil => exact Std.le_refl _
  | cons i js ih => change f i+sumOver js f≤g i+sumOver js g; have hi := h i; grind only
theorem fiveFaceBound {n} (half : R) (joint : TwoHoleUpper half n) (A : Basis n→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    sumOver faces (PhysicalCutCapacities.rowMass half A)≤6*half^n := by
  let L := qubitIndices n
  let P := MixedDefect.oddWords n
  let x := dual (form A 0)
  let y := dual (form A 1)
  let F := volume A
  have gram (i j : Fin 7) : modeGram L (dual (form A i)) (dual (form A j))=if j=i then 1 else 0 := by
    unfold modeGram dual form; simp only [star_star]; rw [←orth j i]
    apply sumOverCongr; intro t; exact CommSemiring.mul_comm _ _
  have hx : modeGram L x x=1 := gram 0 0
  have hy : modeGram L y y=1 := gram 1 1
  have xy : modeGram L x y=0 := gram 0 1
  have alt : Alt3 F := tripleAlternating _ _ _
  have xn (a b) : lower3 L x F a b=0 := by rw [volumeLower A orth]; simp only [Fin.reduceEq,ite_false]; grind only
  have yn (a b) : lower3 L y F a b=0 := by rw [volumeLower A orth]; simp only [Fin.reduceEq,ite_false]; grind only
  have mass := joint x y hx hy xy F alt xn yn
  rw [volumeEnergy _ orth] at mass
  have rX (p) : normSq (gram3 L (singleCol half x y p) F)=36*normSq (columnCoef half A ((3,4),(2,0)) p) := singletonNorm half A 0 1 yn p
  have rY (p) : normSq (gram3 L (singleCol half y x p) F)=36*normSq (columnCoef half A ((3,4),(2,1)) p) := singletonNorm half A 1 0 xn p
  have rF (i p) : gram3 L (raise3 (PhysicalC2Projected.free x y i) (col2 half x y p)) F=gram3 L (raise3 (coord i) (col2 half x y p)) F :=
    PhysicalC2Canonical.readoutFreeEqualsCoordinate L x y i _ F alt xn yn
  unfold L at rX rY rF
  simp only [rX,rY,rF,←sumOverMulLeft] at mass
  let N (a : Four (Fin 7)) := PhysicalCutCapacities.rowMass half A a
  let M (i : Basis n) (p : Word n) := normSq (gram3 L (raise3 (coord i) (col2 half x y p)) F)
  have sub (p : Word n) : sumOver (List.finRange 3) (fun j => 36*normSq (columnCoef half A (others j,(1,0)) p))≤sumOver L (fun i => M i p) := by
    simpa only [x,y,F,doubleNorm half A orth] using freeBessel A orth (col2 half x y p) F alt
  have total := sumLe P _ _ sub
  rw [sumOverSwap,sumOverSwap P L] at total
  conv at total => lhs; arg 2; intro j; rw [←sumOverMulLeft]
  change sumOver (List.finRange 3) (fun j => 36*N (others j,(1,0)))≤sumOver L (fun i => sumOver P (M i)) at total
  change 36*N ((3,4),(2,0))+36*N ((3,4),(2,1))+sumOver L (fun i => sumOver P (M i))≤36*half^n*6 at mass
  change 36*N ((3,4),(1,0))+(36*N ((2,4),(1,0))+(36*N ((2,3),(1,0))+0))≤_ at total
  change N ((3,4),(2,0))+(N ((3,4),(2,1))+(N ((3,4),(1,0))+(N ((2,4),(1,0))+(N ((2,3),(1,0))+0))))≤_
  grind only
def relabel (a b : Fin 7) (i : Fin 7) := (PhysicalOmittedPair.fiveLabels a b++[a,b]).getD i.val 0
def faceSort : ExteriorPauliBase.Permutation := ((3,2),(0,1))
def sorted (a b : Fin 7) (u : Four (Fin 7)) := reorder (PhysicalWedges.mapFourSites (relabel a b) u) faceSort
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
private theorem supportTable : ∀a b : Fin 7,a<b →
    (∀i j,relabel a b i=relabel a b j→i=j) ∧
    (faces.map (sorted a b)).Perm ((ExteriorCuts.wedges.filter (PackingDual.Row.omitPair a b).covers).map FrameExteriorSector.sourceTuple) := by decide
private theorem permSum {S B : Type} [CommRing S] {xs ys : List B} (h : xs.Perm ys) (f : B→S) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ h1 h2 => exact h1.trans h2
private theorem filterSum {S B : Type} [CommRing S] (xs : List B) (sel : B→Bool) (f : B→S) :
    sumOver (xs.filter sel) f=sumOver xs (fun x => if sel x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.filter_cons]; cases h : sel a <;> simp [h,sumOver] at ih ⊢ <;> grind only

/-- From the joint physical two-hole inequality on the three-sector
complement to each of the 21 original omitted-pair packing rows. -/
theorem omittedPairOfTwoHole (half : R) (unit : 2*half=1) (k : Nat) (joint : TwoHoleUpper half (k+3))
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (a b : Fin 7) (ab : a<b) :
    PackingDual.rowMass (fun w => (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w) (.omitPair a b)≤1 := by
  let p := relabel a b
  let B := fun t i => A t (p i)
  obtain ⟨inj,enumeration⟩ := supportTable a b ab
  have orthB : PhysicalCompressionEffect.OrthonormalFrame B := by
    intro i j; change sumOver _ (fun t => star (A t (p i))*A t (p j))=_
    rw [orth]; by_cases e : i=j
    · subst j; simp
    · rw [ite_eq_right (fun h => e (inj i j h)),ite_eq_right e]
  let f := fun w => (PhysicalCompressionEffect.physicalEntries half unit k A).realPart w w
  let ws := ExteriorCuts.wedges.filter (PackingDual.Row.omitPair a b).covers
  let q := 4*half^(k+3)
  let M := fun u => 2*PhysicalCutCapacities.rowMass half A u
  have sortedMass (u : Four (Fin 7)) : M (sorted a b u)=2*PhysicalCutCapacities.rowMass half B u := by
    exact PhysicalCutCapacities.massReorder half unit A (PhysicalWedges.mapFourSites p u) faceSort (by decide)
  have weightMass (w : ExteriorCuts.Wedge7) : M (FrameExteriorSector.sourceTuple w)=(3*q)*f w :=
    PhysicalCutCapacities.coordinateMass half unit k A w
  have eq := permSum enumeration M
  have mapS {U V : Type} (xs : List U) (g : V→R) (s : U→V) :
      sumOver (xs.map s) g=sumOver xs (fun i => g (s i)) := by simp [sumOver,List.map_map,Function.comp_def]
  change sumOver (faces.map (sorted a b)) M=sumOver (ws.map FrameExteriorSector.sourceTuple) M at eq
  rw [mapS,mapS,sumOverCongr faces sortedMass,sumOverCongr ws weightMass,←sumOverMulLeft,←sumOverMulLeft] at eq
  have bound := fiveFaceBound half joint B orthB
  have posHalf (m : Nat) : 0<half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)
  have pos : 0<3*q := OrderedRing.mul_pos (by grind only) (OrderedRing.mul_pos (by grind only) (posHalf _))
  change sumOver ExteriorCuts.wedges (fun w => if (PackingDual.Row.omitPair a b).covers w then f w else 0)≤1
  rw [←filterSum]; change sumOver ws f≤1
  by_cases h : sumOver ws f≤1
  · exact h
  · have bad := OrderedRing.mul_pos pos (show 0<sumOver ws f-1 by grind only)
    change 2*sumOver faces (PhysicalCutCapacities.rowMass half B)=(3*(4*half^(k+3)))*sumOver ws f at eq
    change 0<(3*(4*half^(k+3)))*(sumOver ws f-1) at bad
    grind only
end Order
end RankSeven.FiveFaceCapacity
#print axioms RankSeven.FiveFaceCapacity.fiveFaceBound
#print axioms RankSeven.FiveFaceCapacity.omittedPairOfTwoHole
