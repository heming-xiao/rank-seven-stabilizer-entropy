import Rank7HighestAnchorMoments

namespace RankSeven.HighestCodeTransport

open Lean.Grind Pauli ComplexScalar PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerPopulationRounding SymmetricDefect HighestCodeParseval
open StabilizerOddSector HighestCodeLocalization FiniteProjectionAngles SlaterUnionBound
open CharacterFourOrbits
open PauliPairContraction (normSum image)
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalProjectionAngles (lineProjection)
variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

theorem actPopulation {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (p a : Word n) (x : Basis n→ComplexScalar R) :
    pop half L a (act p x)=pop half L (wordAdd a p) x := by
  let amb := qubitIndices n
  let B := block half L
  let W := wordEntry (imaginaryUnit (R:=R)) p
  have exchanged := wordBlock half L p (wordAdd a p)
  rw [wordAddCancel] at exchanged
  change matMul amb W (B (wordAdd a p))=matMul amb (B a) W at exchanged
  have move : image amb (B a) (act p x)=image amb W (image amb (B (wordAdd a p)) x) := by
    change image amb (B a) (image amb W x)=_; rw [imageComp,←exchanged,←imageComp]
  unfold pop; rw [energyNorm _ _ (lineProjection half h2 L a),energyNorm _ _ (lineProjection half h2 L _)]
  change normSum amb (image amb (B a) (act p x))=_
  rw [move]; exact PauliPairContraction.wordIsometry p _

theorem starPopulation {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (z : TransposeOffset G) (a : Word n) (x : Basis n→ComplexScalar R) :
    pop half L a (fun i => star (x i))=pop half L (wordAdd a z.offset) x := by
  have e := PhysicalProjectionAngles.lineTransport half h2 L z (unitWord n) a x
  have id : PhysicalProjectionAngles.test (unitWord n) x=fun i => star (x i) := by funext i; unfold PhysicalProjectionAngles.test; rw [actIdentity]
  simpa only [id,wordAddZero] using e

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem classPopulation {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (x : Basis n→ComplexScalar R)
    {a b : Word n} (eq : equiv G a b) : pop half L a x=pop half L b x := by
  have m : block half L a=block half L b := by funext i j; unfold block; rw [sameCoset (R:=R) L a b eq]
  unfold pop; rw [m]

private theorem cancel {n : Nat} (a b c : Word n) : wordAdd (wordAdd a c) (wordAdd b c)=wordAdd a b := by
  rw [wordAddComm b c,←wordAddAssoc,wordAddCancel]

private theorem translate {n : Nat} {G : MaximalFamily n} {a b : Word n} (eq : equiv G a b) (p : Word n) :
    equiv G (wordAdd a p) (wordAdd b p) := by unfold equiv; rw [cancel]; exact eq

theorem physicalCodePopulation {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p : Word n) (A : Basis n→Fin 7→ComplexScalar R) (a : Word n) :
    let c := wordAdd a p
    let d := wordAdd a z.offset
    let Q := PhysicalProjectionAngles.code half L c d
    2*codePopulation half L T z p A a=
      energy (qubitIndices n) Q (fun i => A i 0)+energy (qubitIndices n) Q (fun i => A i 1) := by
  let m := mate T z p a
  let x i := A i 0
  let y i := A i 1
  have cm : equiv G m (wordAdd a (wordAdd z.offset p)) := StabilizerCosetTransform.symm (represents T _).2
  have shuffle (a b c : Word n) : wordAdd (wordAdd a (wordAdd b c)) c=wordAdd a b := by rw [←wordAddAssoc,wordAddCancel]
  have qx := translate cm p
  have qy := translate cm z.offset
  rw [shuffle] at qx
  rw [wordAddComm z.offset p,shuffle] at qy
  have ux := classPopulation half L x qx
  have uy := classPopulation half L y qy
  change 2*(half*(pop half L a (act p x)+pop half L a (fun i => star (y i)))+
    half*(pop half L m (act p x)+pop half L m (fun i => star (y i))))=
    energy _ (PhysicalProjectionAngles.code half L _ _) x+energy _ (PhysicalProjectionAngles.code half L _ _) y
  unfold PhysicalProjectionAngles.code; rw [energyAdd,energyAdd]
  simp only [actPopulation half h2,starPopulation half h2 L z,ux,uy]
  change 2*(half*(pop half L (wordAdd a p) x+pop half L (wordAdd a z.offset) y)+half*(pop half L (wordAdd a z.offset) x+pop half L (wordAdd a p) y))=
    (pop half L _ x+pop half L _ x)+(pop half L _ y+pop half L _ y)
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem transitionWeight {n : Nat} {G : MaximalFamily n} (L : Lift G)
    (q : Word n) (A : Basis n→Fin 7→ComplexScalar R) :
    normSq (innerProduct (qubitIndices n) (fun i => star (A i 1)) (act q (fun i => A i 0)))=JointProbePayment.pairWeight A q 0 1 := by
  have e := sourceNorm L q A (unitWord n)
  rw [wordAddComm,wordAddZero] at e
  simpa only [innerProduct,source,L.identity,phase,Bool.false_eq_true,ite_false,Semiring.one_mul,actIdentity,star_star] using e

private theorem subsetMass {α : Type} (xs ys : List α) (xn : xs.Nodup) (yn : ys.Nodup) (full : ∀i,i∈xs) (f : α→R) (nn : ∀i,0≤f i) :
    sumOver ys f≤sumOver xs f := by
  classical
  have price (i : α) : sumOver ys (fun j => if i=j then f j else 0)≤f i := by
    by_cases mem : i∈ys
    · rw [ExteriorPauliBase.sumOnIndex ys i f yn mem]; exact Std.le_refl _
    · have e (j : α) (hj : j∈ys) : (if i=j then f j else 0)=0 := by
        have d : i≠j := fun eq => mem (eq ▸ hj); simp [d]
      rw [AnticommutingDefect.sumCongrMem ys _ _ e]
      have zero (cs : List α) : sumOver cs (fun _ => (0:R))=0 := by
        induction cs with | nil => rfl | cons j cs ih => change 0+sumOver cs _=0; rw [ih]; grind only
      rw [zero]; exact nn i
  have s := Compression.sumOverNonnegative xs (fun i => f i-sumOver ys (fun j => if i=j then f j else 0)) (fun i _ => by have := price i; grind only)
  rw [Compression.sumOverSub,sumOverSwap] at s
  have sum (j : α) : sumOver xs (fun i => if i=j then f j else 0)=f j := by
    have e (i : α) : (if i=j then f j else 0)=(if j=i then f i else 0) := by
      by_cases h : i=j
      · subst i; simp
      · simp [h,Ne.symm h]
    rw [sumOverCongr _ e,ExteriorPauliBase.sumOnIndex xs j f xn (full j)]
  rw [sumOverCongr ys sum] at s; grind only



theorem outsideCodeEnergy {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p q : Word n) (oq : MixedDefect.oddWord q=true)
    (dif : wordAdd z.offset p∉G.labels) (off : wordAdd p q∉G.labels)
    (a : Word n) (ha : a∈T.reps) (x : Basis n→ComplexScalar R) (ux : normSum (qubitIndices n) x=1) :
    let Q := PhysicalProjectionAngles.code half L a (mate T z p a)
    energy (qubitIndices n) Q (act q x)+energy (qubitIndices n) Q (act p x)≤1 := by
  let delta := wordAdd p q
  let t := wordAdd z.offset p
  have dt : wordAdd delta t∉G.labels := by
    have id : wordAdd delta t=wordAdd z.offset q := by
      unfold delta t; rw [wordAddComm p q,cancel,wordAddComm]
    rw [id]; intro h; have v := HighestAnchorOddCoset.evenCoset half h2 z q h
    rw [oq] at v; contradiction
  let H := characterAction T delta t off dif dt
  let i : Line T := ⟨a,ha⟩
  let f (j : Line T) := pop half L j.val (act p x)
  have mass := subsetMass T.reps.attach (orbit H i) (linesNodup T) (orbitNodup H i) (List.mem_attach _)
    f (fun j => popNonnegative half h2 L j.val (act p x))
  have total : sumOver T.reps.attach f=1 :=
    (lineSum T _).trans ((popTotal half h2 L T _).trans ((PauliPairContraction.wordIsometry p x).trans ux))
  rw [total] at mass
  have move (j : Line T) : f (shift T delta j)=pop half L j.val (act q x) := by
    change pop half L (representative T (wordAdd j.val delta)) (act p x)=_
    rw [←classPopulation half L (act p x) (represents T _).2,actPopulation half h2,actPopulation half h2]
    have id : wordAdd (wordAdd j.val delta) p=wordAdd j.val q := by
      unfold delta; rw [wordAddComm p q,←wordAddAssoc,wordAddCancel]
    rw [id]
  change f i+(f (shift T delta i)+(f (shift T t i)+(f (shift T delta (shift T t i))+0)))≤1 at mass
  rw [move,move] at mass
  change pop half L a (act p x)+(pop half L a (act q x)+(pop half L (mate T z p a) (act p x)+(pop half L (mate T z p a) (act q x)+0)))≤1 at mass
  dsimp only; unfold PhysicalProjectionAngles.code; rw [energyAdd,energyAdd]
  change (pop half L a _+pop half L (mate T z p a) _)+(pop half L a _+pop half L (mate T z p a) _)≤1
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem unitColumn {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (i : Fin 7) :
    normSum (qubitIndices n) (fun j => A j i)=1 := by
  have eq := congrArg ComplexScalar.re (orth i i)
  have reSum {β : Type} (ys : List β) (f : β→ComplexScalar R) : (sumOver ys f).re=sumOver ys (fun j => (f j).re) := by
    induction ys with | nil => rfl | cons j ys ih => change (f j+sumOver ys f).re=_; rw [re_add,ih]; rfl
  unfold normSum; simpa only [reSum,ite_true,re_one,re_star_mul_self] using eq

theorem outsidePoint {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G)
    (T : Transversal G) (z : TransposeOffset G) (p q : Word n) (oq : MixedDefect.oddWord q=true)
    (dif : wordAdd z.offset p∉G.labels) (off : wordAdd p q∉G.labels) (a : Word n) (ha : a∈T.reps)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (large : 1≤2*codePopulation half L T z p A a) :
    let b := codePopulation half L T z p A a
    JointProbePayment.pairWeight A q 0 1≤4*b*(1-b) := by
  let x i := A i 0
  let y i := star (A i 1)
  let m := mate T z p a
  let Q := PhysicalProjectionAngles.code half L a m
  let E (v : Basis n→ComplexScalar R) := energy (qubitIndices n) Q v
  let b := codePopulation half L T z p A a
  have qproj := PhysicalProjectionAngles.codeProjection (R:=R) half h2 L a m
    (fun e => mateDifferent T _ dif a (T.separated a ha m (represents T _).1 e))
  have yu : normSum (qubitIndices n) y=1 := by unfold normSum y; simp only [normSq_star]; exact unitColumn A orth 1
  have xu := unitColumn A orth 0
  have u := HighestAnchorMoments.projectionMismatch (qubitIndices n) (HyperplaneIncidence.normalsNodup n)
    qubitIndicesComplete Q qproj y (act q x) yu ((PauliPairContraction.wordIsometry q x).trans xu)
  rw [transitionWeight L q A] at u
  have e := outsideCodeEnergy half h2 L T z p q oq dif off a ha x xu
  change E (act q x)+E (act p x)≤1 at e
  change JointProbePayment.pairWeight A q 0 1≤1-(E y-E (act q x))^2 at u
  have add : 2*b=E y+E (act p x) := by
    unfold E Q PhysicalProjectionAngles.code; rw [energyAdd,energyAdd]
    change 2*(half*(pop half L a (act p x)+pop half L a y)+half*(pop half L m (act p x)+pop half L m y))=
      (pop half L a y+pop half L m y)+(pop half L a (act p x)+pop half L m (act p x))
    grind only
  change 1≤2*b at large
  have v := OrderedRing.mul_nonneg (show 0≤(E y-E (act q x))-(2*b-1) by grind only)
    (show 0≤(E y-E (act q x))+(2*b-1) by grind only)
  change JointProbePayment.pairWeight A q 0 1≤4*b*(1-b)
  grind only

end RankSeven.HighestCodeTransport

#print axioms RankSeven.HighestCodeTransport.physicalCodePopulation
#print axioms RankSeven.HighestCodeTransport.transitionWeight
#print axioms RankSeven.HighestCodeTransport.outsideCodeEnergy
#print axioms RankSeven.HighestCodeTransport.outsidePoint

