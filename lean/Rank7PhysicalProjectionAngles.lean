import Rank7FiniteProjectionAngles

namespace RankSeven.PhysicalProjectionAngles

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup StabilizerCharacterBasis StabilizerCosetTransform
open StabilizerPairedCharacters StabilizerPopulationRounding StabilizerOddSector StabilizerSmallCodes CharacterFourOrbits
open FiniteProjectionAngles SlaterUnionBound
open PauliPairContraction (normSum image)
open PhysicalPairedReduction (dagger)
open PhysicalCompressionEffect (OrthonormalFrame)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def middleCols {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (t : Basis n) (b : Bool) := if b then A t 2 else A t 1
def middleProject {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) := matMul [false,true] (middleCols A) (dagger (middleCols A))
def code {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a b : Word n) := addM (block half L a) (block half L b)
def test {n : Nat} (p : Word n) (x : Basis n→ComplexScalar R) (t : Basis n) := star (StabilizerCharacterBasis.act p x t)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem twoGram {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    matMul (qubitIndices n) (dagger (middleCols A)) (middleCols A)=ident := by
  funext i j; change sumOver _ (fun t => star (middleCols A t i)*middleCols A t j)=ident i j
  cases i <;> cases j <;> simp (config:={decide:=true}) only [middleCols,ite_true,ite_false,ident] <;> rw [orth] <;> rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem middleProjection {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    Projection (qubitIndices n) (middleProject A) := by
  constructor
  · unfold middleProject; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerInvolution]
  · unfold middleProject; rw [matMulAssoc,←matMulAssoc (qubitIndices n) [false,true] _ (middleCols A),
      twoGram A orth,idLeft [false,true] (by decide) (fun b => by cases b <;> decide)]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem middleTrace {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    trace (qubitIndices n) (middleProject A)=2 := by
  unfold middleProject; rw [traceMatMulSwap,twoGram A orth]; change (1:ComplexScalar R)+(1+0)=2; grind only

theorem lineProjection {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    Projection (qubitIndices n) (block half L a) := by
  refine ⟨blockHerm half L a,?_⟩; have e := blockIsometry half h2 L a; rwa [blockHerm] at e

theorem codeProjection {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a b : Word n)
    (apart : ¬equiv G a b) : Projection (qubitIndices n) (code half L a b) := by
  have ab : wordAdd a b∉G.labels := apart; have ba : wordAdd b a∉G.labels := fun h => apart (StabilizerCosetTransform.symm h)
  constructor
  · unfold code; rw [dagAdd,blockHerm,blockHerm]
  · unfold code; rw [addLeft,addRight,addRight,(lineProjection half h2 L a).square,(lineProjection half h2 L b).square,
      blockProduct half h2 L a b,blockProduct half h2 L b a,ite_eq_right ab,ite_eq_right ba]
    funext i j; unfold addM; grind only

theorem codeTrace {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a b : Word n) :
    trace (qubitIndices n) (code half L a b)=2 := by unfold code; rw [traceAdd,blockTrace half h2,blockTrace half h2]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem middleOverlap {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (Q : Mx (Basis n) R) :
    (trace (qubitIndices n) (matMul (qubitIndices n) (middleProject A) Q)).re=
    energy (qubitIndices n) Q (fun x => A x 1)+energy (qubitIndices n) Q (fun x => A x 2) := by
  let amb := qubitIndices n
  let F := middleCols A
  change (trace amb (matMul amb (matMul [false,true] F (dagger F)) Q)).re=_
  rw [matMulAssoc,traceMatMulSwap,matMulAssoc]
  change (matMul amb (dagger F) (matMul amb Q F) false false+(matMul amb (dagger F) (matMul amb Q F) true true+0)).re=_
  rw [Semiring.add_zero,re_add]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem physicalHeadEnergy {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (p : Word n) :
    energy (qubitIndices n) (middleProject A) (test p (fun x => A x 0))=SixPointRounding.headWeight A p := by
  let amb := qubitIndices n
  let F := middleCols A
  let x (u : Basis n) := A u 0
  let z := test p x
  have gr : matMul [false,true] (dagger (dagger F)) (dagger F)=middleProject A := by rw [PhysicalPairedReduction.daggerInvolution]; rfl
  change energy amb (middleProject A) z=_
  rw [←gr,energyGram]
  have dot (i : Fin 7) : sumOver amb (fun j => star (A j i)*z j)=star (JointProbePayment.pairAmplitude A p 0 i) := by
    have e := HeadPauliFourier.physicalAntiAmplitude A p 0 i
    change HeadPauliFourier.element (fun t => star (A t i)) x p=JointProbePayment.pairAmplitude A p 0 i at e
    rw [←e]
    unfold HeadPauliFourier.element PhysicalMixedFrame.pairs
    have pair (f : Basis n×Basis n→ComplexScalar R) : sumOver (productIndices amb amb) f=sumOver amb (fun i => sumOver amb (fun j => f (i,j))) := by
      unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro b; simp [sumOver,List.map_map,Function.comp_def]
    rw [pair,ComplexExterior.starSumOver]; apply sumOverCongr; intro j
    unfold z test StabilizerCharacterBasis.act; rw [ComplexExterior.starSumOver,sumOverMulLeft,ComplexExterior.starSumOver]
    apply sumOverCongr; intro k; simp only [star_star,star_mul]; grind only
  change normSq (sumOver amb (fun j => star (A j 1)*z j))+(normSq (sumOver amb (fun j => star (A j 2)*z j))+0)=_
  rw [dot,dot,normSq_star,normSq_star,Semiring.add_zero]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem testNorm {n : Nat} (p : Word n) (x : Basis n→ComplexScalar R) :
    normSum (qubitIndices n) (test p x)=normSum (qubitIndices n) x := by
  unfold normSum test; simp only [normSq_star]; exact PauliPairContraction.wordIsometry p x

theorem lineTransport {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (z : TransposeOffset G)
    (p a : Word n) (x : Basis n→ComplexScalar R) :
    pop half L a (test p x)=pop half L (wordAdd (wordAdd a z.offset) p) x := by
  let amb := qubitIndices n
  let B a := block half L a
  let W := wordEntry (imaginaryUnit (R:=R)) p
  let u := StabilizerCharacterBasis.act p x
  let b := wordAdd a z.offset
  have flip (i j : Basis n) : B a i j=star (B b i j) := by
    have tr := congrFun (congrFun (conjugateBlock half L z a) i) j
    change B a j i=B b i j at tr; rw [←tr]; exact (congrFun (congrFun (blockHerm (R:=R) half L a) i) j).symm
  have conjugate (i : Basis n) : image amb (B a) (test p x) i=star (image amb (B b) u i) := by
    unfold image; rw [ComplexExterior.starSumOver]; apply sumOverCongr; intro j; rw [flip,star_mul]; rfl
  have b' := wordAddCancel b p
  have exchanged := wordBlock half L p (wordAdd b p)
  rw [b'] at exchanged
  change matMul amb W (B (wordAdd b p))=matMul amb (B b) W at exchanged
  have move : image amb (B b) u=image amb W (image amb (B (wordAdd b p)) x) := by
    change image amb (B b) (image amb W x)=_; rw [imageComp,←exchanged,←imageComp]
  have normEq (v : Basis n→ComplexScalar R) : normSum amb (fun j => star (v j))=normSum amb v := by unfold normSum; simp only [normSq_star]
  unfold pop; rw [energyNorm _ _ (lineProjection half h2 L a),energyNorm _ _ (lineProjection half h2 L _)]
  change normSum amb (image amb (B a) (test p x))=normSum amb (image amb (B (wordAdd b p)) x)
  rw [funext conjugate,normEq,move]; exact PauliPairContraction.wordIsometry p _

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem unitHead {n : Nat} (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) :
    normSum (qubitIndices n) (fun i => A i 0)=1 := by
  have reSum {β : Type} (xs : List β) (f : β→ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
    induction xs with | nil => rfl | cons i xs ih => change (f i+sumOver xs f).re=_; rw [re_add,ih]; rfl
  have o := congrArg ComplexScalar.re (orth 0 0)
  simpa only [normSum,reSum,ite_true,re_one,re_star_mul_self] using o

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem popCongr {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (x : Basis n→ComplexScalar R) {a b : Word n}
    (h : equiv G a b) : pop half L a x=pop half L b x := by
  have m : block half L a=block half L b := by funext i j; unfold block; rw [sameCoset (R:=R) L a b h]
  unfold pop; rw [m]

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

private theorem pairedResponse {α : Type} (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (f : α→R) (pos : ∀i,0≤f i)
    (norm : sumOver xs f=1) (h J : α→α) (inv : ∀i,J (J i)=i) (comm : ∀i,h (J i)=J (h i))
    (a b c d : α) (ab : a≠b) (cd : c≠d) (ha : h a=b) (hb : h b=a) (hc : h c=d) (hd : h d=c) :
    (J c=a ∨ J c=b → f (J a)+f (J b)=f c+f d) ∧
    (¬(J c=a ∨ J c=b) → f (J a)+f (J b)≤1-(f c+f d)) := by
  constructor
  · intro inC; rcases inC with e|e
    · have ja : J a=c := by rw [←e,inv]
      have jb : J b=d := by rw [←ha,←comm,ja,hc]
      rw [ja,jb]
    · have jb : J b=c := by rw [←e,inv]
      have ja : J a=d := by rw [←hb,←comm,jb,hc]
      rw [ja,jb]; grind only
  · intro outside
    have ac : J a≠c := fun e => outside (Or.inl (by rw [←e,inv]))
    have bc : J b≠c := fun e => outside (Or.inr (by rw [←e,inv]))
    have ad : J a≠d := by intro e; have k := congrArg h e; rw [comm,ha,hd] at k; exact bc k
    have bd : J b≠d := by intro e; have k := congrArg h e; rw [comm,hb,hd] at k; exact ac k
    have jj : J a≠J b := by intro e; have k := congrArg J e; rw [inv,inv] at k; exact ab k
    have yn : [J a,J b,c,d].Nodup := by simp [jj,ac,ad,bc,bd,cd]
    have m := subsetMass xs [J a,J b,c,d] nd yn full f pos
    change f (J a)+(f (J b)+(f c+(f d+0)))≤_ at m; rw [norm] at m; grind only

private theorem lineEq {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n) (a b : Line T) :
    shift T w a=b ↔ equiv G (wordAdd a.val w) b.val := by
  constructor
  · intro eq; have h := (represents T (wordAdd a.val w)).2; have v := congrArg Subtype.val eq
    change representative T (wordAdd a.val w)=b.val at v; rwa [v] at h
  · intro h; exact Subtype.ext (repClass T _ _ b.property h)

theorem codeResponse {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (c a b : Word n) (hc : c∈T.reps) (ha : a∈T.reps) (hb : b∈T.reps) (ab : a≠b)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (p : Word n) :
    let head := fun i => A i 0
    let q := energy (qubitIndices n) (code half L a b) (test p head)
    let f := 1-pairedHead half L T A (wordAdd a b) c
    (member z c a b p=true → q=1-f) ∧ (member z c a b p=false → q≤f) := by
  let x (i : Basis n) := A i 0
  let M (i : Line T) := pop half L i.val x
  let t := wordAdd a b
  let v := wordAdd z.offset p
  let h := shift T t
  let J := shift T v
  let a' : Line T := ⟨a,ha⟩
  let b' : Line T := ⟨b,hb⟩
  let c' : Line T := ⟨c,hc⟩
  let d' := h c'
  have ht : t∉G.labels := fun mem => ab (T.separated a ha b hb mem)
  have sh := mateSwaps T a b ha hb
  have swapA : h a'=b' := Subtype.ext sh.1
  have swapB : h b'=a' := Subtype.ext sh.2
  have normal : sumOver T.reps.attach M=1 := (lineSum T _).trans ((popTotal half h2 L T x).trans (unitHead A orth))
  have commuting (i : Line T) : h (J i)=J (h i) := by unfold h J; rw [shiftSum,shiftSum,wordAddComm v t]
  have resp := pairedResponse T.reps.attach (linesNodup T) (List.mem_attach _) M (fun i => popNonnegative half h2 L i.val x)
    normal h J (shiftTwice T v) commuting a' b' c' d' (fun eq => ab (congrArg Subtype.val eq)) (shiftFree T t ht c') swapA swapB rfl (shiftTwice T t c')
  have inside : member z c a b p=true ↔ J c'=a' ∨ J c'=b' := by
    rw [selectorAction,lineEq,lineEq,wordAddAssoc]
  have response (u : Line T) : pop half L u.val (test p x)=M (J u) := by
    rw [lineTransport half h2 L z p,wordAddAssoc]
    exact popCongr half L x (represents T _).2
  have w : energy (qubitIndices n) (code half L a b) (test p x)=M (J a')+M (J b') := by
    unfold code; rw [energyAdd]; exact congrArg (fun z => z+_) (response a') |>.trans (congrArg (fun z => _+z) (response b'))
  change (member z c a b p=true → _=1-(1-(M c'+M d'))) ∧ (member z c a b p=false → _≤1-(M c'+M d'))
  rw [w]; constructor
  · intro yes; have e := resp.1 (inside.mp yes); grind only
  · intro no; apply resp.2; intro h; have e := inside.mpr h; rw [no] at e; contradiction

theorem pointwise {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (T : Transversal G)
    (z : TransposeOffset G) (c a b : Word n) (hc : c∈T.reps) (ha : a∈T.reps) (hb : b∈T.reps) (ab : a≠b)
    (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A) (p : Word n) :
    let e := 2-middlePop half L a A-middlePop half L b A
    let f := 1-pairedHead half L T A (wordAdd a b) c
    (member z c a b p=true → 2*(1-SixPointRounding.headWeight A p)≤3*(e+2*f)) ∧
    (member z c a b p=false → 2*SixPointRounding.headWeight A p≤3*(e+2*f)) := by
  let xs := qubitIndices n
  let P := middleProject A
  let Q := code half L a b
  let x (i : Basis n) := A i 0
  let v := test p x
  let e := 2-middlePop half L a A-middlePop half L b A
  let f := 1-pairedHead half L T A (wordAdd a b) c
  let wt := SixPointRounding.headWeight A p
  let q := energy xs Q v
  have pr : Projection xs P := middleProjection A orth
  have qr : Projection xs Q := codeProjection half h2 L a b (fun h => ab (T.separated a ha b hb h))
  have same : trace xs P=trace xs Q := (middleTrace A orth).trans (codeTrace half h2 L a b).symm
  have unit : normSum xs v=1 := (testNorm p x).trans (unitHead A orth)
  have angles := projectionAngles xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n) P Q pr qr same v unit
  have leak : (trace xs P).re-(trace xs (matMul xs P Q)).re=e := by
    change (trace xs (middleProject A)).re-_=_
    rw [middleTrace A orth,middleOverlap A Q]
    have two : (2:ComplexScalar R).re=2 := by rfl
    rw [two]; dsimp only [Q,code]; rw [energyAdd,energyAdd]
    unfold e middlePop pop; grind only
  change 2*energy xs P v≤3*((trace xs P).re-(trace xs (matMul xs P Q)).re)+6*q ∧
    2*(1-energy xs P v)≤3*((trace xs P).re-(trace xs (matMul xs P Q)).re)+6*(1-q) at angles
  have real : energy xs P v=wt := physicalHeadEnergy A p
  rw [leak,real] at angles
  have resp := codeResponse half h2 L T z c a b hc ha hb ab A orth p
  change (member z c a b p=true → q=1-f) ∧ (member z c a b p=false → q≤f) at resp
  change (member z c a b p=true → 2*(1-wt)≤3*(e+2*f)) ∧ (member z c a b p=false → 2*wt≤3*(e+2*f))
  exact ⟨fun h => by have := resp.1 h; grind only,fun h => by have := resp.2 h; grind only⟩

/-- A small physical shared Gram supplies all four pieces of the rounded
sector witness used by the 200/11 six-point comparison. -/
theorem physicalRoundedSector (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (mu : Fin 7→R) (orth : OrthonormalFrame A) (small : 200*(WeightedProbeShift.physicalPayment half h2 k A mu).kappa≤11) :
    ∃delta,Nonempty (SixPointRounding.RoundedSector half A delta) ∧ 411*delta≤378 := by
  classical
  obtain ⟨C⟩ := physicalSmallCodes half h2 k A mu orth small
  obtain ⟨z⟩ := offsetExists half h2 C.T
  let e := 2-middlePop half C.L C.a A-middlePop half C.L C.b A
  let f := 1-pairedHead half C.L C.T A (wordAdd C.a C.b) C.c
  let delta := 3*half*(e+2*f)
  let flag := member z C.c C.a C.b
  have err : 5*(e+2*f)<3 := C.error
  have scalar : 2*delta=3*(e+2*f) := by unfold delta; have a := congrArg (fun x : R => 3*x*(e+2*f)) h2; grind only
  have pts (p : Word (k+3)) := pointwise half h2 C.L C.T z C.c C.a C.b C.hc C.ha C.hb C.distinct.1 A orth p
  refine ⟨delta,⟨⟨flag,selectorMass half h2 C.T z C.c C.a C.b C.hc C.ha C.hb C.distinct.2.1 C.distinct.2.2 C.distinct.1,
    selectorTrace half h2 C.L C.T z C.c C.a C.b C.hc C.ha C.hb C.distinct.2.1 C.distinct.2.2 C.distinct.1 A orth,?_,?_⟩⟩,by grind only⟩
  · intro p _ hp; have q := (pts p).1 hp; change 2*(1-SixPointRounding.headWeight A p)≤3*(e+2*f) at q; grind only
  · intro p _ hp; have q := (pts p).2 hp; change 2*SixPointRounding.headWeight A p≤3*(e+2*f) at q; grind only

/-- Uniform six-point price for the physical frame, with the small-Gram
case constructed from the Pauli character sectors. -/
theorem uniformPhysicalSixPrice (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar R)
    (mu : Fin 7→R) (orth : OrthonormalFrame A) :
    let M := WeightedProbeShift.physicalPayment half h2 k A mu
    11*M.sixMass≤55+200*M.kappa :=
  SixPointRounding.uniformSixPriceCoarse half h2 k A mu orth (fun sm => physicalRoundedSector half h2 k A mu orth (Std.le_of_lt sm))

end RankSeven.PhysicalProjectionAngles

#print axioms RankSeven.PhysicalProjectionAngles.physicalHeadEnergy
#print axioms RankSeven.PhysicalProjectionAngles.lineTransport
#print axioms RankSeven.PhysicalProjectionAngles.codeResponse
#print axioms RankSeven.PhysicalProjectionAngles.pointwise
#print axioms RankSeven.PhysicalProjectionAngles.physicalRoundedSector
#print axioms RankSeven.PhysicalProjectionAngles.uniformPhysicalSixPrice

