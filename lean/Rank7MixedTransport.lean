import Rank7PhysicalMixedFrame
import Rank7AlternatingTrace
import Rank7WedgeSquareIntertwiner
import Rank7AntiDefectTransport

/-! Matrix transport from the physical odd Pauli two-form squares to the
fully alternating part of the four-copy Pauli frame. -/
namespace RankSeven.MixedTransport

open Lean.Grind Pauli ComplexScalar GenericExteriorKernel FourCopySectors
open ExteriorPauliBase (permutations)
open PhysicalPairedReduction (dagger)
open PhysicalMixedFrame (doubledWord)
open MixedDefect (oddWords)
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
local instance {C : Type} [CommRing C] : IntCast C := Ring.intCast

abbrev TensorSite (n : Nat) := Four (Basis n)
def sites (n : Nat) := fourIndices (qubitIndices n)
def D {n : Nat} (x : TensorSite n) (a : Word n) : ComplexScalar R := doubledWord a x
def W (n : Nat) := matMul (oddWords n) (D (R:=R)) (dagger D)
def twirl (n : Nat) := @unnormalizedTwirl (ComplexScalar R) _ n imaginaryUnit
def altM (n : Nat) := rawBlock .antisymmetric (MixedDefect.idEntry (R:=R) (α:=TensorSite n))

private theorem sitesFull {n : Nat} (x : TensorSite n) : x∈sites n :=
  HyperplaneInduction.pairMember (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
    (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
private theorem sitesNodup (n : Nat) : (sites n).Nodup := by
  have h := HyperplaneIncidence.normalsNodup n
  have t := HyperplaneInduction.pairsNodup _ _ h h
  exact HyperplaneInduction.pairsNodup _ _ t t

private theorem identityLeft {α β : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (full : ∀ a,a∈xs) (T : α → β → ComplexScalar R) :
    matMul xs MixedDefect.idEntry T=T := by
  funext x y
  rw [←ExteriorPauliBase.sumOnIndex xs x (fun s => T s y) nd (full x)]
  apply sumOverCongr; intro s; by_cases e : x=s <;> simp [MixedDefect.idEntry,e] <;> grind only

theorem altM_mul {β : Type} {n : Nat} (F : TensorSite n → β → ComplexScalar R) :
    matMul (sites n) (altM n) F=fun x y => act (coefficient .antisymmetric) (fun z => F z y) x := by
  funext x y
  have transfer (G : TensorSite n → Four Unit → ComplexScalar R) :
      matMul (sites n) (altM n) G=rawBlock .antisymmetric G := by
    rw [altM,←blockLeft,identityLeft _ (sitesNodup n) sitesFull]
  let G (u : TensorSite n) (_ : Four Unit) := F u y
  exact congrFun (congrFun (transfer G) x) (((),()),((),()))

private theorem eqvTwirl (n : Nat) : Equivariant (twirl (R:=R) n) := by
  intro p hp x y; unfold twirl unnormalizedTwirl
  apply sumOverCongr; intro a; exact tensorEquivariant _ p hp x y

private theorem reordInject {α : Type} (p : Perm) (hp : p∈permutations) (u v : Four α)
    (eqv : reorder u p=reorder v p) : u=v := by
  have t : permutations.all (fun p => decide (reorder p (inverse p)=ident))=true := by decide
  have k := _root_.of_decide_eq_true (List.all_eq_true.mp t p hp)
  have comp (x : Four α) : reorder (reorder x p) (inverse p)=reorder x (reorder p (inverse p)) := by
    change ((position (reorder x p) _,position (reorder x p) _),
      (position (reorder x p) _,position (reorder x p) _)) = _
    simp only [position_reorder]; rfl
  have e := congrArg (fun z => reorder z (inverse p)) eqv
  change reorder (reorder u p) _=reorder (reorder v p) _ at e
  rw [comp,comp,k] at e; exact e

private theorem idEqv (n : Nat) : Equivariant (MixedDefect.idEntry (R:=R) (α:=TensorSite n)) := by
  intro p hp x y
  by_cases h : x=y
  · subst y; simp [MixedDefect.idEntry]
  · have k : reorder x p≠reorder y p := fun e => h (reordInject p hp x y e)
    simp [MixedDefect.idEntry,h,k]

private theorem starAlt {α β : Type} (T : Four α → Four β → ComplexScalar R)
    (x : Four α) (y : Four β) :
    star (rawBlock .antisymmetric T x y)=act (coefficient .antisymmetric) (fun z => star (T z y)) x := by
  unfold rawBlock act; rw [ComplexExterior.starSumOver]
  apply sumOverCongr; intro p; rw [star_mul]
  exact congrArg (fun z => z*star (T (reorder x p) y)) ((scalarConjugation (R:=R)).fixesInteger _)

private theorem daggerBlock {α : Type} (T : Four α → Four α → ComplexScalar R)
    (eqv : Equivariant T) (herm : dagger T=T) :
    dagger (rawBlock .antisymmetric T)=rawBlock .antisymmetric T := by
  funext x y
  change star (rawBlock .antisymmetric T y x)=_
  rw [starAlt,AlternatingTrace.alternatingRight T eqv x y]
  have e : (fun z => star (T z x))=T x := by
    funext z; exact congrFun (congrFun herm x) z
  rw [e]

private theorem altMHermitian (n : Nat) : dagger (altM (R:=R) n)=altM n := by
  apply daggerBlock _ (idEqv n)
  funext x y
  change star (MixedDefect.idEntry y x)=MixedDefect.idEntry x y
  by_cases e : x=y
  · subst y; simp only [MixedDefect.idEntry,ite_true]; exact star_ofReal (1:R)
  · simp [MixedDefect.idEntry,e,Ne.symm e]; exact star_ofReal (0:R)

/-- One copy of the alternator extracts exactly the same rows from the
odd doubled-word Gram and the complete Pauli twirl. -/
theorem rawAltW (half : R) (unit : 2*half=1) (n : Nat) :
    rawBlock .antisymmetric (W (R:=R) n) = rawBlock .antisymmetric (twirl n) := by
  have all (p : Perm) (hp : p∈permutations) (x y : TensorSite n) :
      2*W (R:=R) n (reorder x p) y =
      twirl n (reorder x p) y - twirl n (reorder (reorder x p) transposition) y :=
    PhysicalMixedFrame.oddDoubledResolution _ _
  funext x y
  have r : act (coefficient .antisymmetric) (fun z => twirl n z y-twirl n (reorder z transposition) y) x =
      rawBlock .antisymmetric (twirl (R:=R) n) x y-
        act (coefficient .antisymmetric) (fun z => twirl n (reorder z transposition) y) x := by
    unfold rawBlock act; rw [←Compression.sumOverSub]; apply sumOverCongr; intro p; grind only
  have tr (z : TensorSite n) : twirl (R:=R) n (reorder z transposition) y =
      twirl n z (reorder y transposition) := by
    have e := eqvTwirl (R:=R) n transposition (by decide) z (reorder y transposition)
    exact e
  have neg := AlternatingTrace.alternatingColumn (twirl (R:=R) n) (eqvTwirl n) x y transposition (by decide)
  have sg : coefficient .antisymmetric transposition = -1 := by decide
  rw [sg,Ring.intCast_neg,Ring.intCast_one] at neg
  simp only [tr] at r
  change _=rawBlock .antisymmetric _ x y-rawBlock .antisymmetric _ x (reorder y transposition) at r
  rw [neg] at r
  have e : 2*rawBlock .antisymmetric (W (R:=R) n) x y =
      act (coefficient .antisymmetric) (fun z => twirl n z y-twirl n (reorder z transposition) y) x := by
    unfold rawBlock act; rw [sumOverMulLeft]
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    dsimp only; rw [←all p hp x y]; grind only
  simp only [tr] at e; rw [r] at e
  have k : 2*ofReal half=(1:ComplexScalar R) := by
    change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  have t := congrArg (fun z => ofReal half*z) e
  change ofReal half*(2*_)=ofReal half*(_- -1*_) at t
  have scale (v : ComplexScalar R) : ofReal half*(2*v)=v := by
    rw [←Semiring.mul_assoc,CommSemiring.mul_comm (ofReal half) 2,k,Semiring.one_mul]
  rw [scale] at t
  calc
    _ = _ := t
    _ = ofReal half*(2*rawBlock .antisymmetric (twirl n) x y) := by grind only
    _ = _ := scale _

theorem altWCommute (half : R) (unit : 2*half=1) (n : Nat) :
    matMul (sites n) (altM (R:=R) n) (W n)=rawBlock .antisymmetric (twirl n) ∧
    matMul (sites n) (W (R:=R) n) (altM n)=rawBlock .antisymmetric (twirl n) := by
  have left : matMul (sites n) (altM (R:=R) n) (W n)=rawBlock .antisymmetric (twirl n) :=
    (altM_mul _).trans (rawAltW half unit n)
  have wHerm : dagger (W (R:=R) n)=W n := by
    unfold W; rw [PhysicalPairedReduction.daggerProduct,PhysicalPairedReduction.daggerInvolution]
  have eq := congrArg dagger left
  rw [PhysicalPairedReduction.daggerProduct,wHerm,altMHermitian,
    daggerBlock _ (eqvTwirl n) (PhysicalPairedReduction.twirlHermitian n)] at eq
  exact ⟨left,eq⟩

private theorem colScale {α β γ : Type} (xs : List β) (T : α → β → ComplexScalar R)
    (U V : β → γ → ComplexScalar R) (x : α) (b : γ) (s : ComplexScalar R)
    (eq : ∀ i∈xs,U i b=s*V i b) : matMul xs T U x b=s*matMul xs T V x b := by
  unfold matMul; rw [sumOverMulLeft]; apply congrArg List.sum; apply List.map_congr_left
  intro i hi; rw [eq i hi]; grind only

noncomputable def P {n : Nat} (half third : R) :=
  MixedDefect.frameProjection ((2:R)^n) (half^n) third (@SymmetricDefect.anti n)

private theorem dimCancel (half : R) (unit : 2*half=1) (n : Nat) :
    (ofReal half)^n*(2:ComplexScalar R)^n=1 := by
  have z : 2*ofReal half=(1:ComplexScalar R) := by
    change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
  | succ n ih => simp only [Semiring.pow_succ]; grind only

/-- The actual antisymmetric Pauli Gram projector maps the physical
doubled columns exactly onto their alternating part. The statement is on
each physical odd column; no intertwining or idempotence is assumed. -/
theorem physicalColumnTransport (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    {n : Nat} (x : TensorSite n) (b : Word n) (hb : b∈oddWords n) :
    24*matMul (oddWords n) D (P half third) x b =
      WedgeSquareIntertwiner.alternatingWord b x := by
  let xs := sites n
  let os := oddWords n
  let d := (2:ComplexScalar R)^n
  let M := altM (R:=R) n
  let U := @D R _ n
  let V := dagger U
  let F := P (n:=n) half third
  let I := MixedDefect.idEntry (R:=R) (α:=Word n)
  have ev (i : Word n) : matMul xs V U i b=d*d*I i b := WedgeSquareIntertwiner.doubledWordOrthogonal i b
  have id (z : TensorSite n) : matMul os U I z b=U z b := by
    rw [←ExteriorPauliBase.sumOnIndex os b (U z) (MixedDefect.oddWordsNodup n) hb]
    apply sumOverCongr; intro k; by_cases eq : b=k <;> simp [I,MixedDefect.idEntry,eq,Ne.symm] <;> grind only
  have wd (z : TensorSite n) : matMul xs (W n) U z b=(d*d)*U z b := by
    unfold W; rw [matMulAssoc]
    exact (colScale os U _ I z b _ (fun a _ => ev a)).trans (congrArg (fun w => (d*d)*w) (id z))
  have alt (z : TensorSite n) (q : Word n) :
      matMul xs M U z q=WedgeSquareIntertwiner.alternatingWord q z := congrFun (congrFun (altM_mul U) z) q
  have gram (a : Word n) (ha : a∈os) : matMul xs V (matMul xs M U) a b=24*(d*d)*F a b := by
    unfold matMul; change sumOver xs (fun v => V a v * matMul xs M U v b)=_
    simp only [alt]; exact WedgeSquareIntertwiner.doubledWordProjection half third h2 h3 a b
      (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2
  have comm := (altWCommute half h2 n).2.trans (altWCommute half h2 n).1.symm
  have transport : 24*(d*d)*matMul os U F x b=(d*d)*matMul xs M U x b := by
    calc
      _ = matMul os U (matMul xs V (matMul xs M U)) x b := (colScale os U _ F x b _ gram).symm
      _ = matMul xs (matMul xs (W n) M) U x b := by simp only [W,U,V,os,matMulAssoc]
      _ = matMul xs M (matMul xs (W n) U) x b := by rw [comm,matMulAssoc]
      _ = _ := colScale xs M _ U x b _ (fun z _ => wd z)
  have inv := dimCancel half h2 n
  let di := (ofReal half)^n
  change di*d=1 at inv
  have cancel (v : ComplexScalar R) : (di*di)*((d*d)*v)=v := by
    calc
      _ = (di*d)*(di*d)*v := by grind only
      _ = _ := by rw [inv,Semiring.one_mul,Semiring.one_mul]
  have e : (d*d)*(24*matMul os U F x b)=(d*d)*matMul xs M U x b := by rw [←transport]; grind only
  have k := congrArg (fun w => (di*di)*w) e
  change (di*di)*((d*d)*_)=(di*di)*((d*d)*_) at k
  rw [cancel,cancel,alt] at k; exact k

open RectangularPairedReduction (scaleMatrix)

private theorem mulScL {α β γ : Type} (xs : List β) (s : ComplexScalar R)
    (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    matMul xs (scaleMatrix s A) B=scaleMatrix s (matMul xs A B) := by
  funext i j; unfold matMul scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro k; grind only
private theorem mulScR {α β γ : Type} (xs : List β) (s : ComplexScalar R)
    (A : α → β → ComplexScalar R) (B : β → γ → ComplexScalar R) :
    matMul xs A (scaleMatrix s B)=scaleMatrix s (matMul xs A B) := by
  funext i j; unfold matMul scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro k; grind only
private theorem trSc {α : Type} (xs : List α) (s : ComplexScalar R) (T : α → α → ComplexScalar R) :
    trace xs (scaleMatrix s T)=s*trace xs T := (sumOverMulLeft _ _ _).symm

theorem physicalProjectedGram (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (n : Nat) :
    scaleMatrix 24 (matMul (oddWords n) (matMul (oddWords n) D (P half third)) (dagger D)) =
      rawBlock .antisymmetric (twirl n) := by
  rw [←(altWCommute half h2 n).1, W,←matMulAssoc]
  funext x y
  unfold scaleMatrix; change 24*sumOver (oddWords n) _=sumOver (oddWords n) _
  rw [sumOverMulLeft]; apply congrArg List.sum; apply List.map_congr_left; intro b hb
  have h := physicalColumnTransport half third h2 h3 x b hb
  rw [altM_mul]
  change 24*(matMul _ _ _ x b * dagger D b y)=WedgeSquareIntertwiner.alternatingWord b x*dagger D b y
  rw [←h]; grind only

private theorem idRight {α β : Type} [DecidableEq β] (xs : List β) (nd : xs.Nodup) (full : ∀ a,a∈xs)
    (T : α → β → ComplexScalar R) : matMul xs T MixedDefect.idEntry=T := by
  funext x y
  rw [←ExteriorPauliBase.sumOnIndex xs y (T x) nd (full y)]
  apply sumOverCongr; intro s; by_cases eq : s=y <;> simp [MixedDefect.idEntry,eq,Ne.symm] <;> grind only

private theorem equivComm {n : Nat} (T : TensorSite n → TensorSite n → ComplexScalar R)
    (eqv : Equivariant T) :
    matMul (sites n) T (altM n)=rawBlock .antisymmetric T := by
  have hx := fullPermuted (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  change PermutedList (sites n) at hx
  rw [altM,←blockRight _ hx _ _ _ eqv,idRight _ (sitesNodup n) sitesFull]

theorem projectedGramTensor (half : R) (h2 : 2*half=1) {n : Nat}
    (N : Basis n → Basis n → ComplexScalar R) :
    let xs := sites n
    let H := tensorFour N
    let T := twirl (R:=R) n
    let Q := rawBlock .antisymmetric T
    matMul xs (matMul xs Q H) (W n)=matMul xs (matMul xs Q H) T := by
  let xs := sites n
  let H := tensorFour N
  let J := twirl (R:=R) n
  let M := altM (R:=R) n
  have h : matMul xs M H=matMul xs H M := (altM_mul H).trans (equivComm H (tensorEquivariant N)).symm
  have wt : matMul xs M (W n)=matMul xs M J := (altWCommute half h2 n).1.trans (altM_mul J).symm
  change matMul xs (matMul xs (rawBlock .antisymmetric J) H) _ = _
  rw [←equivComm J (eqvTwirl n),matMulAssoc xs xs J M H,h,←matMulAssoc xs xs J H M]
  change matMul xs (matMul xs (matMul xs J H) M) (W n)=matMul xs (matMul xs (matMul xs J H) M) J
  rw [matMulAssoc xs xs (matMul xs J H),matMulAssoc xs xs (matMul xs J H),wt]

private theorem cycleOne {C α β : Type} [CommRing C] (xs : List α) (os : List β)
    (D : α → β → C) (E : β → α → C) (P : β → β → C) (H : α → α → C) :
    trace os (matMul os P (matMul xs E (matMul xs H D))) =
    trace xs (matMul xs (matMul os (matMul os D P) E) H) := by
  rw [←matMulAssoc xs xs E H D,←matMulAssoc os xs P,traceMatMulSwap os xs]
  simp only [matMulAssoc]

private theorem cycleTwo {C α β : Type} [CommRing C] (xs : List α) (os : List β)
    (D : α → β → C) (E : β → α → C) (P : β → β → C) (H : α → α → C) :
    let C := matMul xs E (matMul xs H D)
    trace os (matMul os P (matMul os C C)) =
    trace xs (matMul xs (matMul xs (matMul xs (matMul os (matMul os D P) E) H) (matMul os D E)) H) := by
  let C := matMul xs E (matMul xs H D)
  let T := matMul xs E H
  have h : C=matMul xs T D := (matMulAssoc xs xs E H D).symm
  change trace os (matMul os P (matMul os C C))=_
  conv => lhs; arg 2; arg 3; arg 3; rw [h]
  rw [←matMulAssoc os xs C T D,←matMulAssoc os xs P,traceMatMulSwap os xs]
  simp only [C,T,matMulAssoc]

/-- Both physical moment transports before taking real parts. The linear
identity at N² gives the overlap, the quadratic identity at N gives the
single alternating block. -/
theorem physicalTraceTransport (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    {n : Nat} (N : Basis n → Basis n → ComplexScalar R) :
    let xs := sites n
    let os := oddWords n
    let F := P (n:=n) half third
    let B := MixedDefect.hadamard (PhysicalMixedFrame.K half N)
    let H := tensorFour N
    let r := ofReal (half^n)
    let T := twirl (R:=R) n
    let Q := rawBlock .antisymmetric T
    24*trace os (matMul os F B)=r^2*trace xs (matMul xs Q H) ∧
    24*trace os (matMul os F (MixedDefect.square os B))=r^2*r^2*pairedFrameTrace xs H Q T := by
  dsimp only
  let xs := sites n
  let os := oddWords n
  let F := P (n:=n) half third
  let E := dagger (@D R _ n)
  let H := tensorFour N
  let r := ofReal (half^n)
  let T := twirl (R:=R) n
  let Q := rawBlock .antisymmetric T
  let L := matMul os (matMul os D F) E
  let C := matMul xs E (matMul xs H D)
  have b : MixedDefect.hadamard (PhysicalMixedFrame.K half N)=scaleMatrix (r^2) C := by
    funext a b; unfold scaleMatrix r C; rw [PhysicalPairedReduction.realEmbeddingPow]
    exact (PhysicalMixedFrame.doubledTensorEntry half N a b).symm
  have pl : scaleMatrix 24 L=Q := physicalProjectedGram half third h2 h3 n
  change 24*trace os (matMul os F _) = r^2*trace xs (matMul xs Q H) ∧ _ 
  constructor
  · rw [b,mulScR,trSc,cycleOne]
    change 24*(r^2*trace xs (matMul xs L H))=_
    rw [←pl,mulScL,trSc]; grind only
  · change 24*trace os (matMul os F (MixedDefect.square os _))=r^2*r^2*pairedFrameTrace xs H Q T
    rw [b,MixedDefect.square,mulScL,mulScR,mulScR,mulScR,trSc,trSc]
    change 24*(r^2*(r^2*trace os (matMul os F (matMul os C C))))=_
    rw [cycleTwo]
    have pull : trace xs (matMul xs (matMul xs (matMul xs Q H) (W n)) H)=pairedFrameTrace xs H Q T := by
      rw [projectedGramTensor half h2 N,traceMatMulSwap xs xs _ H]; simp only [pairedFrameTrace,matMulAssoc]; rfl
    rw [←pull,←pl,mulScL,mulScL,mulScL,trSc]; change 24*(r^2*(r^2*_))=r^2*r^2*(24*_)
    unfold W L E; grind only

private theorem framePull {C α β : Type} [CommRing C] (xs : List α) (src : List β)
    (U : α → β → C) (V : β → α → C) (H : β → β → C) (Q T : α → α → C) :
    pairedFrameTrace src H (matMul xs (matMul xs V Q) U) (matMul xs (matMul xs V T) U) =
      pairedFrameTrace xs (matMul src (matMul src U H) V) Q T := by
  unfold pairedFrameTrace
  rw [←matMulAssoc _ _ _ (matMul xs V T) U,traceMatMulSwap src xs]
  simp only [matMulAssoc]

private theorem scBlock {α β : Type} (s : Sector) (k : ComplexScalar R)
    (A : Four α → Four β → ComplexScalar R) :
    rawBlock s (scaleMatrix k A)=scaleMatrix k (rawBlock s A) := by
  funext i j; unfold rawBlock act scaleMatrix; rw [sumOverMulLeft]
  apply sumOverCongr; intro p; grind only

open PhysicalDefectAssembly (pairedState pairedDensity physicalSectorTerms rawSectorTrace)

theorem alternatingRawToAmbient (half : R) {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) :
    let H := tensorFour (pairedState A mu)
    let T := twirl (R:=R) n
    rawSectorTrace half A mu .antisymmetric =
      ((ofReal (half^n))^2*pairedFrameTrace (sites n) H (rawBlock .antisymmetric T) T).re := by
  let src := fourIndices (List.finRange 7)
  let xs := sites n
  let U := tensorFour A
  let V := transpose (tensorFour (ComplexPauliMoment.conjugate A))
  let H := tensorFour (PhysicalPairedReduction.diagonal mu)
  let r := ofReal (half^n)
  let T := twirl (R:=R) n
  have hx : PermutedList xs := fullPermuted _ (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  have ve : Equivariant V := fun p hp x y => tensorEquivariant _ p hp y x
  have amb : tensorFour (pairedState A mu)=matMul src (matMul src U H) V := by
    unfold pairedState; rw [←RectangularPairedReduction.rankSevenCoefficients_eq]
    exact RectangularPairedReduction.fourCoefficients _ _ _ _
  change (pairedFrameTrace src H (rawBlock .antisymmetric (scaleMatrix r (matMul xs (matMul xs V T) U)))
    (scaleMatrix r (matMul xs (matMul xs V T) U))).re = _
  rw [scBlock,blockLeft,blockRight xs hx _ V T ve,RectangularPairedReduction.pairedFrameTraceScale,framePull,←amb]
  apply congrArg ComplexScalar.re; change (r*r)*_=r^2*_; grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem cancel24 (inv24 : R) (h : 24*inv24=1) {a b : R} (e : 24*a=24*b) : a=b := by
  have t := congrArg (fun x => inv24*x) e
  change inv24*(24*a)=inv24*(24*b) at t
  rw [←Semiring.mul_assoc,←Semiring.mul_assoc,CommSemiring.mul_comm inv24 24,h,
    Semiring.one_mul,Semiring.one_mul] at t
  exact t

theorem physicalAlternatingPrice (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (h3 : 3*third=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) :
    let n := k+3
    let os := oddWords n
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    MixedDefect.realTrace os (matMul os (P half third) (MixedDefect.square os (MixedDefect.hadamard K))) =
      (physicalSectorTerms half inv24 k A mu).alternating := by
  let n := k+3
  let os := oddWords n
  let K := PhysicalMixedFrame.K half (pairedState A mu)
  let y := MixedDefect.realTrace os (matMul os (P half third) (MixedDefect.square os (MixedDefect.hadamard K)))
  let di := half^n
  let j := pairedFrameTrace (sites n) (tensorFour (pairedState A mu)) (rawBlock .antisymmetric (twirl n)) (twirl n)
  have ec := (physicalTraceTransport half third h2 h3 (pairedState A mu)).2
  rw [←PhysicalPairedReduction.realEmbeddingPow di 2] at ec
  have er := congrArg ComplexScalar.re ec
  change (ofReal (24:R)*_).re=((ofReal (di^2)*ofReal (di^2))*j).re at er
  simp only [re_mul,im_mul,ofReal,Semiring.zero_mul,Semiring.mul_zero] at er
  have price := alternatingRawToAmbient half A mu
  change rawSectorTrace half A mu .antisymmetric=((ofReal di)^2*j).re at price
  rw [←PhysicalPairedReduction.realEmbeddingPow di 2] at price
  simp only [re_mul,ofReal,Semiring.zero_mul] at price
  rw [PhysicalDefectAssembly.rawAlternatingTransport half h2] at price
  change 24*y-0= (di^2*di^2-0)*j.re-(0+0)*j.im at er
  change y=half^(n+n)*PhysicalDefectAssembly.wedgeSectorTrace half A mu
  rw [Semiring.pow_add]
  apply cancel24 inv24 h24
  change 24*y=24*(di*di*_)
  grind only

theorem physicalOverlapPrice (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1)
    (h3 : 3*third=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let n := k+3
    let os := oddWords n
    let K := PhysicalMixedFrame.K half (pairedState A mu)
    MixedDefect.realTrace os (matMul os (P half third) (MixedDefect.hadamard (MixedDefect.square os K))) =
      (physicalSectorTerms half inv24 k A mu).overlap := by
  let n := k+3
  let os := oddWords n
  let N := pairedState A mu
  let K := PhysicalMixedFrame.K half N
  let F := P (n:=n) half third
  let C := MixedDefect.hadamard (MixedDefect.square os K)
  let N2 := pairedDensity A mu
  let C' := MixedDefect.hadamard (PhysicalMixedFrame.K half N2)
  have c (a b : Word n) (hb : b∈os) : C a b=C' a b := by
    have e := PhysicalMixedFrame.KProduct half h2 N N a b hb
    rw [←PhysicalDefectAssembly.pairedDensity_eq_square A mu orth] at e
    change matMul os K K a b*matMul os K K a b=_
    rw [e]; rfl
  have trc : trace os (matMul os F C)=trace os (matMul os F C') := by
    unfold trace; apply congrArg List.sum; apply List.map_congr_left; intro a ha
    apply sumOverCongr; intro b; rw [c b a ha]
  have e := (physicalTraceTransport half third h2 h3 N2).1
  let T := twirl (R:=R) n
  let Q := rawBlock .antisymmetric T
  let H := tensorFour N2
  let di := half^n
  change 24*trace os (matMul os F C')=(ofReal di)^2*trace (sites n) (matMul (sites n) Q H) at e
  rw [←trc,←PhysicalPairedReduction.realEmbeddingPow di 2] at e
  have paid := AntiDefectTransport.ambientAlternatingOverlap half inv24 h2 k A mu
  rw [AntiDefectTransport.wordFrameFactor,blockLeft] at paid
  let overlap := (physicalSectorTerms half inv24 k A mu).overlap
  let d := (2:R)^n
  change (trace (sites n) (matMul (sites n) Q H)).re=24*d^2*overlap at paid
  let u := MixedDefect.realTrace os (matMul os F C)
  have er := congrArg ComplexScalar.re e
  change (ofReal (24:R)*trace os (matMul os F C)).re = (ofReal (di^2)*_).re at er
  simp only [re_mul,ofReal,Semiring.zero_mul,paid] at er
  change 24*u-0=di^2*(24*d^2*overlap)-0 at er
  change u=overlap
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  apply cancel24 inv24 h24
  calc
    _ = di^2*(24*d^2*overlap) := by grind only
    _ = (d*di)*(d*di)*(24*overlap) := by grind only
    _ = _ := by rw [inv,Semiring.one_mul,Semiring.one_mul]

end Order
end RankSeven.MixedTransport

#print axioms RankSeven.MixedTransport.physicalColumnTransport
#print axioms RankSeven.MixedTransport.physicalTraceTransport
#print axioms RankSeven.MixedTransport.physicalAlternatingPrice
#print axioms RankSeven.MixedTransport.physicalOverlapPrice
