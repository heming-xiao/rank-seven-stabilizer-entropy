import Rank7JointProbePayment

/-! Polarized alternating overlap of two physical exterior-square probes. -/
namespace RankSeven.ProjectedProbeOverlap
open Lean.Grind Pauli ComplexScalar MixedDefect PhysicalMixedFrame FourCopySectors
open PhysicalPairedReduction (diagonal dagger fourWeights)
open PhysicalDefectAssembly (pairedState pairedDensity)
open JointProbePayment (entryProduct pairSpectrum)
open GenericExteriorKernel (reorder)
open ExteriorPauliBase (permutations)
open ExteriorCuts (wedges Wedge7)
variable {R α : Type} [CommRing R]
local instance : IntCast (ComplexScalar R) := Ring.intCast
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def twoByTwo {C α β : Type} [CommRing C] (M N : α → β → C) :=
  tensor (tensor M M) (tensor N N)

/-- The two pairs of tensor slots can carry different physical matrices. -/
theorem doubledMixedEntry (half : R) {n : Nat} (M N : Basis n → Basis n → ComplexScalar R) :
    let xs := MixedTransport.sites n
    let D := @MixedTransport.D R _ n
    RectangularPairedReduction.scaleMatrix ((ofReal half ^ n)^2)
      (matMul xs (dagger D) (matMul xs (twoByTwo M N) D)) =
      entryProduct (K half M) (K half N) := by
  dsimp only
  funext a b
  let ps := pairs n
  let L (r : Pair n) := dual (R:=R) a r
  let V (r : Pair n) := form (R:=R) r b
  let F (T : Basis n → Basis n → ComplexScalar R) (x : Pair n) :=
    sumOver ps (fun y => tensor T T x y*V y)
  have inner (x : Four (Basis n)) : matMul (MixedTransport.sites n) (twoByTwo M N) MixedTransport.D x b =
      F M x.1*F N x.2 := by
    refine (sumOverCongr _ (g:=fun y => (tensor M M x.1 y.1*V y.1)*(tensor N N x.2 y.2*V y.2)) (fun y => ?_)).trans ?_
    · change (_*_)*(V y.1*V y.2)=_; grind only
    · exact factorProductSum ps ps (fun y => tensor M M x.1 y*V y) (fun y => tensor N N x.2 y*V y)
  have outer : sumOver (MixedTransport.sites n) (fun x => star (doubledWord (R:=R) a x)*(F M x.1*F N x.2)) =
      (sumOver ps (fun x => L x*F M x))*(sumOver ps (fun x => L x*F N x)) := by
    refine (sumOverCongr _ (g:=fun x => (L x.1*F M x.1)*(L x.2*F N x.2)) (fun x => ?_)).trans ?_
    · have c (x : Pair n) : star (form (R:=R) x a)=L x := ComplexPauliMoment.wordHermitian a x.1 x.2
      simp only [doubledWord,star_mul,c]; grind only
    · exact factorProductSum ps ps (fun x => L x*F M x) (fun x => L x*F N x)
  change (ofReal half^n)^2 * sumOver (MixedTransport.sites n) (fun x => star (doubledWord a x)*_) = _
  simp only [inner,outer]
  change (ofReal half^n)^2 * (_*_) = (ofReal half^n * sumOver ps (fun x => L x*F M x))*
    (ofReal half^n * sumOver ps (fun x => L x*F N x))
  grind only

private theorem scaledTrace {C α β : Type} [CommRing C] (xs : List α) (ys : List β)
    (a b : C) (P : α → α → C) (D : β → α → C) (E : α → β → C) (H : β → β → C) :
    a*trace xs (matMul xs P (fun i j => b*matMul ys E (matMul ys H D) i j)) =
    b*trace ys (matMul ys (fun i j => a*matMul xs (matMul xs D P) E i j) H) := by
  have cyc : trace xs (matMul xs P (matMul ys E (matMul ys H D))) =
      trace ys (matMul ys (matMul xs (matMul xs D P) E) H) := by
    rw [←matMulAssoc ys ys E H D,←matMulAssoc xs ys P,traceMatMulSwap xs ys]
    simp only [matMulAssoc]
  have left : trace xs (matMul xs P (fun i j => b*matMul ys E (matMul ys H D) i j)) =
      b*trace xs (matMul xs P (matMul ys E (matMul ys H D))) := by
    unfold trace matMul; simp only [sumOverMulLeft]
    apply sumOverCongr; intro i; apply sumOverCongr; intro j; grind only
  have right : trace ys (matMul ys (fun i j => a*matMul xs (matMul xs D P) E i j) H) =
      a*trace ys (matMul ys (matMul xs (matMul xs D P) E) H) := by
    let Z := matMul xs (matMul xs D P) E
    change sumOver ys (fun i => sumOver ys (fun j => (a*Z i j)*H j i))=a*sumOver ys (fun i => sumOver ys (fun j => Z i j*H j i))
    rw [sumOverMulLeft]; apply sumOverCongr; intro i; rw [sumOverMulLeft]; apply sumOverCongr; intro j; grind only
  rw [left,right,cyc]; grind only

theorem physicalProjectedTrace (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) {n : Nat}
    (M N : Basis n → Basis n → ComplexScalar R) :
    let xs := MixedTransport.sites n
    let os := oddWords n
    24*trace os (matMul os (MixedTransport.P half third) (entryProduct (K half M) (K half N))) =
      ((ofReal half)^n)^2*trace xs (matMul xs (rawBlock .antisymmetric (MixedTransport.twirl n)) (twoByTwo M N)) := by
  dsimp only
  rw [←doubledMixedEntry,←MixedTransport.physicalProjectedGram half third h2 h3]
  apply scaledTrace

local instance (n : Nat) : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

private theorem tensorPush {C α β : Type} [CommRing C] (src : List β) (A : α → β → C) (G : β → α → C)
    (M N : β → β → C) :
    twoByTwo (matMul src A (matMul src M G)) (matMul src A (matMul src N G)) =
    matMul (fourIndices src) (tensorFour A) (matMul (fourIndices src) (twoByTwo M N) (tensorFour G)) := by
  simp only [twoByTwo,tensorFour,fourIndices,tensorMatMul]

theorem physicalTraceToSource {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (a b : Fin 7 → R) :
    let xs := MixedTransport.sites n
    let src := fourIndices (List.finRange 7)
    trace xs (matMul xs (rawBlock .antisymmetric (MixedTransport.twirl n))
      (twoByTwo (pairedState A a) (pairedState A b))) =
      trace src (matMul src (rawBlock .antisymmetric (PhysicalPairedReduction.frameTwirl A))
        (twoByTwo (diagonal a) (diagonal b))) := by
  let xs := MixedTransport.sites n
  let src := fourIndices (List.finRange 7)
  let U := tensorFour A
  let V := tensorFour (dagger A)
  let T := MixedTransport.twirl (R:=R) n
  let H := twoByTwo (diagonal a) (diagonal b)
  have h (v : Fin 7 → R) : pairedState A v=matMul (List.finRange 7) A (matMul (List.finRange 7) (diagonal v) (dagger A)) := by
    unfold pairedState; rw [←RectangularPairedReduction.rankSevenCoefficients_eq]; apply matMulAssoc
  have frame : PhysicalPairedReduction.frameTwirl A = matMul xs V (matMul xs T U) := by
    unfold PhysicalPairedReduction.frameTwirl V T U xs MixedTransport.sites MixedTransport.twirl dagger
    rw [fourTranspose,matMulAssoc]
  have full := fullPermuted (qubitIndices n) (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n)
  dsimp only; rw [h,h,tensorPush,frame,blockRight xs full .antisymmetric V _ (tensorEquivariant _),blockLeft]
  change trace xs (matMul xs (rawBlock .antisymmetric T) (matMul src U (matMul src H V)))=_
  rw [←matMulAssoc xs src,←matMulAssoc src src,traceMatMulSwap xs src]; simp only [matMulAssoc]; rfl


private theorem realSum {T : Type} (xs : List T) (f : T → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun x => (f x).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=_; rw [re_add,ih]; rfl

private theorem sumPerm {T : Type} {xs ys : List T} (p : xs.Perm ys) (f : T → R) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ h k => exact h.trans k

def firstPairWeight (a b : α → R) (x : Four α) := a x.1.1*a x.1.2*(b x.2.1*b x.2.2)

/-- Each choice of two slots for the first spectrum occurs once. -/
def sixWeights (a b : α → R) (x : Four α) : R :=
  firstPairWeight a b x +
  firstPairWeight a b (reorder x ((0,2),(1,3))) +
  firstPairWeight a b (reorder x ((0,3),(1,2))) +
  firstPairWeight a b (reorder x ((1,2),(0,3))) +
  firstPairWeight a b (reorder x ((1,3),(0,2))) +
  firstPairWeight a b (reorder x ((2,3),(0,1)))

private theorem weightExpansion (a b : α → R) (x : Four α) :
    fourWeights (fun i => a i+b i) x+fourWeights (fun i => a i-b i) x-
    2*fourWeights a x-2*fourWeights b x=2*sixWeights a b x := by
  rcases x with ⟨⟨v,w⟩,y,z⟩
  change ((a v+b v)*(a w+b w))*((a y+b y)*(a z+b z))+((a v-b v)*(a w-b w))*((a y-b y)*(a z-b z))-
    2*((a v*a w)*(a y*a z))-2*((b v*b w)*(b y*b z))=
    2*(a v*a w*(b y*b z)+a v*a y*(b w*b z)+a v*a z*(b w*b y)+a w*a y*(b v*b z)+a w*a z*(b v*b y)+a y*a z*(b v*b w))
  grind only

private def src := fourIndices (List.finRange 7)

private theorem altDiagonalSymm (T : Four α → Four α → ComplexScalar R) (e : Equivariant T)
    (x : Four α) (p : Perm) (hp : p∈permutations) :
    rawBlock .antisymmetric T (reorder x p) (reorder x p)=rawBlock .antisymmetric T x x := by
  rw [AlternatingTrace.alternatingColumn T e _ x p hp]
  change Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p) * act _ _ (reorder x p)=_
  rw [AlternatingTrace.alternatingRow _ p hp]
  have u : Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p)*Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p)=1 := by
    unfold coefficient; cases ExteriorPauliBase.oddPermutation p <;> simp <;> grind only
  rw [←Semiring.mul_assoc,u,Semiring.one_mul]; rfl

private theorem sumSix (a b : Fin 7 → R) (f : Four (Fin 7) → R)
    (h : ∀ x p, p∈permutations → f (reorder x p)=f x) :
    sumOver src (fun x => sixWeights a b x*f x)=6*sumOver src (fun x => firstPairWeight a b x*f x) := by
  have perm (p : Perm) (hp : p∈permutations) :
      sumOver src (fun x => firstPairWeight a b (reorder x p)*f x)=sumOver src (fun x => firstPairWeight a b x*f x) := by
    have e := sumPerm (fullPermuted (List.finRange 7) (List.nodup_finRange 7) (fun i => List.mem_finRange i) p hp)
      (fun x => firstPairWeight a b x*f x)
    simpa only [sumOver,List.map_map,Function.comp_def,h _ p hp,src] using e
  simp only [sixWeights,Semiring.right_distrib,sumOverAdd]
  rw [perm _ (by decide : ((0,2),(1,3))∈permutations),perm _ (by decide : ((0,3),(1,2))∈permutations),
    perm _ (by decide : ((1,2),(0,3))∈permutations),perm _ (by decide : ((1,3),(0,2))∈permutations),
    perm _ (by decide : ((2,3),(0,1))∈permutations)]
  grind only

private theorem embMul (s t : R) : ofReal (s*t)=ofReal s*ofReal t := by
  apply ComplexScalar.ext <;> simp <;> grind only

private theorem tensorPairDiagonal (a b : Fin 7 → R) :
    twoByTwo (diagonal a) (diagonal b)=diagonal (firstPairWeight a b) := by
  funext u v
  rcases u with ⟨⟨u₀,u₁⟩,u₂,u₃⟩
  rcases v with ⟨⟨v₀,v₁⟩,v₂,v₃⟩
  simp only [twoByTwo,tensor,diagonal,firstPairWeight,Prod.mk.injEq]
  by_cases q : u₀=v₀ <;> by_cases r : u₁=v₁ <;> by_cases s : u₂=v₂ <;> by_cases t : u₃=v₃ <;>
    simp [q,r,s,t,embMul,Semiring.mul_zero,Semiring.zero_mul]

private theorem traceDiag (w : Four (Fin 7) → R) (A : Four (Fin 7) → Four (Fin 7) → ComplexScalar R) :
    (trace src (matMul src A (diagonal w))).re = sumOver src (fun x => w x*(A x x).re) := by
  let ps := productIndices (List.finRange 7) (List.finRange 7)
  have pnd := HyperplaneInduction.pairsNodup _ _ (List.nodup_finRange 7) (List.nodup_finRange 7)
  have nd : src.Nodup := HyperplaneInduction.pairsNodup ps ps pnd pnd
  have full (x : Four (Fin 7)) : x∈src := HyperplaneInduction.pairMember
    (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
    (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
  rw [traceMatMulSwap src src]; unfold trace; rw [realSum]
  apply sumOverCongr; intro x; rw [PhysicalPairedReduction.diagonalAction _ nd _ _ x x (full x)]
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

private theorem expandedSum {T : Type} (xs : List T) (u : T → Four (Fin 7)) (a b : Fin 7 → R) (f : T → R) :
    let Q v := sumOver xs (fun y => fourWeights v (u y)*f y)
    Q (fun i => a i+b i)+Q (fun i => a i-b i)-2*Q a-2*Q b=2*sumOver xs (fun y => sixWeights a b (u y)*f y) := by
  dsimp only
  rw [sumOverMulLeft,sumOverMulLeft,sumOverMulLeft,←sumOverAdd,←Compression.sumOverSub,←Compression.sumOverSub]
  apply sumOverCongr; intro y
  have eq := congrArg (fun z => z*f y) (weightExpansion a b (u y)); grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The alternating trace for two independent diagonal spectra: each sorted
wedge carries the six unordered choices of the two slots occupied by a. -/
theorem sortedMixedTrace (a b : Fin 7 → R) (T : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (eqv : Equivariant T) :
    (trace src (matMul src (rawBlock .antisymmetric T) (twoByTwo (diagonal a) (diagonal b)))).re =
      4*sumOver wedges (fun w => sixWeights a b (FrameExteriorSector.sourceTuple w)*(FrameExteriorSector.exteriorSector T w w).re) := by
  let f x := (rawBlock .antisymmetric T x x).re
  let g (w : Wedge7) := (FrameExteriorSector.exteriorSector T w w).re
  let S v := sumOver src (fun x => fourWeights v x*f x)
  let W v := sumOver wedges (fun w => fourWeights v (FrameExteriorSector.sourceTuple w)*g w)
  have q (v : Fin 7 → R) : S v=24*W v := by
    have e := congrArg ComplexScalar.re (AlternatingTrace.alternatingOverlapToWedges v T eqv)
    change (trace src (matMul src (rawBlock .antisymmetric T) (tensorFour (diagonal v)))).re =
      ((ofReal (24:R))*sumOver wedges (fun w => ofReal (fourWeights v (FrameExteriorSector.sourceTuple w))*FrameExteriorSector.exteriorSector T w w)).re at e
    have sub (r : R) : r-0=r := by grind only
    simp only [PhysicalPairedReduction.tensorDiagonal,traceDiag,re_mul,re_ofReal,im_ofReal,Semiring.zero_mul,
      sub,realSum] at e
    exact e
  have x := expandedSum src id a b f
  have y := expandedSum wedges FrameExteriorSector.sourceTuple a b g
  change S _+S _-2*S a-2*S b=2*sumOver src (fun x => sixWeights a b x*f x) at x
  change W _+W _-2*W a-2*W b=2*sumOver wedges (fun w => sixWeights a b (FrameExteriorSector.sourceTuple w)*g w) at y
  rw [sumSix a b f (fun x p hp => congrArg ComplexScalar.re (altDiagonalSymm T eqv x p hp))] at x
  simp only [q] at x
  rw [tensorPairDiagonal,traceDiag]
  change sumOver src (fun x => firstPairWeight a b x*f x)=4*sumOver wedges (fun w => sixWeights a b (FrameExteriorSector.sourceTuple w)*g w)
  grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem frameFactor {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (w : Wedge7) :
    (FrameExteriorSector.exteriorSector (RectangularPairedReduction.normalizedFrame half A) w w).re=
    half^n*(FrameExteriorSector.exteriorSector (PhysicalPairedReduction.frameTwirl A) w w).re := by
  unfold RectangularPairedReduction.normalizedFrame RectangularPairedReduction.scaleMatrix
  rw [FrameExteriorSector.exteriorSector_scale]
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

/-- Trace of the true physical projector against two exterior squares, for
independent real source spectra on an arbitrary complex seven-column frame. -/
theorem physicalWeightedTrace (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (a b : Fin 7 → R) :
    let n := k+3
    let os := oddWords n
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    3*(2:R)^n*realTrace os (matMul os (MixedTransport.P half third)
      (entryProduct (K half (pairedState A a)) (K half (pairedState A b))))=
      2*sumOver wedges (fun w => sixWeights a b (FrameExteriorSector.sourceTuple w)*E.realPart w w) := by
  let n := k+3
  let d := (2:R)^n
  let di := half^n
  let os := oddWords n
  let F := PhysicalPairedReduction.frameTwirl A
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let B := entryProduct (K half (pairedState A a)) (K half (pairedState A b))
  let u := realTrace os (matMul os (MixedTransport.P half third) B)
  let wt := fun w => sixWeights a b (FrameExteriorSector.sourceTuple w)
  let e (w : Wedge7) := (FrameExteriorSector.exteriorSector F w w).re
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have fa (w : Wedge7) : di*e w=4*E.realPart w w := by
    have f := frameFactor half A w
    rw [FrameExteriorSector.normalizedFrameSector_eq_four_effectEntry half h2] at f
    change (4:R)*E.realPart w w-0*(E.imagPart w w)=di*e w at f; grind only
  have eq := physicalProjectedTrace half third h2 h3 (pairedState A a) (pairedState A b)
  dsimp only at eq
  rw [physicalTraceToSource A a b,←PhysicalPairedReduction.realEmbeddingPow half n,
    ←PhysicalPairedReduction.realEmbeddingPow (half^n) 2] at eq
  have re := congrArg ComplexScalar.re eq
  change (24:R)*u-0*_=di^2*(trace src (matMul src (rawBlock .antisymmetric F) (twoByTwo (diagonal a) (diagonal b)))).re-0*_ at re
  rw [sortedMixedTrace a b F (frameStructure A).1] at re
  change 24*u-0*_=di^2*(4*sumOver wedges (fun w => wt w*e w))-0*_ at re
  have eqw : di*sumOver wedges (fun w => wt w*e w)=4*sumOver wedges (fun w => wt w*E.realPart w w) := by
    rw [sumOverMulLeft,sumOverMulLeft]; apply sumOverCongr; intro w
    have p := congrArg (fun z => wt w*z) (fa w); grind only
  have r : 24*u = 4*di*(di*sumOver wedges (fun w => wt w*e w)) := by grind only
  rw [eqw] at r
  have mul := congrArg (fun z => d*z) r
  change 3*d*u=2*sumOver wedges (fun w => wt w*E.realPart w w)
  calc
    _ = (d*di)*(2*sumOver wedges (fun w => wt w*E.realPart w w)) := by grind
    _ = _ := by rw [inv,Semiring.one_mul]

/-- One term of the weighted four-wedge sum: the selected pair must be the
probe edge, and the other two weights enter as their product. -/
def complementaryPair (i j u v : Fin 7) (r : R) : R :=
  if (u=i ∧ v=j) ∨ (u=j ∧ v=i) then r else 0

def complementaryWeight (i j : Fin 7) (t : Fin 7 → R) (w : Wedge7) : R :=
  complementaryPair i j w.i w.j (t w.k*t w.m)+
  complementaryPair i j w.i w.k (t w.j*t w.m)+
  complementaryPair i j w.i w.m (t w.j*t w.k)+
  complementaryPair i j w.j w.k (t w.i*t w.m)+
  complementaryPair i j w.j w.m (t w.i*t w.k)+
  complementaryPair i j w.k w.m (t w.i*t w.j)

def weightedFourWedge (i j : Fin 7) (t : Fin 7 → R) (diag : Wedge7 → R) : R :=
  sumOver wedges (fun w => complementaryWeight i j t w*diag w)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem complementaryTerm (i j u v : Fin 7) (h : u≠v) (r : R) :
    pairSpectrum i j u*pairSpectrum i j v*r=complementaryPair i j u v r := by
  unfold pairSpectrum complementaryPair
  split <;> split <;> split <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem pairWeightOnWedge (i j : Fin 7) (t : Fin 7 → R) (w : Wedge7) :
    sixWeights (pairSpectrum i j) t (FrameExteriorSector.sourceTuple w)=complementaryWeight i j t w := by
  rcases w with ⟨a,b,c,d,ab,bc,cd⟩
  have h1 : a≠b := by omega
  have h2 : a≠c := by omega
  have h3 : a≠d := by omega
  have h4 : b≠c := by omega
  have h5 : b≠d := by omega
  have h6 : c≠d := by omega
  unfold sixWeights complementaryWeight
  change pairSpectrum i j a*pairSpectrum i j b*_+pairSpectrum i j a*pairSpectrum i j c*_+
    pairSpectrum i j a*pairSpectrum i j d*_+pairSpectrum i j b*pairSpectrum i j c*_+
    pairSpectrum i j b*pairSpectrum i j d*_+pairSpectrum i j c*pairSpectrum i j d*_=_
  rw [complementaryTerm i j a b h1,complementaryTerm i j a c h2,complementaryTerm i j a d h3,
    complementaryTerm i j b c h4,complementaryTerm i j b d h5,complementaryTerm i j c d h6]
  rfl

/-- Exact manuscript normalization: three times the dimension times the
mixed projected trace is twice the weighted sum W_ij. No orthogonality
or spectral sign assumption is needed for this identity. -/
theorem physicalPairWedgeOverlap (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (i j : Fin 7) (t : Fin 7 → R) :
    let os := oddWords (k+3)
    let B := K half (pairedState A (pairSpectrum i j))
    let C := K half (pairedState A t)
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    3*(2:R)^(k+3)*realTrace os (matMul os (MixedTransport.P half third) (entryProduct B C))=
      2*weightedFourWedge i j t (fun w => E.realPart w w) := by
  simpa only [pairWeightOnWedge,weightedFourWedge] using physicalWeightedTrace half third h2 h3 k A (pairSpectrum i j) t

/-- The physical matching polarization is exactly the spectral baseline plus
W_ij minus the normalized sum of pair weights times the matching score. -/
theorem pairPaymentIdentity (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (i j : Fin 7) (ne : i≠j) :
    let n := k+3
    let os := oddWords n
    let t := fun v => (mu v)^2
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    2*JointProbePayment.hs os (JointProbePayment.pairCoordinates half A i j) (JointProbePayment.densityCoordinates half A mu) =
      t i*t j+weightedFourWedge i j t (fun w => E.realPart w w)-
      2*half^n*sumOver os (fun p => JointProbePayment.pairWeight A p i j*JointProbePayment.matchingScore A t p) := by
  have pol := JointProbePayment.physicalMatchingPolarization half third h2 h3 A mu orth i j ne
  dsimp only at pol ⊢
  unfold pairedDensity at pol
  rw [physicalPairWedgeOverlap half third h2 h3 k A i j] at pol
  grind

end Order

end RankSeven.ProjectedProbeOverlap

#print axioms RankSeven.ProjectedProbeOverlap.physicalProjectedTrace
#print axioms RankSeven.ProjectedProbeOverlap.sortedMixedTrace
#print axioms RankSeven.ProjectedProbeOverlap.physicalWeightedTrace
#print axioms RankSeven.ProjectedProbeOverlap.physicalPairWedgeOverlap
#print axioms RankSeven.ProjectedProbeOverlap.pairPaymentIdentity
