import Rank7ProjectedProbeOverlap

/-! Exact real Gram matrix of the highest-edge and joint physical probes. -/
namespace RankSeven.JointProbeGram
open Lean.Grind Pauli ComplexScalar PhysicalMixedFrame MixedDefect JointProbePayment ProjectedProbeOverlap
open PhysicalDefectAssembly (pairedState pairedDensity)
open ExteriorCuts (wedges Wedge7)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def oddAverage (half : R) {n : Nat} (f : Word n → R) := 2*half^n*sumOver (oddWords n) f

private theorem maskSquared (i j : Fin 7) :
    (fun v => (pairSpectrum (R:=R) i j v)^2)=pairSpectrum i j := by
  funext v; unfold pairSpectrum; split <;> grind only

private theorem maskSelf (i j : Fin 7) : pairSpectrum (R:=R) i j i=1 ∧ pairSpectrum (R:=R) i j j=1 := by
  simp [pairSpectrum]

private theorem zeroMixedTerm (i j k a b c d : Fin 7)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    complementaryPair i j a b (pairSpectrum (R:=R) i k c*pairSpectrum i k d)=0 := by
  unfold complementaryPair pairSpectrum
  split
  · split <;> split <;> grind only
  · rfl

private theorem sharedWeightZero (i j k : Fin 7) (w : Wedge7) :
    complementaryWeight i j (pairSpectrum (R:=R) i k) w=0 := by
  rcases w with ⟨a,b,c,d,ab,bc,cd⟩
  unfold complementaryWeight
  simp only
  rw [zeroMixedTerm i j k a b c d (by omega) (by omega) (by omega) (by omega) (by omega),
      zeroMixedTerm i j k a c b d (by omega) (by omega) (by omega) (by omega) (by omega),
      zeroMixedTerm i j k a d b c (by omega) (by omega) (by omega) (by omega) (by omega),
      zeroMixedTerm i j k b c a d (by omega) (by omega) (by omega) (by omega) (by omega),
      zeroMixedTerm i j k b d a c (by omega) (by omega) (by omega) (by omega) (by omega),
      zeroMixedTerm i j k c d a b (by omega) (by omega) (by omega) (by omega) (by omega)]
  grind only

theorem sharedExteriorZero (i j k : Fin 7) (w : Wedge7 → R) :
    weightedFourWedge i j (pairSpectrum i k) w=0 := by
  unfold weightedFourWedge
  simp only [sharedWeightZero,Semiring.zero_mul]
  have zero {T : Type} (xs : List T) : sumOver xs (fun _ => (0:R))=0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
  exact zero _

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem matchingScorePair {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (i j : Fin 7) (ne : i≠j) (p : Word n) (hp : p∈oddWords n) :
    matchingScore A (pairSpectrum i j) p=pairWeight A p i j := by
  have h := physicalMatchingScore half A (pairSpectrum i j) p hp
  rw [physicalPairWeight half A i j ne p hp] at h
  have s := congrArg ComplexScalar.re h
  have d := SectorDefectAccounting.dimensionInverse half h2 n
  change 2*half^n*pairWeight A p i j=2*half^n*matchingScore A (pairSpectrum i j) p at s
  have e := congrArg (fun v => (2:R)^n*v) s
  have normalize (v : R) : (2:R)^n*(2*half^n*v)=2*v := by
    calc
      _ = ((2:R)^n*half^n)*(2*v) := by grind only
      _ = _ := by rw [d,Semiring.one_mul]
  simp only [normalize] at e; grind

/-- Two exterior-square projector probes sharing an index have zero
four-form overlap. Their real Gram therefore contains only the common
spectral coordinate and the odd-Pauli diagonal matching moment. -/
theorem pairGramShared (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (i j l : Fin 7) (ij : i≠j) (il : i≠l) :
    let n := k+3
    let os := oddWords n
    2*hs os (pairCoordinates half A i j) (pairCoordinates half A i l)=
      (if j=l then 1 else 0)-oddAverage half (fun p => pairWeight A p i j*pairWeight A p i l) := by
  let n := k+3
  let os := oddWords n
  let b := pairSpectrum (R:=R) i l
  have e := pairPaymentIdentity half third h2 h3 k A b orth i j ij
  dsimp only at e ⊢
  have dens : densityCoordinates half A b=pairCoordinates half A i l := by
    unfold densityCoordinates pairCoordinates pairedDensity b; rw [maskSquared]
  have spec : b i^2*b j^2=(if j=l then 1 else 0) := by
    change (pairSpectrum i l i)^2*(pairSpectrum i l j)^2=_
    rw [(maskSelf i l).1]; unfold pairSpectrum; by_cases same : j=l <;> simp [same,Ne.symm ij] <;> grind only
  change 2*hs os (pairCoordinates half A i j) (densityCoordinates half A b) =
    b i^2*b j^2+weightedFourWedge i j (fun v => (pairSpectrum i l v)^2) _-
    2*half^n*sumOver os (fun p => pairWeight A p i j*matchingScore A (fun v => (pairSpectrum i l v)^2) p) at e
  rw [dens,spec,maskSquared,sharedExteriorZero] at e
  have scores : sumOver os (fun p => pairWeight A p i j*matchingScore A (pairSpectrum i l) p)=
      sumOver os (fun p => pairWeight A p i j*pairWeight A p i l) := by
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    rw [matchingScorePair half h2 A i l il p hp]
  rw [scores] at e; unfold oddAverage; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem realSum {T : Type} (xs : List T) (f : T → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun y => (f y).re) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change (f x+sumOver xs f).re=_; rw [re_add,ih]; rfl

/-- The normalized first moment of every true pair weight is exactly one. -/
theorem pairWeightAverage {n : Nat} (half : R) (h2 : 2*half=1)
    (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (i j : Fin 7) (ne : i≠j) : oddAverage half (fun p => pairWeight A p i j)=1 := by
  let os := oddWords n
  let b := pairSpectrum (R:=R) i j
  let X := pairedState A b
  let B := K half X
  have e := pairBaseline half h2 A b orth i j ne
  have sq (p : Word n) (hp : p∈os) : matMul os B B p p=B p p := by
    have p2 := KProduct half h2 X X p p hp
    change matMul os B B p p=K half (matMul (qubitIndices n) X X) p p at p2
    rw [pairProjectionIdempotent A i j orth] at p2; exact p2
  have c : pairedDensity A b=X := by unfold pairedDensity b X; rw [maskSquared]
  dsimp only at e
  rw [c] at e
  dsimp only [b] at e
  rw [(maskSelf i j).1,(maskSelf i j).2] at e
  change (sumOver os (fun p => matMul os B B p p)).re=1^2*1^2 at e
  rw [realSum] at e
  have t : sumOver os (fun p => (matMul os B B p p).re)=oddAverage half (fun p => pairWeight A p i j) := by
    unfold oddAverage; rw [sumOverMulLeft]
    apply congrArg List.sum; apply List.map_congr_left; intro p hp
    rw [sq p hp]; change (K half (pairedState A (pairSpectrum i j)) p p).re=_
    rw [physicalPairWeight half A i j ne p hp,re_ofReal]
  rw [t] at e; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgAdd (half : R) {n : Nat} (f g : Word n → R) :
    oddAverage half (fun p => f p+g p)=oddAverage half f+oddAverage half g := by
  unfold oddAverage; rw [sumOverAdd]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgSub (half : R) {n : Nat} (f g : Word n → R) :
    oddAverage half (fun p => f p-g p)=oddAverage half f-oddAverage half g := by
  unfold oddAverage; rw [Compression.sumOverSub]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem complementMoment (half : R) {n : Nat} (f g : Word n → R) :
    oddAverage half (fun p => f p*(1-g p))=oddAverage half f-oddAverage half (fun p => f p*g p) := by
  rw [←avgSub]
  apply congrArg (oddAverage half); funext p; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem hsAddLeft {T : Type} (xs : List T) (f g h : T×T → R) :
    hs xs (fun p => f p+g p) h=hs xs f h+hs xs g h := by
  unfold hs; simp only [Semiring.right_distrib,sumOverAdd]; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem hsAddRight {T : Type} (xs : List T) (f g h : T×T → R) :
    hs xs f (fun p => g p+h p)=hs xs f g+hs xs f h := by
  unfold hs; simp only [Semiring.left_distrib,sumOverAdd]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem gramReverse {T : Type} (xs : List T) (f g : T×T → R) : hs xs f g=hs xs g f := by
  unfold hs; apply congrArg (fun z => 2*z); apply sumOverCongr; intro p; grind only

/-- The three Gram entries of the actual common-leading-label pair probes
are the manuscript's κ, κ₁, and c₁, all with the same normalized Pauli sum. -/
theorem physicalJointGram (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let os := oddWords (k+3)
    let u := sharedProbe half A
    let v := pairCoordinates half A 0 1
    let p₁ := fun p => pairWeight A p 0 1
    let p := fun x => p₁ x+pairWeight A x 0 2
    2*hs os u u=oddAverage half (fun x => p x*(1-p x)) ∧
    2*hs os v v=oddAverage half (fun x => p₁ x*(1-p₁ x)) ∧
    2*hs os u v=oddAverage half (fun x => p₁ x*(1-p x)) := by
  let os := oddWords (k+3)
  let U := pairCoordinates half A 0 1
  let V := pairCoordinates half A 0 2
  let P x := pairWeight A x 0 1
  let Q x := pairWeight A x 0 2
  let M (f g : Word (k+3) → R) := oddAverage half (fun x => f x*g x)
  have u : 2*hs os U U=1-M P P := pairGramShared half third h2 h3 k A orth 0 1 1 (by decide) (by decide)
  have v : 2*hs os V V=1-M Q Q := pairGramShared half third h2 h3 k A orth 0 2 2 (by decide) (by decide)
  have uv : 2*hs os U V=0-M P Q := pairGramShared half third h2 h3 k A orth 0 1 2 (by decide) (by decide)
  have p : oddAverage half P=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have q : oddAverage half Q=1 := pairWeightAverage half h2 A orth 0 2 (by decide)
  let S x := P x+Q x
  have av : oddAverage half S=2 := by change oddAverage half (fun x => P x+Q x)=_; rw [avgAdd,p,q]; grind only
  have ss : M S S=M P P+M P Q+(M P Q+M Q Q) := by
    have a (x) : S x*S x=(P x*P x+P x*Q x)+(P x*Q x+Q x*Q x) := by dsimp only [S]; grind only
    dsimp only [M]; simp only [a,avgAdd]
  have ps : M P S=M P P+M P Q := by
    dsimp only [M,S]; rw [←avgAdd]; apply congrArg (oddAverage half); funext x; grind only
  change 2*hs os (fun x => U x+V x) (fun x => U x+V x)=oddAverage half (fun x => S x*(1-S x)) ∧
    2*hs os U U=oddAverage half (fun x => P x*(1-P x)) ∧
    2*hs os (fun x => U x+V x) U=oddAverage half (fun x => P x*(1-S x))
  simp only [hsAddLeft,hsAddRight,gramReverse os V U,complementMoment,av,p]
  change _=2-M S S ∧ _=1-M P P ∧ _=1-M P S
  rw [ss,ps]; exact ⟨by grind only,u,by grind only⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgMul (half c : R) {n : Nat} (f : Word n → R) :
    oddAverage half (fun x => c*f x)=c*oddAverage half f := by
  unfold oddAverage; rw [←sumOverMulLeft]; grind only

private theorem avgLe (half : R) (h2 : 2*half=1) {n : Nat} {f g : Word n → R} (h : ∀ p∈oddWords n, f p≤g p) :
    oddAverage half f ≤ oddAverage half g := by
  have pos := Compression.sumOverNonnegative (oddWords n) (fun x => g x-f x) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at pos
  have hh : 0≤half := by grind only
  have hn (m : Nat) : 0≤half^m := by
    induction m with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hh
  have sc : 0≤2*half^n := by have := hn n; grind only
  exact OrderedRing.mul_le_mul_of_nonneg_left (by grind only) sc

def highPrice (t : Fin 7 → R) := t 0*t 1+t 2*t 3+t 4*t 5
def secondPrice (t : Fin 7 → R) := t 0*t 2+t 1*t 3+t 4*t 5
def leadingGap (t : Fin 7 → R) := (t 1-t 2)*(t 0-t 3)
def sharedGap (t : Fin 7 → R) := (t 0-t 1)*(t 2-t 3)
def emptyGap (t : Fin 7 → R) := (t 1-t 5)*(t 2-t 4)
def tailGap (t : Fin 7 → R) := t 4*(t 5-t 6)
def referencePair (t : Fin 7 → R) := t 2*t 3+t 4*t 5
def referenceShared (t : Fin 7 → R) := (t 1+t 2)*t 3+t 4*(t 5+t 6)

def sixVertexMass {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) : R :=
  sumOver (SectorDefectAccounting.wedgePairs ((List.finRange 7).filter (fun i => i.val<6)))
    (fun e => pairWeight A p e.1 e.2)

/-- The pointwise conditional matching bound for the highest pair implies
the physical polarization lower bound W₁−W₁,*+Δκ₁. -/
theorem highestPayment (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (price : ∀ p∈oddWords (k+3), let t := fun i => (mu i)^2
      matchingScore A t p≤highPrice t-leadingGap t*(1-pairWeight A p 0 1)) :
    let os := oddWords (k+3)
    let t := fun i => (mu i)^2
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    let P := fun p => pairWeight A p 0 1
    weightedFourWedge 0 1 t (fun w => E.realPart w w)-referencePair t+
      leadingGap t*oddAverage half (fun p => P p*(1-P p))≤
      2*hs os (pairCoordinates half A 0 1) (densityCoordinates half A mu) := by
  let t := fun i => (mu i)^2
  let P p := pairWeight A p 0 1
  let C := matchingScore A t
  let os := oddWords (k+3)
  have p1 : oddAverage half P=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have bd (p : Word (k+3)) (hp : p∈os) : P p*C p≤highPrice t*P p-leadingGap t*(P p*(1-P p)) := by
    have h := OrderedRing.mul_le_mul_of_nonneg_left (price p hp)
      (ComplexScalar.normSq_nonnegative (pairAmplitude A p 0 1))
    change P p*C p≤P p*(highPrice t-leadingGap t*(1-P p)) at h
    grind only
  have avg := avgLe half h2 bd
  rw [avgSub,avgMul,avgMul,p1,Semiring.mul_one] at avg
  have e := pairPaymentIdentity half third h2 h3 k A mu orth 0 1 (by decide)
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W := weightedFourWedge 0 1 t (fun w => E.realPart w w)
  let V := pairCoordinates half A 0 1
  let L := densityCoordinates half A mu
  change 2*hs os V L=t 0*t 1+W-oddAverage half (fun p => P p*C p) at e
  change W-referencePair t+leadingGap t*oddAverage half (fun p => P p*(1-P p))≤2*hs os V L
  have eq : highPrice t=t 0*t 1+referencePair t := by unfold highPrice referencePair; grind only
  rw [eq] at avg; grind only

/-- The conditional matching price with all four types, occupied leading
edges, and the six-vertex mass is integrated against the actual shared probe. -/
theorem sharedPayment (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (price : ∀ p∈oddWords (k+3), let t := fun i => (mu i)^2
      let P := pairWeight A p 0 1+pairWeight A p 0 2
      matchingScore A t p≤secondPrice t+leadingGap t*pairWeight A p 0 1-sharedGap t*(1-P)-
        emptyGap t*(1-P-pairWeight A p 1 2)-tailGap t*(3-sixVertexMass A p)) :
    let os := oddWords (k+3)
    let t := fun i => (mu i)^2
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    let W i := weightedFourWedge 0 i t (fun w => E.realPart w w)
    let P₁ := fun p => pairWeight A p 0 1
    let P := fun p => P₁ p+pairWeight A p 0 2
    W 1+W 2-referenceShared t+sharedGap t*oddAverage half (fun p => P p*(1-P p))+
      leadingGap t*oddAverage half (fun p => P₁ p*(1-P p))+
      emptyGap t*oddAverage half (fun p => P p*(1-P p-pairWeight A p 1 2))-
      tailGap t*(oddAverage half (fun p => P p*sixVertexMass A p)-5)≤
      2*hs os (sharedProbe half A) (densityCoordinates half A mu) := by
  let t := fun i => (mu i)^2
  let os := oddWords (k+3)
  let E := PhysicalCompressionEffect.physicalEntries half h2 k A
  let W i := weightedFourWedge 0 i t (fun w => E.realPart w w)
  let P₁ p := pairWeight A p 0 1
  let P₂ p := pairWeight A p 0 2
  let P p := P₁ p+P₂ p
  let m p := pairWeight A p 1 2
  let C := matchingScore A t
  let S := sixVertexMass A
  let L := densityCoordinates half A mu
  let U := sharedProbe half A
  have a : oddAverage half P₁=1 := pairWeightAverage half h2 A orth 0 1 (by decide)
  have b : oddAverage half P₂=1 := pairWeightAverage half h2 A orth 0 2 (by decide)
  have total : oddAverage half P=2 := by dsimp only [P]; rw [avgAdd,a,b]; grind only
  have bd (p : Word (k+3)) (hp : p∈os) : P p*C p≤secondPrice t*P p+leadingGap t*(P₁ p*P p)-
      sharedGap t*(P p*(1-P p))-emptyGap t*(P p*(1-P p-m p))-
      tailGap t*(3*P p-P p*S p) := by
    have p0 : 0≤P p := by
      have p1 := ComplexScalar.normSq_nonnegative (pairAmplitude A p 0 1)
      have p2 := ComplexScalar.normSq_nonnegative (pairAmplitude A p 0 2)
      change 0≤P₁ p at p1; change 0≤P₂ p at p2; dsimp only [P]; grind only
    have h := OrderedRing.mul_le_mul_of_nonneg_left (price p hp) p0
    change P p*C p≤P p*(secondPrice t+leadingGap t*P₁ p-sharedGap t*(1-P p)-emptyGap t*(1-P p-m p)-tailGap t*(3-S p)) at h
    grind only
  have avg := avgLe half h2 bd
  simp only [avgSub,avgAdd,avgMul,total] at avg
  have cross := complementMoment half P₁ P
  rw [a] at cross
  have sum : oddAverage half (fun p => P p*C p)=oddAverage half (fun p => P₁ p*C p)+oddAverage half (fun p => P₂ p*C p) := by
    dsimp only [P]; simp only [Semiring.right_distrib,avgAdd]
  have eq (i : Fin 7) (ne : 0≠i) := pairPaymentIdentity half third h2 h3 k A mu orth 0 i ne
  have e₁ := eq 1 (by decide); have e₂ := eq 2 (by decide)
  change 2*hs os (pairCoordinates half A 0 1) L=t 0*t 1+W 1-oddAverage half (fun p => P₁ p*C p) at e₁
  change 2*hs os (pairCoordinates half A 0 2) L=t 0*t 2+W 2-oddAverage half (fun p => P₂ p*C p) at e₂
  have shared : 2*hs os U L=t 0*t 1+t 0*t 2+(W 1+W 2)-oddAverage half (fun p => P p*C p) := by
    change 2*hs os (fun e => pairCoordinates half A 0 1 e+pairCoordinates half A 0 2 e) L=_
    rw [hsAddLeft,sum]; grind only
  have e : 2*secondPrice t+leadingGap t=t 0*t 1+t 0*t 2+referenceShared t+tailGap t := by
    unfold secondPrice leadingGap referenceShared tailGap; grind only
  change W 1+W 2-referenceShared t+sharedGap t*oddAverage half (fun p => P p*(1-P p))+
    leadingGap t*oddAverage half (fun p => P₁ p*(1-P p))+
    emptyGap t*oddAverage half (fun p => P p*(1-P p-m p))-
    tailGap t*(oddAverage half (fun p => P p*S p)-5)≤2*hs os U L
  rw [shared,cross]; grind only

end Order

end RankSeven.JointProbeGram

#print axioms RankSeven.JointProbeGram.sharedExteriorZero
#print axioms RankSeven.JointProbeGram.pairGramShared
#print axioms RankSeven.JointProbeGram.pairWeightAverage
#print axioms RankSeven.JointProbeGram.physicalJointGram
#print axioms RankSeven.JointProbeGram.highestPayment
#print axioms RankSeven.JointProbeGram.sharedPayment
