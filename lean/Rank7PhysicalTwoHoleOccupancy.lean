import Rank7FiveFrameContractions

/-! Two-hole occupations on oriented tensor coordinates. Each repeated
contracting covector is linear. Its conjugate occurs in the adjoint creation. -/
namespace RankSeven.PhysicalTwoHoleOccupancy
open Lean.Grind Pauli ComplexScalar
open PhysicalCutCapacities (Triple triples extend)
open PhysicalUniformOccupation (oneHole wave)
variable {R : Type} [CommRing R] {I : Type}

private theorem sum0 {C : Type} [CommRing C] (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with | nil => rfl | cons i xs ih => change 0+sumOver xs _=0; rw [ih]; grind
private theorem sumNeg {C : Type} [CommRing C] (xs : List I) (f : I→C) :
    sumOver xs (fun i => -f i) = -sumOver xs f := by
  induction xs with | nil => change 0=-(0:C); grind | cons i xs ih => change -f i+sumOver xs _= -(f i+sumOver xs _); rw [ih]; grind
private theorem starNeg (z : ComplexScalar R) : star (-z)= -star z := by apply ComplexScalar.ext <;> simp <;> grind
private theorem starSub (z w : ComplexScalar R) : star (z-w)=star z-star w := by apply ComplexScalar.ext <;> simp <;> grind
private theorem star0 : star (0:ComplexScalar R)=0 := star_ofReal (0:R)
private theorem star1 : star (1:ComplexScalar R)=1 := star_ofReal (1:R)

def sum3 {C : Type} [CommRing C] (L : List I) (f : I→I→I→C) := sumOver L fun a => sumOver L fun b => sumOver L (f a b)
def sum2 {C : Type} [CommRing C] (L : List I) (f : I→I→C) := sumOver L fun a => sumOver L (f a)
def gram3 (L : List I) (h k : I→I→I→ComplexScalar R) := sum3 L fun a b c => star (h a b c)*k a b c
def gram2 (L : List I) (h k : I→I→ComplexScalar R) := sum2 L fun a b => star (h a b)*k a b

def lower3 (L : List I) (x : I → ComplexScalar R) (h : I→I→I→ComplexScalar R) (a b : I) :=
  sumOver L (fun c => x c*h a b c)
def lower2 (L : List I) (x : I → ComplexScalar R) (h : I→I→ComplexScalar R) (a : I) :=
  sumOver L (fun c => x c*h a c)
def raise3 (x : I → ComplexScalar R) (e : I→I→ComplexScalar R) (a b c : I) :=
  star (x a)*e b c - star (x b)*e a c +star (x c)*e a b
def Alt3 (h : I→I→I→ComplexScalar R) : Prop :=
    (∀a b c,h b a c= -h a b c) ∧ (∀a b c,h a c b= -h a b c)
def Alt2 (h : I→I→ComplexScalar R) : Prop := ∀a b,h b a= -h a b

private theorem sum3Rotate {C : Type} [CommRing C] (L : List I) (f : I→I→I→C) :
    sum3 L f=sum3 L (fun a b c => f c a b) := by
  unfold sum3
  rw [sumOverSwap]; apply sumOverCongr; intro a; rw [sumOverSwap]
private theorem sum3Swap23 {C : Type} [CommRing C] (L : List I) (f : I→I→I→C) :
    sum3 L f=sum3 L (fun a b c => f a c b) := by
  unfold sum3; apply sumOverCongr; intro a; rw [sumOverSwap]
private theorem sum3Congr {C : Type} [CommRing C] (L : List I) {f g : I→I→I→C} (h : ∀a b c,f a b c=g a b c) :
    sum3 L f=sum3 L g := by
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; exact h a b

/-- The rank-dependent factor three is for ordered triples; each sorted
pair is counted twice and each sorted triple six times. -/
theorem creationAdjoint (L : List I) (x : I→ComplexScalar R) (h : I→I→I→ComplexScalar R)
    (e : I→I→ComplexScalar R) (alt : Alt3 h) : gram3 L h (raise3 x e)=3*gram2 L (lower3 L x h) e := by
  let p (a b c : I) := star (h a b c)*(star (x a)*e b c)
  let q (a b c : I) := star (h a b c)*(star (x b)*e a c)
  let r (a b c : I) := star (h a b c)*(star (x c)*e a b)
  have exp : gram3 L h (raise3 x e)=sum3 L p-sum3 L q+sum3 L r := by
    have each (a b c : I) : star (h a b c)*raise3 x e a b c=p a b c-q a b c+r a b c := by dsimp only [p,q,r,raise3]; grind only
    unfold gram3 sum3; simp only [each,sumOverAdd,Compression.sumOverSub]
  have first : sum3 L p=sum3 L r := by
    rw [sum3Rotate L p]; apply sum3Congr; intro a b c
    have rot : h c a b=h a b c := by rw [alt.1 a c b,alt.2 a b c]; grind only
    unfold p r; rw [rot]
  have second : sum3 L q= -sum3 L r := by
    rw [sum3Swap23 L q]
    calc
      _ = sum3 L (fun a b c => -r a b c) := by apply sum3Congr; intro a b c; unfold q r; rw [alt.2 a b c,starNeg]; grind only
      _ = _ := by simp only [sum3,sumNeg]
  have rt : sum3 L r=gram2 L (lower3 L x h) e := by
    unfold sum3 gram2 sum2; apply sumOverCongr; intro a; apply sumOverCongr; intro b
    simp only [lower3,ComplexExterior.starSumOver,sumOverMulRight,star_mul]; apply sumOverCongr; intro c; unfold r; grind only
  rw [exp,first,second,rt]; grind only

private theorem adjoint3 (L : List I) (u v : I→I→I→ComplexScalar R) :
    star (gram3 L u v)=gram3 L v u := by
  simp only [gram3,sum3,ComplexExterior.starSumOver,star_mul,star_star]
  apply sum3Congr; intro a b c; grind only

private theorem adjoint2 (L : List I) (u v : I→I→ComplexScalar R) :
    star (gram2 L u v)=gram2 L v u := by
  simp only [gram2,sum2,ComplexExterior.starSumOver,star_mul,star_star]
  apply sumOverCongr; intro a; apply sumOverCongr; intro b; grind only

theorem creationAdjointLeft (L : List I) (x : I→ComplexScalar R) (h : I→I→I→ComplexScalar R)
    (e : I→I→ComplexScalar R) (alt : Alt3 h) : gram3 L (raise3 x e) h=3*gram2 L e (lower3 L x h) := by
  rw [←adjoint3,creationAdjoint _ _ _ _ alt,star_mul,adjoint2]
  have three : star (3:ComplexScalar R)=3 := star_ofReal (3:R)
  rw [three]

/-- CAR for annihilation of a created mode on two-form inputs, with
unitary and orthogonality specializations obtained by the mode pairing. -/
theorem lowerRaise (L : List I) (x y : I→ComplexScalar R) (e : I→I→ComplexScalar R) (a b : I) :
    lower3 L x (raise3 y e) a b =
      star (y a)*lower2 L x e b -star (y b)*lower2 L x e a +sumOver L (fun c => x c*star (y c))*e a b := by
  unfold lower3 lower2 raise3
  simp only [sumOverMulLeft,sumOverMulRight,←sumOverAdd,←Compression.sumOverSub]
  apply sumOverCongr; intro c; grind only

def residual (L : List I) (y : I→ComplexScalar R) (h : I→I→I→ComplexScalar R) (a b c : I) :=
  h a b c-raise3 y (lower3 L y h) a b c
private theorem quadrupleSkew (L : List I) (x y : I→ComplexScalar R) (H : I→I→ComplexScalar R)
    (skew : ∀a b,H b a= -H a b) :
    sum2 L (fun a b => x a*(y b*H a b))= -sum2 L (fun a b => y a*(x b*H a b)) := by
  unfold sum2; rw [sumOverSwap,←sumNeg]; apply sumOverCongr; intro a
  rw [←sumNeg]; apply sumOverCongr; intro b; rw [skew a b]; grind only
theorem fromTwice (half : R) (unit : 2*half=1) {z : ComplexScalar R} (h : z= -z) : z=0 := by
  apply ComplexScalar.ext
  · have d := congrArg re h; change z.re= -z.re at d; change z.re=0; have sc := congrArg (fun t => half*t) d; grind only
  · have d := congrArg im h; change z.im= -z.im at d; change z.im=0; have sc := congrArg (fun t => half*t) d; grind only
theorem lowerSquared (half : R) (unit : 2*half=1) (L : List I) (x : I→ComplexScalar R)
    (h : I→I→I→ComplexScalar R) (alt : Alt3 h) (a : I) : lower2 L x (lower3 L x h) a=0 := by
  unfold lower2 lower3; simp only [sumOverMulLeft]
  exact fromTwice half unit (quadrupleSkew L x x _ (alt.2 a))

theorem lowerAlt (L : List I) (x : I→ComplexScalar R) {h : I→I→I→ComplexScalar R} (alt : Alt3 h) :
    Alt2 (lower3 L x h) := by
  intro a b; simp only [lower3,alt.1 a b,Ring.mul_neg,sumNeg]

theorem raiseAlt (x : I→ComplexScalar R) {e : I→I→ComplexScalar R} (alt : Alt2 e) : Alt3 (raise3 x e) := by
  constructor
  · intro a b c; unfold raise3; rw [alt a b]; grind only
  · intro a b c; unfold raise3; rw [alt b c]; grind only

private theorem residualAlt (L : List I) (y : I→ComplexScalar R) {h : I→I→I→ComplexScalar R} (alt : Alt3 h) :
    Alt3 (residual L y h) := by
  have g := raiseAlt y (lowerAlt L y alt)
  constructor
  · intro a b c; unfold residual; rw [alt.1 a b c,g.1 a b c]; grind only
  · intro a b c; unfold residual; rw [alt.2 a b c,g.2 a b c]; grind only

private theorem lowerResidual (L : List I) (x y : I→ComplexScalar R) (h : I→I→I→ComplexScalar R) (a b : I) :
    lower3 L x (residual L y h) a b=lower3 L x h a b-lower3 L x (raise3 y (lower3 L y h)) a b := by
  change sumOver L (fun c => x c*(h a b c-raise3 y (lower3 L y h) a b c))=sumOver L (fun c => x c*h a b c)-sumOver L (fun c => x c*raise3 y (lower3 L y h) a b c)
  rw [←Compression.sumOverSub]; apply sumOverCongr; intro c; grind only
private theorem residualZero (half : R) (unit : 2*half=1) (L : List I) (x : I→ComplexScalar R)
    (hx : sumOver L (fun c => x c*star (x c))=1) (h : I→I→I→ComplexScalar R) (alt : Alt3 h) (a b : I) :
    lower3 L x (residual L x h) a b=0 := by
  rw [lowerResidual,lowerRaise,hx,lowerSquared half unit L x h alt,lowerSquared half unit L x h alt]; grind only
theorem subtractLeft (L : List I) (y : I→ComplexScalar R) (h k : I→I→I→ComplexScalar R) :
    gram3 L (residual L y h) k=gram3 L h k-gram3 L (raise3 y (lower3 L y h)) k := by
  have eq (a b c : I) : star (residual L y h a b c)*k a b c=star (h a b c)*k a b c-star (raise3 y (lower3 L y h) a b c)*k a b c := by rw [residual,starSub]; grind only
  unfold gram3 sum3; simp only [eq,Compression.sumOverSub]
private theorem subtractRight (L : List I) (y : I→ComplexScalar R) (h k : I→I→I→ComplexScalar R) :
    gram3 L h (residual L y k)=gram3 L h k-gram3 L h (raise3 y (lower3 L y k)) := by
  have eq (a b c : I) : star (h a b c)*residual L y k a b c=star (h a b c)*k a b c-star (h a b c)*raise3 y (lower3 L y k) a b c := by rw [residual]; grind only
  unfold gram3 sum3; simp only [eq,Compression.sumOverSub]
private theorem zeroGramLeft (L : List I) {h : I→I→ComplexScalar R} (hzero : ∀a b,h a b=0) (e : I→I→ComplexScalar R) :
    gram2 L h e=0 := by simp only [gram2,sum2,hzero,star0,Semiring.zero_mul,sum0]
theorem zeroGramRight (L : List I) {h : I→I→ComplexScalar R} (hzero : ∀a b,h a b=0) (e : I→I→ComplexScalar R) :
    gram2 L e h=0 := by simp only [gram2,sum2,hzero,Semiring.mul_zero,sum0]

/-- The one-occupied and two-occupied coordinates are orthogonal, with
the tensor normalization verified from their alternating entries. -/
theorem occupationSplit (half : R) (unit : 2*half=1) (L : List I) (y : I→ComplexScalar R)
    (hy : sumOver L (fun c => y c*star (y c))=1) (h k : I→I→I→ComplexScalar R) (ah : Alt3 h) (ak : Alt3 k) :
    gram3 L (residual L y h) (residual L y k)+3*gram2 L (lower3 L y h) (lower3 L y k)=gram3 L h k := by
  rw [subtractRight,creationAdjoint _ _ _ _ (residualAlt L y ah),
    zeroGramLeft L (residualZero half unit L y hy h ah),subtractLeft,creationAdjointLeft _ _ _ _ ak]
  grind only

def anchored {n : Nat} (half : R) (x : Basis n→ComplexScalar R) (c : Word n→ComplexScalar R)
    (a b d : Basis n) := oneHole x (wave half c) ((a,b),d)

theorem anchoredAlternating {n : Nat} (half : R) (x : Basis n→ComplexScalar R) (f : Word n→ComplexScalar R) :
    Alt3 (anchored half x f) := by
  have s1 (a b c t : Basis n) : wave half f ((b,a),(c,t))= -wave half f ((a,b),(c,t)) :=
    FiveFrameContractions.waveReorder half f ((a,b),(c,t)) ((1,0),(2,3)) (by decide)
  have s2 (a b c t : Basis n) : wave half f ((a,c),(b,t))= -wave half f ((a,b),(c,t)) :=
    FiveFrameContractions.waveReorder half f ((a,b),(c,t)) ((0,2),(1,3)) (by decide)
  constructor
  · intro a b c; simp only [anchored,oneHole,extend,s1 a b c,Ring.mul_neg,sumNeg]
  · intro a b c; simp only [anchored,oneHole,extend,s2 a b c,Ring.mul_neg,sumNeg]

theorem physicalTwoHoleSkew {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f : Word n→ComplexScalar R) (a b : Basis n) :
    lower3 (qubitIndices n) x (anchored half y f) a b= -lower3 (qubitIndices n) y (anchored half x f) a b := by
  unfold lower3 anchored oneHole; simp only [sumOverMulLeft]
  apply quadrupleSkew
  intro c t; exact FiveFrameContractions.waveReorder half f ((a,b),(c,t)) ((0,1),(3,2)) (by decide)

def modeGram (L : List I) (x y : I→ComplexScalar R) := sumOver L (fun a => star (x a)*y a)
def waveGram {n : Nat} (half : R) (f g : Word n→ComplexScalar R) :=
    sumOver (fourIndices (qubitIndices n)) (fun u => star (wave half f u)*wave half g u)

theorem modeFlip (L : List I) (x y : I→ComplexScalar R) :
    sumOver L (fun a => x a*star (y a))=modeGram L y x := by
  apply sumOverCongr; intro a; grind only
private theorem modeStar (L : List I) (x y : I→ComplexScalar R) : star (modeGram L x y)=modeGram L y x := by
  simp only [modeGram,ComplexExterior.starSumOver,star_mul,star_star]; apply sumOverCongr; intro a; grind only

private theorem productSum {α β C : Type} [CommRing C] (xs : List α) (ys : List β) (f : α×β→C) :
    sumOver (productIndices xs ys) f=sumOver xs (fun x => sumOver ys (fun y => f (x,y))) := by
  rw [productIndices,sumOverFlatMap]; apply sumOverCongr; intro a; simp only [sumOver,List.map_map,Function.comp_def]
private theorem polarizedPhysicalOccupation {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f g : Word n→ComplexScalar R) :
    (2:ComplexScalar R)^n*gram3 (qubitIndices n) (anchored half x f) (anchored half y g)=modeGram (qubitIndices n) x y * waveGram half f g := by
  have wf (c : Word n→ComplexScalar R) : PhysicalHopping.PlaneField (wave half c) :=
    PhysicalHopping.fieldCombination _ _ _ (fun p _ => PhysicalHopping.pauliColumnField half p)
  have starred : PhysicalHopping.PlaneField (fun t => star (wave half f t)) := by
    constructor
    · intro d t; rw [(wf f).invariant]
    · intro t h; rw [(wf f).supported _ h,star0]
  have raw := PhysicalUniformOccupation.uniformOccupation (fun a => star (x a)) y starred (wf g)
  have cj (t : Triple (Basis n)) :
      oneHole (fun a => star (x a)) (fun u => star (wave half f u)) t= star (oneHole x (wave half f) t) := by
    simp only [oneHole,ComplexExterior.starSumOver,star_mul]
  simpa only [cj,triples,productSum,modeGram,waveGram,gram3,sum3,anchored] using raw

def oneOccupied {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f : Word n→ComplexScalar R) :=
    residual (qubitIndices n) y (anchored half x f)

def twoOccupied {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f : Word n→ComplexScalar R) :=
    lower3 (qubitIndices n) y (anchored half x f)

private theorem earlyZero {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xy : modeGram (qubitIndices n) x y=0) (f : Word n→ComplexScalar R) (a b : Basis n) :
    lower3 (qubitIndices n) x (oneOccupied half x y f) a b=0 := by
  let L := qubitIndices n
  have swap (a b : Basis n) : lower3 L y (anchored half x f) a b= -lower3 L x (anchored half y f) a b :=
    physicalTwoHoleSkew _ _ _ _ _ _
  have zero (a : Basis n) : lower2 L x (lower3 L y (anchored half x f)) a=0 := by
    change sumOver L (fun b => x b*lower3 L y (anchored half x f) a b)=0
    simp only [swap,Ring.mul_neg,sumNeg]
    have d := lowerSquared half unit L x (anchored half y f) (anchoredAlternating _ _ _) a
    change -lower2 L x (lower3 L x (anchored half y f)) a=0; rw [d]; grind only
  have nil := fromTwice half unit (physicalTwoHoleSkew half x x f a b)
  have yx : modeGram L y x=0 := by rw [←modeStar,xy,star0]
  change lower3 L x (residual L y (anchored half x f)) a b=0
  rw [lowerResidual,lowerRaise,zero,zero,modeFlip,yx,nil]; grind only

private theorem splitCross {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xy : modeGram (qubitIndices n) x y=0) (f g : Word n→ComplexScalar R) :
    gram3 (qubitIndices n) (oneOccupied half x y f) (oneOccupied half y x g)=
      gram3 (qubitIndices n) (anchored half x f) (anchored half y g) := by
  let L := qubitIndices n
  change gram3 L (oneOccupied half x y f) (residual L x (anchored half y g))=_
  have alt : Alt3 (oneOccupied half x y f) := residualAlt L y (anchoredAlternating _ _ _)
  rw [subtractRight,creationAdjoint L x (oneOccupied half x y f) _ alt,
    zeroGramLeft L (earlyZero half unit x y xy f)]
  change gram3 L (residual L y (anchored half x f)) (anchored half y g)-3*0=_
  rw [subtractLeft,creationAdjointLeft L _ _ _ (anchoredAlternating _ _ _)]
  have nil (a b : Basis n) := fromTwice half unit (physicalTwoHoleSkew half y y g a b)
  rw [zeroGramRight L nil]; grind only

private theorem reverseTwoGram {n : Nat} (half : R) (x y : Basis n→ComplexScalar R) (f g : Word n→ComplexScalar R) :
    gram2 (qubitIndices n) (twoOccupied half y x f) (twoOccupied half y x g)=
      gram2 (qubitIndices n) (twoOccupied half x y f) (twoOccupied half x y g) := by
  unfold gram2 sum2; apply sumOverCongr; intro a; apply sumOverCongr; intro b
  change star (lower3 (qubitIndices n) x (anchored half y f) a b)*lower3 (qubitIndices n) x (anchored half y g) a b=_
  rw [physicalTwoHoleSkew half x y f,physicalTwoHoleSkew half x y g,starNeg]; dsimp only [twoOccupied]; grind only

/-- Polarized physical occupation identities for the two singly occupied
slots and their common doubly occupied slot. Triple and pair Gram sums use
ordered tensor coordinates, explaining the coefficient three. -/
theorem physicalOccupationGrams {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (f g : Word n→ComplexScalar R) :
    let L := qubitIndices n
    let d := (2:ComplexScalar R)^n
    let Q := gram2 L (twoOccupied half x y f) (twoOccupied half x y g)
    d*(gram3 L (oneOccupied half x y f) (oneOccupied half x y g)+3*Q)=waveGram half f g ∧
    d*(gram3 L (oneOccupied half y x f) (oneOccupied half y x g)+3*Q)=waveGram half f g ∧
    d*gram3 L (oneOccupied half x y f) (oneOccupied half y x g)=0 := by
  dsimp only
  have first (x y : Basis n→ComplexScalar R) (hx : modeGram (qubitIndices n) x x=1) (hy : modeGram (qubitIndices n) y y=1) :
      (2:ComplexScalar R)^n*(gram3 (qubitIndices n) (oneOccupied half x y f) (oneOccupied half x y g)+
        3*gram2 (qubitIndices n) (twoOccupied half x y f) (twoOccupied half x y g))=waveGram half f g := by
    unfold oneOccupied twoOccupied
    rw [occupationSplit half unit _ y ((modeFlip _ y y).trans hy) _ _ (anchoredAlternating _ _ _) (anchoredAlternating _ _ _),
      polarizedPhysicalOccupation,hx]; grind only
  refine ⟨first x y xx yy,?_,?_⟩
  · rw [←reverseTwoGram half x y f g]; exact first y x yy xx
  · rw [splitCross half unit x y xy f g,polarizedPhysicalOccupation,xy]; grind only

private theorem inverseDimension (half : R) (unit : 2*half=1) (n : Nat) :
    (ofReal half)^n*(2:ComplexScalar R)^n=1 := by
  have base : ofReal half*(2:ComplexScalar R)=1 := by
    change ofReal half*ofReal (2:R)=ofReal (1:R)
    apply ComplexScalar.ext
    · change half*2-0*0=1; grind only
    · change half*0+0*2=0; grind only
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
  | succ n ih => rw [Semiring.pow_succ,Semiring.pow_succ]; grind only

/-- In ordered tensor normalization the diagonal occupation bound carries
the factor 1/d and the double contraction carries multiplicity three.
This is precisely (209) after the 4!, 3!, and 2! wedge-norm conventions. -/
theorem physicalOccupation209 {n : Nat} (half : R) (unit : 2*half=1) (x y : Basis n→ComplexScalar R)
    (xx : modeGram (qubitIndices n) x x=1) (yy : modeGram (qubitIndices n) y y=1)
    (xy : modeGram (qubitIndices n) x y=0) (f g : Word n→ComplexScalar R) :
    let L := qubitIndices n
    let target := (ofReal half)^n*waveGram half f g -
      3*gram2 L (twoOccupied half x y f) (twoOccupied half x y g)
    gram3 L (oneOccupied half x y f) (oneOccupied half x y g)=target ∧
    gram3 L (oneOccupied half y x f) (oneOccupied half y x g)=target ∧
    gram3 L (oneOccupied half x y f) (oneOccupied half y x g)=0 := by
  obtain ⟨ex,ey,z⟩ := physicalOccupationGrams half unit x y xx yy xy f g
  have inv := inverseDimension half unit n
  have h1 := congrArg (fun t => (ofReal half)^n*t) ex
  have h2 := congrArg (fun t => (ofReal half)^n*t) ey
  have hz := congrArg (fun t => (ofReal half)^n*t) z
  dsimp only at h1 h2 hz ⊢
  constructor
  · rw [←Semiring.mul_assoc,inv,Semiring.one_mul] at h1; grind only
  constructor
  · rw [←Semiring.mul_assoc,inv,Semiring.one_mul] at h2; grind only
  · rw [←Semiring.mul_assoc,inv,Semiring.one_mul,Semiring.mul_zero] at hz; exact hz

end RankSeven.PhysicalTwoHoleOccupancy
#print axioms RankSeven.PhysicalTwoHoleOccupancy.physicalOccupation209
#print axioms RankSeven.PhysicalTwoHoleOccupancy.physicalOccupationGrams
