import Rank7ReserveMixedNorm

/-! Conversion of odd-cut leakage to disjoint spectral reserve payments. -/
namespace RankSeven.OddCutReserve
open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliReserveSlots
open PhysicalCompressionEffect (OrthonormalFrame)
open FrameExteriorSector (framedWord)
open JointProbePayment (densityCoordinates hs)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

def cutLeak {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (r : Fin 7) (p : Word n) : R :=
  crossLoss (fun i j => normSq (framedWord A p i j)) (cut r) (cut r)

def PairLeakage {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (r : Fin 7) : Prop :=
  ∀ p q : Word n,anti p q=true → 1≤cutLeak A r p+cutLeak A r q

private theorem sumLe {α : Type} (xs : List α) (f g : α → R) (h : ∀ i∈xs,f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have d := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at d; grind only

private theorem powerPos (n : Nat) : 0<(2:R)^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind only)

private theorem neighborhoodNonnegative {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (t : Fin 7 → R) (p : Word n) : 0≤neighborhood A t p := by
  apply Compression.sumOverNonnegative; intro q _; split
  · exact squareNonnegative _
  · exact Std.le_refl _

theorem cutLeakNonnegative {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (p : Word n) (r : Fin 7) : 0≤cutLeak A r p := by
  have e := neighborhoodFourier A orth (cut r) p
  change 2*neighborhood A (cut r) p=(2:R)^n*cutLeak A r p at e
  have h := neighborhoodNonnegative A (cut r) p
  apply Classical.byContradiction; intro no
  have bad := OrderedRing.mul_pos (powerPos (R:=R) n) (show 0< -cutLeak A r p by grind only)
  grind only

theorem cutLeakUpper {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (p : Word n) (r : Fin 7) :
    cutLeak A r p≤Nat.cast (r.val+1) := by
  let f (i : Fin 7) := if i≤r then 1 else 0
  have count : (labels.map f).sum=r.val+1 := by
    have table : ∀ a : Fin 7, (labels.map (fun i => if i≤a then 1 else 0)).sum=a.val+1 := by decide
    exact table r
  have castSum (xs : List (Fin 7)) : sumOver xs (fun i => (Nat.cast (f i):R))=Nat.cast ((xs.map f).sum) := by
    induction xs with
    | nil => change 0=Nat.cast 0; rw [Semiring.natCast_zero]
    | cons i xs ih =>
      change Nat.cast (f i)+sumOver xs _=Nat.cast (f i+(xs.map f).sum)
      rw [Semiring.natCast_add,ih]
  have ident (i : Fin 7) : cut (R:=R) r i*cut r i=Nat.cast (f i) := by
    unfold cut f; split <;> simp only [Semiring.one_mul,Semiring.zero_mul,Semiring.natCast_zero,Semiring.natCast_one]
  have non (i : Fin 7) : 0≤cut (R:=R) r i := by unfold cut; split <;> grind only
  have ns := Compression.sumOverNonnegative labels
    (fun i => sumOver labels (fun j => cut r i*cut r j*normSq (framedWord A p i j)))
    (fun i _ => Compression.sumOverNonnegative labels _ (fun j _ =>
      OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (non i) (non j)) (normSq_nonnegative _)))
  unfold cutLeak crossLoss; rw [sumOverCongr labels ident,castSum,count]; grind only

/-- Charging both endpoints of each anticommuting edge converts one unit of
odd-cut leakage into the comparison of actual two-slot physical reserves.
The rank factor is twice the dimension of the first cut. -/
theorem crossReserve {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (r i : Fin 7) (leak : PairLeakage A i) :
    reserve half A (cut r) (cut r)≤2*(Nat.cast (r.val+1):R)*reserve half A (cut r) (cut i) := by
  let ws := words n
  let d := (2:R)^n
  let m : R := Nat.cast (r.val+1)
  let w p := (coeff A (cut r) p)^2
  let a (p q : Word n) := if anti p q then w q else 0
  let N := neighborhood A (cut r)
  let N' := neighborhood A (cut i)
  let h := cutLeak A i
  have edge (p q : Word n) : w p*a p q≤w p*a p q*h p+w p*a p q*h q := by
    cases e : anti p q with
    | false => simp only [a,e,Bool.false_eq_true,ite_false,Semiring.mul_zero,Semiring.zero_mul,Semiring.add_zero]; exact Std.le_refl _
    | true =>
      have pair := leak p q e
      have nw := OrderedRing.mul_nonneg (squareNonnegative (coeff A (cut r) p)) (squareNonnegative (coeff A (cut r) q))
      change 0≤w p*w q at nw
      have z := OrderedRing.mul_le_mul_of_nonneg_left pair nw
      simp only [a,e,ite_true]; dsimp only [h]; grind only
  have edgeSum := sumLe ws (fun p => sumOver ws (fun q => w p*a p q))
    (fun p => sumOver ws (fun q => w p*a p q*h p+w p*a p q*h q))
    (fun p _ => sumLe ws _ _ (fun q _ => edge p q))
  have ndef (p : Word n) : sumOver ws (a p)=N p := rfl
  have flip (p q : Word n) : w p*a p q*h q=w q*a q p*h q := by
    unfold a; rw [PauliEdgeBlocks.antiSymm p q]; split <;> grind only
  have lhs : sumOver ws (fun p => sumOver ws (fun q => w p*a p q))=sumOver ws (fun p => w p*N p) := by
    apply sumOverCongr; intro p; rw [←sumOverMulLeft,ndef]
  have e1 : sumOver ws (fun p => sumOver ws (fun q => w p*a p q*h p))=
      sumOver ws (fun p => w p*h p*N p) := by
    apply sumOverCongr; intro p
    rw [sumOverCongr ws (g:=fun q => (w p*h p)*a p q) (fun q => by grind only),←sumOverMulLeft,ndef]
  have e2 : sumOver ws (fun p => sumOver ws (fun q => w p*a p q*h q))=
      sumOver ws (fun p => w p*h p*N p) := by
    rw [sumOverSwap]; apply Eq.trans _ e1
    apply sumOverCongr; intro q; apply sumOverCongr; intro p; exact flip p q
  simp only [sumOverAdd] at edgeSum
  rw [lhs,e1,e2] at edgeSum
  have scalar (p : Word n) := neighborhoodFourier A orth (cut i) p
  have cap (p : Word n) : 2*N p≤m*d := by
    have f := neighborhoodFourier A orth (cut r) p
    change 2*N p=d*cutLeak A r p at f
    have z := OrderedRing.mul_le_mul_of_nonneg_left (cutLeakUpper A p r) (Std.le_of_lt (powerPos (R:=R) n))
    change d*cutLeak A r p≤d*m at z; grind only
  have last := sumLe ws (fun p => 2*(w p*h p*N p)) (fun p => 2*m*(w p*N' p)) (fun p _ => by
    have pos := OrderedRing.mul_nonneg (squareNonnegative (coeff A (cut r) p)) (cutLeakNonnegative A orth p i)
    change 0≤w p*h p at pos
    have z := OrderedRing.mul_le_mul_of_nonneg_left (cap p) pos
    have x := scalar p
    change 2*N' p=d*h p at x
    have y := congrArg (fun v => m*w p*v) x; grind only)
  rw [←sumOverMulLeft,←sumOverMulLeft] at last
  have ord : sumOver ws (fun p => w p*N p)≤2*m*sumOver ws (fun p => w p*N' p) := by grind only
  have scaled := OrderedRing.mul_le_mul_of_nonneg_left ord (squareNonnegative (half^n))
  change (half^n)^2*sumOver ws (fun p => w p*N p)≤2*m*((half^n)^2*sumOver ws (fun p => w p*N' p))
  grind only

private def used : List (Fin 7×Fin 7) :=
  [(0,1),(0,5),(1,0),(1,1),(1,2),(2,1),(2,5),(4,5),(5,0),(5,2),(5,4),(5,5),(5,6),(6,5)]

private theorem selectedSlots (X : Fin 7 → Fin 7 → R) (sym : ∀ i j,X j i=X i j) (pos : ∀ i j,0≤X i j) :
    X 1 1+X 5 5+2*(X 1 0+X 1 2+X 5 0+X 5 2+X 5 4+X 5 6)≤
    sumOver labels (fun i => sumOver labels (X i)) := by
  let es := labels.flatMap (fun i => labels.map (fun j => (i,j)))
  let f (e : Fin 7×Fin 7) := X e.1 e.2
  have eq : es.filter used.contains=used := by decide
  have filt (xs : List (Fin 7×Fin 7)) : sumOver (xs.filter used.contains) f≤sumOver xs f := by
    induction xs with
    | nil => exact Std.le_refl _
    | cons a xs ih =>
      rw [List.filter_cons]; split
      · change f a+sumOver (xs.filter _) f≤f a+sumOver xs f; grind only
      · change sumOver (xs.filter _) f≤f a+sumOver xs f; have h : 0≤f a := pos _ _; grind only
  have bound := filt es; rw [eq] at bound
  have all : sumOver es f=sumOver labels (fun i => sumOver labels (X i)) := by
    rw [show es=labels.flatMap (fun i => labels.map (fun j => (i,j))) by rfl,sumOverFlatMap]
    apply sumOverCongr; intro i; simp only [sumOver,List.map_map,Function.comp_def,f]
  rw [all] at bound
  simp only [used,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,f] at bound
  have s1 := sym 1 0; have s2 := sym 1 2; have s3 := sym 5 0; have s4 := sym 5 2
  have s5 := sym 5 4; have s6 := sym 5 6
  change _≤(labels.map (fun i => (labels.map (X i)).sum)).sum
  grind only

/-- The rank-six correction and the strengthened leading-pair reserve are
paid simultaneously by fourteen distinct ordered cut slots. The remaining
per-word input is the unit leakage on the four odd-dimensional cuts. -/
theorem simultaneousOddPayments (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : PauliMatchingPrices.SortedSpectrum (fun i => (mu i)^2))
    (one : PairLeakage A 0) (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6) :
    let t := fun i => (mu i)^2
    let g := gap t
    let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne
    let z := densityCoordinates half A (cut 5)
    let B := 2*hs (MixedDefect.oddWords (k+3)) z z
    (6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2))*K+
      (g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)*B≤12*reserve half A t t := by
  let t := fun i => (mu i)^2
  let g := gap t
  let J r s := reserve half A (cut r) (cut s)
  let X r s := (g r)^2*(g s)^2*J r s
  let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne
  let z := densityCoordinates half A (cut 5)
  let B := 2*hs (MixedDefect.oddWords (k+3)) z z
  have j (r s : Fin 7) : J s r=J r s := reserveSwap half A (cut s) (cut r)
  have sym (r s : Fin 7) : X s r=X r s := by dsimp only [X]; rw [j r s]; grind only
  have pos (r s : Fin 7) : 0≤X r s := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _)) (reserveNonnegative _ _ _ _)
  have all : sumOver labels (fun i => sumOver labels (X i))≤reserve half A t t := allCutSlots half A orth t sorted
  have slots := Std.le_trans (selectedSlots X sym pos) all
  have hk : K≤2*J 1 1 := ReserveMixedNorm.highestPairReserve half inv24 third h2 h24 h3 k A mu orth
  have hb := ReserveMixedNorm.spectralCutReserve half inv24 h2 h24 k A 5 orth
  change hs (MixedDefect.oddWords (k+3)) z z≤J 5 5 at hb
  have bnd : B≤2*J 5 5 := by unfold B; grind only
  have c1 (i : Fin 7) (l : PairLeakage A i) : K≤8*J 1 i := by
    have e := crossReserve half A orth 1 i l
    change J 1 1≤2*(Nat.cast (1+1):R)*J 1 i at e
    simp only [Semiring.natCast_add,Semiring.natCast_one] at e; grind only
  have c6 (i : Fin 7) (l : PairLeakage A i) : B≤24*J 5 i := by
    have e := crossReserve half A orth 5 i l
    change J 5 5≤2*(Nat.cast (5+1):R)*J 5 i at e
    have five' : (Nat.cast 5:R)=5 := by grind only
    simp only [Semiring.natCast_add,Semiring.natCast_one,five'] at e; grind only
  have mult (i j : Fin 7) (a b : R) (ord : a≤b) :
      (g i)^2*(g j)^2*a≤(g i)^2*(g j)^2*b :=
    OrderedRing.mul_le_mul_of_nonneg_left ord (OrderedRing.mul_nonneg (squareNonnegative _) (squareNonnegative _))
  have q0 := mult 1 1 _ _ hk
  have q1 := mult 5 5 _ _ bnd
  have q2 := mult 1 0 _ _ (c1 0 one)
  have q3 := mult 1 2 _ _ (c1 2 three)
  have q4 := mult 5 0 _ _ (c6 0 one)
  have q5 := mult 5 2 _ _ (c6 2 three)
  have q6 := mult 5 4 _ _ (c6 4 five)
  have q7 := mult 5 6 _ _ (c6 6 seven)
  dsimp only [X] at slots
  change (6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2))*K+
    (g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)*B≤12*reserve half A t t
  grind only

def realInner {α : Type} (xs : List α) (u v : α → ComplexScalar R) : R :=
  sumOver xs (fun i => (star (u i)*v i).re)

/-- Two real-orthogonal complex unit vectors obey Bessel's inequality for
their real expectation coordinates. -/
theorem realBesselTwo {α : Type} (xs : List α) (u v z : α → ComplexScalar R)
    (un : PauliPairContraction.normSum xs u=1) (vn : PauliPairContraction.normSum xs v=1)
    (zn : PauliPairContraction.normSum xs z=1) (uv : realInner xs u v=0) :
    (realInner xs z u)^2+(realInner xs z v)^2≤1 := by
  let a := realInner xs z u
  let b := realInner xs z v
  let e i := z i-ofReal a*u i-ofReal b*v i
  have sq (i : α) : normSq (e i)=normSq (z i)+a^2*normSq (u i)+b^2*normSq (v i)-
      (2*a)*(star (z i)*u i).re-(2*b)*(star (z i)*v i).re+(2*a*b)*(star (u i)*v i).re := by
    simp only [e,normSq,re_sub,im_sub,re_mul,im_mul,re_ofReal,im_ofReal,re_star,im_star]; grind only
  have p := Compression.sumOverNonnegative xs (fun i => normSq (e i)) (fun i _ => normSq_nonnegative _)
  rw [sumOverCongr xs sq] at p
  simp only [sumOverAdd,Compression.sumOverSub,←sumOverMulLeft] at p
  change 0≤PauliPairContraction.normSum xs z+a^2*PauliPairContraction.normSum xs u+b^2*PauliPairContraction.normSum xs v-
    2*a*a-2*b*b+2*a*b*realInner xs u v at p
  change a^2+b^2≤1; rw [un,vn,zn,uv] at p; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum {α : Type} (xs : List α) (f : α → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=(f a).re+_; rw [re_add,ih]; rfl

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem innerFlip {α : Type} (xs : List α) (u v : α → ComplexScalar R) :
    realInner xs u v=realInner xs v u := by
  apply sumOverCongr; intro i; simp only [re_mul,re_star,im_star]; grind only

/-- Anticommuting Pauli images of one vector are orthogonal over the
reals. This assertion is valid for every ambient dimension. -/
theorem antiRealOrthogonal {n : Nat} (p q : Word n) (antiPair : anti p q=true) (v : Basis n → ComplexScalar R) :
    let xs := qubitIndices n
    realInner xs (PauliPairContraction.image xs (wordEntry imaginaryUnit p) v)
      (PauliPairContraction.image xs (wordEntry imaginaryUnit q) v)=0 := by
  let xs := qubitIndices n
  let M (a : Word n) := wordEntry (imaginaryUnit (R:=R)) a
  let Z (i : Basis n) (_ : Unit) := v i
  let V a := matMul xs (M a) Z
  let dot (a b : Word n) := matMul xs (PhysicalPairedReduction.dagger (V a)) (V b) () ()
  have diag (a b : Word n) : (dot a b).re=realInner xs (fun i => V a i ()) (fun i => V b i ()) := reSum xs _
  have h (a : Word n) : PhysicalPairedReduction.dagger (M a)=M a := by
    funext i j; exact ComplexPauliMoment.wordHermitian a j i
  have exp (a b : Word n) : dot a b=matMul xs (PhysicalPairedReduction.dagger Z) (matMul xs (matMul xs (M a) (M b)) Z) () () := by
    unfold dot V; rw [PhysicalPairedReduction.daggerProduct,h]; simp only [matMulAssoc]
  have swap (a b : Basis n) : matMul xs (M p) (M q) a b= -matMul xs (M q) (M p) a b := by
    have e := PhysicalAntiQuartic.wordCommutation (imaginaryUnit (R:=R)) imaginaryUnit_sq p q a b
    simpa only [chi,antiPair,phase,ite_true,Ring.neg_mul,Semiring.one_mul] using e
  have opp : dot p q= -dot q p := by
    rw [exp,exp]; change sumOver xs (fun i => star (v i)*sumOver xs (fun j => matMul xs (M p) (M q) i j*v j))=_
    simp only [swap,Ring.neg_mul]
    have ns (f : Basis n → ComplexScalar R) : sumOver xs (fun i => -f i)= -sumOver xs f := by
      have g := sumOverMulLeft xs f (-1); simpa only [Ring.neg_mul,Semiring.one_mul] using g.symm
    simp only [ns,Ring.mul_neg]
    rfl
  have e := congrArg ComplexScalar.re opp
  rw [re_neg,diag,diag,innerFlip xs (fun i => V q i ()) (fun i => V p i ())] at e
  change realInner xs (fun i => V p i ()) (fun i => V q i ())=0
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem firstCut (m : Fin 7 → Fin 7 → R) : crossLoss m (cut 0) (cut 0)=1-m 0 0 := by
  have fin : labels=[0,1,2,3,4,5,6] := by decide
  have finCut : ∀ i : Fin 7, i≤0 ↔ i=0 := by decide
  unfold crossLoss
  simp (config := {decide := true}) only [fin,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    cut,finCut,ite_true,ite_false,Semiring.one_mul,Semiring.zero_mul,Semiring.add_zero] <;> grind only

/-- The rank-one Pauli uncertainty inequality implements the unit odd-cut
leakage on the first source column with no extra premise. -/
theorem firstPairLeakage {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) :
    PairLeakage A 0 := by
  intro p q antiPair
  let xs := qubitIndices n
  let v i := A i 0
  let T (r : Word n) := PauliPairContraction.image xs (wordEntry imaginaryUnit r) v
  have unit : PauliPairContraction.normSum xs v=1 := by
    have a := congrArg ComplexScalar.re (orth 0 0)
    change sumOver (qubitIndices n) (fun i => normSq (A i 0))=1
    simpa only [ite_true,re_one,reSum,re_star_mul_self] using a
  have ui (r : Word n) : PauliPairContraction.normSum xs (T r)=1 := (PauliPairContraction.wordIsometry r v).trans unit
  have o : realInner xs (T p) (T q)=0 := antiRealOrthogonal p q antiPair v
  have b := realBesselTwo xs (T p) (T q) v (ui p) (ui q) unit o
  have entry' (r : Word n) : (framedWord A r 0 0).re=realInner xs v (T r) := reSum xs _
  have gram (r : Word n) : normSq (framedWord A r 0 0)=(realInner xs v (T r))^2 := by
    have e := congrFun (congrFun (framedHerm A r) 0) 0
    change star (framedWord A r 0 0)=framedWord A r 0 0 at e
    have h := congrArg ComplexScalar.im e; rw [im_star] at h
    have im : (framedWord A r 0 0).im=0 := by grind only
    unfold normSq; rw [im,entry']; grind only
  unfold cutLeak; rw [firstCut,firstCut,gram,gram]; grind only

theorem rankSixCross {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (r : Fin 7) (leak : PairLeakage A r) :
    reserve half A (cut 5) (cut 5)≤12*reserve half A (cut 5) (cut r) := by
  have h := crossReserve half A orth 5 r leak
  have f : (Nat.cast (5+1):R)=6 := by grind only
  change _≤2*Nat.cast (5+1)*_ at h; rw [f] at h; grind only

/-- The strongest simultaneous receipt uses no rank-one leakage premise. -/
theorem physicalOddPayments (half inv24 third : R) (h2 : 2*half=1) (h24 : 24*inv24=1) (h3 : 3*third=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : OrthonormalFrame A) (sorted : PauliMatchingPrices.SortedSpectrum (fun i => (mu i)^2))
    (three : PairLeakage A 2) (five : PairLeakage A 4) (seven : PairLeakage A 6) :
    let t := fun i => (mu i)^2
    let g := gap t
    let K := (WeightedProbeShift.physicalPayment half h2 k A mu).kappaOne
    let z := densityCoordinates half A (cut 5)
    let B := 2*hs (MixedDefect.oddWords (k+3)) z z
    (6*(g 1)^4+3*(g 1)^2*((g 0)^2+(g 2)^2))*K+
      (g 5)^2*(6*(g 5)^2+(g 0)^2+(g 2)^2+(g 4)^2+(g 6)^2)*B≤12*reserve half A t t :=
  simultaneousOddPayments half inv24 third h2 h24 h3 k A mu orth sorted (firstPairLeakage A orth) three five seven

end RankSeven.OddCutReserve

#print axioms RankSeven.OddCutReserve.crossReserve
#print axioms RankSeven.OddCutReserve.simultaneousOddPayments
#print axioms RankSeven.OddCutReserve.realBesselTwo
#print axioms RankSeven.OddCutReserve.antiRealOrthogonal
#print axioms RankSeven.OddCutReserve.firstPairLeakage
#print axioms RankSeven.OddCutReserve.rankSixCross
#print axioms RankSeven.OddCutReserve.physicalOddPayments

