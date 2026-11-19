import Rank7PhysicalPairExchange

/-! The holomorphic hopping square in ordered computational coordinates.
An edge field may have arbitrary complex coefficients. -/
namespace RankSeven.PhysicalHopping
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase HyperplaneIncidence
open PhysicalPairExchange (Edge dir shift sumTranslate)
open PhysicalWedges (mapFourSites fourExt mapFourPosition)
variable {C R : Type} [CommRing C] [CommRing R]

/-- The two properties of a Pauli wedge column used in pair exchange. -/
structure PlaneField {n : Nat} (f : Four (Basis n) → C) : Prop where
  invariant (d : Basis n) (u : Four (Basis n)) : f (PlaneOrientation.translate d u) = f u
  supported (u : Four (Basis n)) (h : GenericExteriorKernel.parity u ≠ zero n) : f u = 0

private theorem sumEqMem {I : Type} (xs : List I) (f g : I → C)
    (h : ∀ i∈xs, f i = g i) : sumOver xs f=sumOver xs g := by
  unfold sumOver; rw [List.map_congr_left h]
private theorem sum0 {I : Type} (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs <;> simp_all [sumOver,List.map,AddCommMonoid.zero_add]

theorem fieldCombination {n : Nat} {I : Type} (xs : List I) (c : I → C) (f : I → Four (Basis n) → C)
    (hf : ∀ i∈xs, PlaneField (f i)) : PlaneField (fun u => sumOver xs (fun i => c i*f i u)) := by
  constructor
  · intro d u; apply sumEqMem; intro i hi; rw [(hf i hi).invariant]
  · intro u h; rw [←sum0 (C:=C) xs]; apply sumEqMem; intro i hi; rw [(hf i hi).supported u h,Semiring.mul_zero]

private def doubled {n : Nat} (i : C) (p : Word n) (x : Four (Basis n)) : C :=
  wordEntry i p x.1.1 x.1.2*wordEntry i p x.2.1 x.2.2
private theorem doubleBit (i : C) (p : Axis) (a b c d e : Bool) :
    entry i p (e^^a) (e^^b)*entry i p (e^^c) (e^^d)=entry i p a b*entry i p c d := by
  cases p <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp [entry] <;> grind only
private theorem doubleOff (i : C) (p : Axis) (a b c d : Bool)
    (h : ((a^^b)^^(c^^d))≠false) : entry i p a b*entry i p c d=0 := by
  cases p <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [entry] <;> grind only
private theorem doubleCons {n : Nat} (i : C) (p : Axis) (t : Word n) (u : Four (Basis (n+1))) :
    doubled i (.cons p t) u =
    (entry i p u.1.1.1 u.1.2.1*entry i p u.2.1.1 u.2.2.1) * doubled i t (remainingBits u) := by
  rcases u with ⟨⟨⟨a,a'⟩,b,b'⟩,⟨c,c'⟩,d,d'⟩
  simp only [doubled,remainingBits,wordEntry]; grind only
private theorem doubledField {n : Nat} (i : C) (p : Word n) : PlaneField (doubled i p) := by
  induction p with
  | empty => constructor; intros; rfl; intro u h; exact False.elim (h rfl)
  | cons p t ih =>
    constructor
    · intro d u
      rw [doubleCons,doubleCons]
      change (entry i p (d.1 ^^ u.1.1.1) (d.1 ^^ u.1.2.1)*entry i p (d.1 ^^ u.2.1.1) (d.1 ^^ u.2.2.1)) *
        doubled i t (PlaneOrientation.translate d.2 (remainingBits u))=_
      rw [doubleBit,ih.invariant]
    · intro u h
      rw [doubleCons]
      by_cases e : ((u.1.1.1^^u.1.2.1)^^(u.2.1.1^^u.2.2.1))=false
      · have ht : GenericExteriorKernel.parity (remainingBits u) ≠ zero _ := by
          intro hz; apply h; exact Prod.ext e hz
        rw [ih.supported _ ht,Semiring.mul_zero]
      · rw [doubleOff i p _ _ _ _ e,Semiring.zero_mul]

private theorem moveTranslate {n} (d : Basis n) (u : Four (Basis n)) (p : Permutation) :
    reorder (PlaneOrientation.translate d u) p=PlaneOrientation.translate d (reorder u p) := by
  change reorder (mapFourSites (xorBasis n d) u) p=mapFourSites (xorBasis n d) (reorder u p)
  apply fourExt; intro j; rw [position_reorder,mapFourPosition,mapFourPosition,position_reorder]

theorem pauliColumnField (half : R) {n} (p : Word n) : PlaneField (WedgeSquareIntertwiner.wedgeSquareColumn half p) := by
  have hd := doubledField (imaginaryUnit (R:=R)) p
  change PlaneField (fun u => _ * FourCopySectors.act _ (doubled imaginaryUnit p) u)
  constructor
  · intro d u; unfold FourCopySectors.act; simp only [moveTranslate,hd.invariant]
  · intro u ne; unfold FourCopySectors.act
    have z : ∀ w∈permutations, doubled (imaginaryUnit (R:=R)) p (reorder u w)=0 := fun w hw =>
      hd.supported _ (by rw [parity_reorder u w hw]; exact ne)
    have hzero (k : Permutation → ComplexScalar R) :
        sumOver permutations (fun w => k w * doubled imaginaryUnit p (reorder u w))=0 := by
      rw [←sum0 (C:=ComplexScalar R) permutations]; apply sumEqMem
      intro i hi; rw [z i hi,Semiring.mul_zero]
    rw [hzero,Semiring.mul_zero]

private theorem xorEqZero {n : Nat} (a b : Basis n) : xorBasis n a b=zero n ↔ a=b := by
  induction n with
  | zero => cases a; cases b; simp [zero,xorBasis]
  | succ n ih =>
    rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩
    change (a ^^ b,xorBasis n x y)=(false,zero n) ↔ (a,x)=(b,y)
    simp only [Prod.mk.injEq,ih]
    cases a <;> cases b <;> simp

private theorem align {n : Nat} (p q : Edge n) (eq : dir p=dir q) :
    shift (xorBasis n p.1 q.1) p=q ∧ shift (xorBasis n p.1 q.1) q=p := by
  induction n with
  | zero => rcases p with ⟨⟨⟩,⟨⟩⟩; rcases q with ⟨⟨⟩,⟨⟩⟩; exact ⟨rfl,rfl⟩
  | succ n ih =>
    rcases p with ⟨⟨a,x⟩,b,y⟩; rcases q with ⟨⟨c,z⟩,d,w⟩
    change (a ^^ b,dir (x,y))=(c ^^ d,dir (z,w)) at eq
    obtain ⟨h,t⟩ := Prod.mk.inj eq
    obtain ⟨u,v⟩ := ih (x,y) (z,w) t
    simp only [shift,Prod.mk.injEq] at u v
    simp only [shift,xorBasis]
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private def entryProduct {n} (f g : Four (Basis n) → C) (p q : Edge n) (s t : Basis n) :=
  f (p,(s,t))*g (q,(s,t))

private theorem vanishes {n} {f g : Four (Basis n) → C} (hf : PlaneField f) (hg : PlaneField g)
    (p q : Edge n) (ne : dir p≠dir q) (s t : Basis n) : entryProduct f g p q s t=0 := by
  unfold entryProduct
  by_cases e : dir p=dir (s,t)
  · have bad : GenericExteriorKernel.parity (q,(s,t))≠zero n := fun z => ne (e.trans ((xorEqZero _ _).mp z).symm)
    rw [hg.supported _ bad,Semiring.mul_zero]
  · have bad : GenericExteriorKernel.parity (p,(s,t))≠zero n := fun z => e ((xorEqZero _ _).mp z)
    rw [hf.supported _ bad,Semiring.zero_mul]

/-- Coordinate pair exchange for every two physical plane fields. -/
theorem coordinateExchange {n} {f g : Four (Basis n) → C} (hf : PlaneField f) (hg : PlaneField g) (p q : Edge n) :
    sumOver (qubitIndices n) (fun s => sumOver (qubitIndices n) (fun t => entryProduct f g p q s t)) =
    sumOver (qubitIndices n) (fun s => sumOver (qubitIndices n) (fun t => entryProduct f g q p s t)) := by
  by_cases eq : dir p=dir q
  · let d := xorBasis n p.1 q.1
    have pe := (align p q eq).1
    have qe := (align p q eq).2
    have row (s t : Basis n) : entryProduct f g p q s t =
        entryProduct f g q p (xorBasis n d s) (xorBasis n d t) := by
      unfold entryProduct
      have l := hf.invariant d (p,(s,t))
      have r := hg.invariant d (q,(s,t))
      change f (shift d p,shift d (s,t))=_ at l
      change g (shift d q,shift d (s,t))=_ at r
      rw [pe] at l; rw [qe] at r; rw [←l,←r]; rfl
    simp only [row,sumTranslate]
    exact sumTranslate d (fun s => sumOver (qubitIndices n) (entryProduct f g q p s))
  · simp only [vanishes hf hg p q eq,vanishes hf hg q p (Ne.symm eq)]

def edges (n : Nat) := productIndices (qubitIndices n) (qubitIndices n)
private theorem byEdges {n} (f : Edge n → C) :
    sumOver (edges n) f=sumOver (qubitIndices n) (fun i => sumOver (qubitIndices n) (fun j => f (i,j))) := by
  unfold edges productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i
  simp [sumOver,List.map_map,Function.comp_def]

def contract {n} (a : Edge n → C) (f : Four (Basis n) → C) (r : Edge n) : C :=
  sumOver (edges n) (fun p => a p*f (p,r))

def pairing {n} (f g : Edge n → ComplexScalar R) :=
  sumOver (edges n) (fun r => star (f r)*g r)

private theorem transpose3 {I J K : Type} (xs : List I) (ys : List J) (zs : List K) (f : I → J → K → C) :
    sumOver xs (fun x => sumOver ys (fun y => sumOver zs (f x y))) =
    sumOver ys (fun y => sumOver zs (fun z => sumOver xs (fun x => f x y z))) := by
  rw [sumOverSwap]; apply sumOverCongr; intro y; rw [sumOverSwap]

private theorem gramExpansion {n} (a b : Edge n → ComplexScalar R) (f g : Four (Basis n) → ComplexScalar R) :
    pairing (contract a f) (contract b g)=sumOver (edges n) (fun p => sumOver (edges n) (fun q =>
      (star (a p)*b q) * sumOver (edges n) (fun r => star (f (p,r))*g (q,r)))) := by
  unfold pairing contract
  simp only [ComplexExterior.starSumOver,star_mul,sumOverMulRight,sumOverMulLeft]
  rw [transpose3,sumOverSwap]; apply sumOverCongr; intro p; apply sumOverCongr; intro q; apply sumOverCongr; intro r
  grind only

private theorem starField {n} {f : Four (Basis n) → ComplexScalar R} (hf : PlaneField f) :
    PlaneField (fun u => star (f u)) := by
  constructor
  · intro d u; rw [hf.invariant]
  · intro u ne; rw [hf.supported u ne]; exact star_ofReal (0:R)

/-- Sesquilinear two-hole exchange with the two conjugations needed for complex frames. -/
theorem complexPairExchange {n} {f g : Four (Basis n) → ComplexScalar R}
    (hf : PlaneField f) (hg : PlaneField g) (a b : Edge n → ComplexScalar R) :
    pairing (contract a f) (contract b g) =
    pairing (contract (fun p => star (b p)) f) (contract (fun p => star (a p)) g) := by
  have cross (p q : Edge n) :
      sumOver (edges n) (fun r => star (f (p,r))*g (q,r)) =
      sumOver (edges n) (fun r => star (f (q,r))*g (p,r)) := by
    rw [byEdges,byEdges]; exact coordinateExchange (starField hf) hg p q
  rw [gramExpansion,gramExpansion,sumOverSwap]
  apply sumOverCongr; intro q; apply sumOverCongr; intro p
  rw [star_star,cross]; grind only

private theorem squareExpansion {I S : Type} (xs : List I) (rs : List S) (z : I → S → ComplexScalar R) :
    sumOver xs (fun i => sumOver xs (fun j => sumOver rs (fun t => star (z j t)*z i t))) =
    sumOver rs (fun t => ofReal (normSq (sumOver xs (fun i => z i t)))) := by
  simp only [←star_mul_self,ComplexExterior.starSumOver,sumOverMulRight,sumOverMulLeft]
  rw [←transpose3]

/-- The complete single-contraction cross term for a fixed first index is an explicit
sum of squared norms. Both the frame covectors and the Pauli-column coefficients
may be complex; neither orthogonality nor reality is required for this identity. -/
theorem hoppingSquare {n} {I : Type} (xs : List I) (a : I → Edge n → ComplexScalar R)
    (f : I → Four (Basis n) → ComplexScalar R) (hf : ∀ i, PlaneField (f i)) :
    sumOver xs (fun i => sumOver xs (fun j => pairing (contract (a i) (f j)) (contract (a j) (f i)))) =
    sumOver (edges n) (fun r => ofReal (normSq (sumOver xs (fun j =>
      contract (fun p => star (a j p)) (f j) r)))) := by
  have row (i j : I) := complexPairExchange (hf j) (hf i) (a i) (a j)
  exact (sumOverCongr xs (fun i => sumOverCongr xs (row i))).trans (squareExpansion xs (edges n)
    (fun i r => contract (fun p => star (a i p)) (f i) r))

/-- Equation (194) summed over both exchanged modes, for arbitrary elements
of the span of the actual Pauli wedge columns in every dimension. -/
theorem physicalHoppingSquare {n} {I : Type} (half : R) (xs : List I)
    (a : I → Edge n → ComplexScalar R) (c : I → Word n → ComplexScalar R) :
    let f := fun j u => sumOver (MixedDefect.oddWords n) (fun p => c j p*WedgeSquareIntertwiner.wedgeSquareColumn half p u)
    sumOver xs (fun i => sumOver xs (fun j => pairing (contract (a i) (f j)) (contract (a j) (f i)))) =
    sumOver (edges n) (fun r => ofReal (normSq (sumOver xs (fun j =>
      contract (fun p => star (a j p)) (f j) r)))) := by
  apply hoppingSquare; intro j; apply fieldCombination; intro p _; exact pauliColumnField half p

end RankSeven.PhysicalHopping
#print axioms RankSeven.PhysicalHopping.physicalHoppingSquare
#print axioms RankSeven.PhysicalHopping.pauliColumnField
#print axioms RankSeven.PhysicalHopping.coordinateExchange
