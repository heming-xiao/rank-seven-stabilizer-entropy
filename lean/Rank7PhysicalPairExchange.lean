import Rank7PhysicalCutCapacities

/-! Ordered-coordinate proof of the unrestricted physical two-hole exchange.
In characteristic two, translation of either four-site argument separately
preserves the physical signed Pauli kernel. -/
namespace RankSeven.PhysicalPairExchange
open Lean.Grind Pauli GenericExteriorKernel HyperplaneIncidence ExteriorPauliBase PlaneOrientation
open PhysicalWedges (mapFourSites fourExt mapFourPosition)
variable {C : Type} [CommRing C]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
private theorem leftBit : ∀ a b c d e f g h j : Bool,
    allowedBit ((j ^^ a,j ^^ b),(j ^^ c,j ^^ d)) ((e,f),(g,h)) =
      allowedBit ((a,b),(c,d)) ((e,f),(g,h)) := by decide
private theorem rightBit : ∀ a b c d e f g h j : Bool,
    allowedBit ((a,b),(c,d)) ((j ^^ e,j ^^ f),(j ^^ g,j ^^ h)) =
      allowedBit ((a,b),(c,d)) ((e,f),(g,h)) := by decide
private theorem allowedTranslate {n : Nat} (t : Basis n) (x y : Four (Basis n)) :
    allowedTwirlEntry n (translate t x) y=allowedTwirlEntry n x y ∧
    allowedTwirlEntry n x (translate t y)=allowedTwirlEntry n x y := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h := ih t.2 (remainingBits x) (remainingBits y)
    constructor
    · change (allowedBit ((t.1 ^^ x.1.1.1,t.1 ^^ x.1.2.1),(t.1 ^^ x.2.1.1,t.1 ^^ x.2.2.1)) (firstBits y) &&
        allowedTwirlEntry n (translate t.2 (remainingBits x)) (remainingBits y))=_
      rw [leftBit,h.1]; rfl
    · change (allowedBit (firstBits x) ((t.1 ^^ y.1.1.1,t.1 ^^ y.1.2.1),(t.1 ^^ y.2.1.1,t.1 ^^ y.2.2.1)) &&
        allowedTwirlEntry n (remainingBits x) (translate t.2 (remainingBits y)))=_
      rw [rightBit,h.2]; rfl

theorem kernelTranslate {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1) (t : Basis n) (x y : Four (Basis n)) :
    exteriorKernel i h (translate t x) y=exteriorKernel i h x y ∧
    exteriorKernel i h x (translate t y)=exteriorKernel i h x y := by
  have move (p : Permutation) : reorder (translate t y) p=translate t (reorder y p) := by
    change reorder (mapFourSites (xorBasis n t) y) p=mapFourSites (xorBasis n t) (reorder y p)
    apply fourExt; intro j; rw [position_reorder,mapFourPosition,mapFourPosition,position_reorder]
  constructor
  · simp only [kernel_as_signed_translations i h hi hh,(allowedTranslate t _ _).1]
  · simp only [kernel_as_signed_translations i h hi hh,move,(allowedTranslate t _ _).2]

private theorem translatePerm {n : Nat} (t : Basis n) :
    ((qubitIndices n).map (xorBasis n t)).Perm (qubitIndices n) := by
  have nd := HyperplaneIncidence.normalsNodup n
  have inj (a b : Basis n) (e : xorBasis n t a=xorBasis n t b) : a=b := by
    have eq := congrArg (xorBasis n t) e; simpa only [xorCancelLeft] using eq
  have mapped : ((qubitIndices n).map (xorBasis n t)).Nodup :=
    List.Pairwise.map _ (fun a b (ne : a≠b) e => ne (inj a b e)) nd
  apply List.perm_iff_count.mpr; intro a
  have mem : a∈(qubitIndices n).map (xorBasis n t) :=
    List.mem_map.mpr ⟨xorBasis n t a,qubitIndicesComplete _,xorCancelLeft n t a⟩
  rw [mapped.count,nd.count]; simp [mem,qubitIndicesComplete]

private theorem sumPerm {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

theorem sumTranslate {n : Nat} (t : Basis n) (f : Basis n → C) :
    sumOver (qubitIndices n) (fun a => f (xorBasis n t a))=sumOver (qubitIndices n) f := by
  simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (translatePerm t) f

private theorem xorEqZero {n : Nat} (a b : Basis n) : xorBasis n a b=zero n ↔ a=b := by
  induction n with
  | zero => cases a; cases b; simp [zero,xorBasis]
  | succ n ih =>
    rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩
    change (a ^^ b,xorBasis n x y)=(false,zero n) ↔ (a,x)=(b,y)
    simp only [Prod.mk.injEq,ih]
    cases a <;> cases b <;> simp

abbrev Edge (n : Nat) := Basis n × Basis n
def dir {n : Nat} (e : Edge n) := xorBasis n e.1 e.2
def shift {n : Nat} (d : Basis n) (e : Edge n) : Edge n := (xorBasis n d e.1,xorBasis n d e.2)
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

def exchangeEntry {n : Nat} (i h : C) (x y : Four (Basis n)) (p q : Edge n) (s t : Basis n) :=
  exteriorKernel i h x (p,(s,t))*exteriorKernel i h (q,(s,t)) y

private theorem vanishes {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1) (x y : Four (Basis n))
    (p q : Edge n) (ne : dir p≠dir q) (s t : Basis n) : exchangeEntry i h x y p q s t=0 := by
  unfold exchangeEntry
  by_cases pe : dir p=dir (s,t)
  · have bad : GenericExteriorKernel.parity (q,(s,t))≠zero n := fun e => ne (pe.trans ((xorEqZero _ _).mp e).symm)
    rw [nonplane_exterior_kernel i h hi hh _ _ bad,Semiring.mul_zero]
  · have bad : GenericExteriorKernel.parity (p,(s,t))≠zero n := fun e => pe ((xorEqZero _ _).mp e)
    rw [nonplane_right_exterior_kernel i h hi hh _ _ bad,Semiring.zero_mul]

/-- Equality of the two-hole cross Grams, in full ordered coordinates.
The two sums use both orders of the residual pair and hence have the
same factor of two relative to increasing exterior coordinates. -/
theorem physicalPairExchange {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1) (x y : Four (Basis n)) (p q : Edge n) :
    sumOver (qubitIndices n) (fun s => sumOver (qubitIndices n) (fun t => exchangeEntry i h x y p q s t)) =
    sumOver (qubitIndices n) (fun s => sumOver (qubitIndices n) (fun t => exchangeEntry i h x y q p s t)) := by
  let xs := qubitIndices n
  by_cases eq : dir p=dir q
  · let d := xorBasis n p.1 q.1
    have pe := (align p q eq).1
    have qe := (align p q eq).2
    have row (s t : Basis n) : exchangeEntry i h x y p q s t =
        exchangeEntry i h x y q p (xorBasis n d s) (xorBasis n d t) := by
      unfold exchangeEntry
      have l := (kernelTranslate i h hi hh d x (p,(s,t))).2
      have r := (kernelTranslate i h hi hh d (q,(s,t)) y).1
      change exteriorKernel i h x (shift d p,shift d (s,t))=_ at l
      change exteriorKernel i h (shift d q,shift d (s,t)) y=_ at r
      rw [pe] at l; rw [qe] at r; rw [←l,←r]; rfl
    simp only [row,sumTranslate]
    exact sumTranslate d (fun s => sumOver xs (exchangeEntry i h x y q p s))
  · simp only [vanishes i h hi hh x y p q eq,vanishes i h hi hh x y q p (Ne.symm eq)]

end RankSeven.PhysicalPairExchange
#print axioms RankSeven.PhysicalPairExchange.physicalPairExchange
