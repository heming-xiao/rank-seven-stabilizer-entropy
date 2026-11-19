import Rank7PhysicalCutCapacities
import Rank7FiveShuffleCAR

/-! Particle-hole antisymmetry of the physical 3-to-5 exterior kernel.
The finite table concerns only one binary coordinate. Tensor induction proves
the unrestricted result in all qubit dimensions. -/
namespace RankSeven.PhysicalEightTransport
open Lean.Grind Pauli ComplexScalar GenericExteriorKernel ExteriorPauliBase
open PhysicalCutCapacities (Triple extend)
open FiveShuffleCAR (Five atSlot)
variable {C α β : Type} [CommRing C]
abbrev Eight (α : Type) := Triple α × Five α
def boundarySwap (x : Eight α) : Eight α := ((x.1.1,x.2.1.1),((x.1.2,x.2.1.2),x.2.2))
def mapFive (F : α → β) (u : Five α) : Five β := ((F u.1.1,F u.1.2),(F u.2.1.1,F u.2.1.2),F u.2.2)
def mapEight (F : α → β) (u : Eight α) : Eight β := (((F u.1.1.1,F u.1.1.2),F u.1.2),mapFive F u.2)
def skip (j : Fin 5) (k : Fin 4) : Fin 5 := ⟨if k.val<j.val then k.val else k.val+1,by split <;> omega⟩
def drop (v : Five α) (j : Fin 5) : Four α :=
  ((atSlot v (skip j 0),atSlot v (skip j 1)),(atSlot v (skip j 2),atSlot v (skip j 3)))
abbrev Symbol := Fin 5 × ExteriorPauliBase.Permutation
private def directions : List Symbol := productIndices (List.finRange 5) ExteriorPauliBase.permutations
private def left (r : Symbol) (u : Eight α) := extend u.1 (atSlot u.2 r.1)
private def right (r : Symbol) (u : Eight α) := reorder (drop u.2 r.1) r.2
private def sign (r : Symbol) := (r.1.val%2==1) ^^ oddPermutation r.2
private def onBit (r : Symbol) (u : Eight Bool) := allowedBit (left r u) (right r u)
private def onSite {n} (r : Symbol) (u : Eight (Basis n)) := allowedTwirlEntry n (left r u) (right r u)

private theorem mapSlot (F : α → β) (v : Five α) (i : Fin 5) : atSlot (mapFive F v) i=F (atSlot v i) := by
  have e : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by revert i; decide
  rcases e with rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem mapLeft (F : α → β) (u : Eight α) (r : Symbol) :
    left r (mapEight F u)=PhysicalWedges.mapFourSites F (left r u) := by
  unfold left mapEight extend PhysicalWedges.mapFourSites; simp only [mapSlot]
private theorem mapRight (F : α → β) (u : Eight α) (r : Symbol) :
    right r (mapEight F u)=PhysicalWedges.mapFourSites F (right r u) := by
  have md : drop (mapFive F u.2) r.1=PhysicalWedges.mapFourSites F (drop u.2 r.1) := by
    unfold drop PhysicalWedges.mapFourSites; simp only [mapSlot]
  change reorder (drop (mapFive F u.2) r.1) r.2=_
  rw [md]; apply PhysicalWedges.fourExt; intro i
  simp only [position_reorder,PhysicalWedges.mapFourPosition,right]

private def wordSelector (k : Fin 120) : Symbol :=
  ((Fin.ofNat 5 (k.val/24)),[((0,1),(2,3)),
    ((0,1),(3,2)),
    ((0,2),(1,3)),
    ((0,2),(3,1)),
    ((0,3),(1,2)),
    ((0,3),(2,1)),
    ((1,0),(2,3)),
    ((1,0),(3,2)),
    ((1,2),(0,3)),
    ((1,2),(3,0)),
    ((1,3),(0,2)),
    ((1,3),(2,0)),
    ((2,0),(1,3)),
    ((2,0),(3,1)),
    ((2,1),(0,3)),
    ((2,1),(3,0)),
    ((2,3),(0,1)),
    ((2,3),(1,0)),
    ((3,0),(1,2)),
    ((3,0),(2,1)),
    ((3,1),(0,2)),
    ((3,1),(2,0)),
    ((3,2),(0,1)),
    ((3,2),(1,0))].getD (k.val%24) ((0,1),(2,3)))
private def mate (k : Fin 120) : Fin 120 :=
  [1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,
    14,17,16,19,18,21,20,23,22,48,49,72,73,96,97,
    54,55,103,102,79,78,89,88,113,112,64,65,118,119,94,
    95,70,71,24,25,74,75,98,99,30,31,106,107,82,83,
    84,85,108,109,40,41,116,117,92,93,46,47,26,27,50,
    51,100,101,35,34,104,105,58,59,60,61,110,111,37,36,
    114,115,68,69,44,45,28,29,52,53,76,77,33,32,80,
    81,56,57,62,63,86,87,39,38,90,91,66,67,42,43].getD k.val 0
private theorem labels : (List.finRange 120).map wordSelector=directions := by decide
private theorem matesPerm : ((List.finRange 120).map mate).Perm (List.finRange 120) := by decide

/- The eight truth-table columns enumerate all one-bit eight-tuples. Each
bitwise expression below thus represents 256 ordinary Boolean evaluations. -/
private def columns : Eight (BitVec 256) :=
  (((0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),((0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),0xffffffffffffffffffffffffffffffff00000000000000000000000000000000))
private def code (u : Eight Bool) : Fin 256 := Fin.ofNat 256 (
    u.1.1.1.toNat+2*u.1.1.2.toNat+4*u.1.2.toNat+8*u.2.1.1.toNat+
    16*u.2.1.2.toNat+32*u.2.2.1.1.toNat+64*u.2.2.1.2.toNat+128*u.2.2.2.toNat)
private def readAt (k : Fin 256) (v : BitVec 256) := v[k.val]
set_option maxRecDepth 40000 in
private theorem completeBits : ∀ a b c d e f g h : Bool,
    let u : Eight Bool := (((a,b),c),((d,e),(f,g),h))
    mapEight (readAt (code u)) columns=u := by decide

private def mask (r : Symbol) (u : Eight (BitVec 256)) : BitVec 256 :=
  let a := left r u
  let b := right r u
  let t := a.1.1 ^^^ b.1.1
  ~~~((t ^^^ (a.1.2 ^^^ b.1.2)) ||| (t ^^^ (a.2.1 ^^^ b.2.1)) |||
      (t ^^^ (a.2.2 ^^^ b.2.2)) ||| ((a.1.1 ^^^ a.1.2) ^^^ (a.2.1 ^^^ a.2.2)))
private theorem booleanForm (a b c d e f g h : Bool) :
    (!((((a^^e)^^(b^^f)) || ((a^^e)^^(c^^g)) || ((a^^e)^^(d^^h))) || ((a^^b)^^(c^^d)))) =
    allowedBit ((a,b),(c,d)) ((e,f),(g,h)) := by revert a b c d e f g h; decide
private theorem reflectMask (r : Symbol) (u : Eight (BitVec 256)) (k : Fin 256) :
    readAt k (mask r u)=onBit r (mapEight (readAt k) u) := by
  unfold onBit; rw [mapLeft,mapRight]; unfold readAt mask PhysicalWedges.mapFourSites
  simp only [BitVec.getElem_not,BitVec.getElem_or,BitVec.getElem_xor]
  exact booleanForm _ _ _ _ _ _ _ _

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1600000 in
private theorem matchTable : ∀ k : Fin 120,
    mask (wordSelector k) (boundarySwap columns)=mask (wordSelector (mate k)) columns ∧
    sign (wordSelector k)= !sign (wordSelector (mate k)) := by decide

private theorem bitExchange (k : Fin 120) (u : Eight Bool) :
    onBit (wordSelector k) (boundarySwap u)=onBit (wordSelector (mate k)) u := by
  rcases u with ⟨⟨⟨a,b⟩,c⟩,⟨d,e⟩,⟨f,g⟩,h⟩
  let u : Eight Bool := (((a,b),c),((d,e),(f,g),h))
  have hu := completeBits a b c d e f g h
  change mapEight (readAt (code u)) columns=u at hu
  have eq := congrArg (readAt (code u)) (matchTable k).1
  rw [reflectMask,reflectMask,show mapEight (readAt (code u)) (boundarySwap columns)=boundarySwap (mapEight (readAt (code u)) columns) from rfl,hu] at eq
  exact eq

private theorem step {n} (r : Symbol) (u : Eight (Basis (n+1))) :
    onSite r u=(onBit r (mapEight Prod.fst u) && onSite r (mapEight Prod.snd u)) := by
  change Eight (Bool × Basis n) at u
  unfold onSite onBit; simp only [mapLeft,mapRight]; rfl
private theorem siteExchange {n} (k : Fin 120) (u : Eight (Basis n)) :
    onSite (wordSelector k) (boundarySwap u)=onSite (wordSelector (mate k)) u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [step,step]
    change (onBit (wordSelector k) (boundarySwap (mapEight Prod.fst u)) && onSite (wordSelector k) (boundarySwap (mapEight Prod.snd u)))=_
    rw [bitExchange,ih]

def transportKernel {n} (i h : C) (u : Triple (Basis n)) (v : Five (Basis n)) :=
  sumOver (List.finRange 5) (fun j => signed (j.val%2==1) (exteriorKernel i h (extend u (atSlot v j)) (drop v j)))

private theorem productSum {A B : Type} (xs : List A) (ys : List B) (F : A × B → C) :
    sumOver (productIndices xs ys) F=sumOver xs (fun i => sumOver ys (fun j => F (i,j))) := by
  unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
private theorem minusSum {A : Type} (xs : List A) (F : A → C) : sumOver xs (fun i => -F i)= -sumOver xs F := by
  have e := sumOverMulLeft xs F (-1); simp only [Ring.neg_mul,Semiring.one_mul] at e; exact e.symm
private theorem signedSum {A : Type} (xs : List A) (a : Bool) (F : A → C) :
    signed a (sumOver xs F)=sumOver xs (fun i => signed a (F i)) := by
  cases a <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true]; exact (minusSum _ _).symm

private def entry {n} (h : C) (r : Symbol) (u : Eight (Basis n)) :=
  if onSite r u then signed (sign r) (h^n) else 0
private theorem expand {n} (i h : C) (hi : i^4=1) (hh : 2*h=1) (u : Eight (Basis n)) :
    transportKernel i h u.1 u.2=sumOver (List.finRange 120) (fun k => entry h (wordSelector k) u) := by
  have flat : sumOver directions (fun r => entry h r u)=sumOver (List.finRange 120) (fun k => entry h (wordSelector k) u) := by
    rw [←labels]; simp only [sumOver,List.map_map,Function.comp_def]
  refine Eq.trans ?_ flat
  unfold directions transportKernel; rw [productSum]; simp only [kernel_as_signed_translations i h hi hh,signedSum]
  apply sumOverCongr; intro j; apply sumOverCongr; intro p
  change signed (j.val%2==1) (if onSite (j,p) u then signed (oddPermutation p) (h^n) else 0)=entry h (j,p) u
  unfold entry sign
  cases (j.val%2==1) <;> cases (oddPermutation p) <;> cases (onSite (j,p) u) <;> simp [signed] <;> grind only

private theorem permSum {A : Type} {xs ys : List A} (p : xs.Perm ys) (f : A → C) :
    sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind only
  | trans _ _ e1 e2 => exact e1.trans e2

/-- Particle-hole antisymmetry at the boundary of the three and five slots.
This holds for all computational indices, including coincidences. -/
theorem transportCross {n} (i h : C) (hi : i^4=1) (hh : 2*h=1)
    (a b c d e f g j : Basis n) :
    transportKernel i h ((a,b),d) ((c,e),(f,g),j)=
      -transportKernel i h ((a,b),c) ((d,e),(f,g),j) := by
  let u : Eight (Basis n) := (((a,b),c),((d,e),(f,g),j))
  change transportKernel i h (boundarySwap u).1 (boundarySwap u).2= -transportKernel i h u.1 u.2
  rw [expand i h hi hh (boundarySwap u),expand i h hi hh u]
  have row (k : Fin 120) : entry h (wordSelector k) (boundarySwap u)= -entry h (wordSelector (mate k)) u := by
    unfold entry; rw [siteExchange,(matchTable k).2]
    cases onSite (wordSelector (mate k)) u <;> cases sign (wordSelector (mate k)) <;> simp [signed] <;> grind only
  rw [sumOverCongr _ row,minusSum]
  apply congrArg Neg.neg
  simpa only [sumOver,List.map_map,Function.comp_def] using permSum matesPerm (fun k => entry h (wordSelector k) u)

end RankSeven.PhysicalEightTransport
#print axioms RankSeven.PhysicalEightTransport.transportCross
