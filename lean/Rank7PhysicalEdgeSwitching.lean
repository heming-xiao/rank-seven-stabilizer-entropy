import Rank7PauliEdgeBlocks
import Rank7PhysicalAntiQuartic

namespace RankSeven.PhysicalEdgeSwitching

open Lean.Grind Pauli PauliEdgeBlocks PhysicalAntiQuartic
open SymmetricDefect (anti chi phase unitWord)

theorem productLabelIsWordAdd {n : Nat} (p q : Word n) : productLabel p q=wordAdd p q := by
  induction p with
  | empty => cases q; rfl
  | cons a p ih =>
    cases q with
    | cons b q =>
      simp only [productLabel,wordAdd,ih]
      cases a <;> cases b <;> rfl

private theorem directionLabel {n : Nat} (a s : Word n) : productLabel a (wordAdd a s) = s := by
  rw [productLabelIsWordAdd, ←wordAddAssoc, wordAddSelf, wordAddComm (unitWord n) s, wordAddZero]

private theorem directionAnti {n : Nat} (a s : Word n) (as_anti : anti a s=true) :
    anti a (wordAdd a s)=true := by
  rw [antiAddRight, antiSelf, as_anti]
  rfl

private theorem quadPhasePairs {C : Type} [CommRing C] (i : C) (isq : i^2= -1)
    {n : Nat} (a b c d : Word n) :
    quadPhase i a b c d = cocycle i a b*cocycle i c d*cocycle i (productLabel a b) (productLabel c d) := by
  unfold quadPhase
  rw [Semiring.mul_assoc,cocycleLaw i isq (productLabel a b) c d, ←Semiring.mul_assoc]

def edgeNegative {n : Nat} (s r u : Word n) : Bool :=
  let a := wordAdd r u
  negativeProduct a (wordAdd a s)

/-- The cyclic order depends on the commutation bit of the two representatives. -/
def cycleWords {n : Nat} (s r u v : Word n) : Four (Word n) :=
  let a := wordAdd r u
  let b := wordAdd r v
  let a' := wordAdd a s
  let b' := wordAdd b s
  if anti u v then ((a,a'),(b',b)) else ((a,a'),(b,b'))

theorem cycleWordsCyclic {n : Nat} (s r u v : Word n) (sr : anti s r=true)
    (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    let p := cycleWords s r u v
    anti p.1.1 p.1.2 = true ∧ anti p.1.2 p.2.1 = true ∧
      anti p.2.1 p.2.2 = true ∧ anti p.2.2 p.1.1 = true := by
  let a := wordAdd r u
  let b := wordAdd r v
  have as_anti := (edgeRepresentative s r u sr hu).1
  have bs_anti := (edgeRepresentative s r v sr hv).1
  change anti a s=true at as_anti
  change anti b s=true at bs_anti
  have ab := representativesPairing s r u v hu hv
  change anti a b = anti u v at ab
  have sa := (antiSymm s a).trans as_anti
  have sb := (antiSymm s b).trans bs_anti
  have ba := (antiSymm b a).trans ab
  have one := directionAnti a s as_anti
  have two := directionAnti b s bs_anti
  have twoReversed := (antiSymm (wordAdd b s) b).trans two
  have ab' : anti (wordAdd a s) b=(anti u v ^^ true) := by rw [antiAddLeft,ab,sb]
  have b'a : anti (wordAdd b s) a=(anti u v ^^ true) := by rw [antiAddLeft,ba,sa]
  have a'b' : anti (wordAdd a s) (wordAdd b s)=anti u v := by
    rw [antiAddRight,ab',antiAddLeft,as_anti,antiSelf]
    cases anti u v <;> rfl
  change let p := if anti u v then ((a,wordAdd a s),(wordAdd b s,b)) else ((a,wordAdd a s),(b,wordAdd b s))
    anti p.1.1 p.1.2 = true ∧ anti p.1.2 p.2.1 = true ∧
      anti p.2.1 p.2.2 = true ∧ anti p.2.2 p.1.1 = true
  cases h : anti u v <;> simp [h,one,two,twoReversed,ab',b'a,a'b',ba]

theorem cycleWordsLabelZero {n : Nat} (s r u v : Word n) :
    let p := cycleWords s r u v
    quadLabel p.1.1 p.1.2 p.2.1 p.2.2 = unitWord n := by
  unfold cycleWords
  generalize wordAdd r u = a
  generalize wordAdd r v = b
  cases h : anti u v
  · simp only [Bool.false_eq_true, ite_false,quadLabel,directionLabel,
      PhysicalAntiQuartic.labelAssoc,PhysicalAntiQuartic.labelSelf]
  · simp only [ite_true,quadLabel,directionLabel,PhysicalAntiQuartic.labelAssoc]
    rw [PhysicalAntiQuartic.labelComm (wordAdd b s) b,directionLabel,PhysicalAntiQuartic.labelSelf]

/-- Actual relative phase of the four-word Pauli product on the cyclic
ordering of two anticommuting edges. -/
theorem cyclicPhysicalPhase {C : Type} [CommRing C] (i : C) (isq : i^2= -1)
    {n : Nat} (s r u v : Word n) (sr : anti s r=true)
    (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    let p := cycleWords s r u v
    quadPhase i p.1.1 p.1.2 p.2.1 p.2.2 =
      -(phase (edgeNegative s r u) : C) * phase (edgeNegative s r v) * chi u v := by
  let a := wordAdd r u
  let b := wordAdd r v
  have ah := directionAnti a s (edgeRepresentative s r u sr hu).1
  have bh := directionAnti b s (edgeRepresentative s r v sr hv).1
  have stepA := anticommutingProductSign i isq a (wordAdd a s) ah
  have stepB := anticommutingProductSign i isq b (wordAdd b s) bh
  change _ = i*phase (edgeNegative s r u) at stepA
  change _ = i*phase (edgeNegative s r v) at stepB
  have revB : cocycle i (wordAdd b s) b = -(i * phase (edgeNegative s r v)) := by
    rw [cocycleSwap i (wordAdd b s) b,stepB]
    unfold chi
    rw [antiSymm (wordAdd b s) b,bh]
    change (-1:C)*_ = _
    grind
  have mulI : i*i = -1 := by
    simpa only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] using isq
  have ordinary :
      quadPhase i a (wordAdd a s) b (wordAdd b s) =
        -(phase (edgeNegative s r u) : C)*phase (edgeNegative s r v) := by
    rw [quadPhasePairs i isq, directionLabel,directionLabel,cocycleSelf,stepA,stepB]
    grind
  have flipped :
      quadPhase i a (wordAdd a s) (wordAdd b s) b =
        (phase (edgeNegative s r u) : C)*phase (edgeNegative s r v) := by
    rw [quadPhasePairs i isq, directionLabel,PhysicalAntiQuartic.labelComm (wordAdd b s) b,
      directionLabel,cocycleSelf,stepA,revB]
    grind
  dsimp only [cycleWords]
  unfold chi
  cases h : anti u v
  · simp only [Bool.false_eq_true,ite_false]
    rw [ordinary]
    change _ = _ * (1:C)
    exact (Semiring.mul_one _).symm
  · simp only [ite_true]
    rw [flipped]
    change (phase (edgeNegative s r u) : C)*phase (edgeNegative s r v) =
      -phase (edgeNegative s r u)*phase (edgeNegative s r v)*(-1)
    grind

section Real

open ComplexScalar (imaginaryUnit ofReal)
variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

/-- The off-diagonal entry is the normalized trace of the actual cyclic
physical Pauli product. The same edge paired with itself has adjacency zero. -/
noncomputable def physicalEdgeMatrix {n : Nat} (half : R) (s r u v : Word n) : R :=
  if u=v then 0
  else
    let p := cycleWords s r u v
    half^n * (quadTrace (qubitIndices n) (wordEntry imaginaryUnit p.1.1)
      (wordEntry imaginaryUnit p.1.2) (wordEntry imaginaryUnit p.2.1)
      (wordEntry imaginaryUnit p.2.2)).re

theorem physicalEdgeEntry (half : R) (unit : 2*half=1) {n : Nat}
    (s r u v : Word n) (sr : anti s r=true) (hu : perpendicular s r u=true)
    (hv : perpendicular s r v=true) :
    physicalEdgeMatrix half s r u v = edgeAdjacency (edgeNegative s r) u v := by
  by_cases e : u=v
  · simp [physicalEdgeMatrix,edgeAdjacency,e]
  · simp only [physicalEdgeMatrix,edgeAdjacency,ite_eq_right e]
    rw [physicalQuadTrace imaginaryUnit ComplexScalar.imaginaryUnit_sq,
      cycleWordsLabelZero,ite_eq_left rfl, cyclicPhysicalPhase imaginaryUnit ComplexScalar.imaginaryUnit_sq s r u v sr hu hv]
    have scale := SectorDefectAccounting.dimensionInverse half unit n
    have pn (b : Bool) : (phase b : ComplexScalar R)=ofReal (phase b : R) := by
      cases b <;> simp [phase] <;> apply ComplexScalar.ext <;> simp <;> grind
    have c : (chi u v : ComplexScalar R)=ofReal (chi u v : R) := pn (anti u v)
    have embed : (2:ComplexScalar R)^n = ofReal ((2:R)^n) :=
      (PhysicalPairedReduction.realEmbeddingPow (2:R) n).symm
    rw [embed,pn,pn,c]
    simp only [ComplexScalar.re_mul,ComplexScalar.im_mul,ComplexScalar.re_ofReal,
      ComplexScalar.im_ofReal,ComplexScalar.re_neg,ComplexScalar.im_neg]
    grind

theorem physicalEdgeNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
    [OrderedRing R] (half : R) (unit : 2*half=1) {n : Nat} (s r : Word (n+1))
    (sr : anti s r=true) (z : Word (n+1) → R) :
    let xs := perpendicularWords s r
    0 ≤ ((2:R)^n-1)*sumOver xs (fun u => (z u)^2) +
      sumOver xs (fun u => sumOver xs (fun v => z u*physicalEdgeMatrix half s r u v*z v)) := by
  dsimp only
  let xs := perpendicularWords s r
  have form :
      sumOver xs (fun u => sumOver xs (fun v => z u*physicalEdgeMatrix half s r u v*z v)) =
      sumOver xs (fun u => sumOver xs (fun v => z u*edgeAdjacency (edgeNegative s r) u v*z v)) := by
    apply AnticommutingDefect.sumCongrMem
    intro u hu
    apply AnticommutingDefect.sumCongrMem
    intro v hv
    rw [physicalEdgeEntry half unit s r u v sr (List.mem_filter.mp hu).2 (List.mem_filter.mp hv).2]
  rw [form]
  exact edgeDefectNonnegative half unit s r sr (edgeNegative s r) z

end Real

end RankSeven.PhysicalEdgeSwitching

#print axioms RankSeven.PhysicalEdgeSwitching.cycleWordsCyclic
#print axioms RankSeven.PhysicalEdgeSwitching.cyclicPhysicalPhase
#print axioms RankSeven.PhysicalEdgeSwitching.physicalEdgeEntry
#print axioms RankSeven.PhysicalEdgeSwitching.physicalEdgeNonnegative
