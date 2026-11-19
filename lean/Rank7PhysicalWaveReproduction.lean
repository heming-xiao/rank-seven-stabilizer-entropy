import Rank7PhysicalTwoHoleOccupancy
import Rank7PhysicalPairExchange

/-! The odd Pauli four-form columns form a tight frame on the physical
plane-wave image, in the ordered four-copy tensor convention. -/
namespace RankSeven.PhysicalWaveReproduction
open Lean.Grind Pauli GenericExteriorKernel HyperplaneIncidence
open ExteriorPauliBase (permutations oddPermutation)
open PhysicalHopping (PlaneField)
open PhysicalUniformOccupation (wave)
open WedgeSquareIntertwiner (wedgeSquareColumn)
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
attribute [local instance] Ring.intCast Semiring.natCast
variable {R C : Type} [CommRing R] [CommRing C]

private theorem sumMem {I : Type} (xs : List I) {f g : I→C} (h : ∀i∈xs,f i=g i) :
    sumOver xs f=sumOver xs g := by unfold sumOver; rw [List.map_congr_left h]
private theorem permSum {I : Type} {xs ys : List I} (p : xs.Perm ys) (f : I→C) : sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
private theorem sum0 {I : Type} (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with | nil => rfl | cons a xs ih => change 0+sumOver xs _=0; rw [ih]; grind only
private theorem xcomm {n : Nat} (a b : Basis n) : xorBasis n a b=xorBasis n b a := by
  induction n with | zero => rfl | succ n ih => simp only [xorBasis,Bool.xor_comm a.1 b.1,ih a.2 b.2]; rfl
private theorem transInj {n : Nat} {a b : Basis n} {u : Four (Basis n)} (h : PlaneOrientation.translate a u=PlaneOrientation.translate b u) : a=b := by
  have e := congrArg (fun q : Four (Basis n) => xorBasis n u.1.1 q.1.1) h
  change xorBasis n u.1.1 (xorBasis n a u.1.1)=xorBasis n u.1.1 (xorBasis n b u.1.1) at e
  rw [xcomm a u.1.1,xcomm b u.1.1,xorCancelLeft,xorCancelLeft] at e; exact e

private theorem tabTranslate {n : Nat} (d : Basis n) (u : Four (Basis n)) (j : Fin 4) :
    position (PlaneOrientation.translate d u) j=xorBasis n d (position u j) := by
  have cases4 : ∀j : Fin 4,j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
  rcases cases4 j with rfl|rfl|rfl|rfl <;> rfl
private theorem allowedImage {n : Nat} (u v : Four (Basis n)) (hp : parity u=zero n) :
    allowedTwirlEntry n u v=true ↔ ∃d,PlaneOrientation.translate d u=v := by
  rw [allowed_iff_translation,and_iff_right hp]
  constructor
  · rintro ⟨d,h⟩; exact ⟨d,PhysicalWedges.fourExt (fun j => (tabTranslate d u j).trans (h j).symm)⟩
  · rintro ⟨d,rfl⟩; exact ⟨d,tabTranslate d u⟩

private theorem projectorScalar (h : C) (hh : 2*h=1) (n : Nat) : ((qubitIndices n).length:C)*h^n=1 := by
  rw [qubitIndicesLength]
  induction n with
  | zero => simp only [Semiring.natCast_one,Semiring.pow_zero,Semiring.one_mul]
  | succ n ih =>
    rw [Nat.pow_succ,Semiring.natCast_mul,Semiring.pow_succ]
    have two : ((2:Nat):C)=2 := by change ((1+1:Nat):C)=2; rw [Semiring.natCast_succ,Semiring.natCast_one]; grind only
    rw [two]; calc
      _ = (((2^n : Nat):C)*h^n)*(2*h) := by grind only
      _ = 1 := by rw [ih,hh,Semiring.one_mul]

private theorem constantSum {I : Type} (xs : List I) (c : C) : sumOver xs (fun _ => c)=(xs.length:C)*c := by
  induction xs with
  | nil => change 0=((0:Nat):C)*c; rw [Semiring.natCast_zero]; grind only
  | cons a xs ih =>
    change c+sumOver xs _=((xs.length+1:Nat):C)*c
    rw [ih,Semiring.natCast_succ]; grind only

theorem translationProjection {n : Nat} (h : C) (hh : 2*h=1) {f : Four (Basis n)→C} (hf : PlaneField f) (u : Four (Basis n)) :
    sumOver (fourIndices (qubitIndices n)) (fun v => if allowedTwirlEntry n u v then h^n*f v else 0)=f u := by
  let L := qubitIndices n
  let Q := fourIndices L
  by_cases hp : parity u=zero n
  · have each (v : Four (Basis n)) :
        (if allowedTwirlEntry n u v then h^n*f v else 0)=sumOver L (fun d => if PlaneOrientation.translate d u=v then h^n*f v else 0) := by
      by_cases act : allowedTwirlEntry n u v=true
      · obtain ⟨d,hd⟩ := (allowedImage u v hp).mp act
        rw [ite_eq_left act]
        have ind (t : Basis n) : (if PlaneOrientation.translate t u=v then h^n*f v else 0)=(if d=t then h^n*f v else 0) := by
          by_cases eq : d=t
          · subst t; rw [ite_eq_left hd,ite_eq_left rfl]
          · have ne : PlaneOrientation.translate t u≠v := fun e => eq (transInj (hd.trans e.symm))
            rw [ite_eq_right ne,ite_eq_right eq]
        rw [sumOverCongr L ind,ExteriorPauliBase.sumOnIndex L d (fun _ => h^n*f v) (normalsNodup _) (qubitIndicesComplete _)]
      · rw [ite_eq_right act]
        have ind (t : Basis n) : (if PlaneOrientation.translate t u=v then h^n*f v else 0)=0 :=
          ite_eq_right (fun e => act ((allowedImage u v hp).mpr ⟨t,e⟩))
        rw [sumOverCongr L ind,sum0]
    have two := HyperplaneInduction.pairsNodup L L (normalsNodup n) (normalsNodup n)
    have nd : Q.Nodup := HyperplaneInduction.pairsNodup _ _ two two
    have full (z : Four (Basis n)) : z∈Q := HyperplaneInduction.pairMember
        (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
        (HyperplaneInduction.pairMember (qubitIndicesComplete _) (qubitIndicesComplete _))
    rw [sumOverCongr Q each,sumOverSwap]
    have collapse (d : Basis n) : sumOver Q (fun v => if PlaneOrientation.translate d u=v then h^n*f v else 0)=h^n*f u := by
      rw [ExteriorPauliBase.sumOnIndex Q _ (fun v => h^n*f v) nd (full _),hf.invariant]
    rw [sumOverCongr L collapse,constantSum,←Semiring.mul_assoc,projectorScalar h hh,Semiring.one_mul]
  · have zeroes (v : Four (Basis n)) : (if allowedTwirlEntry n u v then h^n*f v else 0)=0 :=
      ite_eq_right (fun e => hp ((allowed_iff_translation u v).mp e).1)
    rw [sumOverCongr Q zeroes,sum0,hf.supported _ hp]

/-- The full 24-term physical Pauli four-minor acts as 24 times identity
on each alternating, translation-invariant physical plane field. -/
theorem exteriorReproduces {n : Nat} (i h : C) (hi : i^4=1) (hh : 2*h=1)
    {f : Four (Basis n)→C} (hf : PlaneField f) (alt : ∀p∈permutations,∀u,f (reorder u p)=signed (oddPermutation p) (f u)) (u : Four (Basis n)) :
    sumOver (fourIndices (qubitIndices n)) (fun v => exteriorKernel i h u v*f v)=24*f u := by
  let L := qubitIndices n
  let Q := fourIndices L
  have closed := FourCopySectors.fullPermuted L (normalsNodup n) (fun j => qubitIndicesComplete j)
  simp only [kernel_as_signed_translations i h hi hh,sumOverMulRight]
  rw [sumOverSwap]
  have each (p : ExteriorPauliBase.Permutation) (hp : p∈permutations) :
      sumOver Q (fun v => (if allowedTwirlEntry n u (reorder v p) then signed (oddPermutation p) (h^n) else 0)*f v)=f u := by
    let g (v : Four (Basis n)) := if allowedTwirlEntry n u v then h^n*f v else 0
    have b (v : Four (Basis n)) : (if allowedTwirlEntry n u (reorder v p) then signed (oddPermutation p) (h^n) else 0)*f v=g (reorder v p) := by
      unfold g; rw [alt p hp]; cases e : allowedTwirlEntry n u (reorder v p) <;> cases z : oddPermutation p <;> simp [signed] <;> grind only
    rw [sumOverCongr Q b]
    have reindex := permSum (closed p hp) g
    have normalized := translationProjection h hh hf u
    exact (show sumOver Q (fun v => g (reorder v p))=sumOver Q g by simpa only [sumOver,List.map_map,Function.comp_def] using reindex).trans normalized
  rw [sumMem permutations each,constantSum]
  have size : permutations.length=24 := by decide
  rw [size]; congr 1
  repeat rw [Semiring.natCast_succ]
  rw [Semiring.natCast_zero]; grind only

open ComplexScalar
private theorem halfC (half : R) (unit : 2*half=1) : 2*ofReal half=(1:ComplexScalar R) := by
  change ofReal (2:R)*ofReal half=ofReal (1:R); apply ComplexScalar.ext <;> simp <;> grind only

def gramFour {n : Nat} (f g : Four (Basis n)→ComplexScalar R) :=
  sumOver (fourIndices (qubitIndices n)) (fun v => star (f v)*g v)

/-- The coefficient 36 is the physical 3/2 tight-frame constant multiplied
by 24 permutations in ordered coordinates. -/
theorem physicalWaveReproduction {n : Nat} (half : R) (unit : 2*half=1) {f : Four (Basis n)→ComplexScalar R}
    (hf : PlaneField f) (alt : ∀p∈permutations,∀u,f (reorder u p)=signed (oddPermutation p) (f u)) (u : Four (Basis n)) :
    sumOver (MixedDefect.oddWords n) (fun p => wedgeSquareColumn half p u*gramFour (wedgeSquareColumn half p) f)=36*f u := by
  let Q := fourIndices (qubitIndices n)
  let P := MixedDefect.oddWords n
  let H (v : Four (Basis n)) := sumOver P (fun p => wedgeSquareColumn half p u*star (wedgeSquareColumn half p v))
  let K := exteriorKernel (imaginaryUnit (R:=R)) (ofReal half) (n:=n)
  have hh := halfC half unit
  have wh (v : Four (Basis n)) : H v=(3*ofReal half)*K u v := by
    have e := WedgeSquareIntertwiner.physicalWedgeSquareGram half unit u v
    change 2*H v=3*K u v at e
    have s := congrArg (fun c => ofReal half*c) e
    rw [←Semiring.mul_assoc,CommSemiring.mul_comm (ofReal half) 2,hh,Semiring.one_mul] at s; rw [s]; grind only
  have exp : sumOver P (fun p => wedgeSquareColumn half p u*gramFour (wedgeSquareColumn half p) f)=
      sumOver Q (fun v => H v*f v) := by
    unfold gramFour H; simp only [sumOverMulLeft,sumOverMulRight]; rw [sumOverSwap]
    apply sumOverCongr; intro v; apply sumOverCongr; intro p; grind only
  rw [exp]; simp only [wh,Semiring.mul_assoc,←sumOverMulLeft]
  have raw : sumOver Q (fun v => K u v*f v)=24*f u := exteriorReproduces _ _ imaginaryUnit_fourth hh hf alt u
  rw [raw]; calc
    _ = (2*ofReal half)*(36*f u) := by grind only
    _ = _ := by rw [hh,Semiring.one_mul]

theorem columnAlternating {n : Nat} (half : R) (p : Word n) (s : ExteriorPauliBase.Permutation)
    (hs : s∈permutations) (u : Four (Basis n)) : wedgeSquareColumn half p (reorder u s)=
      signed (oddPermutation s) (wedgeSquareColumn (R:=R) half p u) := by
  unfold wedgeSquareColumn WedgeSquareIntertwiner.alternatingWord
  rw [AlternatingTrace.alternatingRow _ s hs]
  let z := WedgeSquareIntertwiner.alternatingWord (R:=R) p u
  change ofReal half^(n+2)*(Int.cast (R:=ComplexScalar R) (FourCopySectors.coefficient .antisymmetric s)*z)=signed (oddPermutation s) (ofReal half^(n+2)*z)
  unfold signed FourCopySectors.coefficient
  cases oddPermutation s <;> simp only [Bool.false_eq_true,ite_false,ite_true,Ring.intCast_one,Ring.intCast_neg,Semiring.one_mul] <;> grind only

theorem columnReproduction {n : Nat} (half : R) (unit : 2*half=1) (p : Word n) (u : Four (Basis n)) :
    sumOver (MixedDefect.oddWords n) (fun r => wedgeSquareColumn half r u*gramFour (wedgeSquareColumn half r) (wedgeSquareColumn half p))
      =36*wedgeSquareColumn (R:=R) half p u :=
  physicalWaveReproduction half unit (PhysicalHopping.pauliColumnField half p) (columnAlternating half p) u

end RankSeven.PhysicalWaveReproduction
#print axioms RankSeven.PhysicalWaveReproduction.columnReproduction
