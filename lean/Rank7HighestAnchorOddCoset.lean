import Rank7HighestAnchorCommutation

namespace RankSeven.HighestAnchorOddCoset

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup
open StabilizerCosetTransform StabilizerOddSector StabilizerPairedCharacters
open JointProbeGram (oddAverage)
open MixedDefect (oddWord oddWords)
open PhysicalCompressionEffect (OrthonormalFrame)
open JointProbePayment (pairWeight)
open WeightedProbeShift (physicalPayment)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
attribute [local instance] Semiring.natCast

/-- The unique coset on which transpose parity is constant has even sign.
The global Gauss sum is positive and every other coset has zero signed sum. -/
theorem evenCoset {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (z : TransposeOffset G) (c : Word n)
    (same : equiv G z.offset c) : oddWord c=false := by
  classical
  obtain ⟨T⟩ := transversalExists G
  let d := (2:R)^n
  let s (p : Word n) := (wordSign p:R)
  have sumS : sumOver (words n) s=d := by
    have g := MixedDefect.transposeGauss (C:=R) (unitWord n) (unitWord n)
    have a (p : Word n) : (chi p (unitWord n):R)=1 := by rw [chi,antiZero]; rfl
    have id : s (unitWord n)=1 := by unfold s; rw [MixedDefect.oddWordTransposeSign,oddId]; rfl
    change sumOver (words n) (fun p => s p*chi p (unitWord n)*chi p (unitWord n))=d*s (unitWord n)*s (unitWord n)*chi (unitWord n) (unitWord n) at g
    simp only [a,id,Semiring.mul_one] at g; exact g
  have eq (p g : Word n) (hg : g∈G.labels) : s (wordAdd g p)=s p*chi (wordAdd z.offset p) g := by
    unfold s; rw [signAdd,charAddLeft,chiSymm g p,MixedDefect.oddWordTransposeSign g,z.agrees g hg]; unfold chi; grind only
  have all := enumerate T s
  have eval (p : Word n) : sumOver G.labels (fun g => s (wordAdd g p))=if equiv G z.offset p then s p*d else 0 := by
    rw [AnticommutingDefect.sumCongrMem G.labels _ _ (eq p),←sumOverMulLeft,characterSum,cardinalCast (R:=R)]
    unfold equiv; split <;> grind only
  simp only [eval] at all
  obtain ⟨r,hr,hrz⟩ := T.cover z.offset
  have rep (p : Word n) (hp : p∈T.reps) : equiv G z.offset p ↔ p=r :=
    ⟨fun e => T.separated p hp r hr (trans (symm e) hrz),fun e => e ▸ hrz⟩
  rw [AnticommutingDefect.sumCongrMem T.reps _ (fun p => if r=p then s r*d else 0) (fun p hp => by
    rw [rep p hp]; by_cases h : p=r <;> simp [h,Ne.symm]),ExteriorPauliBase.sumOnIndex T.reps r _ T.nodup hr] at all
  have ce : equiv G c r := trans (symm same) hrz
  let g := wordAdd c r
  have src : wordAdd g r=c := wordAddCancel c r
  have C := eq r g ce
  have commute := (G.criterion (wordAdd z.offset r)).mp hrz g ce
  change s (wordAdd g r)=s r*chi (wordAdd z.offset r) g at C
  rw [src,chi,commute] at C
  change s c=s r*1 at C
  have inv : d*half^n=1 := SectorDefectAccounting.dimensionInverse half h2 n
  rw [sumS] at all
  have b := congrArg (fun y => y*half^n) all
  have nrm := congrArg (fun z => s r*z) inv
  have h : s c=1 := by grind only
  unfold s at h; rw [MixedDefect.oddWordTransposeSign] at h
  cases o : oddWord c
  · rfl
  · rw [o] at h; change -(1:R)=1 at h; have := OrderedRing.zero_lt_one (R:=R); grind only

theorem oddKernel {n : Nat} {G : MaximalFamily n} (z : TransposeOffset G) (p g : Word n)
    (op : oddWord p=true) (hg : g∈G.labels) :
    oddWord (wordAdd g p)=true ↔ anti (wordAdd z.offset p) g=false := by
  rw [oddAdd,z.agrees g hg,op,antiAddLeft,antiSymm g p]
  cases anti z.offset g <;> cases anti p g <;> decide

section Field
variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F]
noncomputable local instance : DecidableRel ((·<·) : F→F→Prop) := fun _ _ => Classical.propDecidable _

/-- A genuine half-sized, all-odd Pauli coset carries more than 5/8 of the highest-pair norm. -/
theorem physicalOddCoset (half : F) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3)→Fin 7→ComplexScalar F)
    (mu : Fin 7 → F) (orth : OrthonormalFrame A) (small : 15*(physicalPayment half h2 k A mu).kappaOne≤2) :
    let n := k+3
    ∃p∈oddWords n,∃G : MaximalFamily n,∃z : TransposeOffset G,
      let t := wordAdd z.offset p
      t∉G.labels ∧ 2*half^n*sumOver G.labels (fun g => if anti t g then 0 else (1:F))=1 ∧
      (∀g∈G.labels,oddWord (wordAdd g p)=true ↔ anti t g=false) ∧
      5<8*oddAverage half (fun q => if wordAdd p q∈G.labels then pairWeight A q 0 1 else 0) := by
  classical
  obtain ⟨p,hp,u,G,contained,mass⟩ := HighestAnchorCommutation.physicalHeavyCoset half h2 k A mu orth small
  obtain ⟨T⟩ := transversalExists G
  obtain ⟨z⟩ := offsetExists half h2 T
  have op := (List.mem_filter.mp hp).2
  change oddWord p=true at op
  have diff : wordAdd z.offset p∉G.labels := by
    intro h; have bad := evenCoset half h2 z p h; rw [bad] at op; contradiction
  refine ⟨p,hp,G,z,diff,halfGroup half h2 (G:=G) _ diff,fun g hg => oddKernel z p g op hg,?_⟩
  let f (q : Word (k+3)) := pairWeight A q 0 1
  let a (q : Word (k+3)) := if u<f q then f q else 0
  let b (q : Word (k+3)) := if wordAdd p q∈G.labels then f q else 0
  have each (q : Word (k+3)) (hq : q∈oddWords (k+3)) : a q≤b q := by
    have nn : 0≤f q := normSq_nonnegative _
    by_cases h : u<f q
    · have t := contained q hq h; simp [a,b,h,t]
    · unfold a b; simp only [h,ite_false]; split <;> grind only
  have raw := Compression.sumOverNonnegative (oddWords (k+3)) (fun q => b q-a q) (fun q hq => by have := each q hq; grind only)
  rw [Compression.sumOverSub] at raw
  have nn (r : Nat) : 0≤half^r := by
    induction r with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ r ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have le := OrderedRing.mul_le_mul_of_nonneg_left (show sumOver (oddWords (k+3)) a≤sumOver (oddWords (k+3)) b by grind only)
    (show 0≤2*half^(k+3) by have := nn (k+3); grind only)
  change oddAverage half a≤oddAverage half b at le
  change 5<8*oddAverage half a at mass
  change 5<8*oddAverage half b; grind only

end Field

end RankSeven.HighestAnchorOddCoset

#print axioms RankSeven.HighestAnchorOddCoset.evenCoset
#print axioms RankSeven.HighestAnchorOddCoset.oddKernel
#print axioms RankSeven.HighestAnchorOddCoset.physicalOddCoset

