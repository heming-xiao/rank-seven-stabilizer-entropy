import Rank7PhysicalCompressionEffect

/-! Exact accounting for the three surviving fourth-copy sectors and the
normalized rank-seven exterior compression loss. -/
namespace RankSeven.SectorDefectAccounting

open Lean.Grind Pauli Compression
open ExteriorCuts (Wedge7 wedges amplitude)
open PhysicalCompressionEffect (physicalEntries)
open GenericExteriorKernel (supportedPair)
open PhysicalWedges (Coordinate)

variable {R α : Type} [CommRing R]

/-- Each unordered pair of positions occurs once, even at repeated eigenvalues. -/
def wedgePairs {α : Type} : List α → List (α × α)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ wedgePairs xs

private theorem sumAppend (xs ys : List α) (f : α → R) :
    sumOver (xs ++ ys) f = sumOver xs f + sumOver ys f := by
  induction xs with
  | nil => simp [sumOver] <;> grind
  | cons x xs ih =>
    simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *
    grind

theorem wedgePairTrace (xs : List α) (f : α → R) :
    2*sumOver (wedgePairs xs) (fun ij => f ij.1*f ij.2) =
      (sumOver xs f)^2 - sumOver xs (fun i => (f i)^2) := by
  induction xs with
  | nil => simp [wedgePairs,sumOver] <;> grind
  | cons x xs ih =>
    rw [wedgePairs,sumAppend]
    have head : sumOver (xs.map (fun y => (x,y))) (fun ij => f ij.1*f ij.2) =
        f x * sumOver xs f := by
      rw [sumOverMulLeft]
      simp [sumOver,List.map_map,Function.comp_def]
    rw [head]
    change _ = (f x + sumOver xs f)^2 - ((f x)^2+sumOver xs (fun i => (f i)^2))
    grind

/-- Physical eigen-amplitudes μ give Tr[(Λ²N)⁴] on distinct index pairs. -/
theorem wedgeFourthSpectrum (xs : List α) (mu : α → R) :
    2*sumOver (wedgePairs xs) (fun ij => (mu ij.1*mu ij.2)^4) =
      (sumOver xs (fun i => (mu i)^4))^2 - sumOver xs (fun i => (mu i)^8) := by
  have productIdentity (ij : α × α) : (mu ij.1*mu ij.2)^4=(mu ij.1)^4*(mu ij.2)^4 := by grind
  have squareIdentity (i : α) : ((mu i)^4)^2 = (mu i)^8 := by grind
  rw [sumOverCongr _ productIdentity,wedgePairTrace xs (fun i => (mu i)^4),sumOverCongr _ squareIdentity]

/-- The mixed entry is the squared HS norm of *one* copy of [2,2]. -/
structure SectorTerms (R : Type) where
  symmetric : R
  mixed : R
  alternating : R
  overlap : R
  pauliFourth : R
  wedgeFourth : R

def sectorTotal (d : R) (s : SectorTerms R) : R :=
  d^2*(s.symmetric + 2*s.mixed + s.alternating)

def symmetricDefect (di : R) (s : SectorTerms R) : R :=
  di^3*s.pauliFourth - s.symmetric + s.alternating

def mixedDefect (di : R) (s : SectorTerms R) : R :=
  8*di^2*s.wedgeFourth + 12*di*s.overlap + 4*s.alternating - 2*s.mixed

def anticommutingDefect (d traceFourSq traceEight : R) (s : SectorTerms R) : R :=
  3*d*traceFourSq - 2*d*traceEight + 6*d^2*s.overlap - s.pauliFourth

def totalDefect (d di traceFourSq traceEight : R) (s : SectorTerms R) : R :=
  d^2*symmetricDefect di s + d^2*mixedDefect di s + di*anticommutingDefect d traceFourSq traceEight s

def spectralInvariant (traceFourSq traceEight : R) : R := 7*traceFourSq - 6*traceEight

/-- Algebraic elimination from the individual symmetric, mixed, and
anticommuting defect definitions, including the mixed multiplicity. -/
theorem sectorElimination (d di traceFourSq traceEight : R) (s : SectorTerms R)
    (inverse : d*di=1) (wedge : 2*s.wedgeFourth=traceFourSq-traceEight) :
    sectorTotal d s = spectralInvariant traceFourSq traceEight + 6*d^2*s.alternating +
      18*d*s.overlap - totalDefect d di traceFourSq traceEight s := by
  unfold sectorTotal spectralInvariant totalDefect symmetricDefect mixedDefect anticommutingDefect
  grind

def normOverlap (a : Wedge7 → R) (t : HermitianEntries Wedge7 R) : R :=
  diagonalLoss wedges a (fun i => t.realPart i i)

def normAlt (a : Wedge7 → R) (t : HermitianEntries Wedge7 R) : R :=
  t.realQuadraticTrace wedges a

def compressionLoss (a : Wedge7 → R) (t : HermitianEntries Wedge7 R) : R :=
  normOverlap a t - normAlt a t

theorem dimensionInverse (half : R) (unit : 2*half=1) (n : Nat) :
    (2:R)^n*half^n=1 := by
  induction n with
  | zero => grind
  | succ n ih =>
    simp only [Semiring.pow_succ]
    calc
      _ = ((2:R)^n*half^n)*(2*half) := by grind
      _ = 1 := by rw [ih,unit]; grind

theorem normalization (half : R) (unit : 2*half=1) (n : Nat) :
    (2:R)^n*PhysicalChartRestriction.weight half n=4 := by
  unfold PhysicalChartRestriction.weight
  have := dimensionInverse half unit n
  grind

/-- Both constants are independent of the qubit count. -/
theorem gainLossFactors (d eta : R) (scale : d*eta=4) :
    (6*d^2*eta+18*d)*eta=168 ∧ 6*d^2*eta^2=96 := by grind

/-- The difference formula before using equality at the computational reference.
The physical trace-scale identifications are explicit inputs. -/
theorem twoFrameDifference (d di eta traceFourSq traceEight : R) (s r : SectorTerms R)
    (inverse : d*di=1) (scale : d*eta=4)
    (ws : 2*s.wedgeFourth=traceFourSq-traceEight) (wr : 2*r.wedgeFourth=traceFourSq-traceEight)
    (a : Wedge7 → R) (t ref : HermitianEntries Wedge7 R)
    (cs : s.overlap=eta*normOverlap a t) (cr : r.overlap=eta*normOverlap a ref)
    (qs : s.alternating=eta^2*normAlt a t) (qr : r.alternating=eta^2*normAlt a ref) :
    sectorTotal d s - sectorTotal d r =
      168*(normOverlap a t - normOverlap a ref) -
      (totalDefect d di traceFourSq traceEight s - totalDefect d di traceFourSq traceEight r) -
      96*(compressionLoss a t - compressionLoss a ref) := by
  rw [sectorElimination d di traceFourSq traceEight s inverse ws,
    sectorElimination d di traceFourSq traceEight r inverse wr,cs,cr,qs,qr]
  unfold compressionLoss
  grind

/-- The normalized exterior loss of the actual Pauli matrix is nonnegative. -/
theorem physicalLossNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (a : Wedge7 → R) :
    0 ≤ compressionLoss a (physicalEntries half unit k A) := by
  let t := physicalEntries half unit k A
  have he := PhysicalCompressionEffect.rankSevenPhysicalEffect half unit k A orth
  apply t.realLossNonnegative
  intro i _
  exact t.effectRowSlack wedges ExteriorCuts.wedgesNodup ExteriorCuts.memWedges he i

/-- Sorted computational sites in the first seven binary labels; larger
dimensions add leading zero bits. -/
def cbSite : (k : Nat) → Fin 7 → Basis (k+3)
  | 0, i => ExteriorPauliBase.qubitBits ⟨i.val,by omega⟩
  | k+1, i => (false, cbSite k i)

private theorem cbLabel (k : Nat) (i : Fin 7) : PlaneOrientation.label (k+3) (cbSite k i)=i.val := by
  induction k with
  | zero => revert i; decide
  | succ k ih => simpa [cbSite,PlaneOrientation.label] using ih

def cbTuple (k : Nat) (w : Wedge7) : Four (Basis (k+3)) :=
  ((cbSite k w.i,cbSite k w.j),(cbSite k w.k,cbSite k w.m))

def cbCoordinate (k : Nat) (w : Wedge7) : Coordinate (k+3) :=
  ⟨cbTuple k w,by
    simp only [PlaneOrientation.Increasing,cbTuple,cbLabel]
    exact ⟨w.ij,w.jk,w.km⟩⟩

/-- A sorted four-subset is an affine plane exactly when its four labels XOR to zero. -/
def planeFlag (w : Wedge7) : Bool := (w.i.val ^^^ w.j.val ^^^ w.k.val ^^^ w.m.val) == 0

private theorem cbDiagonal (w : Wedge7) : supportedPair (cbTuple 0 w) (cbTuple 0 w)=planeFlag w := by
  letI : DecidableEq (Basis 3) := HyperplaneInduction.cubeDecEq 3
  have tab : wedges.all (fun w => decide (GenericExteriorKernel.parity (cbTuple 0 w) =
    HyperplaneIncidence.zero 3 ↔ planeFlag w=true))=true := by decide
  apply Bool.eq_iff_iff.mpr
  rw [PhysicalExteriorSupport.supported_diagonal]
  exact of_decide_eq_true (List.all_eq_true.mp tab w (ExteriorCuts.memWedges w))

private theorem cbActivePair (u v : Wedge7) (hu : planeFlag u=true) (hv : planeFlag v=true) :
    supportedPair (cbTuple 0 u) (cbTuple 0 v)=decide (u=v) := by
  let planes := wedges.filter planeFlag
  have tab : planes.all (fun x => planes.all (fun y =>
    supportedPair (cbTuple 0 x) (cbTuple 0 y) == decide (x=y)))=true := by decide
  have um : u∈planes := List.mem_filter.mpr ⟨ExteriorCuts.memWedges _,hu⟩
  have vm : v∈planes := List.mem_filter.mpr ⟨ExteriorCuts.memWedges _,hv⟩
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp tab u um) v vm)

theorem cbSupport (k : Nat) (u v : Wedge7) :
    supportedPair (cbTuple k u) (cbTuple k v) = decide (u=v ∧ planeFlag u=true) := by
  induction k with
  | zero =>
    by_cases hu : planeFlag u=true
    · by_cases hv : planeFlag v=true
      · simp [cbActivePair u v hu hv,hu]
      · have no : supportedPair (cbTuple 0 u) (cbTuple 0 v) ≠ true := by
          intro yes
          exact hv ((cbDiagonal v).symm.trans
            (PhysicalExteriorPositivity.supportedTrans (PhysicalExteriorPositivity.supportedSymm yes) yes))
        have ne : u≠v := fun e => hv (e ▸ hu)
        simp [Bool.eq_false_iff.mpr no,ne]
    · have no : supportedPair (cbTuple 0 u) (cbTuple 0 v) ≠ true := by
        intro yes
        exact hu ((cbDiagonal u).symm.trans
          (PhysicalExteriorPositivity.supportedTrans yes (PhysicalExteriorPositivity.supportedSymm yes)))
      simp [Bool.eq_false_iff.mpr no,hu]
  | succ k ih =>
    let addZero (x : Basis (k+3)) : Basis ((k+3)+1) := (false,x)
    have lift := PhysicalExteriorSupport.supportedPair_map_affine addZero
      (fun _ _ e => congrArg Prod.snd e) (by intro x y z; rfl) (cbTuple k u) (cbTuple k v)
    exact lift.trans ih

def referenceEntries (R : Type) [CommRing R] : HermitianEntries Wedge7 R where
  realPart u v := if u=v ∧ planeFlag u=true then 1 else 0
  imagPart _ _ := 0
  realSymmetric u v := by by_cases e : u=v <;> simp_all [Ne.symm]
  imagSkew _ _ := by grind

/-- The computational 35 by 35 matrix is the literal restriction of the
normalized Pauli projector to the first seven coordinate columns. -/
theorem cbKernel (half : R) (unit : 2*half=1) (k : Nat) (u v : Wedge7) :
    PhysicalExteriorCompression.physicalKernel half (cbCoordinate k u,cbCoordinate k v) =
      PhysicalChartRestriction.weight half (k+3)*(referenceEntries R).realPart u v := by
  rw [PhysicalExteriorCompression.physicalKernel_eq half unit]
  change (if supportedPair (cbTuple k u) (cbTuple k v) then _ else _) = _
  rw [cbSupport]
  by_cases e : u=v ∧ planeFlag u=true <;> simp [e,referenceEntries] <;> grind

theorem cbOverlap (a : Wedge7 → R) : normOverlap a (referenceEntries R)=
    sumOver wedges (fun u => if planeFlag u then (a u)^2 else 0) := by
  apply sumOverCongr; intro u
  change a u^2*(if u=u ∧ planeFlag u=true then 1 else 0) = _
  cases planeFlag u <;> simp <;> grind

theorem referenceLossZero (a : Wedge7 → R) : compressionLoss a (referenceEntries R)=0 := by
  have row (i : Wedge7) : sumOver wedges (fun j => a i*a j*(referenceEntries R).mass i j)=
      a i^2*(referenceEntries R).realPart i i := by
    calc
      _ = sumOver wedges (fun j => if i=j then a j^2*(referenceEntries R).realPart j j else 0) := by
        apply sumOverCongr; intro j
        by_cases e : i=j
        · subst j; cases h : planeFlag i <;> simp [referenceEntries,HermitianEntries.mass,h] <;> grind
        · simp [referenceEntries,HermitianEntries.mass,e] <;> grind
      _ = _ := ExteriorPauliBase.sumOnIndex _ _ _ ExteriorCuts.wedgesNodup (ExteriorCuts.memWedges _)
  unfold compressionLoss normOverlap normAlt
  rw [HermitianEntries.realQuadraticTrace_eq]
  unfold quadraticTrace diagonalLoss
  rw [sumOverCongr wedges row]
  grind

def computationalValue (xs : List α) (mu : α → R) (a : Wedge7 → R) : R :=
  spectralInvariant ((sumOver xs (fun i => (mu i)^4))^2) (sumOver xs (fun i => (mu i)^8)) +
    168*normOverlap a (referenceEntries R)

def exteriorGain (a : Wedge7 → R) (t : HermitianEntries Wedge7 R) : R :=
  sumOver wedges (fun u => (a u)^2*(t.realPart u u-(referenceEntries R).realPart u u))

theorem gainDifference (a : Wedge7 → R) (t : HermitianEntries Wedge7 R) :
    exteriorGain a t=normOverlap a t - normOverlap a (referenceEntries R) := by
  unfold exteriorGain normOverlap diagonalLoss
  rw [← sumOverSub]; apply sumOverCongr; intro i; grind

/-- With the sector traces identified on the physical frame, the comparison
against the closed computational value has its full normalized loss. -/
theorem physicalDefectAccounting (half : R) (unit : 2*half=1)
    (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (s : SectorTerms R)
    (ws : s.wedgeFourth = sumOver (wedgePairs (List.finRange 7)) (fun ij => (mu ij.1*mu ij.2)^4))
    (cs : s.overlap = PhysicalChartRestriction.weight half (k+3) *
      normOverlap (amplitude mu) (physicalEntries half unit k A))
    (qs : s.alternating = (PhysicalChartRestriction.weight half (k+3))^2 *
      normAlt (amplitude mu) (physicalEntries half unit k A)) :
    let d := (2:R)^(k+3)
    let di := half^(k+3)
    let xs := List.finRange 7
    let t := physicalEntries half unit k A
    let a := amplitude mu
    sectorTotal d s - computationalValue xs mu a =
      168*exteriorGain a t - totalDefect d di ((sumOver xs (fun i => (mu i)^4))^2)
        (sumOver xs (fun i => (mu i)^8)) s - 96*compressionLoss a t := by
  dsimp only
  have sp := wedgeFourthSpectrum (List.finRange 7) mu
  rw [← ws] at sp
  rw [sectorElimination _ _ _ _ s (dimensionInverse half unit _) sp,cs,qs,gainDifference]
  unfold compressionLoss computationalValue
  have scale := normalization half unit (k+3)
  grind

/-- Rescaling the mixed and anticommuting sum-of-squares certificates by
their factors in the full sector defect. The pair count is unordered. -/
theorem rescaledCertificates (d di traceFourSq traceEight : R) (s : SectorTerms R)
    (inverse : d*di=1) (edgeTriangle linearResidual antiPairs projectedEdges : R)
    (mixed : mixedDefect di s=4*di*edgeTriangle+32*di^2*linearResidual)
    (anti : anticommutingDefect d traceFourSq traceEight s=4*di*antiPairs+16*di*projectedEdges) :
    totalDefect d di traceFourSq traceEight s = d^2*symmetricDefect di s +
      4*d*edgeTriangle+32*linearResidual+4*di^2*antiPairs+16*di^2*projectedEdges := by
  unfold totalDefect
  rw [mixed,anti]
  grind

/-- The spectral expression in probability coordinates tᵢ=μᵢ². -/
theorem computationalSpectrumValue (mu : Fin 7 → R) :
    let t (i : Fin 7) := (mu i)^2
    computationalValue (List.finRange 7) mu (amplitude mu) =
      7*(sumOver (List.finRange 7) (fun i => t i^2))^2 -
      6*sumOver (List.finRange 7) (fun i => t i^4) +
      168*sumOver wedges (fun w => if planeFlag w then amplitude t w else 0) := by
  dsimp only
  unfold computationalValue spectralInvariant
  rw [cbOverlap]
  have sq (i : Fin 7) : ((mu i)^2)^2=(mu i)^4 := by grind
  have fourth (i : Fin 7) : ((mu i)^2)^4=(mu i)^8 := by grind
  simp only [sq,fourth]
  congr 1
  congr 1
  apply sumOverCongr; intro i
  split
  · unfold amplitude ExteriorCuts.product4; grind
  · rfl

/-- If each computational sector defect vanishes, the literal three-sector
total equals the explicit computational value. -/
theorem referenceEvaluation (d di eta : R) (inverse : d*di=1) (scale : d*eta=4)
    (mu : Fin 7 → R) (r : SectorTerms R)
    (wr : r.wedgeFourth=sumOver (wedgePairs (List.finRange 7)) (fun ij => (mu ij.1*mu ij.2)^4))
    (cr : r.overlap=eta*normOverlap (amplitude mu) (referenceEntries R))
    (qr : r.alternating=eta^2*normAlt (amplitude mu) (referenceEntries R))
    (sr : symmetricDefect di r=0) (mr : mixedDefect di r=0)
    (ar : anticommutingDefect d ((sumOver (List.finRange 7) (fun i => (mu i)^4))^2)
      (sumOver (List.finRange 7) (fun i => (mu i)^8)) r=0) :
    sectorTotal d r = computationalValue (List.finRange 7) mu (amplitude mu) := by
  have sp := wedgeFourthSpectrum (List.finRange 7) mu
  rw [← wr] at sp
  have loss := referenceLossZero (amplitude mu)
  unfold compressionLoss at loss
  rw [sectorElimination _ _ _ _ r inverse sp,qr,cr]
  unfold computationalValue totalDefect
  rw [sr,mr,ar]
  grind

end RankSeven.SectorDefectAccounting

#print axioms RankSeven.SectorDefectAccounting.sectorElimination
#print axioms RankSeven.SectorDefectAccounting.cbKernel
#print axioms RankSeven.SectorDefectAccounting.physicalDefectAccounting
#print axioms RankSeven.SectorDefectAccounting.physicalLossNonnegative
#print axioms RankSeven.SectorDefectAccounting.referenceEvaluation
