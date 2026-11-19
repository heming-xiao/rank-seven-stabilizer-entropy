import Rank7SectorDefectAccounting
import Rank7RectangularPairedReduction

/-! Exact fourth exterior coordinates for the standard seven computational columns. -/
namespace RankSeven.ComputationalExterior

open Lean.Grind Pauli Compression HyperplaneInduction ExteriorCuts ExteriorPauliBase
open PhysicalWedges SectorDefectAccounting RectangularPairedReduction
open PhysicalExteriorCompression (wedgeRows physicalKernel inverseWeight)
open PhysicalCompressionEffect (physicalEntries OrthonormalFrame)
open ComplexScalar (ofReal star)
open PlaneOrientation (label)

variable {R C α : Type} [CommRing R] [CommRing C]

private theorem siteLabel (k : Nat) (i : Fin 7) : label (k+3) (cbSite k i) = i.val := by
  induction k with
  | zero => revert i; decide
  | succ k ih => simpa [cbSite,label] using ih

private theorem siteIff (k : Nat) (i : Fin 7) (s : Basis (k+3)) :
    label (k+3) s = i.val ↔ cbSite k i = s := by
  rw [←siteLabel k i]
  constructor
  · intro h; exact PlaneOrientation.labelInjective _ _ _ h.symm
  · intro h; rw [h]

theorem computationalFrame_orthonormal (k : Nat) :
    OrthonormalFrame (computationalFrame (R := R) k) := by
  classical
  intro i j
  let xs := qubitIndices (k+3)
  calc
    _ = sumOver xs (fun s => if cbSite k i = s then computationalFrame k s j else 0) := by
      apply sumOverCongr
      intro s
      by_cases h : cbSite k i=s
      · simp [computationalFrame, (siteIff k i s).mpr h, h, Semiring.one_mul,
          show star (1 : ComplexScalar R) = 1 from ComplexScalar.star_ofReal (1 : R)]
      · have no : label (k+3) s ≠ i.val := fun e => h ((siteIff k i s).mp e)
        simp [computationalFrame, no, h, Semiring.zero_mul,
          show star (0 : ComplexScalar R) = 0 from ComplexScalar.star_ofReal (0 : R)]
    _ = computationalFrame k (cbSite k i) j := sumOnIndex _ _ _ (HyperplaneIncidence.normalsNodup _)
      (qubitIndicesComplete _)
    _ = _ := by
      have eqv : i.val = j.val ↔ i = j := ⟨Fin.ext, congrArg Fin.val⟩
      simp [computationalFrame,siteLabel,eqv]

private def identity4 : Permutation := ((0,1),(2,3))

private theorem identityMember : identity4 ∈ permutations := by decide
private theorem identityEven : oddPermutation identity4 = false := by decide

private theorem sourceStrict (w : Wedge7) (a b : Fin 4) :
    (sourceSite w a).val < (sourceSite w b).val ↔ a < b := by
  have cases4 : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  have h₁ := w.ij; have h₂ := w.jk; have h₃ := w.km
  rcases cases4 a with rfl|rfl|rfl|rfl <;> rcases cases4 b with rfl|rfl|rfl|rfl <;>
    simp [sourceSite] <;> omega

private def aligned (k : Nat) (r : Coordinate (k+3)) (w : Wedge7) (p : Permutation) : Prop :=
  label (k+3) r.val.1.1 = (sourceSite w p.1.1).val ∧
  label (k+3) r.val.1.2 = (sourceSite w p.1.2).val ∧
  label (k+3) r.val.2.1 = (sourceSite w p.2.1).val ∧
  label (k+3) r.val.2.2 = (sourceSite w p.2.2).val

private theorem matchingIff (k : Nat) (r : Coordinate (k+3)) (w : Wedge7) (p : Permutation) :
    aligned k r w p ↔ cbCoordinate k w = r ∧ identity4 = p := by
  constructor
  · rintro ⟨h₀,h₁,h₂,h₃⟩
    obtain ⟨a,b,c⟩ := r.property
    have h01 : p.1.1 < p.1.2 := (sourceStrict w _ _).mp (h₀ ▸ h₁ ▸ a)
    have h12 : p.1.2 < p.2.1 := (sourceStrict w _ _).mp (h₁ ▸ h₂ ▸ b)
    have h23 : p.2.1 < p.2.2 := (sourceStrict w _ _).mp (h₂ ▸ h₃ ▸ c)
    have sorted : ∀ a b c d : Fin 4, a < b → b < c → c < d → identity4 = ((a,b),(c,d)) := by decide
    have perm : identity4=p := sorted _ _ _ _ h01 h12 h23
    subst p
    refine ⟨Subtype.ext (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)),rfl⟩
    all_goals apply PlaneOrientation.labelInjective (k+3)
    · exact (siteLabel k w.i).trans h₀.symm
    · exact (siteLabel k w.j).trans h₁.symm
    · exact (siteLabel k w.k).trans h₂.symm
    · exact (siteLabel k w.m).trans h₃.symm
  · rintro ⟨rfl,rfl⟩
    exact ⟨siteLabel k w.i,siteLabel k w.j,siteLabel k w.k,siteLabel k w.m⟩

private theorem deltaProduct (a b c d i j k l : Nat) :
    ((if a=i then 1 else 0) : C) * (if b=j then 1 else 0) *
      (if c=k then 1 else 0) * (if d=l then 1 else 0) =
      (if a=i ∧ b=j ∧ c=k ∧ d=l then 1 else 0) := by
  by_cases e₁ : a=i <;> by_cases e₂ : b=j <;> by_cases e₃ : c=k <;> by_cases e₄ : d=l <;>
    simp [e₁,e₂,e₃,e₄,Semiring.zero_mul,Semiring.mul_zero,Semiring.one_mul]

/-- Every computational exterior column has just one increasing coordinate,
whose orientation agrees with the ordered source wedge. -/
theorem computationalMinor (k : Nat) (r : Coordinate (k+3)) (w : Wedge7) :
    minor4 (computationalFrame (R := R) k) (wedgeRows r) w = if cbCoordinate k w = r then 1 else 0 := by
  letI (p : Permutation) : Decidable (aligned k r w p) := by unfold aligned; infer_instance
  unfold minor4
  let delta : ComplexScalar R := if cbCoordinate k w = r then 1 else 0
  calc
    _ = sumOver permutations (fun p => if identity4=p then delta else 0) := by
      apply sumOverCongr
      intro p
      unfold computationalFrame
      rw [deltaProduct]
      change (if oddPermutation p then -(if aligned k r w p then 1 else 0) else
          (if aligned k r w p then 1 else 0)) = _
      simp only [matchingIff]
      by_cases idp : identity4 = p
      · subst p; simp [identityEven,delta]
      · simp [idp]
        grind
    _ = _ := sumOnIndex permutations identity4 (fun _ => delta) complete_basis_counts.2.2.2 identityMember

private theorem deltaPullback [DecidableEq α] (xs : List α) (nd : xs.Nodup) (i j : α)
    (hi : i∈xs) (hj : j∈xs) (K : α × α → R) :
    sumOver xs (fun a => sumOver xs (fun b =>
      star (if i=a then (1 : ComplexScalar R) else 0) * ofReal (K (a,b)) * (if j=b then 1 else 0))) =
      ofReal (K (i,j)) := by
  have sz : star (0 : ComplexScalar R) = 0 := ComplexScalar.star_ofReal (0 : R)
  have so : star (1 : ComplexScalar R) = 1 := ComplexScalar.star_ofReal (1 : R)
  calc
    _ = sumOver xs (fun a => if i=a then ofReal (K (a,j)) else 0) := by
      apply sumOverCongr
      intro a
      let f b := star (if i=a then (1 : ComplexScalar R) else 0) * ofReal (K (a,b))
      have inner : sumOver xs (fun b => f b * (if j=b then 1 else 0)) = f j := by
        calc
          _ = sumOver xs (fun b => if j=b then f b else 0) := by
            apply sumOverCongr
            intro b
            by_cases h : j=b <;> simp [h,Semiring.mul_one,Semiring.mul_zero]
          _ = _ := sumOnIndex xs j f nd hj
      change sumOver xs (fun b => f b * (if j=b then 1 else 0)) = _
      rw [inner]
      by_cases h : i=a <;> simp [h,f,sz,so,Semiring.zero_mul,Semiring.one_mul]
    _ = _ := sumOnIndex xs i _ nd hi

/-- The unscaled double sum selects the two embedded wedge coordinates;
the reciprocal physical weight cancels their kernel scale. -/
theorem computationalMatrix (half : R) (halfUnit : 2*half=1) (k : Nat) (u v : Wedge7) :
    ExteriorCompressionEffect.normalizedMatrix (coords (k+3)) (physicalKernel half)
      (fun r w => minor4 (computationalFrame k) (wedgeRows r) w) (inverseWeight R k) u v =
      ofReal ((referenceEntries R).realPart u v) := by
  rw [ExteriorCompressionEffect.normalizedMatrix_entry]
  simp only [computationalMinor]
  rw [deltaPullback _ (coordsNodup _) _ _ (memCoords _) (memCoords _),cbKernel half halfUnit]
  have inv := PhysicalExteriorCompression.inverseWeight_mul_weight half halfUnit k
  have cancel := congrArg (fun z => z * (referenceEntries R).realPart u v) inv
  apply ComplexScalar.ext <;> simp <;> grind

private theorem entriesExt {E F : HermitianEntries α R}
    (hre : ∀ i j, E.realPart i j=F.realPart i j)
    (him : ∀ i j, E.imagPart i j=F.imagPart i j) : E=F := by
  cases E; cases F
  congr
  · exact funext (fun i => funext (hre i))
  · exact funext (fun i => funext (him i))

/-- The physical Hermitian matrix of the seven computational columns equals
the diagonal reference matrix on the 35 source coordinates. -/
theorem computationalEntries_eq_reference (half : R) (halfUnit : 2*half=1) (k : Nat) :
    physicalEntries half halfUnit k (computationalFrame k) = referenceEntries R := by
  apply entriesExt
  · intro i j
    exact congrArg ComplexScalar.re (computationalMatrix half halfUnit k i j)
  · intro i j
    exact congrArg ComplexScalar.im (computationalMatrix half halfUnit k i j)

end RankSeven.ComputationalExterior

#print axioms RankSeven.ComputationalExterior.computationalFrame_orthonormal
#print axioms RankSeven.ComputationalExterior.computationalMinor
#print axioms RankSeven.ComputationalExterior.computationalEntries_eq_reference
