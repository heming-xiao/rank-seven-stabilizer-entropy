import Rank7HermitianEffect

namespace RankSeven.Compression

open Lean.Grind

variable {R V : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
  [Zero V] [Sub V] [SMul R V]

/-- The one-hole compression estimate from an occupation effect with
    exactly half occupation on the projected vector. The proof works
    on the annihilated subspace and does not require a complementary
    projection to be explicitly constructed. -/
theorem halfOccupationCompression (B : RealInnerForm R V) (Pi T : V → V)
    (projector : IsOrthogonalProjection B Pi)
    (selfAdjoint : ∀ x y, B.inner (T x) y = B.inner x (T y))
    (nonnegative : ∀ x, 0 ≤ B.inner x (T x))
    (bounded : ∀ x, B.inner x (T x) ≤ B.squaredNorm x)
    (v : V) (annihilated : T v = 0)
    (halfOccupation : 2 * B.inner (Pi v) (T (Pi v)) = B.squaredNorm (Pi v)) :
    2 * B.squaredNorm (Pi v) ≤ B.squaredNorm v := by
  let w := Pi v
  have cross : B.inner v (w - T w) = B.squaredNorm w := by
    rw [B.subRight, ← selfAdjoint v w, annihilated, B.zeroLeft]
    have eq := projectionSquaredNormEq B Pi projector v
    change B.squaredNorm w = B.inner v w at eq
    grind
  have effect := effectNormLeQuadratic B T selfAdjoint nonnegative bounded w
  have norm : 2 * B.squaredNorm (w - T w) ≤ B.squaredNorm w := by
    rw [B.squaredNormSub]
    change 2 * B.inner w (T w) = B.squaredNorm w at halfOccupation
    grind
  have residual := B.nonnegative (v - (2 : R) • (w-T w))
  change 0 ≤ B.squaredNorm (v - (2 : R) • (w-T w)) at residual
  rw [B.squaredNormSub, B.squaredNormSmul, B.smulRight, cross] at residual
  change 2 * B.squaredNorm w ≤ B.squaredNorm v
  grind

end RankSeven.Compression

#print axioms RankSeven.Compression.halfOccupationCompression
