import Rank7CompressionCuts
import Rank7ProjectionBound

namespace RankSeven.Compression

open Lean.Grind

section Operator

variable {R V : Type} [CommRing R] [LE R] [LT R]
  [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
  [Zero V] [Sub V] [SMul R V]

/-- A self-adjoint effect has nonnegative quadratic form for (T-T^2).
    Splitting the defect into two nonnegative forms avoids diagonalization. -/
theorem effectNormLeQuadratic (inner : RealInnerForm R V) (T : V → V)
    (selfAdjoint : ∀ v w, inner.inner (T v) w = inner.inner v (T w))
    (nonnegative : ∀ v, 0 ≤ inner.inner v (T v))
    (bounded : ∀ v, inner.inner v (T v) ≤ inner.squaredNorm v)
    (v : V) :
    inner.squaredNorm (T v) ≤ inner.inner v (T v) := by
  have atDifference := nonnegative (v - T v)
  have atImage := bounded (T v)
  have expansion :
      inner.inner (v-T v) (T (v-T v)) =
        inner.inner v (T v) - 2 * inner.squaredNorm (T v) + inner.inner (T v) (T (T v)) := by
    rw [inner.subLeft, ← selfAdjoint v (v - T v), ← selfAdjoint (T v) (v - T v)]
    rw [inner.subRight, inner.subRight, selfAdjoint (T v) (T v)]
    have sym := inner.symmetric (T (T v)) v
    have norm := selfAdjoint (T v) v
    unfold RealInnerForm.squaredNorm
    grind
  rw [expansion] at atDifference
  grind

end Operator

end RankSeven.Compression

#print axioms RankSeven.Compression.effectNormLeQuadratic
