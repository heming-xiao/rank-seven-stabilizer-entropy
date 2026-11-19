import Init.Grind

namespace RankSeven

open Lean.Grind

variable {R V : Type} [CommRing R] [LE R] [Zero V] [Sub V] [SMul R V]

/-- The real inner-product laws used by the projection comparison. Real parts of
complex inner products satisfy the same laws with real scalar multiplication. -/
structure RealInnerForm (R V : Type) [Zero R] [Sub R] [Mul R] [LE R]
    [Zero V] [Sub V] [SMul R V] where
  inner : V → V → R
  symmetric : ∀ x y, inner x y = inner y x
  zeroLeft : ∀ y, inner 0 y = 0
  subLeft : ∀ x y z, inner (x - y) z = inner x z - inner y z
  smulLeft : ∀ (c : R) x y, inner (c • x) y = c * inner x y
  nonnegative : ∀ x, 0 ≤ inner x x
  eqZeroOfInnerSelfEqZero : ∀ x, inner x x = 0 → x = 0

namespace RealInnerForm

def squaredNorm (B : RealInnerForm R V) (v : V) : R := B.inner v v

theorem zeroRight (B : RealInnerForm R V) (v : V) : B.inner v 0 = 0 := by
  rw [B.symmetric v 0, B.zeroLeft]

theorem subRight (B : RealInnerForm R V) (v x y : V) :
    B.inner v (x - y) = B.inner v x - B.inner v y := by
  rw [B.symmetric v (x - y), B.subLeft, B.symmetric x v, B.symmetric y v]

theorem smulRight (B : RealInnerForm R V) (c : R) (x y : V) :
    B.inner x (c • y) = c * B.inner x y := by
  rw [B.symmetric x (c • y), B.smulLeft, B.symmetric y x]

theorem squaredNormSmul (B : RealInnerForm R V) (c : R) (x : V) :
    B.squaredNorm (c • x) = c * c * B.squaredNorm x := by
  simp only [squaredNorm, B.smulLeft, B.smulRight]
  grind

theorem squaredNormSub (B : RealInnerForm R V) (x y : V) :
    B.squaredNorm (x - y) = B.squaredNorm x - 2 * B.inner x y + B.squaredNorm y := by
  simp only [squaredNorm, B.subLeft, B.subRight, B.symmetric y x]
  grind

end RealInnerForm

/-- An orthogonal projection satisfies idempotence and self-adjointness. -/
structure IsOrthogonalProjection (B : RealInnerForm R V) (P : V → V) : Prop where
  idempotent : ∀ v, P (P v) = P v
  selfAdjoint : ∀ v w, B.inner (P v) w = B.inner v (P w)

theorem projectionSquaredNormEq (B : RealInnerForm R V) (P : V → V)
    (hP : IsOrthogonalProjection B P) (v : V) :
    B.squaredNorm (P v) = B.inner v (P v) := by
  change B.inner (P v) (P v) = B.inner v (P v)
  rw [hP.selfAdjoint, hP.idempotent]

private theorem projectionCross (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (v : V) (fixed : P v = v) :
    B.inner v (P (Pi v)) = B.squaredNorm (Pi v) := by
  calc
    _ = B.inner (P v) (Pi v) := (hP.selfAdjoint v (Pi v)).symm
    _ = _ := by rw [fixed, projectionSquaredNormEq B Pi hPi v]

theorem projectionSandwichSquaredNorm (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (q : R) (sandwich : ∀ w, Pi (P (Pi w)) = q • Pi w) (v : V) :
    B.squaredNorm (P (Pi v)) = q * B.squaredNorm (Pi v) := by
  calc
    _ = B.inner (Pi v) (P (Pi v)) := projectionSquaredNormEq B P hP (Pi v)
    _ = B.inner v (Pi (P (Pi v))) := hPi.selfAdjoint v (P (Pi v))
    _ = B.inner v (q • Pi v) := congrArg (B.inner v) (sandwich v)
    _ = _ := by rw [B.smulRight, projectionSquaredNormEq B Pi hPi v]

/-- The exact sum-of-squares identity for the projection comparison. -/
theorem projectionSandwichSOS (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (q : R) (sandwich : ∀ w, Pi (P (Pi w)) = q • Pi w) (v : V) (fixed : P v = v) :
    q * q * B.squaredNorm v - q * B.squaredNorm (Pi v) =
      B.squaredNorm (q • v - P (Pi v)) := by
  rw [B.squaredNormSub, B.squaredNormSmul, B.smulLeft, projectionCross B P Pi hP hPi v fixed,
    projectionSandwichSquaredNorm B P Pi hP hPi q sandwich v]
  grind

variable [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- On the fixed subspace of P, the occupation projection Pi has squared
norm at most q times the squared norm of the vector if Pi P Pi = q Pi. -/
theorem projectionSandwichBound (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (q : R) (hq : 0 ≤ q) (sandwich : ∀ w, Pi (P (Pi w)) = q • Pi w)
    (v : V) (fixed : P v = v) :
    B.squaredNorm (Pi v) ≤ q * B.squaredNorm v := by
  by_cases positive : 0 < q
  · have sos := projectionSandwichSOS B P Pi hP hPi q sandwich v fixed
    have nonnegative : 0 ≤ B.squaredNorm (q • v - P (Pi v)) :=
      B.nonnegative (q • v - P (Pi v))
    by_cases comparison : B.squaredNorm (Pi v) ≤ q * B.squaredNorm v
    · exact comparison
    · have difference : 0 < B.squaredNorm (Pi v) - q * B.squaredNorm v := by grind
      have contradiction := OrderedRing.mul_pos positive difference
      grind
  · have zero : q = 0 := by grind
    have normZero := projectionSandwichSquaredNorm B P Pi hP hPi q sandwich v
    have innerZero : B.inner (P (Pi v)) (P (Pi v)) = 0 := by
      change B.squaredNorm (P (Pi v)) = 0
      grind
    have projectedZero := B.eqZeroOfInnerSelfEqZero (P (Pi v)) innerZero
    have cross := projectionCross B P Pi hP hPi v fixed
    rw [projectedZero, B.zeroRight] at cross
    grind

/-- The half-occupation case stated without division in the scalar ring. -/
theorem projectionSandwichHalfBound (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (q : R) (half : 2 * q = 1) (sandwich : ∀ w, Pi (P (Pi w)) = q • Pi w)
    (v : V) (fixed : P v = v) :
    2 * B.squaredNorm (Pi v) ≤ B.squaredNorm v := by
  have onePos : (0 : R) < 1 := OrderedRing.zero_lt_one
  have hq : 0 ≤ q := by grind
  have bound := projectionSandwichBound B P Pi hP hPi q hq sandwich v fixed
  have slack : 0 ≤ q * B.squaredNorm v - B.squaredNorm (Pi v) := by grind
  have twiceSlack := OrderedRing.mul_nonneg (show (0 : R) ≤ 2 by grind) slack
  have halfNorm := congrArg (fun a => a * B.squaredNorm v) half
  grind

/-- If the half sandwich is supplied as a doubled operator identity, the
comparison still needs no scalar division. -/
theorem projectionSandwichHalfBoundOfDouble (B : RealInnerForm R V) (P Pi : V → V)
    (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (sandwich : ∀ w, (2 : R) • Pi (P (Pi w)) = Pi w) (v : V) (fixed : P v = v) :
    2 * B.squaredNorm (Pi v) ≤ B.squaredNorm v := by
  have twiceProjected : 2 * B.squaredNorm (P (Pi v)) = B.squaredNorm (Pi v) := by
    calc
      _ = 2 * B.inner (Pi v) (P (Pi v)) := by rw [projectionSquaredNormEq B P hP]
      _ = B.inner v ((2 : R) • Pi (P (Pi v))) := by rw [B.smulRight, hPi.selfAdjoint]
      _ = B.inner v (Pi v) := congrArg (B.inner v) (sandwich v)
      _ = _ := (projectionSquaredNormEq B Pi hPi v).symm
  have residual : 0 ≤ B.squaredNorm (v - (2 : R) • P (Pi v)) :=
    B.nonnegative _
  rw [B.squaredNormSub, B.squaredNormSmul, B.smulRight, projectionCross B P Pi hP hPi v fixed]
    at residual
  grind

/-- A wedge or other map can use the bound pointwise as soon as its image is
known to be fixed by the range projection. -/
theorem projectionSandwichBoundOnRange {W : Type} (B : RealInnerForm R V)
    (P Pi : V → V) (hP : IsOrthogonalProjection B P) (hPi : IsOrthogonalProjection B Pi)
    (q : R) (hq : 0 ≤ q) (sandwich : ∀ w, Pi (P (Pi w)) = q • Pi w)
    (F : W → V) (fixedRange : ∀ w, P (F w) = F w) (w : W) :
    B.squaredNorm (Pi (F w)) ≤ q * B.squaredNorm (F w) :=
  projectionSandwichBound B P Pi hP hPi q hq sandwich (F w) (fixedRange w)

end RankSeven
