import Rank7LowerSignedExterior
import Rank7UpperRayGeometry
import Rank7LowerReplay
import Rank7UpperPairCap

namespace RankSeven.LowerPhysicalRay
open Lean.Grind ExteriorCuts UpperEndpoint UpperInterior UpperPhysicalInterior UpperFrameTrace
open LowerSignedExterior LowerCorner
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def project (r : RayData R) : RealRay R :=
  ⟨r.n,r.v,r.m,r.peak,r.constant,r.improvement,r.tail,r.traceShared⟩

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem agree (j : Fin 7) : project (UpperEndpoint.rayAt realArithmetic j)=LowerCorner.realRayAt (R:=R) j := by
  have finite : ∀ j : Fin 7,j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6 := by decide
  rcases finite j with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem geo {r : RayData R} (g : UpperRayGeometry.Geometry r) :
    project r=realRay r.n r.v r.traceShared := by
  rcases g with ⟨hm,hp,hz,hj,ht⟩
  cases r; dsimp [project,realRay] at *
  subst_vars
  rfl

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem linear (z y x b : R) (p : Prices R) (right : Bool) (a e : R) (s t : RayData R) :
    let L := fun rr => realLeafPair z y x b p right (project rr)
    (L (combineRay a e s t)).1=a*(L s).1+e*(L t).1 ∧
    (L (combineRay a e s t)).2=a*(L s).2+e*(L t).2 := by
  dsimp only [realLeafPair,project,combineRay]
  rw [Field.div_eq_mul_inv,Field.div_eq_mul_inv,Field.div_eq_mul_inv]
  constructor <;> grind only

private theorem convexPositive (a b s t L₁ L₂ H₁ H₂ : R) (a0 : 0≤a) (b0 : 0≤b) (nz : 0<a+b)
    (s0 : 0≤s) (t0 : 0≤t) (low : 0<s*L₁+t*L₂) (high : 0<s*H₁+t*H₂) :
    0<a*L₁+b*H₁ ∨ 0<a*L₂+b*H₂ := by
  by_cases ap : 0<a
  · have pos := OrderedRing.mul_pos ap low
    have nn := OrderedRing.mul_nonneg b0 (Std.le_of_lt high)
    by_cases pos1 : 0<a*L₁+b*H₁
    · exact Or.inl pos1
    · right; by_cases good2 : 0<a*L₂+b*H₂
      · exact good2
      have sN := OrderedRing.mul_le_mul_of_nonneg_left (show a*L₁+b*H₁≤0 by grind only) s0
      have tN := OrderedRing.mul_le_mul_of_nonneg_left (show a*L₂+b*H₂≤0 by grind only) t0
      grind only
  · have bp : 0<b := by grind only
    have good := OrderedRing.mul_pos bp high
    have nn := OrderedRing.mul_nonneg a0 (Std.le_of_lt low)
    by_cases pos1 : 0<a*L₁+b*H₁
    · exact Or.inl pos1
    · right; by_cases good2 : 0<a*L₂+b*H₂
      · exact good2
      have sN := OrderedRing.mul_le_mul_of_nonneg_left (show a*L₁+b*H₁≤0 by grind only) s0
      have tN := OrderedRing.mul_le_mul_of_nonneg_left (show a*L₂+b*H₂≤0 by grind only) t0
      grind only

theorem sectorPositive (z y x b : R) (p : Prices R) (j : Fin 6) (a e : R)
    (ha : 0≤a) (he : 0≤e) (nz : 0<a+e) (right : Bool)
    (pass : let l := realLeafPair z y x b p right (LowerCorner.realRayAt (left j))
            let h := realLeafPair z y x b p right (LowerCorner.realRayAt (UpperInterior.right j))
            ∃ s t : R,0≤s ∧ 0≤t ∧ 0<s*l.1+t*l.2 ∧ 0<s*h.1+t*h.2) :
    let r := sectorRay j a e
    let P := realLeafPair z y x b p right (realRay r.n r.v r.traceShared)
    0<P.1 ∨ 0<P.2 := by
  let r := sectorRay j a e
  have g := geo (UpperRayGeometry.actualGeometry j a e ha he)
  have eq := linear z y x b p right a e (UpperEndpoint.rayAt realArithmetic (left j)) (UpperEndpoint.rayAt realArithmetic (UpperInterior.right j))
  change (realLeafPair z y x b p right (project r)).1=_ ∧ (realLeafPair z y x b p right (project r)).2=_ at eq
  dsimp only at eq
  rw [agree,agree] at eq
  obtain ⟨s,t,s0,t0,h1,h2⟩ := pass
  change 0<(realLeafPair z y x b p right (realRay r.n r.v r.traceShared)).1 ∨ 0<(realLeafPair z y x b p right (realRay r.n r.v r.traceShared)).2
  rw [← g,eq.1,eq.2]
  exact convexPositive a e s t _ _ _ _ ha he nz s0 t0 h1 h2

end RankSeven.LowerPhysicalRay
#print axioms RankSeven.LowerPhysicalRay.sectorPositive