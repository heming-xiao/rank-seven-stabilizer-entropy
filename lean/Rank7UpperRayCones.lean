import Rank7UpperInterior

/-! Exact positive cones for the seven trace rays. -/
namespace RankSeven.UpperRayCones
open Lean.Grind UpperEndpoint UpperInterior
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem cover (n v : R) (hn : 0≤n) (hv : 0≤v) (hnv : 0<n+v) :
    ∃ (j : Fin 6) (a b : R),0≤a ∧ 0≤b ∧ 0<a+b ∧ (sectorRay j a b).n=n ∧ (sectorRay j a b).v=v := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have p2 : (2:R)*(1/2)=1 := UpperContractor.quotientEq _ (by grind only)
  have p3 : (3:R)*(2/3)=2 := UpperContractor.quotientEq _ (by grind only)
  have halfv : (2:R)*(v/2)=v := UpperContractor.quotientEq _ (by grind only)
  by_cases c0 : 2*v≤n
  · refine ⟨0,n-2*v,2*v,by grind only,by grind only,by grind only,?_,?_⟩
    · change (n-2*v)*1+2*v*1=n; grind only
    · change (n-2*v)*0+2*v*(1/2)=v; grind only
  by_cases c1 : 3*v≤2*n
  · refine ⟨1,4*n-6*v,6*v-3*n,by grind only,by grind only,by grind only,?_,?_⟩
    · change _*1+_*1=n; grind only
    · change (4*n-6*v)*(1/2)+(6*v-3*n)*(2/3)=v; grind only
  by_cases c2 : v≤n
  · refine ⟨2,3*(n-v),3*v-2*n,by grind only,by grind only,by grind only,?_,?_⟩
    · change _*1+_*1=n; grind only
    · change (3*(n-v))*(2/3)+(3*v-2*n)*1=v; grind only
  by_cases c3 : v≤2*n
  · refine ⟨3,2*n-v,v-n,by grind only,by grind only,by grind only,?_,?_⟩
    · change _*1+_*1=n; grind only
    · change (2*n-v)*1+(v-n)*2=v; grind only
  by_cases c4 : v≤4*n
  · refine ⟨4,2*n-v/2,v/2-n,by grind only,by grind only,by grind only,?_,?_⟩
    · change _*1+_*1=n; grind only
    · change (2*n-v/2)*2+(v/2-n)*4=v; grind only
  · refine ⟨5,n,v-4*n,hn,by grind only,by grind only,?_,?_⟩
    · change n*1+(v-4*n)*0=n; grind only
    · change n*4+(v-4*n)*1=v; grind only


private theorem traceQuadratic (a b K : R) (z₀ z₁ m₀ m₁ t₀ t₁ : R) (ha : 0≤a) (hb : 0≤b)
    (cap : K*(a*m₀+b*m₁)≤1) (l₀ : 0≤z₀-t₀) (l₁ : 0≤z₁-t₁)
    (eq₀ : K*m₀*(z₀-t₀)=z₀*z₀) (eq₁ : K*m₁*(z₁-t₁)=z₁*z₁)
    (cross : 0≤K*m₀*(z₁-t₁)+K*m₁*(z₀-t₀)-2*z₀*z₁) :
    a*t₀+b*t₁≤(a*z₀+b*z₁)*(1-(a*z₀+b*z₁)) := by
  let L := a*(z₀-t₀)+b*(z₁-t₁)
  have l : 0≤L := by have x := OrderedRing.mul_nonneg ha l₀; have y := OrderedRing.mul_nonneg hb l₁; unfold L; grind only
  have bound := OrderedRing.mul_le_mul_of_nonneg_right cap l
  have var := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg ha hb) cross
  have id : K*(a*m₀+b*m₁)*L-(a*z₀+b*z₁)*(a*z₀+b*z₁)=
      a*a*(K*m₀*(z₀-t₀)-z₀*z₀)+b*b*(K*m₁*(z₁-t₁)-z₁*z₁)+
        (a*b)*(K*m₀*(z₁-t₁)+K*m₁*(z₀-t₀)-2*z₀*z₁) := by unfold L; grind only
  rw [eq₀,eq₁] at id
  have v : 0≤K*(a*m₀+b*m₁)*L-(a*z₀+b*z₁)*(a*z₀+b*z₁) := by rw [id]; grind only
  have h : (a*z₀+b*z₁)*(a*z₀+b*z₁)≤L := by grind only
  unfold L at h; grind only

structure TraceCell (K m₀ m₁ z₀ z₁ t₀ t₁ : R) : Prop where
  l₀ : 0≤z₀-t₀
  l₁ : 0≤z₁-t₁
  eq₀ : K*m₀*(z₀-t₀)=z₀*z₀
  eq₁ : K*m₁*(z₁-t₁)=z₁*z₁
  cross : 0≤K*m₀*(z₁-t₁)+K*m₁*(z₀-t₀)-2*z₀*z₁

private theorem traceTable (j : Fin 6) :
    let s := rayAt (realArithmetic (R:=R)) (left j)
    let t := rayAt (realArithmetic (R:=R)) (right j)
    let K : R := if j.val<2 then 2 else 3
    let l := if j.val<2 then s.n else s.v
    let r := if j.val<2 then t.n else t.v
    TraceCell K l r s.v t.v s.traceOne t.traceOne ∧ TraceCell K l r s.n t.n s.traceShared t.traceShared := by
  have cs : ∀ j : Fin 6,j=0∨j=1∨j=2∨j=3∨j=4∨j=5 := by decide
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have h1_2 := UpperContractor.quotientEq (1:R) (by grind only : (0:R)<2)
  have h3_8 := UpperContractor.quotientEq (3:R) (by grind only : (0:R)<8)
  have h2_3 := UpperContractor.quotientEq (2:R) (by grind only : (0:R)<3)
  have h4_9 := UpperContractor.quotientEq (4:R) (by grind only : (0:R)<9)
  have h4_3 := UpperContractor.quotientEq (4:R) (by grind only : (0:R)<3)
  have h5_6 := UpperContractor.quotientEq (5:R) (by grind only : (0:R)<6)
  have h8_3 := UpperContractor.quotientEq (8:R) (by grind only : (0:R)<3)
  have h11_12 := UpperContractor.quotientEq (11:R) (by grind only : (0:R)<12)
  rcases cs j with rfl|rfl|rfl|rfl|rfl|rfl
  · change TraceCell 2 1 1 0 (1/2) 0 (3/8) ∧ TraceCell 2 1 1 1 1 (1/2) (1/2)
    constructor <;> constructor <;> grind only
  · change TraceCell 2 1 1 (1/2) (2/3) (3/8) (4/9) ∧ TraceCell 2 1 1 1 1 (1/2) (1/2)
    constructor <;> constructor <;> grind only
  · change TraceCell 3 (2/3) 1 (2/3) 1 (4/9) (2/3) ∧ TraceCell 3 (2/3) 1 1 1 (1/2) (2/3)
    constructor <;> constructor <;> grind only
  · change TraceCell 3 1 2 1 2 (2/3) (4/3) ∧ TraceCell 3 1 2 1 1 (2/3) (5/6)
    constructor <;> constructor <;> grind only
  · change TraceCell 3 2 4 2 4 (4/3) (8/3) ∧ TraceCell 3 2 4 1 1 (5/6) (11/12)
    constructor <;> constructor <;> grind only
  · change TraceCell 3 4 1 4 1 (8/3) (2/3) ∧ TraceCell 3 4 1 1 0 (11/12) 0
    constructor <;> constructor <;> grind only

/-- The homogeneous chord trace prices sit below the genuine fractional
trace bounds for every sector, including the final axis sector. -/
theorem traceBounds (j : Fin 6) (a b : R) (ha : 0≤a) (hb : 0≤b)
    (nCap : 2*(sectorRay j a b).n≤1) (vCap : 3*(sectorRay j a b).v≤1) :
    let r := sectorRay j a b
    r.traceOne≤r.v*(1-r.v) ∧ r.traceShared≤r.n*(1-r.n) := by
  let s := rayAt (realArithmetic (R:=R)) (left j)
  let t := rayAt (realArithmetic (R:=R)) (right j)
  let K : R := if j.val<2 then 2 else 3
  let l := if j.val<2 then s.n else s.v
  let r := if j.val<2 then t.n else t.v
  have cap : K*(a*l+b*r)≤1 := by
    dsimp only [K,l,r]; split <;> first | exact nCap | exact vCap
  obtain ⟨hi,sh⟩ := traceTable (R:=R) j
  exact ⟨traceQuadratic a b K s.v t.v l r _ _ ha hb cap hi.l₀ hi.l₁ hi.eq₀ hi.eq₁ hi.cross,
    traceQuadratic a b K s.n t.n l r _ _ ha hb cap sh.l₀ sh.l₁ sh.eq₀ sh.eq₁ sh.cross⟩

end RankSeven.UpperRayCones
#print axioms RankSeven.UpperRayCones.cover
#print axioms RankSeven.UpperRayCones.traceBounds
