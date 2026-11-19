import Rank7UpperRayCones

/-! Integer certificates for the eleven facets defining the five geometric
ray statistics and their common active facets on each closed ratio cone. -/
namespace RankSeven.UpperRayGeometry
open Lean.Grind Interval UpperEndpoint UpperInterior
attribute [local instance] Ring.intCast
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

structure Form where
  n : Int
  v : Int
  m : Int
  peak : Int
  constant : Int
  improvement : Int
  tail : Int
  deriving DecidableEq

def forms : List Form :=
  [⟨-2,0,2,0,0,0,0⟩,
   ⟨0,-1,2,0,0,0,0⟩,
   ⟨-1,0,0,1,0,0,0⟩,
   ⟨0,-1,0,1,0,0,0⟩,
   ⟨-5,0,0,0,2,0,0⟩,
   ⟨0,-4,0,0,2,0,0⟩,
   ⟨-4,-2,0,0,2,0,0⟩,
   ⟨0,0,0,0,0,1,0⟩,
   ⟨-2,-1,3,0,0,1,0⟩,
   ⟨0,-2,0,0,0,0,2⟩,
   ⟨-1,0,0,0,0,0,2⟩]

def atForm (j : Fin 11) := forms[j.val]'j.isLt

def selected (j : Fin 6) : List (Fin 11) :=
  [if j.val<4 then 0 else 1,if j.val<3 then 2 else 3,if j.val=0 then 4 else if j.val<4 then 6 else 5,
   if j.val<3∨j.val=5 then 7 else 8,if j.val=0 then 10 else 9]

def vertex (j : Fin 7) : RayData Int :=
  ([⟨72,0,72,72,180,0,36,0,36⟩,
    ⟨72,36,72,72,180,0,36,27,36⟩,
    ⟨72,48,72,72,192,0,48,32,36⟩,
    ⟨72,72,72,72,216,0,72,48,48⟩,
    ⟨72,144,72,144,288,72,144,96,60⟩,
    ⟨72,288,144,288,576,0,288,192,66⟩,
    ⟨0,72,36,72,144,0,72,48,0⟩] : List (RayData Int))[j.val]'j.isLt

def Form.eval {S : Type} [CommRing S] (f : Form) (r : RayData S) : S :=
  Int.cast f.n*r.n+Int.cast f.v*r.v+Int.cast f.m*r.m+Int.cast f.peak*r.peak+Int.cast f.constant*r.constant+Int.cast f.improvement*r.improvement+Int.cast f.tail*r.tail

def certified (j : Fin 6) (z : RayData Int) : Bool :=
  (List.finRange 11).all (fun i => decide (0≤(atForm i).eval z)) &&
    (selected j).all (fun i => decide ((atForm i).eval z=0))

private theorem certificate : ∀ j : Fin 6,certified j (vertex (left j))=true ∧ certified j (vertex (right j))=true := by decide

def Face (j : Fin 6) (r : RayData R) : Prop :=
  (∀ i : Fin 11,0≤(atForm i).eval r) ∧ ∀ i∈selected j,(atForm i).eval r=0

def scale : Grid := ⟨72,by decide⟩
def decode (r : RayData Int) : RayData R := r.map (UpperContractor.value scale)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem decodeForm (f : Form) (r : RayData Int) :
    f.eval (decode (R:=R) r)=UpperContractor.value scale (f.eval r) := by
  have id (x : Int) : Int.cast (R:=Int) x=x := by cases x <;> rfl
  unfold Form.eval decode UpperContractor.value RayData.map
  simp only [id]
  simp only [Field.div_eq_mul_inv,Ring.intCast_add,Ring.intCast_mul]
  grind only

private theorem fromCertificate (j : Fin 6) (r : RayData Int) (pass : certified j r=true) :
    Face j (decode (R:=R) r) := by
  obtain ⟨weak,strong⟩ := Bool.and_eq_true_iff.mp pass
  have z : UpperContractor.value (R:=R) scale 0=0 := by unfold UpperContractor.value; simp only [Ring.intCast_zero,Field.div_eq_mul_inv,Semiring.zero_mul]
  refine ⟨?_,?_⟩
  · intro i; rw [decodeForm,←z]; apply UpperContractor.valueLe
    exact of_decide_eq_true (List.all_eq_true.mp weak i (List.mem_finRange i))
  · intro i mem; rw [decodeForm,←z]; apply congrArg
    exact of_decide_eq_true (List.all_eq_true.mp strong i mem)

private theorem coneFace (j : Fin 6) (r s : RayData R) (x y : R) (hx : 0≤x) (hy : 0≤y)
    (fr : Face j r) (fs : Face j s) : Face j (combineRay x y r s) := by
  have linear (f : Form) : f.eval (combineRay x y r s)=x*f.eval r+y*f.eval s := by unfold Form.eval combineRay; grind only
  refine ⟨?_,?_⟩
  · intro i; rw [linear]; have q := OrderedRing.mul_nonneg hx (fr.1 i); have t := OrderedRing.mul_nonneg hy (fs.1 i); grind only
  · intro i hi; rw [linear,fr.2 i hi,fs.2 i hi]; grind only

def Geometry (r : RayData R) : Prop :=
  r.m=UpperWeighted.larger r.n (r.v/2) ∧ r.peak=UpperWeighted.larger r.n r.v ∧
  r.constant=UpperWeighted.larger (UpperWeighted.larger ((5/2:R)*r.n) (2*r.v)) (2*r.n+r.v) ∧
  r.improvement=UpperPrices.positivePart (2*r.n+r.v-3*r.m) ∧ r.tail=UpperWeighted.larger r.v (r.n/2)

private theorem max₂ (x y z : R) (hx : x≤z) (hy : y≤z) (pick : z=x ∨ z=y) :
    z=UpperWeighted.larger x y := by unfold UpperWeighted.larger; split <;> rcases pick with e|e <;> grind only
private theorem max₃ (x y z v : R) (hx : x≤v) (hy : y≤v) (hz : z≤v) (pick : v=x ∨ v=y ∨ v=z) :
    v=UpperWeighted.larger (UpperWeighted.larger x y) z := by
  by_cases h : y≤x
  · by_cases k : z≤x <;> simp [UpperWeighted.larger,h,k] <;> rcases pick with e|e|e <;> grind only
  · by_cases k : z≤y <;> simp [UpperWeighted.larger,h,k] <;> rcases pick with e|e|e <;> grind only

theorem geometryOfFace (j : Fin 6) (r : RayData R) (h : Face j r) : Geometry r := by
  have two : (0:R)<2 := by have := OrderedRing.zero_lt_one (R:=R); grind only
  have vn := UpperContractor.quotientEq r.v two; have nn := UpperContractor.quotientEq r.n two
  have fn := UpperContractor.quotientEq (5:R) two
  have fmul := congrArg (fun z : R => z*r.n) fn
  have h0 := h.1 (0 : Fin 11)
  have h1 := h.1 (1 : Fin 11)
  have h2 := h.1 (2 : Fin 11)
  have h3 := h.1 (3 : Fin 11)
  have h4 := h.1 (4 : Fin 11)
  have h5 := h.1 (5 : Fin 11)
  have h6 := h.1 (6 : Fin 11)
  have h7 := h.1 (7 : Fin 11)
  have h8 := h.1 (8 : Fin 11)
  have h9 := h.1 (9 : Fin 11)
  have h10 := h.1 (10 : Fin 11)
  have pick (i : Fin 11) (m : i∈selected j) := h.2 i m
  have mM : (atForm (if j.val<4 then 0 else 1)).eval r=0 := pick _ (by simp [selected])
  have mP : (atForm (if j.val<3 then 2 else 3)).eval r=0 := pick _ (by simp [selected])
  have mZ : (atForm (if j.val=0 then 4 else if j.val<4 then 6 else 5)).eval r=0 := pick _ (by simp [selected])
  have mJ : (atForm (if j.val<3∨j.val=5 then 7 else 8)).eval r=0 := pick _ (by simp [selected])
  have mB : (atForm (if j.val=0 then 10 else 9)).eval r=0 := pick _ (by simp [selected])
  have e0 : (atForm 0).eval r=2*r.m-2*r.n := by
    change Int.cast (R:=R) (-2:Int)*r.n+Int.cast (R:=R) (0:Int)*r.v+Int.cast (R:=R) (2:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e1 : (atForm 1).eval r=2*r.m-r.v := by
    change Int.cast (R:=R) (0:Int)*r.n+Int.cast (R:=R) (-1:Int)*r.v+Int.cast (R:=R) (2:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e2 : (atForm 2).eval r=r.peak-r.n := by
    change Int.cast (R:=R) (-1:Int)*r.n+Int.cast (R:=R) (0:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (1:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e3 : (atForm 3).eval r=r.peak-r.v := by
    change Int.cast (R:=R) (0:Int)*r.n+Int.cast (R:=R) (-1:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (1:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e4 : (atForm 4).eval r=2*r.constant-5*r.n := by
    change Int.cast (R:=R) (-5:Int)*r.n+Int.cast (R:=R) (0:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (2:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e5 : (atForm 5).eval r=2*r.constant-4*r.v := by
    change Int.cast (R:=R) (0:Int)*r.n+Int.cast (R:=R) (-4:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (2:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e6 : (atForm 6).eval r=2*r.constant-(4*r.n+2*r.v) := by
    change Int.cast (R:=R) (-4:Int)*r.n+Int.cast (R:=R) (-2:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (2:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e7 : (atForm 7).eval r=r.improvement := by
    change Int.cast (R:=R) (0:Int)*r.n+Int.cast (R:=R) (0:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (1:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e8 : (atForm 8).eval r=r.improvement-(2*r.n+r.v-3*r.m) := by
    change Int.cast (R:=R) (-2:Int)*r.n+Int.cast (R:=R) (-1:Int)*r.v+Int.cast (R:=R) (3:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (1:Int)*r.improvement+Int.cast (R:=R) (0:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e9 : (atForm 9).eval r=2*r.tail-2*r.v := by
    change Int.cast (R:=R) (0:Int)*r.n+Int.cast (R:=R) (-2:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (2:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  have e10 : (atForm 10).eval r=2*r.tail-r.n := by
    change Int.cast (R:=R) (-1:Int)*r.n+Int.cast (R:=R) (0:Int)*r.v+Int.cast (R:=R) (0:Int)*r.m+Int.cast (R:=R) (0:Int)*r.peak+Int.cast (R:=R) (0:Int)*r.constant+Int.cast (R:=R) (0:Int)*r.improvement+Int.cast (R:=R) (2:Int)*r.tail=_
    try simp only [Ring.intCast_neg]
    grind only
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  rw [e6] at h6
  rw [e7] at h7
  rw [e8] at h8
  rw [e9] at h9
  rw [e10] at h10
  have mPick : r.m=r.n ∨ r.m=r.v/2 := by split at mM <;> first | rw [e0] at mM; grind only | rw [e1] at mM; grind only
  have pPick : r.peak=r.n ∨ r.peak=r.v := by split at mP <;> first | rw [e2] at mP; grind only | rw [e3] at mP; grind only
  have zPick : r.constant=(5/2:R)*r.n ∨ r.constant=2*r.v ∨ r.constant=2*r.n+r.v := by
    split at mZ
    · rw [e4] at mZ; grind only
    · split at mZ
      · rw [e6] at mZ; grind only
      · rw [e5] at mZ; grind only
  have jPick : r.improvement=0∨r.improvement=2*r.n+r.v-3*r.m := by
    split at mJ <;> first | rw [e7] at mJ; grind only | rw [e8] at mJ; grind only
  have bPick : r.tail=r.v∨r.tail=r.n/2 := by
    split at mB <;> first | rw [e10] at mB; grind only | rw [e9] at mB; grind only
  refine ⟨max₂ _ _ _ (by grind only) (by grind only) mPick,max₂ _ _ _ (by grind only) (by grind only) pPick,
    max₃ _ _ _ _ (by grind only) (by grind only) (by grind only) zPick,?_,max₂ _ _ _ (by grind only) (by grind only) bPick⟩
  unfold UpperPrices.positivePart; split <;> rcases jPick with z|z <;> grind only


omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem rebuild (r : RayData R) (g : Geometry r) :
    rayFrom realArithmetic r.n r.v r.traceOne r.traceShared=r := by
  obtain ⟨hm,hp,hz,hj,ht⟩ := g
  cases r with
  | mk n v m peak constant improvement tail t₁ ts =>
    change m=UpperWeighted.larger n (v/2) at hm
    change peak=UpperWeighted.larger n v at hp
    change constant=UpperWeighted.larger (UpperWeighted.larger ((5/2:R)*n) (2*v)) (2*n+v) at hz
    change improvement=UpperPrices.positivePart (2*n+v-3*m) at hj
    change tail=UpperWeighted.larger v (n/2) at ht
    change (⟨n,v,UpperWeighted.larger n (v/2),UpperWeighted.larger n v,
      UpperWeighted.larger (UpperWeighted.larger ((5/2:R)*n) (2*v)) (2*n+v),
      UpperPrices.positivePart (2*n+v-3*UpperWeighted.larger n (v/2)),UpperWeighted.larger v (n/2),t₁,ts⟩ : RayData R)=_
    rw [←hm,←hp,←hz,←hj,←ht]

private theorem vertexGeometry (j : Fin 7) : Geometry (decode (R:=R) (vertex j)) := by
  by_cases a : j.val<6
  · let k : Fin 6 := ⟨j.val,a⟩
    have h := (certificate k).1
    exact geometryOfFace k _ (fromCertificate k _ h)
  · have e : j=6 := by apply Fin.ext; change j.val=6; omega
    subst j; exact geometryOfFace 5 _ (fromCertificate 5 _ (certificate 5).2)

private theorem denValue (x : R) (i : Int) (scaled : 72*x=Int.cast i) : x=UpperContractor.value scale i := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have pos : (0:R)<72 := by grind only
  have eq := UpperContractor.quotientEq (Int.cast (R:=R) i) pos
  unfold UpperContractor.value
  change x=Int.cast i/Int.cast (R:=R) (72:Int)
  rw [show Int.cast (R:=R) (72:Int)=72 from Ring.intCast_ofNat 72]
  apply Std.le_antisymm <;> apply UpperContractor.cancelLe pos <;> grind only

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem congrRay (n v o s n' v' o' s' : R) (hn : n=n') (hv : v=v') (ho : o=o') (hs : s=s') :
    rayFrom realArithmetic n v o s=rayFrom realArithmetic n' v' o' s' := by rw [hn,hv,ho,hs]

theorem actualVertex (j : Fin 7) : rayAt (realArithmetic (R:=R)) j=decode (vertex j) := by
  rw [←rebuild _ (vertexGeometry j)]
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have h1_2 := UpperContractor.quotientEq (1:R) (by grind only : (0:R)<2)
  have h3_8 := UpperContractor.quotientEq (3:R) (by grind only : (0:R)<8)
  have h2_3 := UpperContractor.quotientEq (2:R) (by grind only : (0:R)<3)
  have h4_9 := UpperContractor.quotientEq (4:R) (by grind only : (0:R)<9)
  have h4_3 := UpperContractor.quotientEq (4:R) (by grind only : (0:R)<3)
  have h5_6 := UpperContractor.quotientEq (5:R) (by grind only : (0:R)<6)
  have h8_3 := UpperContractor.quotientEq (8:R) (by grind only : (0:R)<3)
  have h11_12 := UpperContractor.quotientEq (11:R) (by grind only : (0:R)<12)
  have cs : ∀ i : Fin 7,i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6 := by decide
  rcases cs j with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply congrRay 1 0 0 (1/2) (UpperContractor.value scale 72) (UpperContractor.value scale 0) (UpperContractor.value scale 0) (UpperContractor.value scale 36) <;> apply denValue <;> grind only
  · apply congrRay 1 (1/2) (3/8) (1/2) (UpperContractor.value scale 72) (UpperContractor.value scale 36) (UpperContractor.value scale 27) (UpperContractor.value scale 36) <;> apply denValue <;> grind only
  · apply congrRay 1 (2/3) (4/9) (1/2) (UpperContractor.value scale 72) (UpperContractor.value scale 48) (UpperContractor.value scale 32) (UpperContractor.value scale 36) <;> apply denValue <;> grind only
  · apply congrRay 1 1 (2/3) (2/3) (UpperContractor.value scale 72) (UpperContractor.value scale 72) (UpperContractor.value scale 48) (UpperContractor.value scale 48) <;> apply denValue <;> grind only
  · apply congrRay 1 2 (4/3) (5/6) (UpperContractor.value scale 72) (UpperContractor.value scale 144) (UpperContractor.value scale 96) (UpperContractor.value scale 60) <;> apply denValue <;> grind only
  · apply congrRay 1 4 (8/3) (11/12) (UpperContractor.value scale 72) (UpperContractor.value scale 288) (UpperContractor.value scale 192) (UpperContractor.value scale 66) <;> apply denValue <;> grind only
  · apply congrRay 0 1 (2/3) 0 (UpperContractor.value scale 0) (UpperContractor.value scale 72) (UpperContractor.value scale 48) (UpperContractor.value scale 0) <;> apply denValue <;> grind only

/-- All five max and positive-part terms in the two geometric estimates are
exactly their homogeneous values at the actual interior (n,v). -/
theorem actualGeometry (j : Fin 6) (a b : R) (ha : 0≤a) (hb : 0≤b) : Geometry (sectorRay j a b) := by
  unfold sectorRay; rw [actualVertex,actualVertex]
  apply geometryOfFace j
  exact coneFace j _ _ a b ha hb (fromCertificate _ _ (certificate j).1) (fromCertificate _ _ (certificate j).2)

end RankSeven.UpperRayGeometry
#print axioms RankSeven.UpperRayGeometry.actualVertex
#print axioms RankSeven.UpperRayGeometry.actualGeometry

