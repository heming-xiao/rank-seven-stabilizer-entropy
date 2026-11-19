import Rank7HermitianCoordinates

/-! Finite reducing blocks for the two-hole operator bound. The proof
removes columns by orthogonal projection after multiplication by their
squared norms, so it works over any linearly ordered commutative ring. -/
namespace RankSeven.TwoHoleReducingBlock

open Lean.Grind
variable {R V : Type} [CommRing R] [LE R] [Zero V] [Sub V] [SMul R V]

def perpendicular (B : RealInnerForm R V) (cols : List V) (w : V) : Prop := ∀a∈cols,B.inner a w=0

private def remove (B : RealInnerForm R V) (a w : V) : V := (B.inner a a) • w - (B.inner a w) • a

private theorem removeLeft (B : RealInnerForm R V) (a v w : V) :
    B.inner (remove B a v) w = B.inner a a*B.inner v w - B.inner a v*B.inner a w := by
  rw [remove,B.subLeft,B.smulLeft,B.smulLeft]

private theorem removeRight (B : RealInnerForm R V) (a v w : V) :
    B.inner v (remove B a w) = B.inner a a*B.inner v w - B.inner a w*B.inner v a := by
  rw [remove,B.subRight,B.smulRight,B.smulRight]

private theorem priorRemoved (B : RealInnerForm R V) (prior : List V) (a w : V)
    (ha : perpendicular B prior a) (hw : perpendicular B prior w) :
    perpendicular B (a::prior) (remove B a w) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl|hp
  · rw [removeRight]; grind only
  · rw [removeRight,ha _ hp,hw _ hp]; grind only

variable [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem reduceQuadratic (B : RealInnerForm R V) (D : V → V → R)
    (sym : ∀v w,D v w=D w v)
    (sub : ∀v w z,D (v-w) z=D v z-D w z)
    (scale : ∀(k:R) v w,D (k•v) w=k*D v w)
    (count : Nat) (cols : List V) (length : cols.length=count)
    (prior : List V) (inside : ∀a∈cols,perpendicular B prior a)
    (null : ∀a∈cols,∀w,D a w=0)
    (complement : ∀w,perpendicular B prior w → perpendicular B cols w → 0≤D w w) :
    ∀v,perpendicular B prior v → 0≤D v v := by
  induction count generalizing cols prior with
  | zero =>
    have e : cols=[] := List.length_eq_zero_iff.mp length
    subst cols; intro v hv; exact complement _ hv (by intro a ha; cases ha)
  | succ count ih =>
    cases cols with
    | nil => simp at length
    | cons a tail =>
      have taillen : tail.length=count := by simpa using length
      have head := inside a (by simp)
      have annih := null a (by simp)
      intro v hv
      by_cases az : B.inner a a=0
      · have eq := B.eqZeroOfInnerSelfEqZero a az
        subst a
        apply ih tail taillen prior (fun y hy => inside y (by simp [hy]))
          (fun y hy => null y (by simp [hy])) _ v hv
        intro w hp ht; apply complement w hp; intro x hx
        rcases List.mem_cons.mp hx with rfl|mem
        · exact B.zeroLeft _
        · exact ht _ mem
      · have pos : 0<B.inner a a := by have h := B.nonnegative a; grind
        let cols' := tail.map (remove B a)
        let prev := a::prior
        have len' : cols'.length=count := by simpa only [cols',List.length_map] using taillen
        have in' (t : V) (mem : t∈cols') : perpendicular B prev t := by
          obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
          exact priorRemoved B prior a k head (inside _ (by simp [hk]))
        have null' (t : V) (mem : t∈cols') (w : V) : D t w=0 := by
          obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
          rw [remove,sub,scale,scale,annih,null k (by simp [hk])]; grind only
        have comp' (w : V) (hp : perpendicular B prev w) (hc : perpendicular B cols' w) : 0≤D w w := by
          have pw := hp a (by simp [prev])
          apply complement w (by intro e he; exact hp e (by simp [prev,he]))
          intro c h
          rcases List.mem_cons.mp h with rfl|ht
          · exact pw
          · have rz := hc (remove B a c) (List.mem_map.mpr ⟨c,ht,rfl⟩)
            rw [removeLeft,pw] at rz
            by_cases z : B.inner c w=0
            · exact z
            · by_cases pp : 0<B.inner c w
              · have pp' := OrderedRing.mul_pos pos pp; grind only
              · have pp' := OrderedRing.mul_pos pos (show 0< -B.inner c w by grind); grind only
        have nonneg := ih cols' len' prev in' null' comp' (remove B a v) (priorRemoved B prior a v head hv)
        have coef (x : V) : D (remove B a v) x=B.inner a a*D v x := by
          rw [remove,sub,scale,scale,annih]; grind only
        rw [coef,sym v (remove B a v),coef] at nonneg
        by_cases result : 0≤D v v
        · exact result
        · have positive := OrderedRing.mul_pos pos (OrderedRing.mul_pos pos (show 0< -D v v by grind))
          grind only

/-- The whole quadratic form is bounded if the listed columns are
q-eigenvectors and the bound holds on their common orthogonal complement.
For a complex range, list each spanning column and its imaginary multiple. -/
theorem boundFromReducingColumns (B : RealInnerForm R V) (q : R) (T : V → V)
    (selfAdjoint : ∀v w,B.inner v (T w)=B.inner (T v) w) (cols : List V)
    (eigen : ∀a∈cols,∀w,B.inner (T a) w=q*B.inner a w)
    (complement : ∀w,perpendicular B cols w → B.inner w (T w)≤q*B.inner w w)
    (v : V) : B.inner v (T v)≤q*B.inner v v := by
  let D (x y : V) := q*B.inner x y-B.inner x (T y)
  have sym (x y : V) : D x y=D y x := by
    unfold D; rw [selfAdjoint x y,B.symmetric (T x) y,B.symmetric x y]
  have sub (x y z : V) : D (x-y) z=D x z-D y z := by
    unfold D; rw [B.subLeft,B.subLeft]; grind only
  have scale (c : R) (x y : V) : D (c•x) y=c*D x y := by
    unfold D; rw [B.smulLeft,B.smulLeft]; grind only
  have h := reduceQuadratic B D sym sub scale cols.length cols rfl [] (by intro a ha c hc; cases hc)
    (by intro a ha w; unfold D; rw [selfAdjoint,eigen a ha]; grind only)
    (by intro w _ orth; exact show 0≤q*B.inner w w-B.inner w (T w) by have e := complement w orth; grind)
    v (by intro c hc; cases hc)
  change 0≤q*B.inner v v-B.inner v (T v) at h
  grind only

/-- Finite-dimensional conclusion of the two-hole reducing argument.
The two diagonal occupations, opposite occupations, M-intertwinings,
and upper bound for M are the respective operator inputs in (208)-(210). -/
theorem boundFromTwoHoleBlocks {W : Type} [Zero W] [Sub W] [SMul R W]
    (B : RealInnerForm R V) (U : RealInnerForm R W) (q : R)
    (X Y : W → V) (xd yd : V → W) (Q : W → W) (M T : V → V)
    (basis : List W) (total : ∀z,(∀a∈basis,U.inner a z=0) → z=0)
    (xAdj : ∀a w,B.inner (X a) w=U.inner a (xd w))
    (yAdj : ∀a w,B.inner (Y a) w=U.inner a (yd w))
    (mSelf : ∀v w,B.inner v (M w)=B.inner (M v) w)
    (decomp : ∀v w,B.inner (T v) w=U.inner (xd v) (xd w)+U.inner (yd v) (yd w)+B.inner (M v) w)
    (xx : ∀a,xd (X a)=q•a-Q a) (yy : ∀a,yd (Y a)=q•a-Q a)
    (xy : ∀a,xd (Y a)=0) (yx : ∀a,yd (X a)=0)
    (decX : ∀a,M (X a)=X (Q a)) (decY : ∀a,M (Y a)=Y (Q a))
    (mUpper : ∀w,B.inner w (M w)≤q*B.inner w w) (v : V) :
    B.inner v (T v)≤q*B.inner v v := by
  have tSelf (a b : V) : B.inner a (T b)=B.inner (T a) b := by
    rw [B.symmetric a (T b),decomp,decomp,U.symmetric (xd b) (xd a),U.symmetric (yd b) (yd a),←mSelf,B.symmetric]
  let cols := basis.map X ++ basis.map Y
  apply boundFromReducingColumns B q T tSelf cols _ _ v
  · intro t h w
    rcases List.mem_append.mp h with x|y
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp x
      rw [decomp,xx,yx,U.zeroLeft,decX,xAdj,xAdj,U.subLeft,U.smulLeft]; grind only
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp y
      rw [decomp,yy,xy,U.zeroLeft,decY,yAdj,yAdj,U.subLeft,U.smulLeft]; grind only
  · intro w orth
    have hx : xd w=0 := total _ (by intro a ha; rw [←xAdj]; exact orth _ (List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)))
    have hy : yd w=0 := total _ (by intro a ha; rw [←yAdj]; exact orth _ (List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩)))
    rw [tSelf,decomp,hx,hy,U.zeroLeft,←mSelf]
    have h := mUpper w; grind only

end RankSeven.TwoHoleReducingBlock
#print axioms RankSeven.TwoHoleReducingBlock.boundFromTwoHoleBlocks
#print axioms RankSeven.TwoHoleReducingBlock.boundFromReducingColumns
