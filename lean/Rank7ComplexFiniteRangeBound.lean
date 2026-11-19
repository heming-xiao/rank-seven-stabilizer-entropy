import Rank7PhysicalTwoHoleOccupancy

/-! Fraction-free reducing-column criterion on a complex linear slice. -/
namespace RankSeven.ComplexFiniteRangeBound
open Lean.Grind ComplexScalar
variable {R V : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem scalarCancel {q : R} (pos : 0<q) (z : ComplexScalar R) (eq : ofReal q*z=0) : z=0 := by
  have component (r : R) (hz : q*r=0) : r=0 := by
    by_cases pp : 0<r
    · have h := OrderedRing.mul_pos pos pp; grind only
    · by_cases nn : r<0
      · have h := OrderedRing.mul_pos pos (show 0< -r by grind); grind only
      · grind
  have re0 := congrArg re eq; have im0 := congrArg im eq
  apply ComplexScalar.ext
  · apply component; simp only [re_mul,ofReal] at re0; change q*z.re-0*z.im=0 at re0; grind only
  · apply component; simp only [im_mul,ofReal] at im0; change q*z.im+0*z.re=0 at im0; grind only

/-- The ambient pairing H need only be positive definite on the vector
coordinates being used. N gives its real squared norm. E is the Hermitian
defect form, P the linear slice of interest. -/
theorem boundFromColumns (H E : V→V→ComplexScalar R) (N : V→R) (P : V→Prop) (comb : V→V→V)
    (nnonneg : ∀a,0≤N a) (nself : ∀a,H a a=ofReal (N a)) (nnull : ∀a,N a=0 → ∀w,H a w=0)
    (hRight : ∀a c w,H c (comb a w)=ofReal (N a)*H c w-H a w*H c a)
    (hLeft : ∀a c w,H (comb a c) w=ofReal (N a)*H c w-star (H a c)*H a w)
    (eRight : ∀a c w,E c (comb a w)=ofReal (N a)*E c w-H a w*E c a)
    (eLeft : ∀a c w,E (comb a c) w=ofReal (N a)*E c w-star (H a c)*E a w)
    (eSym : ∀a w,E w a=star (E a w))
    (pComb : ∀a w,P a → P w → P (comb a w))
    (cols : List V) (inside : ∀a∈cols,P a) (null : ∀a∈cols,∀w,P w → E a w=0)
    (complement : ∀w,P w → (∀a∈cols,H a w=0) → 0≤(E w w).re) (v : V) (inV : P v) : 0≤(E v v).re := by
  let perp (prev : List V) (w : V) := ∀a∈prev,H a w=0
  have clean (prev : List V) (a w : V) (ha : perp prev a) (hw : perp prev w) : perp (a::prev) (comb a w) := by
    intro c hc; rcases List.mem_cons.mp hc with rfl|hh <;> rw [hRight]
    · rw [nself]; grind only
    · rw [ha c hh,hw c hh]; grind only
  have eliminate (k : Nat) (rows prior : List V) (len : rows.length=k)
      (hin : ∀a∈rows,P a ∧ perp prior a) (hn : ∀a∈rows,∀w,P w→E a w=0)
      (bound : ∀w,P w→perp prior w→perp rows w→0≤(E w w).re) :
      ∀w,P w→perp prior w→0≤(E w w).re := by
    induction k generalizing rows prior with
    | zero =>
      have e := List.length_eq_zero_iff.mp len; subst rows
      intro w pw pr; exact bound w pw pr (by intro a h; cases h)
    | succ k ih =>
      cases rows with
      | nil => simp at len
      | cons a others =>
        have kl : others.length=k := by simpa using len
        obtain ⟨pa,ha⟩ := hin a (by simp)
        have na := hn a (by simp)
        intro w pw hw
        by_cases az : N a=0
        · apply ih others prior kl (fun c hc => hin c (by simp [hc])) (fun c hc => hn c (by simp [hc])) _ w pw hw
          intro t pt pr rs; apply bound t pt pr; intro c h
          rcases List.mem_cons.mp h with rfl|ht
          · exact nnull _ az _
          · exact rs c ht
        · have pos : 0<N a := by have h := nnonneg a; grind
          let rest := others.map (comb a)
          let prev := a::prior
          have lin : rest.length=k := by simpa only [rest,List.length_map] using kl
          have in' (c : V) (hc : c∈rest) : P c ∧ perp prev c := by
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
            obtain ⟨pj,hprior⟩ := hin j (by simp [hj]); exact ⟨pComb a j pa pj,clean prior a j ha hprior⟩
          have n' (c : V) (hc : c∈rest) (z : V) (pz : P z) : E c z=0 := by
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
            rw [eLeft,na z pz,hn j (by simp [hj]) z pz]; grind only
          have b' (z : V) (pz : P z) (pr : perp prev z) (rs : perp rest z) : 0≤(E z z).re := by
            have za := pr a (by simp [prev])
            apply bound z pz (fun t ht => pr t (by simp [prev,ht])); intro t ht
            rcases List.mem_cons.mp ht with rfl|tm
            · exact za
            · have zt := rs (comb a t) (List.mem_map.mpr ⟨t,tm,rfl⟩)
              rw [hLeft,za] at zt; apply scalarCancel pos _; grind only
          have lower := ih rest prev lin in' n' b' (comb a w) (pComb a w pa pw) (clean prior a w ha hw)
          have zeroA : E w a=0 := by rw [eSym,na w pw]; exact star_ofReal (0:R)
          have level : E (comb a w) (comb a w)=ofReal (N a)*(ofReal (N a)*E w w) := by
            rw [eLeft,na _ (pComb a w pa pw),eRight,zeroA]; grind only
          have rp (q : R) (u : ComplexScalar R) : (ofReal q*u).re=q*u.re := by simp [re_mul,ofReal]; grind only
          rw [level,rp,rp] at lower
          by_cases z : 0≤(E w w).re
          · exact z
          · have h := OrderedRing.mul_pos pos (OrderedRing.mul_pos pos (show 0< -(E w w).re by grind)); grind only
  exact eliminate cols.length cols [] rfl (fun a ha => ⟨inside a ha,by intro c hc; cases hc⟩) null
    (fun w pw _ hs => complement w pw hs) v inV (by intro c hc; cases hc)

open Pauli (sumOver sumOverCongr sumOverMulLeft sumOverMulRight)
def mass (H : V→V→ComplexScalar R) (rows : List V) (u v : V) :=
  sumOver rows (fun a => H u a*H a v)
def costs (H : V→V→ComplexScalar R) (rows : List V) (v : V) :=
  sumOver rows (fun a => normSq (H a v))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem scalarStarSub (a b : ComplexScalar R) : star (a-b)=star a-star b := by
  apply ComplexScalar.ext <;> simp <;> grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem massSym (H : V→V→ComplexScalar R) (hs : ∀a w,H w a=star (H a w)) (rows : List V) (u v : V) :
    mass H rows v u=star (mass H rows u v) := by
  rw [mass,mass,ComplexExterior.starSumOver]; apply sumOverCongr; intro a; rw [star_mul,←hs,←hs]; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem massSelf (H : V→V→ComplexScalar R) (hs : ∀a w,H w a=star (H a w)) (rows : List V) (u : V) :
    mass H rows u u=ofReal (costs H rows u) := by
  unfold mass costs
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    change H u x*H x u+sumOver xs _=ofReal (normSq (H x u)+sumOver xs _)
    rw [hs x u,star_mul_self,ih]; apply ComplexScalar.ext <;> simp <;> grind
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem costsZero (H : V→V→ComplexScalar R) (rows : List V) (w : V) (zero : ∀a∈rows,H a w=0) :
    costs H rows w=0 := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    change normSq (H a w)+costs H rows w=0
    rw [zero a (by simp),normSq_zero,ih (fun t ht => zero t (by simp [ht]))]; grind only

/-- Eigen-row identities and the upper bound for the remaining synthesis
columns imply the full Bessel inequality on a prescribed complex slice. -/
theorem besselFromEigenRows (H : V→V→ComplexScalar R) (N : V→R) (P : V→Prop) (comb : V→V→V)
    (hSym : ∀a w,H w a=star (H a w))
    (nnonneg : ∀a,0≤N a) (nself : ∀a,H a a=ofReal (N a)) (nnull : ∀a,N a=0 → ∀w,H a w=0)
    (hRight : ∀a c w,H c (comb a w)=ofReal (N a)*H c w-H a w*H c a)
    (hLeft : ∀a c w,H (comb a c) w=ofReal (N a)*H c w-star (H a c)*H a w)
    (pComb : ∀a w,P a→P w→P (comb a w))
    (rows others : List V) (q : R) (inside : ∀t∈rows,P t)
    (eigen : ∀a∈rows,∀w,P w→mass H rows a w+mass H others a w=ofReal q*H a w)
    (upper : ∀w,P w→costs H others w≤q*N w) (v : V) (pv : P v) :
    costs H rows v+costs H others v≤q*N v := by
  let E (a b : V) := ofReal q*H a b-mass H rows a b-mass H others a b
  have mr (ls : List V) (a c w : V) : mass H ls c (comb a w)=ofReal (N a)*mass H ls c w-H a w*mass H ls c a := by
    unfold mass; rw [sumOverMulLeft,sumOverMulLeft,←Compression.sumOverSub]; apply sumOverCongr; intro t; rw [hRight]; grind only
  have ml (ls : List V) (a c w : V) : mass H ls (comb a c) w=ofReal (N a)*mass H ls c w-star (H a c)*mass H ls a w := by
    unfold mass; rw [sumOverMulLeft,sumOverMulLeft,←Compression.sumOverSub]; apply sumOverCongr; intro t; rw [hLeft]; grind only
  have er (a c w : V) : E c (comb a w)=ofReal (N a)*E c w-H a w*E c a := by unfold E; rw [hRight,mr,mr]; grind only
  have el (a c w : V) : E (comb a c) w=ofReal (N a)*E c w-star (H a c)*E a w := by unfold E; rw [hLeft,ml,ml]; grind only
  have sym (a w : V) : E w a=star (E a w) := by
    unfold E; rw [scalarStarSub,scalarStarSub,star_mul,star_ofReal,←hSym,←massSym H hSym,←massSym H hSym]
  have diag (w : V) : (E w w).re = q*N w-costs H rows w-costs H others w := by
    unfold E; rw [nself,massSelf H hSym,massSelf H hSym]
    change (q*N w-0*0)-costs H rows w-costs H others w= _; grind only
  have result := boundFromColumns H E N P comb nnonneg nself nnull hRight hLeft er el sym pComb rows inside
    (by intro a ha w pw; unfold E; rw [←eigen a ha w pw]; grind only)
    (by intro w pw hw; rw [diag,costsZero H rows w hw]; have h := upper w pw; grind only) v pv
  rw [diag] at result; grind only

end RankSeven.ComplexFiniteRangeBound
#print axioms RankSeven.ComplexFiniteRangeBound.besselFromEigenRows
