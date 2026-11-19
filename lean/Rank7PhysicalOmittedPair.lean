import Rank7PhysicalCutCapacities
import Rank7PackingDual
import Rank7ExteriorDeterminantBridge

/-! Five-column cofactor reductions for the physical omitted-pair capacity.
All exterior weights use the normalized rank-seven Pauli kernel. -/
namespace RankSeven.PhysicalOmittedPair

open Lean.Grind Pauli ExteriorCuts HyperplaneInduction ComplexScalar PhysicalWedges
open GenericExteriorKernel (supportedPair)
open PhysicalCompressionEffect (physicalEntries OrthonormalFrame)
open PhysicalExteriorCompression (wedgeRows physicalKernel inverseWeight)
open PackingDual (occupied)
variable {R : Type} [CommRing R]

def fiveLabels (a b : Fin 7) := (List.finRange 7).filter fun i => (i != a) && (i != b)

def label (a b : Fin 7) (j : Fin 5) := (fiveLabels a b)[j.val]?.getD 0

def skip (j : Fin 5) (i : Fin 4) : Fin 5 := ⟨if i.val<j.val then i.val else i.val+1,by split <;> omega⟩

def fourFace (a b : Fin 7) (j : Fin 5) : Wedge7 :=
  let f (i : Fin 4) := label a b (skip j i)
  if h : f 0<f 1 ∧ f 1<f 2 ∧ f 2<f 3 then ⟨_,_,_,_,h.1,h.2.1,h.2.2⟩ else ⟨0,1,2,3,by decide,by decide,by decide⟩

def faces (a b : Fin 7) := wedges.filter fun w => !occupied w a && !occupied w b

private def neg (j : Fin 5) := j.val%2==1

theorem facesExact (a b : Fin 7) (ab : a<b) :
    ((List.finRange 5).map (fourFace a b)).Perm (faces a b) ∧
    (∀ j k, label a b j=label a b k ↔ j=k) ∧
    (∀ j i, sourceSite (fourFace a b j) i=label a b (skip j i)) := by
  revert a b; decide

private theorem permSum {C α : Type} [CommRing C] {xs ys : List α} (perm : xs.Perm ys) (f : α → C) :
    sumOver xs f=sumOver ys f := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ a b => exact a.trans b

private theorem realSum {α : Type} (xs : List α) (f : α → ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change (f a+sumOver xs f).re=(f a).re+sumOver xs _; rw [re_add,ih]

private theorem conjSum {α : Type} (xs : List α) (f : α → ComplexScalar R) : star (sumOver xs f)=sumOver xs (fun i => star (f i)) := by
  induction xs with
  | nil => exact star_ofReal (0:R)
  | cons a xs ih => change star (f a+sumOver xs f)=star (f a)+sumOver xs _; rw [star_add,ih]

private theorem filteredSum {C α : Type} [CommRing C] (xs : List α) (sel : α → Bool) (f : α → C) :
    sumOver (xs.filter sel) f=sumOver xs (fun i => if sel i then f i else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases h : sel x <;> simp [h,sumOver] at ih ⊢ <;> grind

private theorem signedSquare (b : Bool) (z v : ComplexScalar R) :
    star (if b then -z else z)*(if b then -v else v)=star z*v := by cases b <;> apply ComplexScalar.ext <;> simp <;> grind

def laplace {S : Type} (A : S → Fin 7 → ComplexScalar R) (a b : Fin 7) (row : Fin 4 → S) (t : S) : ComplexScalar R :=
  sumOver (List.finRange 5) fun j =>
    (if neg j then -minor4 A row (fourFace a b j) else minor4 A row (fourFace a b j))*A t (label a b j)

/-- Contracting the spectator in the genuine five-column Laplace expansion
recovers the exact sum of the five four-minor products. -/
theorem spectatorContraction {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (a b : Fin 7) (ab : a<b) (u v : Fin 4 → Basis n) :
    sumOver (qubitIndices n) (fun t => star (laplace A a b u t)*laplace A a b v t)=
      sumOver (faces a b) (fun w => star (minor4 A u w)*minor4 A v w) := by
  let J := List.finRange 5
  let xs := qubitIndices n
  let m (k : Fin 4 → Basis n) (j : Fin 5) := if neg j then -minor4 A k (fourFace a b j) else minor4 A k (fourFace a b j)
  have row (t : Basis n) : star (laplace A a b u t)*laplace A a b v t=
      sumOver J (fun j => sumOver J (fun k => (star (m u j)*m v k)*(star (A t (label a b j))*A t (label a b k)))) := by
    unfold laplace; rw [conjSum,sumOverMulRight]; apply sumOverCongr; intro j
    rw [sumOverMulLeft]; apply sumOverCongr; intro k; rw [star_mul]
    change star (m u j)*star (A t (label a b j))*(m v k*A t (label a b k))=_
    grind
  rw [sumOverCongr _ row,sumOverSwap]
  have collapse (j : Fin 5) :
    sumOver xs (fun t => sumOver J (fun k => (star (m u j)*m v k)*(star (A t (label a b j))*A t (label a b k))))=
      star (minor4 A u (fourFace a b j))*minor4 A v (fourFace a b j) := by
    rw [sumOverSwap]
    have term (k : Fin 5) : sumOver xs (fun t => (star (m u j)*m v k)*(star (A t (label a b j))*A t (label a b k)))=
        if j=k then star (m u j)*m v k else 0 := by
      rw [←sumOverMulLeft,orth]
      by_cases e : j=k
      · subst k; simp; grind
      · have ne : label a b j≠label a b k := fun h => e (((facesExact a b ab).2.1 j k).mp h)
        simp [e,ne]; grind
    rw [sumOverCongr _ term,ExteriorPauliBase.sumOnIndex J j _ (List.nodup_finRange 5) (List.mem_finRange _)]
    exact signedSquare _ _ _
  rw [sumOverCongr J collapse]
  simpa only [sumOver,List.map_map,Function.comp_def] using permSum (facesExact a b ab).1 (fun w => star (minor4 A u w)*minor4 A v w)

private theorem supportEntry (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R) (w : Wedge7) :
    (physicalEntries half unit k A).realPart w w =
      (sumOver (coords (k+3)) (fun u => sumOver (coords (k+3)) (fun v => if supportedPair u.val v.val then
        star (minor4 A (wedgeRows u) w)*minor4 A (wedgeRows v) w else 0))).re := by
  let xs := coords (k+3)
  let z (u : Coordinate (k+3)) := minor4 A (wedgeRows u) w
  change (ofReal (inverseWeight R k)*sumOver xs (fun u => star (z u)*sumOver xs (fun v => ofReal (physicalKernel half (u,v))*z v))).re=_
  apply congrArg ComplexScalar.re
  rw [sumOverMulLeft]; apply sumOverCongr; intro u
  rw [←Semiring.mul_assoc,sumOverMulLeft]; apply sumOverCongr; intro v
  rw [PhysicalExteriorCompression.physicalKernel_eq half unit]
  have inv := PhysicalExteriorCompression.inverseWeight_mul_weight half unit k
  by_cases h : supportedPair u.val v.val=true
  · rw [ite_eq_left h,ite_eq_left h]
    have mul : ofReal (inverseWeight R k)*ofReal (PhysicalChartRestriction.weight half (k+3))=(1:ComplexScalar R) := by
      apply ComplexScalar.ext <;> simp <;> grind
    change (ofReal (inverseWeight R k)*star (z u))*(ofReal (PhysicalChartRestriction.weight half (k+3))*z v)=star (z u)*z v
    grind
  · rw [ite_eq_right h,ite_eq_right h]; change (_*star (z u))*(0*z v)=0; grind

/-- Exact common-spectator kernel formula on an arbitrary orthonormal complex
seven-frame, after the normalization by q used in the LP rows. -/
theorem omittedSpectatorTrace (half : R) (unit : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (a b : Fin 7) (ab : a<b) :
    PackingDual.rowMass (fun w => (physicalEntries half unit k A).realPart w w) (.omitPair a b)=
      (sumOver (coords (k+3)) (fun u => sumOver (coords (k+3)) (fun v => if supportedPair u.val v.val then
        sumOver (qubitIndices (k+3)) (fun t => star (laplace A a b (wedgeRows u) t)*laplace A a b (wedgeRows v) t) else 0))).re := by
  let xs := coords (k+3)
  let C (w : Wedge7) (u v : Coordinate (k+3)) := if supportedPair u.val v.val then
    star (minor4 A (wedgeRows u) w)*minor4 A (wedgeRows v) w else 0
  have left : PackingDual.rowMass (fun w => (physicalEntries half unit k A).realPart w w) (.omitPair a b)=
    (sumOver (faces a b) (fun w => sumOver xs (fun u => sumOver xs (C w u)))).re := by
    rw [realSum,faces,filteredSum]; apply sumOverCongr; intro w
    change (if !occupied w a && !occupied w b then _ else 0)=if !occupied w a && !occupied w b then _ else 0
    split <;> first | exact supportEntry half unit k A w | rfl
  rw [left,sumOverSwap]; apply congrArg ComplexScalar.re; apply sumOverCongr; intro u; rw [sumOverSwap]
  apply sumOverCongr; intro v
  rw [spectatorContraction A orth a b ab]
  by_cases h : supportedPair u.val v.val=true
  · simp only [C,h,ite_true]
  · simp only [C,ite_eq_right h]
    have zero (ls : List Wedge7) : sumOver ls (fun _ => (0:ComplexScalar R))=0 := by
      induction ls with | nil => rfl | cons w ls ih => change 0+sumOver ls _=0; rw [ih]; grind
    exact zero _

open ExteriorOccupation (Point points)
open ExteriorOperators (Form exteriorProduct annihilate create pairing site lowerCoeff toggle Mask)
open ExteriorPauliBase (Wedge qubitBits)
open ExteriorPauliBase (wedgeIndices)
open ExteriorPauliBase (maskIndex restrictFour)
open ExteriorDeterminantBridge (columnsOf baseRows)

attribute [local instance] Ring.intCast

private def terms {C : Type} [CommRing C] (u : Point → C) :
    List (Point → C) → List (C × List (Point → C))
  | [] => []
  | v::vs => (ExteriorOperators.pairing u v,vs)::(terms u vs).map (fun h => (-h.1,v::h.2))

private theorem contractTerms {C : Type} [CommRing C] (u : Point → C) (vs : List (Point → C)) (m : Mask) :
    annihilate u (exteriorProduct vs) m=sumOver (terms u vs) (fun h => h.1*exteriorProduct h.2 m) := by
  induction vs generalizing m with
  | nil => change annihilate u ExteriorOperators.vacuum m=0; rw [ExteriorOperators.annihilate_vacuum]
  | cons v vs ih =>
    have car := ExteriorOperators.annihilate_create_car u v (exteriorProduct vs) m
    have lin : create v (annihilate u (exteriorProduct vs)) m =
       sumOver (terms u vs) (fun h => h.1*create v (exteriorProduct h.2) m) := by
      unfold create ExteriorOperators.combine site
      simp only [ih,←Semiring.mul_assoc,sumOverMulLeft]
      rw [sumOverSwap]; apply sumOverCongr; intro h
      apply sumOverCongr; intro i; grind
    rw [lin] at car
    change annihilate u (create v (exteriorProduct vs)) m =
      ExteriorOperators.pairing u v*exteriorProduct vs m + sumOver ((terms u vs).map (fun h => (-h.1,v::h.2))) (fun h => h.1*exteriorProduct h.2 m)
    have negsum (ls : List (C × List (Point → C))) : sumOver (ls.map (fun h => (-h.1,v::h.2))) (fun h => h.1*exteriorProduct h.2 m) =
        -sumOver ls (fun h => h.1*create v (exteriorProduct h.2) m) := by
      induction ls with
      | nil => change 0=-(0:C); grind
      | cons x ls ih =>
        change (-x.1)*create v (exteriorProduct x.2) m+sumOver _ _ = -(x.1*create v (exteriorProduct x.2) m+sumOver ls _)
        rw [ih]; grind
    rw [negsum]; grind only

private def delta {C : Type} [CommRing C] (t i : Point) : C := if t=i then 1 else 0

private theorem deltaSum {C : Type} [CommRing C] (t : Point) (f : Point → C) :
    sumOver points (fun i => delta t i*f i)=f t := by
  rw [←ExteriorPauliBase.sumOnIndex points t f (List.nodup_finRange 8) (List.mem_finRange _)]; apply sumOverCongr
  intro i; unfold delta; split <;> grind

omit [CommRing R] in
private theorem labelColumns (a b : Fin 7) (ab : a<b) (j : Fin 5) (A : Point → Fin 7 → ComplexScalar R) :
    columnsOf A (fourFace a b j) = ([0,1,2,3] : List (Fin 4)).map fun i => fun t => A t (label a b (skip j i)) := by
  have h := (facesExact a b ab).2.2 j
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  change (fourFace a b j).i=_ at h0; change (fourFace a b j).j=_ at h1
  change (fourFace a b j).k=_ at h2; change (fourFace a b j).m=_ at h3
  simp [columnsOf,h0,h1,h2,h3]

def fiveForm (A : Point → Fin 7 → ComplexScalar R) (a b : Fin 7) :=
  exteriorProduct ((List.finRange 5).map fun j => fun t => A t (label a b j))

/-- The spectator cofactor at an eight-site wedge is the matching signed
coordinate contraction of one common five-form. -/
theorem baseCofactor (A : Point → Fin 7 → ComplexScalar R) (a b : Fin 7) (ab : a<b) (u : Wedge) (t : Point) :
    laplace A a b (baseRows u) t = site lowerCoeff t (fiveForm A a b) (maskIndex u) := by
  have ct := contractTerms (delta (C:=ComplexScalar R) t) ((List.finRange 5).map fun j => fun i => A i (label a b j)) (maskIndex u)
  change sumOver points (fun i => delta t i*site lowerCoeff i (fiveForm A a b) (maskIndex u))=_ at ct
  rw [deltaSum] at ct; rw [ct]
  unfold laplace
  have mm (j : Fin 5) : minor4 A (baseRows u) (fourFace a b j) =
     exteriorProduct (([0,1,2,3] : List (Fin 4)).map fun i => fun s => A s (label a b (skip j i))) (maskIndex u) := by
    rw [←ExteriorDeterminantBridge.exteriorProduct_eq_minor4,labelColumns a b ab]; rfl
  simp only [mm]
  have js : List.finRange 5=([0,1,2,3,4] : List (Fin 5)) := by decide
  rw [js]
  have d (j : Fin 5) : ExteriorOperators.pairing (delta t) (fun i => A i (label a b j))=A t (label a b j) := deltaSum _ _
  simp only [terms,List.map_cons,List.map_nil,d]
  simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  let c (j : Fin 5) (i : Point) := A i (label a b j)
  let E (i j k l : Fin 5) := exteriorProduct [c i,c j,c k,c l] (maskIndex u)
  change E 1 2 3 4*c 0 t + (-E 0 2 3 4*c 1 t + (E 0 1 3 4*c 2 t + (-E 0 1 2 4*c 3 t + (E 0 1 2 3*c 4 t+0)))) =
    c 0 t*E 1 2 3 4 + (-c 1 t*E 0 2 3 4 + (-(-c 2 t)*E 0 1 3 4 + (-(-(-c 3 t))*E 0 1 2 4 + (-(-(-(-c 4 t)))*E 0 1 2 3+0))))
  grind only
private def activeBase (u : Wedge) :=
  letI : DecidableEq (Basis 3) := inferInstanceAs (DecidableEq (Bool × Bool × Bool × Unit))
  decide (GenericExteriorKernel.parity (baseCoordinate u).val=HyperplaneIncidence.zero 3)

private theorem supportedBaseSelf (u : Wedge) :
    supportedPair (baseCoordinate u).val (baseCoordinate u).val=activeBase u := by
  apply Bool.eq_iff_iff.mpr
  exact (PhysicalExteriorSupport.supported_diagonal _).trans (by simp [activeBase])

private theorem gramNonzero (u v : Wedge) (h : supportedPair (baseCoordinate u).val (baseCoordinate v).val=true) :
    ExteriorPauliBase.planeGram u v≠0 := by
  let half : Fin 3 := 2
  have unit : 2*half=1 := by decide
  have kernel := GenericExteriorKernel.sorted_kernel_entry (1:Fin 3) half (by decide) unit
    (baseCoordinate u).val (baseCoordinate v).val (baseCoordinate u).property (baseCoordinate v).property
  rw [PhysicalExteriorCompression.baseKernel, ExteriorDeterminantBridge.normalized_physical_eq_gram _ _ (by decide) unit] at kernel
  change half*Int.cast (ExteriorPauliBase.planeGram u v)=(if supportedPair (baseCoordinate u).val (baseCoordinate v).val then PhysicalChartRestriction.weight half 3 else 0) at kernel
  rw [h,ite_eq_left rfl,PhysicalChartRestriction.weightThree half unit] at kernel
  intro e; rw [e,Ring.intCast_ofNat,Semiring.mul_zero] at kernel
  exact (by decide : (0:Fin 3)≠half) kernel

private theorem waveSupports (u : Wedge) (n : ExteriorOccupation.Direction) (t : Point)
    (eq : ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf u)≠0)
    (outside : lowerCoeff t (maskIndex u)≠0) :
    ExteriorPauliBase.maskOf u=ExteriorOccupation.cosetMask n (!ExteriorOccupation.side n t) := by
  have membership : ∀ (n : ExteriorOccupation.Direction) (t : Point) (b : Bool),
      (ExteriorOccupation.cosetMask n b).testBit t.val = (ExteriorOccupation.side n t==b) := by decide
  have bit : (ExteriorPauliBase.maskOf u).testBit t.val=false := by
    have q : ExteriorOperators.occupied t (maskIndex u)=false := by
      cases e : ExteriorOperators.occupied t (maskIndex u) <;> simp [ExteriorOperators.lowerCoeff,e] at *
    simpa only [ExteriorOperators.occupied,ExteriorPauliBase.maskIndexVal] using q
  unfold ExteriorOccupation.planeWave at eq
  split at eq
  next yes =>
    obtain hl|hr := Bool.or_eq_true_iff.mp yes <;> rw [beq_iff_eq] at * <;>
      first | rw [hl,membership] at bit; rw [hl]; cases e : ExteriorOccupation.side n t <;> simp_all
            | rw [hr,membership] at bit; rw [hr]; cases e : ExteriorOccupation.side n t <;> simp_all
  next no => exact False.elim (eq rfl)

set_option maxRecDepth 60000 in
private theorem noCrossBase (u v : Wedge) (t : Point)
    (supported : supportedPair (baseCoordinate u).val (baseCoordinate v).val=true)
    (hu : lowerCoeff t (maskIndex u)≠0) (hv : lowerCoeff t (maskIndex v)≠0) : u=v := by
  have neq := gramNonzero u v supported
  have existsWave : ∃ n : ExteriorOccupation.Direction, ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf u)≠0 ∧
     ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf v)≠0 := by
    apply Classical.byContradiction; intro no; apply neq
    unfold ExteriorPauliBase.planeGram
    have z (n : ExteriorOccupation.Direction) : ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf u)*
        ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf v)=0 := by
      by_cases e : ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf u)=0
      · rw [e]; grind
      · have d : ExteriorOccupation.planeWave n (ExteriorPauliBase.maskOf v)=0 := Classical.byContradiction (fun h => no ⟨n,e,h⟩)
        rw [d]; grind
    simp only [z]; decide
  obtain ⟨n,nu,nv⟩ := existsWave
  have masks := (waveSupports u n t nu hu).trans (waveSupports v n t nv hv).symm
  have inj : ∀ (i j : Wedge), ExteriorPauliBase.maskOf i=ExteriorPauliBase.maskOf j → i=j := by decide
  exact inj _ _ masks

private def allFive (activeOnly : Bool) : List Mask :=
    (wedgeIndices.filter (fun u => !activeOnly || activeBase u)).flatMap fun u =>
      (points.filter (fun t => lowerCoeff t (maskIndex u)!=0)).map fun t => toggle t (maskIndex u)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
private theorem maskMultiplicity :
    (allFive false).Perm (allFive true ++ allFive true ++ allFive true ++ allFive true ++ allFive true) := by decide
private theorem minorNorm [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] (n : Nat) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (w : Wedge7) :
    sumOver (coords n) (fun u => star (minor4 A (wedgeRows u) w)*minor4 A (wedgeRows u) w)=1 := by
  let d (z : Wedge7) : ComplexScalar R := if w=z then 1 else 0
  have lifted (u : Coordinate n) :
      exteriorLift (fun t : Coordinate n => GenericExteriorKernel.position t.val) A d u=minor4 A (wedgeRows u) w := by
    unfold exteriorLift
    rw [←ExteriorPauliBase.sumOnIndex wedges w (fun z => minor4 A (wedgeRows u) z) wedgesNodup (memWedges _)]
    apply sumOverCongr; intro z; change minor4 A (wedgeRows u) z * (if w=z then 1 else 0)=_
    split <;> grind
  have eq := ExteriorIsometry.physicalIsometry n A orth d d
  rw [sumOverCongr _ (fun u => congrArg (fun q => star q*q) (lifted u))] at eq
  rw [eq,←ExteriorPauliBase.sumOnIndex wedges w (fun _ => (1:ComplexScalar R)) wedgesNodup (memWedges _)]
  apply sumOverCongr; intro z
  by_cases h : w=z <;> simp only [d,h,ite_true,ite_false]
  · rw [show star (1:ComplexScalar R)=1 from star_ofReal (1:R)]; grind
  · grind

/-- All five spectator presentations together have squared norm five,
by fourth exterior isometry applied once to each retained four-face. -/
theorem totalCofactorMass [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] (n : Nat) (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A)
    (a b : Fin 7) (ab : a<b) :
    sumOver (coords n) (fun u => sumOver (qubitIndices n) (fun t =>
      star (laplace A a b (wedgeRows u) t)*laplace A a b (wedgeRows u) t))=5 := by
  simp only [spectatorContraction A orth a b ab]
  rw [sumOverSwap]; simp only [minorNorm n A orth]
  rw [←permSum (facesExact a b ab).1]
  change ((1:ComplexScalar R)+(1+(1+(1+(1+0)))))=5; grind

private theorem sumSiteSquares (f : Form (ComplexScalar R)) (onlyPlanes : Bool) :
  sumOver wedgeIndices (fun u => if !onlyPlanes || activeBase u then sumOver points (fun t =>
    star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex u)) else 0)=
  sumOver (allFive onlyPlanes) (fun m => star (f m)*f m) := by
  have signs : ∀ (t : Point) (w : Wedge), lowerCoeff t (maskIndex w)=0 ∨
    lowerCoeff t (maskIndex w)=1 ∨ lowerCoeff t (maskIndex w)= -1 := by set_option maxRecDepth 100000 in decide
  rw [allFive,sumOverFlatMap,filteredSum]; apply sumOverCongr; intro u
  split
  · simp only [sumOver,List.map_map,Function.comp_def]
    change sumOver points (fun t => star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex u))=
       sumOver (points.filter (fun t => lowerCoeff t (maskIndex u)!=0)) (fun t => star (f (toggle t (maskIndex u)))*f (toggle t (maskIndex u)))
    rw [filteredSum]; apply sumOverCongr; intro t
    have unit (z : ComplexScalar R) : star (-z)*(-z)=star z*z := signedSquare true z z
    obtain h|h|h := signs t u <;>
      simp only [site,h,Ring.intCast_neg,ne_eq,bne_iff_ne] <;> first | rfl | grind
  · rfl

private theorem baseMaskTrace (f : Form (ComplexScalar R)) :
    sumOver wedgeIndices (fun u => sumOver wedgeIndices (fun v => if supportedPair (baseCoordinate u).val (baseCoordinate v).val then
      sumOver points (fun t => star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex v)) else 0))=
    sumOver (allFive true) (fun m => star (f m)*f m) := by
  rw [←sumSiteSquares]; apply sumOverCongr; intro u
  have diag (v : Wedge) :
    (if supportedPair (baseCoordinate u).val (baseCoordinate v).val then
      sumOver points (fun t => star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex v)) else 0)=
    (if u=v then (if activeBase u then sumOver points (fun t =>
      star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex u)) else 0) else 0) := by
    by_cases same : u=v
    · subst v; rw [supportedBaseSelf,ite_eq_left rfl]
    · rw [ite_eq_right same]; split
      next yes =>
        have each (t : Point) : star (site lowerCoeff t f (maskIndex u))*site lowerCoeff t f (maskIndex v)=0 := by
          by_cases h : lowerCoeff t (maskIndex u)=0
          · have q : site lowerCoeff t f (maskIndex u)=0 := by unfold site; rw [h]; grind
            rw [q,show star (0:ComplexScalar R)=0 from star_ofReal (0:R)]; grind
          · have hv : lowerCoeff t (maskIndex v)=0 := Classical.byContradiction (fun d => same (noCrossBase _ _ _ yes h d))
            have q : site lowerCoeff t f (maskIndex v)=0 := by unfold site; rw [hv]; grind
            rw [q]; grind
        simp only [each]; change 0+(0+(0+(0+(0+(0+(0+(0+0)))))))=(0:ComplexScalar R); grind
      next no => rfl
  rw [sumOverCongr _ diag,ExteriorPauliBase.sumOnIndex wedgeIndices u (fun _ => _) (List.nodup_finRange _) (List.mem_finRange _)]
  rfl
private theorem pointSums {C : Type} [CommRing C] (f : Basis 3 → C) :
    sumOver (qubitIndices 3) f=sumOver points (fun t => f (qubitBits t)) := by
  letI : DecidableEq (Basis 3) := inferInstanceAs (DecidableEq (Bool × Bool × Bool × Unit))
  have h : (points.map qubitBits).Perm (qubitIndices 3) := by decide
  simpa only [sumOver,List.map_map,Function.comp_def] using permSum h.symm f

private theorem baseCofactorAt (A : Basis 3 → Fin 7 → ComplexScalar R) (a b : Fin 7) (ab : a<b) (u : Wedge) (t : Point) :
    laplace A a b (wedgeRows (baseCoordinate u)) (qubitBits t)=
      site lowerCoeff t (fiveForm (fun i => A (qubitBits i)) a b) (maskIndex u) := by
  rw [←baseCofactor _ a b ab u t]
  simp only [laplace,minor4,wedgeRows,baseRows,baseCoordinateAt]

/-- Every normalized omitted-pair row is exactly saturated for arbitrary
orthonormal complex seven-frames in the three-qubit ambient space. -/
theorem physicalOmittedPairEight [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (half : R) (unit : 2*half=1) (A : Basis 3 → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (a b : Fin 7) (ab : a<b) :
    PackingDual.rowMass (fun w => (physicalEntries half unit 0 A).realPart w w) (.omitPair a b)=1 := by
  let f := fiveForm (fun i => A (qubitBits i)) a b
  let M (m : Mask) := star (f m)*f m
  have allMass : sumOver (allFive false) M=5 := by
    have total := totalCofactorMass 3 A orth a b ab
    simp only [baseSums,pointSums,baseCofactorAt A a b ab] at total
    rw [←sumSiteSquares f false]
    simpa only [Bool.not_false,Bool.true_or,ite_true] using total
  have trace := omittedSpectatorTrace half unit 0 A orth a b ab
  change _=(sumOver (coords 3) (fun u => sumOver (coords 3) (fun v => if supportedPair u.val v.val then
    sumOver (qubitIndices 3) (fun t => star (laplace A a b (wedgeRows u) t)*laplace A a b (wedgeRows v) t) else 0))).re at trace
  simp only [baseSums,pointSums,baseCofactorAt A a b ab,baseMaskTrace] at trace
  change _=(sumOver (allFive true) M).re at trace
  have p := permSum maskMultiplicity M
  have joined (xs ys : List Mask) : sumOver (xs++ys) M=sumOver xs M+sumOver ys M := by
    induction xs with
    | nil => change sumOver ys M=0+sumOver ys M; grind
    | cons m xs ih => change M m+sumOver (xs++ys) M=M m+sumOver xs M+sumOver ys M; rw [ih]; grind
  simp only [joined,allMass] at p
  let x := (sumOver (allFive true) M).re
  have h := congrArg ComplexScalar.re p
  simp only [re_add] at h
  change 5=x+x+x+x+x at h
  rw [trace]
  change x=1
  grind only
end RankSeven.PhysicalOmittedPair
