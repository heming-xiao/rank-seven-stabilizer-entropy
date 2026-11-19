import Rank7PackingDual

/-! Exact classification of restored tail coefficients and continuous
interpolation of their two physical probe charges. -/
namespace RankSeven.PackingInterpolation

open Lean.Grind Pauli ExteriorCuts PackingDual
attribute [local instance] Semiring.natCast

def tailLabel (i : Fin 7) : Bool := decide (3≤i.val ∧ i.val≤5)

def hasTail (m : Gap) : Bool := tailLabel m.1.1 || tailLabel m.1.2 || tailLabel m.2.1 || tailLabel m.2.2

def restoredGaps : List Gap := (fourIndices (List.finRange 7)).filter fun m =>
  decide (m.1.1≤m.1.2 ∧ m.1.2≤m.2.1 ∧ m.2.1≤m.2.2) && hasTail m

def unlistedGaps : List Gap := restoredGaps.filter fun m => !adjustedGaps.contains m

theorem restoredGapMem (m : Gap) : m∈restoredGaps ↔ sortedGap m ∧ hasTail m=true := by
  have full (a : Fin 7) := List.mem_finRange a
  have all : m∈fourIndices (List.finRange 7) := HyperplaneInduction.pairMember
    (HyperplaneInduction.pairMember (full _) (full _)) (HyperplaneInduction.pairMember (full _) (full _))
  simp only [restoredGaps,List.mem_filter,all,true_and,Bool.and_eq_true_iff,decide_eq_true_eq,sortedGap]

theorem unlistedGapMem (m : Gap) : m∈unlistedGaps ↔ m∈restoredGaps ∧ m∉adjustedGaps := by
  simp [unlistedGaps]

set_option maxRecDepth 4096 in
/-- Complete cardinalities in the partition of the 175 restored monomials. -/
theorem restoredPartition :
    restoredGaps.length=175 ∧ restoredGaps.Nodup ∧ unlistedGaps.length=127 ∧
    adjustedGaps.length=48 ∧ adjustedGaps.all (fun m => restoredGaps.contains m)=true := by decide

def noProbe (m : Gap) : Bool :=
  !exceptional m && probeCount m 0 2 1 3 == 0 && probeCount m 0 1 2 3 == 0 &&
    probeCount m 1 1 2 3 == 0 && probeCount m 1 2 2 3 == 0

private theorem countMonotone {α : Type} (xs : List α) (f g : α → Bool) (h : ∀ x, f x=true → g x=true) :
    xs.countP f≤xs.countP g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    rw [List.countP_cons,List.countP_cons]
    have hx := h x
    cases hf : f x <;> cases hg : g x <;> simp_all <;> omega

private theorem probeMonotone (m : Gap) (g h i j i' j' : Fin 7) (lo : i≤i') (hi : j≤j') :
    probeCount m g h i' j'≤probeCount m g h i j := by
  apply countMonotone; intro z eq
  obtain ⟨a,b,c,d⟩ := _root_.of_decide_eq_true eq
  exact _root_.decide_eq_true ⟨a,b,Fin.le_trans lo c,Fin.le_trans hi d⟩

private def group00 : List Gap := [((0,0),(0,3)),((0,0),(0,4)),((0,0),(0,5)),((0,0),(1,3)),((0,0),(1,4)),((0,0),(1,5)),((0,0),(2,3)),((0,0),(2,4))]
private theorem noProbe00 : group00.all noProbe=true := by decide
private def group01 : List Gap := [((0,0),(2,5)),((0,0),(3,3)),((0,0),(3,4)),((0,0),(3,5)),((0,0),(3,6)),((0,0),(4,4)),((0,0),(4,5)),((0,0),(4,6))]
private theorem noProbe01 : group01.all noProbe=true := by decide
private def group02 : List Gap := [((0,0),(5,5)),((0,0),(5,6)),((0,1),(1,3)),((0,1),(1,4)),((0,1),(1,5)),((0,3),(3,3)),((0,3),(3,4)),((0,3),(3,5))]
private theorem noProbe02 : group02.all noProbe=true := by decide
private def group03 : List Gap := [((0,3),(3,6)),((0,3),(4,4)),((0,3),(4,5)),((0,3),(4,6)),((0,3),(5,5)),((0,3),(5,6)),((0,3),(6,6)),((0,4),(4,4))]
private theorem noProbe03 : group03.all noProbe=true := by decide
private def group04 : List Gap := [((0,4),(4,5)),((0,4),(4,6)),((0,4),(5,5)),((0,4),(5,6)),((0,4),(6,6)),((0,5),(5,5)),((0,5),(5,6)),((0,5),(6,6))]
private theorem noProbe04 : group04.all noProbe=true := by decide
private def group05 : List Gap := [((1,1),(1,3)),((1,1),(1,4)),((1,1),(1,5)),((1,3),(3,3)),((1,3),(3,4)),((1,3),(3,5)),((1,3),(3,6)),((1,3),(4,4))]
private theorem noProbe05 : group05.all noProbe=true := by decide
private def group06 : List Gap := [((1,3),(4,5)),((1,3),(4,6)),((1,3),(5,5)),((1,3),(5,6)),((1,3),(6,6)),((1,4),(4,4)),((1,4),(4,5)),((1,4),(4,6))]
private theorem noProbe06 : group06.all noProbe=true := by decide
private def group07 : List Gap := [((1,4),(5,5)),((1,4),(5,6)),((1,4),(6,6)),((1,5),(5,5)),((1,5),(5,6)),((1,5),(6,6)),((2,2),(2,3)),((2,2),(2,4))]
private theorem noProbe07 : group07.all noProbe=true := by decide
private def group08 : List Gap := [((2,2),(2,5)),((2,2),(3,3)),((2,2),(3,4)),((2,2),(3,5)),((2,2),(3,6)),((2,2),(4,4)),((2,2),(4,5)),((2,2),(4,6))]
private theorem noProbe08 : group08.all noProbe=true := by decide
private def group09 : List Gap := [((2,2),(5,5)),((2,2),(5,6)),((2,3),(3,3)),((2,3),(3,4)),((2,3),(3,5)),((2,3),(3,6)),((2,3),(4,4)),((2,3),(4,5))]
private theorem noProbe09 : group09.all noProbe=true := by decide
private def group10 : List Gap := [((2,3),(4,6)),((2,3),(5,5)),((2,3),(5,6)),((2,3),(6,6)),((2,4),(4,4)),((2,4),(4,5)),((2,4),(4,6)),((2,4),(5,5))]
private theorem noProbe10 : group10.all noProbe=true := by decide
private def group11 : List Gap := [((2,4),(5,6)),((2,4),(6,6)),((2,5),(5,5)),((2,5),(5,6)),((2,5),(6,6)),((3,3),(3,3)),((3,3),(3,4)),((3,3),(3,5))]
private theorem noProbe11 : group11.all noProbe=true := by decide
private def group12 : List Gap := [((3,3),(3,6)),((3,3),(4,4)),((3,3),(4,5)),((3,3),(4,6)),((3,3),(5,5)),((3,3),(5,6)),((3,3),(6,6)),((3,4),(4,4))]
private theorem noProbe12 : group12.all noProbe=true := by decide
private def group13 : List Gap := [((3,4),(4,5)),((3,4),(4,6)),((3,4),(5,5)),((3,4),(5,6)),((3,4),(6,6)),((3,5),(5,5)),((3,5),(5,6)),((3,5),(6,6))]
private theorem noProbe13 : group13.all noProbe=true := by decide
private def group14 : List Gap := [((3,6),(6,6)),((4,4),(4,4)),((4,4),(4,5)),((4,4),(4,6)),((4,4),(5,5)),((4,4),(5,6)),((4,4),(6,6)),((4,5),(5,5))]
private theorem noProbe14 : group14.all noProbe=true := by decide
private def group15 : List Gap := [((4,5),(5,6)),((4,5),(6,6)),((4,6),(6,6)),((5,5),(5,5)),((5,5),(5,6)),((5,5),(6,6)),((5,6),(6,6))]
private theorem noProbe15 : group15.all noProbe=true := by decide
private def groups : List (List Gap) := [group00,group01,group02,group03,group04,group05,group06,group07,group08,group09,group10,group11,group12,group13,group14,group15]
set_option maxRecDepth 4096 in
private theorem unlistedComplete : unlistedGaps=groups.flatten := by decide
private theorem noProbes : groups.all (fun xs => xs.all noProbe)=true := by
  simp only [groups,List.all_cons,List.all_nil,noProbe00,noProbe01,noProbe02,noProbe03,noProbe04,noProbe05,noProbe06,noProbe07,noProbe08,noProbe09,noProbe10,noProbe11,noProbe12,noProbe13,noProbe14,noProbe15]
  rfl

theorem unlistedNoProbe (m : Gap) (hm : m∈unlistedGaps) : exceptional m=false ∧
    ∀ w (u y : Bool), subtractCost2 m u y w=0 := by
  rw [unlistedComplete] at hm
  obtain ⟨xs,hs,hm⟩ := List.mem_flatten.mp hm
  have fact := List.all_eq_true.mp (List.all_eq_true.mp noProbes xs hs) m hm
  unfold noProbe at fact
  simp only [Bool.and_eq_true_iff,Bool.not_eq_true',beq_iff_eq] at fact
  obtain ⟨⟨⟨⟨regular,c02⟩,c01⟩,c11⟩,c12⟩ := fact
  refine ⟨regular,?_⟩; intro w u y
  have not0256 : m≠((0,2),(5,6)) := by rintro rfl; contradiction
  have kg : (2 : Fin 7)≤w.k := by have := w.ij; have := w.jk; omega
  have mg : (3 : Fin 7)≤w.m := by have := w.ij; have := w.jk; have := w.km; omega
  let p := occupied w 0 && occupied w 1
  let q := occupied w 0 && occupied w 2
  let t := if p then (1 : Fin 7) else w.k
  have tg : (1 : Fin 7)≤t := by unfold t; split <;> omega
  have z02 (i : Fin 7) (hi : 1≤i) : probeCount m 0 2 i w.m=0 := by
    have le := probeMonotone m 0 2 1 3 i w.m hi mg; omega
  have z (g h : Fin 7) (e : probeCount m g h 2 3=0) : probeCount m g h w.k w.m=0 := by
    have le := probeMonotone m g h 2 3 w.k w.m kg mg; omega
  change u.toNat*(p.toNat*probeCount m 0 2 w.k w.m+q.toNat*probeCount m 0 2 t w.m)+
    y.toNat*(p.toNat*(probeCount m 0 1 w.k w.m+probeCount m 1 1 w.k w.m+probeCount m 1 2 w.k w.m))+
    (if m=((0,2),(5,6)) then _ else 0)=0
  simp [not0256,z02 w.k (by omega),z02 t tg,z _ _ c01,z _ _ c11,z _ _ c12]


def sharedProbe (m : Gap) (w : Wedge7) : Nat :=
  let p := occupied w 0 && occupied w 1
  let q := occupied w 0 && occupied w 2
  p.toNat*probeCount m 0 2 w.k w.m + q.toNat*probeCount m 0 2 (if p then 1 else w.k) w.m

def highestProbe (m : Gap) (w : Wedge7) : Nat :=
  (occupied w 0 && occupied w 1).toNat*
    (probeCount m 0 1 w.k w.m+probeCount m 1 1 w.k w.m+probeCount m 1 2 w.k w.m)

def restoration (m : Gap) (w : Wedge7) : Nat :=
  if m=((0,2),(5,6)) then (occupied w 0 && occupied w 1).toNat+(occupied w 0 && occupied w 2).toNat else 0

private theorem subtractProbes (m : Gap) (u y : Bool) (w : Wedge7) : subtractCost2 m u y w=
    u.toNat*sharedProbe m w+y.toNat*highestProbe m w+(2-u.toNat)*restoration m w := by
  unfold subtractCost2 sharedProbe highestProbe restoration; split <;> simp

variable {R : Type} [CommRing R]

def referenceWeight (w : Wedge7) : R := if SectorDefectAccounting.planeFlag w then 1 else 0

def evaluate (x c : Wedge7 → R) := sumOver wedges fun w => c w*x w

def gain (x c : Wedge7 → R) := evaluate x c-evaluate referenceWeight c

/-- The actual two-probe column cost, with z and y in physical price units. -/
def probeCost (m : Gap) (z y : R) (w : Wedge7) : R :=
  Nat.cast (forwardCost m w)-z*Nat.cast (sharedProbe m w)-y*Nat.cast (highestProbe m w)-
    (1-z)*Nat.cast (restoration m w)

private theorem referenceEval (c : Wedge7 → Nat) :
    evaluate referenceWeight (fun w => (Nat.cast (c w):R))=Nat.cast (referenceCost c) := by
  unfold evaluate referenceCost
  suffices all : ∀ xs : List Wedge7, sumOver xs (fun w => (Nat.cast (c w):R)*referenceWeight w)=
      Nat.cast (xs.map (fun w => if SectorDefectAccounting.planeFlag w then c w else 0)).sum by exact all wedges
  intro xs; induction xs with
  | nil => exact (Semiring.natCast_zero).symm
  | cons w ws ih =>
    change Nat.cast (c w)*referenceWeight w+sumOver ws _=Nat.cast ((if SectorDefectAccounting.planeFlag w then c w else 0)+(ws.map (fun t => if SectorDefectAccounting.planeFlag t then c t else 0)).sum)
    rw [ih,Semiring.natCast_add]; unfold referenceWeight; cases SectorDefectAccounting.planeFlag w <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Semiring.natCast_zero] <;> grind

private theorem scaleEval (x f : Wedge7 → R) (k : R) : evaluate x (fun w => k*f w)=k*evaluate x f := by
  unfold evaluate; rw [sumOverMulLeft]; apply sumOverCongr; intro w; grind

private theorem addEval (x f g : Wedge7 → R) : evaluate x (fun w => f w+g w)=evaluate x f+evaluate x g := by
  unfold evaluate; rw [←sumOverAdd]; apply sumOverCongr; intro w; grind

private theorem scaleGain (x f : Wedge7 → R) (k : R) : gain x (fun w => k*f w)=k*gain x f := by
  unfold gain; rw [scaleEval,scaleEval]; grind

private theorem addGain (x f g : Wedge7 → R) : gain x (fun w => f w+g w)=gain x f+gain x g := by
  unfold gain; rw [addEval,addEval]; grind

def blend (s t p q r v : R) := (1-s)*(1-t)*p+(1-s)*t*q+s*(1-t)*r+s*t*v

private theorem blendGain (x p q r v : Wedge7 → R) (s t : R) :
    gain x (fun w => blend s t (p w) (q w) (r w) (v w))=blend s t (gain x p) (gain x q) (gain x r) (gain x v) := by
  unfold blend; simp only [addGain,scaleGain]

private theorem cornerCast (m : Gap) (u y : Bool) (w : Wedge7) (exactCost : subtractCost2 m u y w≤2*forwardCost m w) :
    (Nat.cast (cornerCost2 m u y w):R)=2*Nat.cast (forwardCost m w)-Nat.cast u.toNat*Nat.cast (sharedProbe m w)-
      Nat.cast y.toNat*Nat.cast (highestProbe m w)-(2-Nat.cast u.toNat)*Nat.cast (restoration m w) := by
  have h : cornerCost2 m u y w+subtractCost2 m u y w=2*forwardCost m w := Nat.sub_add_cancel exactCost
  rw [subtractProbes] at h
  have cast := congrArg (fun a : Nat => (Nat.cast a:R)) h
  simp only [Semiring.natCast_add,Semiring.natCast_mul] at cast
  cases u <;> cases y <;> simp only [Bool.toNat] at cast ⊢ <;>
    grind

theorem physicalCornerInterpolation (m : Gap) (z y : R) (w : Wedge7)
    (faithful : ∀ a b, subtractCost2 m a b w≤2*forwardCost m w) :
    2*probeCost m z y w =
      blend (2*z) (2*y) (Nat.cast (cornerCost2 m false false w)) (Nat.cast (cornerCost2 m false true w))
        (Nat.cast (cornerCost2 m true false w)) (Nat.cast (cornerCost2 m true true w)) := by
  rw [cornerCast m false false w (faithful _ _),cornerCast m false true w (faithful _ _),
    cornerCast m true false w (faithful _ _),cornerCast m true true w (faithful _ _)]
  unfold probeCost blend; simp only [Bool.toNat]; grind

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem natGain (x : Wedge7 → R) (c : Wedge7 → Nat) (h : score x c≤Nat.cast (referenceCost c)) :
    gain x (fun w => Nat.cast (c w))≤0 := by
  unfold gain; rw [referenceEval]; change score x c-Nat.cast (referenceCost c)≤0; grind

private theorem restoredCorner (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (m : Gap) (ht : m∈restoredGaps) (a b : Bool) :
    (∀ w, subtractCost2 m a b w≤2*forwardCost m w) ∧ gain x (fun w => Nat.cast (cornerCost2 m a b w))≤0 := by
  by_cases hm : m∈adjustedGaps
  · obtain ⟨f,g⟩ := weightedCornerBound x nx rows m hm a b
    exact ⟨f,natGain _ _ g⟩
  have h := unlistedNoProbe m ((unlistedGapMem m).mpr ⟨ht,hm⟩)
  have cert := ordinaryForwardBound x nx rows m ((restoredGapMem m).mp ht).1 h.1
  refine ⟨fun w => by rw [h.2]; exact Nat.zero_le _,?_⟩
  have unweighted := natGain x (forwardCost m) cert
  have eq : (fun w => (Nat.cast (cornerCost2 m a b w):R))=(fun w => 2*Nat.cast (forwardCost m w)) := by
    funext w; simp only [cornerCost2,h.2,Nat.sub_zero,Semiring.natCast_mul]; grind
  rw [eq,scaleGain]; grind

/-- All 175 restored quartic costs are paid throughout the continuous
two-probe square, including the signed 0256 shared-pair correction. -/
theorem restoredProbeGain (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (m : Gap) (sorted : sortedGap m) (restored : hasTail m=true) (z y : R)
    (z0 : 0≤z) (zHalf : 2*z≤1) (y0 : 0≤y) (yHalf : 2*y≤1) : gain x (probeCost m z y)≤0 := by
  have corners := restoredCorner x nx rows m ((restoredGapMem m).mpr ⟨sorted,restored⟩)
  let f (a b : Bool) (w : Wedge7) : R := Nat.cast (cornerCost2 m a b w)
  have weight : (fun w => 2*probeCost m z y w)=(fun w => blend (2*z) (2*y) (f false false w) (f false true w) (f true false w) (f true true w)) := by
    funext w; exact physicalCornerInterpolation m z y w (fun a b => (corners a b).1 w)
  have total := congrArg (gain x) weight
  rw [scaleGain,blendGain] at total
  have neg (a b : Bool) : gain x (f a b)≤0 := (corners a b).2
  have pay (u v h : R) (hu : 0≤u) (hv : 0≤v) (hh : h≤0) : u*v*h≤0 := by
    have q := OrderedRing.mul_le_mul_of_nonneg_left hh (OrderedRing.mul_nonneg hu hv); grind
  have c00 := pay _ _ _ (show 0≤1-2*z by grind) (show 0≤1-2*y by grind) (neg false false)
  have c01 := pay _ _ _ (show 0≤1-2*z by grind) (show 0≤2*y by grind) (neg false true)
  have c10 := pay _ _ _ (show 0≤2*z by grind) (show 0≤1-2*y by grind) (neg true false)
  have c11 := pay _ _ _ (show 0≤2*z by grind) (show 0≤2*y by grind) (neg true true)
  unfold blend at total; grind

def fullGaps : List Gap := (fourIndices (List.finRange 7)).filter fun m =>
  decide (m.1.1≤m.1.2 ∧ m.1.2≤m.2.1 ∧ m.2.1≤m.2.2)

def exceptionList : List Gap := [((0,1),(6,6)),((0,2),(5,6)),((0,2),(6,6)),((1,1),(6,6)),((1,2),(6,6))]

set_option maxRecDepth 4096 in
theorem fiveExceptions : fullGaps.filter exceptional=exceptionList := by decide

def pairColumn (i j : Fin 7) (w : Wedge7) : Nat := (occupied w i && occupied w j).toNat

def sharedColumn (w : Wedge7) := pairColumn 0 1 w+pairColumn 0 2 w

def usesShared (m : Gap) := m==((0,2),(5,6)) || m==((0,2),(6,6))

def debitColumn (m : Gap) (w : Wedge7) := if usesShared m then sharedColumn w else pairColumn 0 1 w

private def residualCost (m : Gap) (w : Wedge7) := forwardCost m w-debitColumn m w

private def residualPrices (m : Gap) : Prices :=
  if m=((0,2),(5,6)) then [(1,.directed 6 0),(1,.triple 0 1 2)]
  else if m=((1,2),(6,6)) then [(1,.omitPair 3 4),(1,.omitPair 3 5),(1,.omitPair 3 6),
    (1,.omitPair 4 5),(1,.omitPair 4 6),(1,.omitPair 5 6)]
  else []

private theorem residualCertificates : exceptionList.all (fun m =>
    let ps := residualPrices m
    ps.all (fun p => p.2.legal) &&
    wedges.all (fun w => decide (debitColumn m w≤forwardCost m w ∧ residualCost m w≤cover ps w)) &&
    decide (priceCap ps=referenceCost (residualCost m)))=true := by decide

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem gainZero (x : Wedge7 → R) : gain x (fun _ => 0)=0 := by
  have eq : (fun _ : Wedge7 => (0:R))=(fun _ => (0:R)*1) := by funext w; grind
  rw [eq,scaleGain]; grind

/-- The physical rows alone pay the residual of each exceptional column once
its signed L01 or L01+L02 contribution is retained explicitly. -/
theorem exceptionalDebit (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (m : Gap) (exc : exceptional m=true) :
    gain x (fun w => Nat.cast (forwardCost m w))≤gain x (fun w => Nat.cast (debitColumn m w)) := by
  have mem : m∈exceptionList := List.contains_iff_mem.mp exc
  have fact := List.all_eq_true.mp residualCertificates m mem
  obtain ⟨h,cap⟩ := Bool.and_eq_true_iff.mp fact
  obtain ⟨legal,coords⟩ := Bool.and_eq_true_iff.mp h
  have col (w : Wedge7) := _root_.of_decide_eq_true (List.all_eq_true.mp coords w (memWedges w))
  have res := weakDual x nx rows (residualCost m) (residualPrices m) (referenceCost (residualCost m))
    ⟨legal,List.all_eq_true.mpr (fun w _ => _root_.decide_eq_true (col w).2),Nat.le_of_eq (_root_.of_decide_eq_true cap)⟩
  have paid := natGain x _ res
  have split : (fun w => (Nat.cast (forwardCost m w):R))=(fun w => Nat.cast (residualCost m w)+Nat.cast (debitColumn m w)) := by
    funext w; rw [←Semiring.natCast_add]; exact congrArg Nat.cast (Nat.sub_add_cancel (col w).1).symm
  rw [split,addGain]; grind

def monomial (b : Fin 7 → R) (m : Gap) := b m.1.1*b m.1.2*b m.2.1*b m.2.2

private theorem monomialNonnegative (b : Fin 7 → R) (bn : ∀ j, 0≤b j) (m : Gap) : 0≤monomial b m :=
  OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (bn _) (bn _)) (bn _)) (bn _)

private theorem sumMonoMem {α : Type} (xs : List α) (f g : α → R) (le : ∀ a∈xs, f a≤g a) :
    sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons a xs ih =>
    change f a+sumOver xs f≤g a+sumOver xs g
    have h := le a List.mem_cons_self
    have t := ih (fun q hq => le q (List.mem_cons_of_mem _ hq))
    grind

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem filterSum {α : Type} (xs : List α) (p : α → Bool) (f : α → R) :
    sumOver (xs.filter p) f=sumOver xs (fun a => if p a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.filter_cons]; cases h : p a <;> simp [h,sumOver] at ih ⊢ <;> grind

/-- Summing the five signed exceptions with their nonnegative gap monomials
needs no extra fixed-pair capacity. The two factors multiply the actual
minus computational shared-pair mass and highest-pair mass respectively. -/
theorem signedForwardDebit (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (b : Fin 7 → R) (bn : ∀ j, 0≤b j) :
    sumOver fullGaps (fun m => monomial b m*gain x (fun w => Nat.cast (forwardCost m w)))≤
      (b 0*b 2*b 6*(b 5+b 6))*gain x (fun w => Nat.cast (sharedColumn w))+
      ((b 6)^2*b 1*(b 0+b 1+b 2))*gain x (fun w => Nat.cast (pairColumn 0 1 w)) := by
  let F (m : Gap) := monomial b m*gain x (fun w => Nat.cast (debitColumn m w))
  have eq : sumOver fullGaps (fun m => if exceptional m then F m else 0)=sumOver exceptionList F := by
    rw [←filterSum,fiveExceptions]
  have bound := sumMonoMem fullGaps (fun m => monomial b m*gain x (fun w => Nat.cast (forwardCost m w)))
    (fun m => if exceptional m then F m else 0) (by
      intro m hm
      have sorted := _root_.of_decide_eq_true (List.mem_filter.mp hm).2
      have pos := monomialNonnegative b bn m
      cases e : exceptional m
      · simp only [Bool.false_eq_true,ite_false]
        have le := natGain x _ (ordinaryForwardBound x nx rows m sorted e)
        have prod := OrderedRing.mul_le_mul_of_nonneg_left le pos
        grind
      · simp only [ite_true]; exact OrderedRing.mul_le_mul_of_nonneg_left (exceptionalDebit x nx rows m e) pos)
  rw [eq] at bound
  have eq2 : sumOver exceptionList F =
      (b 0*b 2*b 6*(b 5+b 6))*gain x (fun w => Nat.cast (sharedColumn w))+
      ((b 6)^2*b 1*(b 0+b 1+b 2))*gain x (fun w => Nat.cast (pairColumn 0 1 w)) := by
    let S := gain x (fun w => (Nat.cast (sharedColumn w):R))
    let V := gain x (fun w => (Nat.cast (pairColumn 0 1 w):R))
    change b 0*b 1*b 6*b 6*V+(b 0*b 2*b 5*b 6*S+(b 0*b 2*b 6*b 6*S+
      (b 1*b 1*b 6*b 6*V+(b 1*b 2*b 6*b 6*V+0))))= (b 0*b 2*b 6*(b 5+b 6))*S+((b 6)^2*b 1*(b 0+b 1+b 2))*V
    grind
  exact eq2 ▸ bound

theorem restoredProbeSum (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (b : Fin 7 → R) (bn : ∀ j, 0≤b j) (z y : R) (z0 : 0≤z) (zHalf : 2*z≤1) (y0 : 0≤y) (yHalf : 2*y≤1) :
    sumOver restoredGaps (fun m => monomial b m*gain x (probeCost m z y))≤0 := by
  have zeros (xs : List Gap) : sumOver xs (fun _ => (0:R))=0 := by
    induction xs with | nil => rfl | cons a xs ih => change 0+sumOver xs (fun _ => (0:R))=0; rw [ih]; grind
  rw [←zeros restoredGaps]; apply sumMonoMem; intro m hm
  obtain ⟨sorted,tag⟩ := (restoredGapMem m).mp hm
  have le := restoredProbeGain x nx rows m sorted tag z y z0 zHalf y0 yHalf
  have prod := OrderedRing.mul_le_mul_of_nonneg_left le (monomialNonnegative b bn m)
  grind
end RankSeven.PackingInterpolation

#print axioms RankSeven.PackingInterpolation.unlistedNoProbe
#print axioms RankSeven.PackingInterpolation.restoredProbeGain
#print axioms RankSeven.PackingInterpolation.restoredProbeSum
#print axioms RankSeven.PackingInterpolation.exceptionalDebit
#print axioms RankSeven.PackingInterpolation.signedForwardDebit
