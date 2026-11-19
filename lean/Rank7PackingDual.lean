import Rank7ExteriorCuts
import Rank7SectorDefectAccounting

/-! Integer-cleared LP dual certificates for rank-seven wedge packing.
Rows refer to actual four-label wedge coordinates. -/
namespace RankSeven.PackingDual

open Lean.Grind Pauli ExteriorCuts
attribute [local instance] Semiring.natCast

def occupied (w : Wedge7) (i : Fin 7) : Bool :=
  w.i==i || w.j==i || w.k==i || w.m==i

inductive Row
  | directed (ignored fixed : Fin 7)
  | triple (a b c : Fin 7)
  | omitPair (a b : Fin 7)
  deriving DecidableEq, Repr

def Row.legal : Row → Bool
  | .directed i j => i != j
  | .triple i j k => decide (i<j ∧ j<k)
  | .omitPair i j => decide (i<j)

def Row.covers (row : Row) (w : Wedge7) : Bool :=
  match row with
  | .directed i j => !occupied w i && occupied w j
  | .triple i j k => occupied w i && occupied w j && occupied w k
  | .omitPair i j => !occupied w i && !occupied w j

def Row.cap : Row → Nat | .directed .. => 2 | _ => 1

abbrev Prices := List (Nat × Row)

def cover : Prices → Wedge7 → Nat
  | [],_ => 0
  | (p,r)::ps,w => (if r.covers w then p else 0)+cover ps w

def priceCap : Prices → Nat
  | [] => 0
  | (p,r)::ps => p*r.cap+priceCap ps

variable {R : Type} [CommRing R]

def score (x : Wedge7 → R) (c : Wedge7 → Nat) : R := sumOver wedges fun w => Nat.cast (c w)*x w

def rowMass (x : Wedge7 → R) (r : Row) := sumOver wedges fun w => if r.covers w then x w else 0

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def RowsHold (x : Wedge7 → R) : Prop := ∀ r : Row, r.legal=true → rowMass x r≤Nat.cast r.cap

private theorem natMono {a b : Nat} (h : a≤b) : (Nat.cast a:R)≤Nat.cast b := by
  have split := Nat.add_sub_of_le h
  have pos : (0:R)≤Nat.cast (b-a) := OrderedRing.natCast_nonneg
  conv => rhs; rw [←split,Semiring.natCast_add]
  grind

private theorem sumMono {α : Type} (xs : List α) (f g : α → R) (h : ∀ i∈xs, f i≤g i) : sumOver xs f≤sumOver xs g := by
  induction xs with
  | nil => exact Std.le_refl _
  | cons x xs ih =>
    change f x+sumOver xs f ≤ g x+sumOver xs g
    have a := h x List.mem_cons_self
    have b := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    grind

private theorem rowsPrice (x : Wedge7 → R) (rows : RowsHold x) (ps : Prices) (legal : ps.all (fun pr => pr.2.legal)=true) :
    score x (cover ps)≤Nat.cast (priceCap ps) := by
  induction ps with
  | nil =>
    unfold score; have zeros (ws : List Wedge7) : sumOver ws (fun w => Nat.cast (cover [] w)*x w)=0 := by
      induction ws with | nil => rfl | cons y ys ih => change (Nat.cast 0:R)*x y+sumOver ys (fun w => Nat.cast (cover [] w)*x w)=0; rw [ih,Semiring.natCast_zero]; grind
    rw [zeros]; exact OrderedRing.natCast_nonneg
  | cons pr ps ih =>
    obtain ⟨p,r⟩ := pr
    have lh := Bool.and_eq_true_iff.mp legal
    have next := ih lh.2
    have row := OrderedRing.mul_le_mul_of_nonneg_left (rows r lh.1) (show (0:R)≤Nat.cast p from OrderedRing.natCast_nonneg)
    have eq : score x (cover ((p,r)::ps))=Nat.cast p*rowMass x r+score x (cover ps) := by
      unfold score rowMass; rw [sumOverMulLeft,←sumOverAdd]; apply sumOverCongr; intro w
      change Nat.cast ((if r.covers w then p else 0)+cover ps w)*x w=Nat.cast p*(if r.covers w then x w else 0)+Nat.cast (cover ps w)*x w
      rw [Semiring.natCast_add]; cases r.covers w <;> simp only [Bool.false_eq_true,ite_false,ite_true,Semiring.natCast_zero] <;> grind
    rw [eq,priceCap,Semiring.natCast_add,Semiring.natCast_mul]; grind

/-- A sparse dual yields an inequality for every nonnegative physical-coordinate
vector satisfying the listed row capacities. Prices and costs are integer-cleared. -/
theorem weakDual (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x) (c : Wedge7 → Nat) (ps : Prices)
    (bound : Nat) (certificate : ps.all (fun pr => pr.2.legal)=true ∧
      wedges.all (fun w => decide (c w≤cover ps w))=true ∧ priceCap ps≤bound) :
    score x c≤Nat.cast bound := by
  have point := sumMono wedges (fun w => Nat.cast (c w)*x w) (fun w => Nat.cast (cover ps w)*x w)
    (fun w hw => OrderedRing.mul_le_mul_of_nonneg_right (natMono (_root_.of_decide_eq_true (List.all_eq_true.mp certificate.2.1 w hw))) (nx w))
  exact Std.le_trans point (Std.le_trans (rowsPrice x rows ps certificate.1) (natMono certificate.2.2))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem scaleScore (x : Wedge7 → R) (m : Nat) (c : Wedge7 → Nat) :
    score x (fun w => m*c w)=Nat.cast m*score x c := by
  unfold score; rw [sumOverMulLeft]; apply sumOverCongr; intro w; rw [Semiring.natCast_mul,Semiring.mul_assoc]

inductive Block
  | T1_zero | T1_shared | T1_highest | T2_zero | T2_shared | T2_highest | T3_zero | T3_shared | T3_highest
  | TH_cross | N_zero | N_shared | N_highest | N_cross | head_pairs | two_shared_plus_x
  deriving DecidableEq, Repr

/-- Twice each raw (possibly half-integral) geometric cost. -/
def blockCost2 (block : Block) (w : Wedge7) : Nat :=
  let p := (occupied w 0).toNat
  let q := (occupied w 1).toNat
  let r := (occupied w 2).toNat
  let v := p*q
  let s := v+p*r
  let a := v*r
  match block with
  | .T1_zero => 2*p
  | .T1_shared => 2*(p+s)
  | .T1_highest => 2*p+v
  | .T2_zero => 2*(p+q)
  | .T2_shared => 2*(p+q+2*s)
  | .T2_highest => 2*(p+q+v)
  | .T3_zero => 2*(p+q+r)
  | .T3_shared => 2*(p+q+r+3*s)
  | .T3_highest => 2*(p+q+r)+3*v
  | .TH_cross => 2*(p+q+r+2*s+v+a)
  | .N_zero => 2
  | .N_shared => 2+5*s
  | .N_highest => 2*(1+2*v)
  | .N_cross => 2*(1+2*s+v)
  | .head_pairs => 2*(s+q*r)
  | .two_shared_plus_x => 2*(2*s-a)

def blockUpper : Block → Nat
  | .T1_zero => 4
  | .T1_shared => 8
  | .T1_highest => 5
  | .T2_zero => 8
  | .T2_shared => 16
  | .T2_highest => 10
  | .T3_zero => 12
  | .T3_shared => 24
  | .T3_highest => 15
  | .TH_cross => 23
  | .N_zero => 7
  | .N_shared => 17
  | .N_highest => 11
  | .N_cross => 17
  | .head_pairs => 6
  | .two_shared_plus_x => 8

/-- Sparse input duals with common denominator 18. -/
def blockPrices : Block → Prices
  | .T1_zero => [(6,.directed 1 0),(6,.directed 2 0),(6,.directed 3 0),(6,.directed 4 0),(6,.directed 5 0),(6,.directed 6 0)]
  | .T1_shared => [(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0)]
  | .T1_highest => [(9,.directed 2 0),(9,.directed 3 0),(9,.directed 4 0),(9,.directed 5 0),(9,.directed 6 0)]
  | .T2_zero => [(12,.directed 0 1),(9,.directed 2 0),(3,.directed 2 1),(9,.directed 3 0),(3,.directed 3 1),(9,.directed 4 0),(3,.directed 4 1),(9,.directed 5 0),(3,.directed 5 1),(9,.directed 6 0),(3,.directed 6 1)]
  | .T2_shared => [(18,.directed 2 1),(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0),(18,.omitPair 3 4),(18,.omitPair 3 5),(18,.omitPair 3 6),(18,.omitPair 4 5),(18,.omitPair 4 6),(18,.omitPair 5 6)]
  | .T2_highest => [(9,.directed 2 0),(9,.directed 2 1),(9,.directed 3 0),(9,.directed 3 1),(9,.directed 4 0),(9,.directed 4 1),(9,.directed 5 0),(9,.directed 5 1),(9,.directed 6 0),(9,.directed 6 1)]
  | .T3_zero => [(18,.directed 2 0),(18,.directed 2 1),(18,.directed 3 2),(18,.directed 4 2),(18,.directed 5 2),(18,.directed 6 2)]
  | .T3_shared => [(18,.directed 1 2),(18,.directed 2 1),(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0),(36,.omitPair 3 4),(36,.omitPair 3 5),(36,.omitPair 3 6),(36,.omitPair 4 5),(36,.omitPair 4 6),(36,.omitPair 5 6)]
  | .T3_highest => [(18,.directed 0 2),(9,.directed 2 1),(18,.directed 3 0),(9,.directed 3 1),(18,.directed 4 0),(9,.directed 4 1),(18,.directed 5 0),(9,.directed 5 1),(18,.directed 6 0),(9,.directed 6 1)]
  | .TH_cross => [(18,.directed 2 1),(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0),(18,.omitPair 0 1),(36,.omitPair 3 4),(36,.omitPair 3 5),(36,.omitPair 3 6),(36,.omitPair 4 5),(36,.omitPair 4 6),(36,.omitPair 5 6)]
  | .N_zero => [(10,.directed 0 1),(4,.directed 0 3),(6,.directed 1 2),(4,.directed 1 4),(4,.directed 1 5),(4,.directed 1 6),(4,.directed 2 0),(2,.directed 2 3),(6,.directed 3 1),(4,.directed 4 0),(2,.directed 4 1),(4,.directed 5 0),(2,.directed 5 1),(4,.directed 6 0),(2,.directed 6 1),(2,.omitPair 2 3)]
  | .N_shared => [(9,.directed 1 2),(9,.directed 2 1),(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0),(9,.omitPair 0 1),(9,.omitPair 0 2),(18,.omitPair 3 4),(18,.omitPair 3 5),(18,.omitPair 3 6),(18,.omitPair 4 5),(18,.omitPair 4 6),(18,.omitPair 5 6)]
  | .N_highest => [(9,.directed 3 0),(9,.directed 3 1),(9,.directed 4 0),(9,.directed 4 1),(9,.directed 5 0),(9,.directed 5 1),(18,.omitPair 0 1),(9,.omitPair 2 3),(9,.omitPair 2 4),(9,.omitPair 2 5),(18,.omitPair 2 6),(9,.omitPair 3 6),(9,.omitPair 4 6),(9,.omitPair 5 6)]
  | .N_cross => [(18,.directed 2 1),(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0),(18,.omitPair 0 1),(18,.omitPair 3 4),(18,.omitPair 3 5),(18,.omitPair 3 6),(18,.omitPair 4 5),(18,.omitPair 4 6),(18,.omitPair 5 6)]
  | .head_pairs => [(18,.omitPair 3 4),(18,.omitPair 3 5),(18,.omitPair 3 6),(18,.omitPair 4 5),(18,.omitPair 4 6),(18,.omitPair 5 6)]
  | .two_shared_plus_x => [(18,.directed 3 0),(18,.directed 4 0),(18,.directed 5 0),(18,.directed 6 0)]

theorem blockCertificate (b : Block) :
    (blockPrices b).all (fun pr => pr.2.legal)=true ∧
    wedges.all (fun w => decide (9*blockCost2 b w≤cover (blockPrices b) w))=true ∧
    priceCap (blockPrices b)=18*blockUpper b := by cases b <;> decide

theorem uniformBlockBound (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x) (b : Block) :
    score x (blockCost2 b)≤2*Nat.cast (blockUpper b) := by
  have cert := blockCertificate b
  have raw := weakDual x nx rows (fun w => 9*blockCost2 b w) (blockPrices b) (18*blockUpper b)
    ⟨cert.1,cert.2.1,Nat.le_of_eq cert.2.2⟩
  rw [scaleScore,Semiring.natCast_mul] at raw
  simp only [show (Nat.cast 9:R)=9 from by grind,show (Nat.cast 18:R)=18 from by grind] at raw
  grind


abbrev Gap := Four (Fin 7)

/-- Distinct assignments of the four gap indices to the ordered wedge slots.
Equal indices contribute once to each assignment. -/
def assignments (m : Gap) : List Gap :=
  (ExteriorPauliBase.permutations.map (GenericExteriorKernel.reorder m)).eraseDups

def forwardCost (m : Gap) (w : Wedge7) : Nat :=
  (assignments m).countP fun z =>
    decide (w.i≤z.1.1 ∧ w.j≤z.1.2 ∧ w.k≤z.2.1 ∧ w.m≤z.2.2)

/-- Coefficient of the two anchored probes after fixing their first
two gap factors. The last two slots are the two remaining wedge labels. -/
def probeCount (m : Gap) (g h i j : Fin 7) : Nat :=
  (assignments m).countP fun z => decide (z.1.1=g ∧ z.1.2=h ∧ i≤z.2.1 ∧ j≤z.2.2)

def subtractCost2 (m : Gap) (u y : Bool) (w : Wedge7) : Nat :=
  let p := occupied w 0 && occupied w 1
  let q := occupied w 0 && occupied w 2
  let t := if p then (1 : Fin 7) else w.k
  let cu := p.toNat * probeCount m 0 2 w.k w.m + q.toNat * probeCount m 0 2 t w.m
  let cy := p.toNat * (probeCount m 0 1 w.k w.m + probeCount m 1 1 w.k w.m + probeCount m 1 2 w.k w.m)
  let correction := if m=((0,2),(5,6)) then (2-u.toNat)*(p.toNat+q.toNat) else 0
  u.toNat*cu+y.toNat*cy+correction

def cornerCost2 (m : Gap) (u y : Bool) (w : Wedge7) : Nat := 2*forwardCost m w-subtractCost2 m u y w

def referenceCost (c : Wedge7 → Nat) : Nat :=
  (wedges.map fun w => if SectorDefectAccounting.planeFlag w then c w else 0).sum

def key (m : Gap) := ((m.1.1.val*7+m.1.2.val)*7+m.2.1.val)*7+m.2.2.val

private def gaps : List Gap := (fourIndices (List.finRange 7)).filter fun m => decide (m.1.1≤m.1.2 ∧ m.1.2≤m.2.1 ∧ m.2.1≤m.2.2)

def sortedGap (m : Gap) := m.1.1≤m.1.2 ∧ m.1.2≤m.2.1 ∧ m.2.1≤m.2.2

private theorem gapMem (m : Gap) (h : sortedGap m) : m∈gaps := by
  have full (a : Fin 7) := List.mem_finRange a
  have all : m∈fourIndices (List.finRange 7) := HyperplaneInduction.pairMember
    (HyperplaneInduction.pairMember (full _) (full _)) (HyperplaneInduction.pairMember (full _) (full _))
  exact List.mem_filter.mpr ⟨all, _root_.decide_eq_true h⟩

def exceptional (m : Gap) : Bool := [((0,1),(6,6)),((0,2),(5,6)),((0,2),(6,6)),((1,1),(6,6)),((1,2),(6,6))].contains m

private def dualOK (den : Nat) (c : Wedge7 → Nat) (ps : Prices) : Bool :=
  ps.all (fun t => t.2.legal) && wedges.all (fun w => decide (den*c w≤cover ps w)) && decide (priceCap ps=den*referenceCost c)

private def asRow : Nat → Row
  | 0 => .directed 0 1
  | 1 => .directed 0 2
  | 2 => .directed 0 3
  | 3 => .directed 0 4
  | 4 => .directed 0 5
  | 5 => .directed 0 6
  | 6 => .directed 1 0
  | 7 => .directed 1 2
  | 8 => .directed 1 3
  | 9 => .directed 1 4
  | 10 => .directed 1 5
  | 11 => .directed 1 6
  | 12 => .directed 2 0
  | 13 => .directed 2 1
  | 14 => .directed 2 3
  | 15 => .directed 2 4
  | 16 => .directed 2 5
  | 17 => .directed 2 6
  | 18 => .directed 3 0
  | 19 => .directed 3 1
  | 20 => .directed 3 2
  | 21 => .directed 3 4
  | 22 => .directed 3 5
  | 23 => .directed 3 6
  | 24 => .directed 4 0
  | 25 => .directed 4 1
  | 26 => .directed 4 2
  | 27 => .directed 4 3
  | 28 => .directed 4 5
  | 29 => .directed 4 6
  | 30 => .directed 5 0
  | 31 => .directed 5 1
  | 32 => .directed 5 2
  | 33 => .directed 5 3
  | 34 => .directed 5 4
  | 35 => .directed 5 6
  | 36 => .directed 6 0
  | 37 => .directed 6 1
  | 38 => .directed 6 2
  | 39 => .directed 6 3
  | 40 => .directed 6 4
  | 41 => .directed 6 5
  | 42 => .triple 4 5 6
  | 43 => .triple 3 5 6
  | 44 => .triple 3 4 6
  | 45 => .triple 3 4 5
  | 46 => .triple 2 5 6
  | 47 => .triple 2 4 6
  | 48 => .triple 2 4 5
  | 49 => .triple 2 3 6
  | 50 => .triple 2 3 5
  | 51 => .triple 2 3 4
  | 52 => .triple 1 5 6
  | 53 => .triple 1 4 6
  | 54 => .triple 1 4 5
  | 55 => .triple 1 3 6
  | 56 => .triple 1 3 5
  | 57 => .triple 1 3 4
  | 58 => .triple 1 2 6
  | 59 => .triple 1 2 5
  | 60 => .triple 1 2 4
  | 61 => .triple 1 2 3
  | 62 => .triple 0 5 6
  | 63 => .triple 0 4 6
  | 64 => .triple 0 4 5
  | 65 => .triple 0 3 6
  | 66 => .triple 0 3 5
  | 67 => .triple 0 3 4
  | 68 => .triple 0 2 6
  | 69 => .triple 0 2 5
  | 70 => .triple 0 2 4
  | 71 => .triple 0 2 3
  | 72 => .triple 0 1 6
  | 73 => .triple 0 1 5
  | 74 => .triple 0 1 4
  | 75 => .triple 0 1 3
  | 76 => .triple 0 1 2
  | 77 => .omitPair 0 1
  | 78 => .omitPair 0 2
  | 79 => .omitPair 0 3
  | 80 => .omitPair 0 4
  | 81 => .omitPair 0 5
  | 82 => .omitPair 0 6
  | 83 => .omitPair 1 2
  | 84 => .omitPair 1 3
  | 85 => .omitPair 1 4
  | 86 => .omitPair 1 5
  | 87 => .omitPair 1 6
  | 88 => .omitPair 2 3
  | 89 => .omitPair 2 4
  | 90 => .omitPair 2 5
  | 91 => .omitPair 2 6
  | 92 => .omitPair 3 4
  | 93 => .omitPair 3 5
  | 94 => .omitPair 3 6
  | 95 => .omitPair 4 5
  | 96 => .omitPair 4 6
  | 97 => .omitPair 5 6
  | _ => .directed 0 0

private def ordinaryPrices : Nat → Nat × Prices
  | 0 => (1,[])
  | 1 => (1,[])
  | 2 => (1,[])
  | 3 => (1,[])
  | 4 => (1,[])
  | 5 => (1,[])
  | 6 => (1,[])
  | 8 => (1,[])
  | 9 => (1,[])
  | 10 => (1,[])
  | 11 => (1,[])
  | 12 => (1,[])
  | 13 => (1,[])
  | 16 => (1,[])
  | 17 => (1,[])
  | 18 => (1,[])
  | 19 => (1,[])
  | 20 => (1,[])
  | 24 => (1,[])
  | 25 => (1,[])
  | 26 => (1,[])
  | 27 => (1,[])
  | 32 => (1,[])
  | 33 => (1,[])
  | 34 => (1,[])
  | 40 => (1,[])
  | 41 => (1,[])
  | 48 => (1,[])
  | 57 => (1,[])
  | 58 => (1,[])
  | 59 => (1,[])
  | 60 => (1,[])
  | 61 => (1,[])
  | 62 => (1,[])
  | 65 => (1,[])
  | 66 => (1,[(1,asRow 61)])
  | 67 => (1,[(1,asRow 97)])
  | 68 => (1,[(1,asRow 76)])
  | 69 => (1,[(1,asRow 76)])
  | 73 => (1,[(1,asRow 61)])
  | 74 => (1,[(1,asRow 61),(1,asRow 97)])
  | 75 => (1,[(1,asRow 96),(1,asRow 97)])
  | 76 => (1,[(1,asRow 75),(1,asRow 76)])
  | 81 => (1,[(1,asRow 97)])
  | 82 => (1,[(1,asRow 36),(1,asRow 97)])
  | 83 => (1,[(1,asRow 74),(1,asRow 75),(1,asRow 76)])
  | 89 => (1,[(1,asRow 36)])
  | 90 => (1,[(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)])
  | 114 => (1,[])
  | 115 => (1,[(1,asRow 61)])
  | 116 => (1,[(1,asRow 97)])
  | 117 => (1,[(1,asRow 76)])
  | 118 => (1,[(1,asRow 76)])
  | 122 => (1,[(2,asRow 61)])
  | 123 => (1,[(2,asRow 61),(2,asRow 97)])
  | 124 => (1,[(1,asRow 61),(1,asRow 76),(1,asRow 96),(1,asRow 97)])
  | 125 => (1,[(1,asRow 76),(1,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 130 => (1,[(2,asRow 97)])
  | 131 => (1,[(1,asRow 36),(2,asRow 76),(1,asRow 97)])
  | 132 => (1,[(1,asRow 30),(1,asRow 36),(2,asRow 76)])
  | 138 => (1,[(1,asRow 36),(1,asRow 76)])
  | 171 => (1,[(1,asRow 61)])
  | 172 => (1,[(2,asRow 61),(1,asRow 97)])
  | 173 => (1,[(1,asRow 61),(1,asRow 96),(1,asRow 97)])
  | 174 => (1,[(1,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 179 => (1,[(1,asRow 61),(2,asRow 97)])
  | 180 => (1,[(1,asRow 36),(1,asRow 61),(1,asRow 96),(3,asRow 97)])
  | 181 => (1,[(1,asRow 30),(1,asRow 36),(1,asRow 71),(1,asRow 75),(1,asRow 76),(1,asRow 97)])
  | 187 => (1,[(1,asRow 36),(1,asRow 96),(1,asRow 97)])
  | 188 => (1,[(1,asRow 24),(1,asRow 30),(2,asRow 36),(1,asRow 96),(1,asRow 97)])
  | 195 => (1,[(1,asRow 24),(1,asRow 30),(1,asRow 36)])
  | 228 => (1,[(1,asRow 97)])
  | 229 => (1,[(1,asRow 36),(2,asRow 97)])
  | 230 => (1,[(1,asRow 30),(1,asRow 36),(1,asRow 97)])
  | 236 => (1,[(2,asRow 36),(1,asRow 97)])
  | 237 => (3,[(1,asRow 6),(1,asRow 12),(1,asRow 18),(1,asRow 24),(4,asRow 30),(10,asRow 36),(3,asRow 97)])
  | 244 => (3,[(1,asRow 6),(1,asRow 12),(1,asRow 18),(1,asRow 24),(4,asRow 30),(4,asRow 36)])
  | 285 => (1,[(1,asRow 36)])
  | 286 => (3,[(1,asRow 6),(1,asRow 12),(1,asRow 18),(1,asRow 24),(1,asRow 30),(7,asRow 36)])
  | 293 => (3,[(2,asRow 6),(2,asRow 12),(2,asRow 18),(2,asRow 24),(2,asRow 30),(5,asRow 36)])
  | 342 => (3,[(1,asRow 6),(1,asRow 12),(1,asRow 18),(1,asRow 24),(1,asRow 30),(1,asRow 36)])
  | 400 => (1,[])
  | 401 => (1,[])
  | 402 => (1,[])
  | 403 => (1,[])
  | 404 => (1,[])
  | 405 => (1,[])
  | 408 => (1,[])
  | 409 => (1,[(1,asRow 61)])
  | 410 => (1,[(1,asRow 97)])
  | 411 => (1,[(1,asRow 76)])
  | 412 => (1,[(1,asRow 76)])
  | 416 => (1,[(1,asRow 61)])
  | 417 => (1,[(1,asRow 61),(1,asRow 97)])
  | 418 => (1,[(1,asRow 96),(1,asRow 97)])
  | 419 => (1,[(1,asRow 75),(1,asRow 76)])
  | 424 => (1,[(1,asRow 97)])
  | 425 => (1,[(1,asRow 36),(1,asRow 97)])
  | 426 => (1,[(1,asRow 74),(1,asRow 75),(1,asRow 76)])
  | 432 => (1,[(1,asRow 36)])
  | 433 => (1,[(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)])
  | 457 => (1,[])
  | 458 => (1,[(2,asRow 61)])
  | 459 => (1,[(2,asRow 97)])
  | 460 => (1,[(2,asRow 76)])
  | 461 => (1,[(2,asRow 76)])
  | 465 => (1,[(4,asRow 61)])
  | 466 => (1,[(4,asRow 95),(4,asRow 97)])
  | 467 => (1,[(1,asRow 75),(3,asRow 76),(2,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 468 => (1,[(1,asRow 75),(3,asRow 76),(1,asRow 95),(1,asRow 96),(2,asRow 97)])
  | 473 => (1,[(4,asRow 97)])
  | 474 => (1,[(1,asRow 36),(1,asRow 37),(2,asRow 76),(4,asRow 97)])
  | 475 => (1,[(1,asRow 74),(1,asRow 75),(3,asRow 76),(1,asRow 93),(1,asRow 94),(1,asRow 95),(1,asRow 96),(2,asRow 97)])
  | 481 => (1,[(1,asRow 36),(1,asRow 37),(2,asRow 76)])
  | 482 => (1,[(1,asRow 73),(1,asRow 74),(1,asRow 75),(2,asRow 76),(1,asRow 92),(1,asRow 93),(2,asRow 94),(1,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 514 => (1,[(2,asRow 61)])
  | 515 => (1,[(4,asRow 95),(2,asRow 97)])
  | 516 => (1,[(2,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 517 => (1,[(1,asRow 61),(1,asRow 75),(1,asRow 76),(1,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 522 => (1,[(2,asRow 95),(4,asRow 97)])
  | 523 => (1,[(1,asRow 36),(1,asRow 37),(2,asRow 95),(2,asRow 96),(6,asRow 97)])
  | 524 => (1,[(1,asRow 30),(1,asRow 31),(1,asRow 36),(1,asRow 37),(1,asRow 75),(1,asRow 76),(1,asRow 95),(2,asRow 96),(3,asRow 97)])
  | 530 => (1,[(1,asRow 36),(1,asRow 37),(2,asRow 96),(2,asRow 97)])
  | 531 => (1,[(1,asRow 24),(1,asRow 25),(1,asRow 30),(1,asRow 31),(2,asRow 36),(2,asRow 37),(1,asRow 75),(1,asRow 76),(1,asRow 96),(1,asRow 97)])
  | 538 => (1,[(1,asRow 24),(1,asRow 25),(1,asRow 36),(1,asRow 37),(1,asRow 90),(1,asRow 93),(1,asRow 95),(1,asRow 97)])
  | 571 => (1,[(2,asRow 97)])
  | 572 => (1,[(1,asRow 36),(1,asRow 37),(4,asRow 97)])
  | 573 => (1,[(1,asRow 30),(1,asRow 31),(1,asRow 36),(1,asRow 37),(2,asRow 97)])
  | 579 => (1,[(2,asRow 36),(2,asRow 37),(2,asRow 97)])
  | 580 => (2,[(1,asRow 6),(1,asRow 13),(1,asRow 19),(1,asRow 25),(3,asRow 30),(3,asRow 31),(7,asRow 36),(7,asRow 37),(1,asRow 62),(3,asRow 97)])
  | 587 => (6,[(4,asRow 0),(3,asRow 12),(1,asRow 13),(3,asRow 18),(1,asRow 19),(3,asRow 24),(1,asRow 25),(9,asRow 30),(7,asRow 31),(9,asRow 36),(7,asRow 37)])
  | 628 => (1,[(1,asRow 36),(1,asRow 37)])
  | 629 => (6,[(4,asRow 0),(3,asRow 12),(1,asRow 13),(3,asRow 18),(1,asRow 19),(3,asRow 24),(1,asRow 25),(3,asRow 30),(1,asRow 31),(15,asRow 36),(13,asRow 37)])
  | 636 => (3,[(4,asRow 0),(3,asRow 12),(1,asRow 13),(3,asRow 18),(1,asRow 19),(3,asRow 24),(1,asRow 25),(3,asRow 30),(1,asRow 31),(6,asRow 36),(4,asRow 37)])
  | 685 => (6,[(4,asRow 0),(3,asRow 12),(1,asRow 13),(3,asRow 18),(1,asRow 19),(3,asRow 24),(1,asRow 25),(3,asRow 30),(1,asRow 31),(3,asRow 36),(1,asRow 37)])
  | 800 => (1,[])
  | 801 => (1,[(1,asRow 61)])
  | 802 => (1,[(1,asRow 97)])
  | 803 => (1,[(1,asRow 76)])
  | 804 => (1,[(1,asRow 76)])
  | 808 => (1,[(3,asRow 61)])
  | 809 => (1,[(3,asRow 95),(3,asRow 97)])
  | 810 => (1,[(2,asRow 76),(2,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 811 => (1,[(2,asRow 76),(1,asRow 95),(1,asRow 96),(2,asRow 97)])
  | 816 => (1,[(3,asRow 97)])
  | 817 => (1,[(1,asRow 76),(1,asRow 94),(1,asRow 96),(4,asRow 97)])
  | 818 => (1,[(2,asRow 76),(1,asRow 93),(1,asRow 94),(1,asRow 95),(1,asRow 96),(2,asRow 97)])
  | 824 => (1,[(1,asRow 76),(1,asRow 94),(1,asRow 96),(1,asRow 97)])
  | 825 => (1,[(1,asRow 76),(1,asRow 92),(1,asRow 93),(2,asRow 94),(1,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 832 => (1,[(1,asRow 92),(1,asRow 93),(1,asRow 94),(1,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 857 => (1,[(3,asRow 61)])
  | 858 => (1,[(6,asRow 95),(3,asRow 97)])
  | 859 => (1,[(1,asRow 76),(4,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 860 => (1,[(2,asRow 61),(1,asRow 76),(2,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 865 => (1,[(3,asRow 95),(6,asRow 97)])
  | 866 => (1,[(1,asRow 36),(3,asRow 76),(1,asRow 82),(1,asRow 94),(4,asRow 95),(3,asRow 96),(7,asRow 97)])
  | 867 => (1,[(1,asRow 30),(1,asRow 37),(1,asRow 38),(1,asRow 64),(2,asRow 76),(1,asRow 81),(1,asRow 93),(3,asRow 95),(4,asRow 96),(6,asRow 97)])
  | 873 => (2,[(2,asRow 36),(1,asRow 38),(1,asRow 54),(1,asRow 61),(1,asRow 75),(3,asRow 76),(1,asRow 82),(1,asRow 94),(5,asRow 96),(5,asRow 97)])
  | 874 => (10,[(2,asRow 5),(2,asRow 7),(2,asRow 19),(2,asRow 20),(10,asRow 24),(8,asRow 25),(6,asRow 26),(10,asRow 30),(8,asRow 31),(6,asRow 32),(19,asRow 36),(19,asRow 37),(17,asRow 38),(1,asRow 39),(10,asRow 61),(6,asRow 71),(4,asRow 75),(18,asRow 76),(19,asRow 96),(19,asRow 97)])
  | 881 => (1,[(1,asRow 24),(1,asRow 25),(1,asRow 26),(1,asRow 30),(1,asRow 31),(1,asRow 32),(1,asRow 41),(1,asRow 94),(1,asRow 96),(2,asRow 97)])
  | 914 => (1,[(3,asRow 97)])
  | 915 => (1,[(1,asRow 36),(2,asRow 76),(1,asRow 82),(1,asRow 94),(1,asRow 96),(5,asRow 97)])
  | 916 => (1,[(1,asRow 30),(1,asRow 31),(1,asRow 32),(1,asRow 36),(1,asRow 37),(1,asRow 38),(1,asRow 76),(2,asRow 97)])
  | 922 => (1,[(2,asRow 36),(2,asRow 82),(2,asRow 94),(2,asRow 96),(5,asRow 97)])
  | 923 => (7,[(4,asRow 8),(2,asRow 13),(2,asRow 15),(3,asRow 18),(1,asRow 19),(5,asRow 20),(2,asRow 21),(3,asRow 24),(5,asRow 25),(3,asRow 26),(7,asRow 35),(22,asRow 36),(24,asRow 37),(24,asRow 38),(1,asRow 44),(2,asRow 81),(11,asRow 93),(11,asRow 95),(34,asRow 97)])
  | 930 => (6,[(3,asRow 18),(3,asRow 19),(3,asRow 20),(3,asRow 21),(6,asRow 28),(12,asRow 35),(7,asRow 36),(7,asRow 37),(7,asRow 38),(4,asRow 39),(1,asRow 40),(3,asRow 93),(12,asRow 95),(17,asRow 97)])
  | 971 => (1,[(1,asRow 36),(1,asRow 82),(1,asRow 94),(1,asRow 96),(1,asRow 97)])
  | 972 => (1,[(1,asRow 18),(1,asRow 19),(1,asRow 20),(1,asRow 27),(1,asRow 33),(3,asRow 36),(3,asRow 82),(1,asRow 94),(2,asRow 96),(2,asRow 97)])
  | 979 => (9,[(18,asRow 20),(4,asRow 24),(4,asRow 25),(4,asRow 26),(4,asRow 27),(10,asRow 29),(14,asRow 30),(4,asRow 34),(15,asRow 36),(15,asRow 37),(15,asRow 38),(6,asRow 39),(6,asRow 41),(14,asRow 81),(18,asRow 88)])
  | 1028 => (1,[(1,asRow 12),(1,asRow 13),(1,asRow 20),(1,asRow 26),(1,asRow 32),(1,asRow 38)])
  | 1200 => (1,[(1,asRow 61)])
  | 1201 => (1,[(3,asRow 95),(1,asRow 97)])
  | 1202 => (1,[(2,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 1203 => (1,[(1,asRow 61),(1,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 1208 => (1,[(3,asRow 95),(3,asRow 97)])
  | 1209 => (1,[(1,asRow 36),(1,asRow 82),(4,asRow 95),(2,asRow 96),(5,asRow 97)])
  | 1210 => (2,[(2,asRow 30),(1,asRow 37),(1,asRow 38),(1,asRow 39),(3,asRow 61),(1,asRow 64),(2,asRow 81),(4,asRow 95),(4,asRow 96),(8,asRow 97)])
  | 1216 => (1,[(1,asRow 36),(1,asRow 82),(1,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 1217 => (1,[(1,asRow 5),(1,asRow 24),(1,asRow 30),(1,asRow 36),(1,asRow 37),(1,asRow 38),(1,asRow 39),(1,asRow 61),(1,asRow 95),(2,asRow 96),(2,asRow 97)])
  | 1224 => (2,[(2,asRow 24),(2,asRow 34),(1,asRow 36),(1,asRow 37),(1,asRow 38),(1,asRow 39),(2,asRow 80),(4,asRow 95),(1,asRow 96),(1,asRow 97)])
  | 1257 => (1,[(1,asRow 95),(3,asRow 97)])
  | 1258 => (1,[(2,asRow 36),(2,asRow 82),(2,asRow 95),(1,asRow 96),(7,asRow 97)])
  | 1259 => (1,[(2,asRow 30),(1,asRow 37),(1,asRow 38),(1,asRow 39),(1,asRow 64),(2,asRow 81),(1,asRow 95),(1,asRow 96),(5,asRow 97)])
  | 1265 => (1,[(4,asRow 36),(4,asRow 82),(1,asRow 95),(2,asRow 96),(5,asRow 97)])
  | 1266 => (3,[(2,asRow 0),(2,asRow 5),(2,asRow 10),(2,asRow 12),(2,asRow 13),(2,asRow 24),(2,asRow 26),(6,asRow 30),(2,asRow 31),(6,asRow 32),(4,asRow 33),(10,asRow 36),(10,asRow 37),(12,asRow 38),(10,asRow 39),(8,asRow 97)])
  | 1273 => (27,[(18,asRow 0),(18,asRow 10),(26,asRow 27),(1,asRow 29),(51,asRow 30),(33,asRow 31),(42,asRow 32),(42,asRow 33),(15,asRow 34),(37,asRow 36),(37,asRow 37),(28,asRow 38),(28,asRow 39),(25,asRow 41),(9,asRow 77),(9,asRow 88),(9,asRow 89),(35,asRow 92)])
  | 1314 => (1,[(2,asRow 36),(2,asRow 82),(1,asRow 96),(1,asRow 97)])
  | 1315 => (9,[(3,asRow 0),(6,asRow 5),(3,asRow 10),(3,asRow 12),(3,asRow 18),(3,asRow 24),(4,asRow 26),(5,asRow 29),(12,asRow 30),(20,asRow 36),(23,asRow 37),(23,asRow 38),(23,asRow 39),(5,asRow 41),(9,asRow 81),(3,asRow 86),(4,asRow 89)])
  | 1322 => (3,[(2,asRow 0),(4,asRow 5),(2,asRow 10),(2,asRow 12),(2,asRow 18),(2,asRow 24),(6,asRow 28),(8,asRow 30),(2,asRow 32),(2,asRow 33),(3,asRow 36),(5,asRow 37),(5,asRow 38),(5,asRow 39),(2,asRow 40),(4,asRow 41),(4,asRow 81),(4,asRow 95)])
  | 1371 => (21,[(7,asRow 0),(7,asRow 1),(7,asRow 5),(7,asRow 10),(7,asRow 16),(7,asRow 18),(11,asRow 24),(4,asRow 25),(4,asRow 26),(4,asRow 27),(13,asRow 28),(16,asRow 30),(2,asRow 31),(2,asRow 32),(9,asRow 33),(17,asRow 35),(8,asRow 36),(8,asRow 37),(8,asRow 38),(8,asRow 39),(12,asRow 40)])
  | 1600 => (1,[(1,asRow 97)])
  | 1601 => (1,[(1,asRow 36),(1,asRow 82),(3,asRow 97)])
  | 1602 => (3,[(3,asRow 30),(1,asRow 36),(1,asRow 37),(1,asRow 38),(1,asRow 39),(1,asRow 40),(3,asRow 81),(5,asRow 97)])
  | 1608 => (1,[(3,asRow 36),(3,asRow 82),(3,asRow 97)])
  | 1609 => (18,[(9,asRow 0),(3,asRow 1),(3,asRow 2),(3,asRow 3),(12,asRow 10),(24,asRow 30),(9,asRow 31),(15,asRow 32),(15,asRow 33),(15,asRow 34),(38,asRow 36),(35,asRow 37),(29,asRow 38),(29,asRow 39),(29,asRow 40),(6,asRow 88),(6,asRow 89),(6,asRow 92),(22,asRow 97)])
  | 1616 => (6,[(3,asRow 0),(1,asRow 2),(1,asRow 7),(1,asRow 9),(4,asRow 10),(1,asRow 18),(3,asRow 19),(14,asRow 30),(2,asRow 33),(5,asRow 36),(6,asRow 37),(3,asRow 38),(5,asRow 39),(3,asRow 40),(12,asRow 81),(1,asRow 86),(2,asRow 89),(1,asRow 97)])
  | 1657 => (1,[(3,asRow 36),(3,asRow 82),(1,asRow 97)])
  | 1658 => (12,[(16,asRow 0),(16,asRow 10),(20,asRow 30),(8,asRow 32),(8,asRow 33),(8,asRow 34),(31,asRow 36),(31,asRow 37),(23,asRow 38),(23,asRow 39),(23,asRow 40),(15,asRow 41),(8,asRow 77),(4,asRow 81),(8,asRow 88),(8,asRow 89),(8,asRow 92)])
  | 1665 => (9,[(12,asRow 0),(12,asRow 5),(24,asRow 10),(26,asRow 30),(2,asRow 31),(14,asRow 32),(14,asRow 33),(14,asRow 34),(10,asRow 36),(22,asRow 37),(10,asRow 38),(10,asRow 39),(10,asRow 40),(27,asRow 41),(12,asRow 88),(12,asRow 89),(12,asRow 92)])
  | 1714 => (3,[(2,asRow 5),(2,asRow 10),(2,asRow 16),(2,asRow 23),(2,asRow 29),(5,asRow 30),(2,asRow 33),(2,asRow 34),(3,asRow 37),(2,asRow 38),(4,asRow 41),(3,asRow 81),(1,asRow 87)])
  | 2000 => (1,[(1,asRow 36),(1,asRow 82)])
  | 2001 => (12,[(4,asRow 0),(12,asRow 10),(4,asRow 13),(4,asRow 19),(4,asRow 25),(4,asRow 30),(9,asRow 36),(13,asRow 37),(9,asRow 38),(9,asRow 39),(9,asRow 40),(9,asRow 41),(4,asRow 81),(8,asRow 86)])
  | 2008 => (2,[(2,asRow 0),(2,asRow 5),(1,asRow 8),(3,asRow 10),(1,asRow 18),(1,asRow 22),(3,asRow 30),(1,asRow 32),(1,asRow 33),(1,asRow 34),(1,asRow 36),(3,asRow 37),(1,asRow 38),(2,asRow 39),(1,asRow 40),(4,asRow 41),(1,asRow 88),(2,asRow 89),(1,asRow 92)])
  | 2057 => (4,[(5,asRow 0),(1,asRow 2),(2,asRow 3),(2,asRow 5),(1,asRow 7),(3,asRow 9),(4,asRow 10),(2,asRow 12),(2,asRow 24),(1,asRow 28),(3,asRow 29),(5,asRow 30),(1,asRow 32),(2,asRow 34),(3,asRow 36),(4,asRow 37),(1,asRow 38),(4,asRow 41),(3,asRow 88),(1,asRow 92)])
  | 2400 => (9,[(5,asRow 0),(2,asRow 2),(3,asRow 7),(2,asRow 9),(2,asRow 10),(2,asRow 11),(2,asRow 12),(1,asRow 14),(3,asRow 19),(2,asRow 24),(1,asRow 25),(2,asRow 30),(1,asRow 31),(2,asRow 36),(1,asRow 37),(1,asRow 88)])
  | _ => (1,[])

private def ordinaryOK (m : Gap) : Bool :=
  let prices := ordinaryPrices (key m)
  decide (0<prices.1) && dualOK prices.1 (forwardCost m) prices.2
private def gapChunk00 : List Gap := [((0,0),(0,0)),((0,0),(0,1)),((0,0),(0,2)),((0,0),(0,3)),((0,0),(0,4)),((0,0),(0,5))]
private theorem ordinary00 : gapChunk00.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk01 : List Gap := [((0,0),(0,6)),((0,0),(1,1)),((0,0),(1,2)),((0,0),(1,3)),((0,0),(1,4)),((0,0),(1,5))]
private theorem ordinary01 : gapChunk01.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk02 : List Gap := [((0,0),(1,6)),((0,0),(2,2)),((0,0),(2,3)),((0,0),(2,4)),((0,0),(2,5)),((0,0),(2,6))]
private theorem ordinary02 : gapChunk02.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk03 : List Gap := [((0,0),(3,3)),((0,0),(3,4)),((0,0),(3,5)),((0,0),(3,6)),((0,0),(4,4)),((0,0),(4,5))]
private theorem ordinary03 : gapChunk03.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk04 : List Gap := [((0,0),(4,6)),((0,0),(5,5)),((0,0),(5,6)),((0,0),(6,6)),((0,1),(1,1)),((0,1),(1,2))]
private theorem ordinary04 : gapChunk04.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk05 : List Gap := [((0,1),(1,3)),((0,1),(1,4)),((0,1),(1,5)),((0,1),(1,6)),((0,1),(2,2)),((0,1),(2,3))]
private theorem ordinary05 : gapChunk05.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk06 : List Gap := [((0,1),(2,4)),((0,1),(2,5)),((0,1),(2,6)),((0,1),(3,3)),((0,1),(3,4)),((0,1),(3,5))]
private theorem ordinary06 : gapChunk06.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk07 : List Gap := [((0,1),(3,6)),((0,1),(4,4)),((0,1),(4,5)),((0,1),(4,6)),((0,1),(5,5)),((0,1),(5,6))]
private theorem ordinary07 : gapChunk07.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk08 : List Gap := [((0,1),(6,6)),((0,2),(2,2)),((0,2),(2,3)),((0,2),(2,4)),((0,2),(2,5)),((0,2),(2,6))]
private theorem ordinary08 : gapChunk08.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk09 : List Gap := [((0,2),(3,3)),((0,2),(3,4)),((0,2),(3,5)),((0,2),(3,6)),((0,2),(4,4)),((0,2),(4,5))]
private theorem ordinary09 : gapChunk09.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk10 : List Gap := [((0,2),(4,6)),((0,2),(5,5)),((0,2),(5,6)),((0,2),(6,6)),((0,3),(3,3)),((0,3),(3,4))]
private theorem ordinary10 : gapChunk10.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk11 : List Gap := [((0,3),(3,5)),((0,3),(3,6)),((0,3),(4,4)),((0,3),(4,5)),((0,3),(4,6)),((0,3),(5,5))]
private theorem ordinary11 : gapChunk11.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk12 : List Gap := [((0,3),(5,6)),((0,3),(6,6)),((0,4),(4,4)),((0,4),(4,5)),((0,4),(4,6)),((0,4),(5,5))]
private theorem ordinary12 : gapChunk12.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk13 : List Gap := [((0,4),(5,6)),((0,4),(6,6)),((0,5),(5,5)),((0,5),(5,6)),((0,5),(6,6)),((0,6),(6,6))]
private theorem ordinary13 : gapChunk13.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk14 : List Gap := [((1,1),(1,1)),((1,1),(1,2)),((1,1),(1,3)),((1,1),(1,4)),((1,1),(1,5)),((1,1),(1,6))]
private theorem ordinary14 : gapChunk14.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk15 : List Gap := [((1,1),(2,2)),((1,1),(2,3)),((1,1),(2,4)),((1,1),(2,5)),((1,1),(2,6)),((1,1),(3,3))]
private theorem ordinary15 : gapChunk15.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk16 : List Gap := [((1,1),(3,4)),((1,1),(3,5)),((1,1),(3,6)),((1,1),(4,4)),((1,1),(4,5)),((1,1),(4,6))]
private theorem ordinary16 : gapChunk16.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk17 : List Gap := [((1,1),(5,5)),((1,1),(5,6)),((1,1),(6,6)),((1,2),(2,2)),((1,2),(2,3)),((1,2),(2,4))]
private theorem ordinary17 : gapChunk17.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk18 : List Gap := [((1,2),(2,5)),((1,2),(2,6)),((1,2),(3,3)),((1,2),(3,4)),((1,2),(3,5)),((1,2),(3,6))]
private theorem ordinary18 : gapChunk18.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk19 : List Gap := [((1,2),(4,4)),((1,2),(4,5)),((1,2),(4,6)),((1,2),(5,5)),((1,2),(5,6)),((1,2),(6,6))]
private theorem ordinary19 : gapChunk19.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk20 : List Gap := [((1,3),(3,3)),((1,3),(3,4)),((1,3),(3,5)),((1,3),(3,6)),((1,3),(4,4)),((1,3),(4,5))]
private theorem ordinary20 : gapChunk20.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk21 : List Gap := [((1,3),(4,6)),((1,3),(5,5)),((1,3),(5,6)),((1,3),(6,6)),((1,4),(4,4)),((1,4),(4,5))]
private theorem ordinary21 : gapChunk21.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk22 : List Gap := [((1,4),(4,6)),((1,4),(5,5)),((1,4),(5,6)),((1,4),(6,6)),((1,5),(5,5)),((1,5),(5,6))]
private theorem ordinary22 : gapChunk22.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk23 : List Gap := [((1,5),(6,6)),((1,6),(6,6)),((2,2),(2,2)),((2,2),(2,3)),((2,2),(2,4)),((2,2),(2,5))]
private theorem ordinary23 : gapChunk23.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk24 : List Gap := [((2,2),(2,6)),((2,2),(3,3)),((2,2),(3,4)),((2,2),(3,5)),((2,2),(3,6)),((2,2),(4,4))]
private theorem ordinary24 : gapChunk24.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk25 : List Gap := [((2,2),(4,5)),((2,2),(4,6)),((2,2),(5,5)),((2,2),(5,6)),((2,2),(6,6)),((2,3),(3,3))]
private theorem ordinary25 : gapChunk25.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk26 : List Gap := [((2,3),(3,4)),((2,3),(3,5)),((2,3),(3,6)),((2,3),(4,4)),((2,3),(4,5)),((2,3),(4,6))]
private theorem ordinary26 : gapChunk26.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk27 : List Gap := [((2,3),(5,5)),((2,3),(5,6)),((2,3),(6,6)),((2,4),(4,4)),((2,4),(4,5)),((2,4),(4,6))]
private theorem ordinary27 : gapChunk27.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk28 : List Gap := [((2,4),(5,5)),((2,4),(5,6)),((2,4),(6,6)),((2,5),(5,5)),((2,5),(5,6)),((2,5),(6,6))]
private theorem ordinary28 : gapChunk28.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk29 : List Gap := [((2,6),(6,6)),((3,3),(3,3)),((3,3),(3,4)),((3,3),(3,5)),((3,3),(3,6)),((3,3),(4,4))]
private theorem ordinary29 : gapChunk29.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk30 : List Gap := [((3,3),(4,5)),((3,3),(4,6)),((3,3),(5,5)),((3,3),(5,6)),((3,3),(6,6)),((3,4),(4,4))]
private theorem ordinary30 : gapChunk30.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk31 : List Gap := [((3,4),(4,5)),((3,4),(4,6)),((3,4),(5,5)),((3,4),(5,6)),((3,4),(6,6)),((3,5),(5,5))]
private theorem ordinary31 : gapChunk31.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk32 : List Gap := [((3,5),(5,6)),((3,5),(6,6)),((3,6),(6,6)),((4,4),(4,4)),((4,4),(4,5)),((4,4),(4,6))]
private theorem ordinary32 : gapChunk32.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk33 : List Gap := [((4,4),(5,5)),((4,4),(5,6)),((4,4),(6,6)),((4,5),(5,5)),((4,5),(5,6)),((4,5),(6,6))]
private theorem ordinary33 : gapChunk33.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def gapChunk34 : List Gap := [((4,6),(6,6)),((5,5),(5,5)),((5,5),(5,6)),((5,5),(6,6)),((5,6),(6,6)),((6,6),(6,6))]
private theorem ordinary34 : gapChunk34.all (fun m => exceptional m || ordinaryOK m)=true := by decide
private def orderedChunks : List (List Gap) := [gapChunk00,gapChunk01,gapChunk02,gapChunk03,gapChunk04,gapChunk05,gapChunk06,gapChunk07,gapChunk08,gapChunk09,gapChunk10,gapChunk11,gapChunk12,gapChunk13,gapChunk14,gapChunk15,gapChunk16,gapChunk17,gapChunk18,gapChunk19,gapChunk20,gapChunk21,gapChunk22,gapChunk23,gapChunk24,gapChunk25,gapChunk26,gapChunk27,gapChunk28,gapChunk29,gapChunk30,gapChunk31,gapChunk32,gapChunk33,gapChunk34]
set_option maxRecDepth 4096 in
private theorem chunksCover : gaps=orderedChunks.flatten := by decide
private theorem ordinaryChunks : orderedChunks.all (fun ms => ms.all (fun m => exceptional m || ordinaryOK m))=true := by
  simp only [orderedChunks,List.all_cons,List.all_nil,ordinary00,ordinary01,ordinary02,ordinary03,ordinary04,ordinary05,ordinary06,ordinary07,ordinary08,ordinary09,ordinary10,ordinary11,ordinary12,ordinary13,ordinary14,ordinary15,ordinary16,ordinary17,ordinary18,ordinary19,ordinary20,ordinary21,ordinary22,ordinary23,ordinary24,ordinary25,ordinary26,ordinary27,ordinary28,ordinary29,ordinary30,ordinary31,ordinary32,ordinary33,ordinary34]
  rfl

private theorem ordinaryVerified (m : Gap) (sorted : sortedGap m) (regular : exceptional m=false) : ordinaryOK m=true := by
  have h := gapMem m sorted; rw [chunksCover] at h
  obtain ⟨xs,hs,hm⟩ := List.mem_flatten.mp h
  have test := List.all_eq_true.mp (List.all_eq_true.mp ordinaryChunks _ hs) _ hm
  simpa only [regular,Bool.false_or] using test

private theorem checkedScore (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x) (c : Wedge7 → Nat)
    (d : Nat) (p : Prices) (positive : 0<d) (valid : dualOK d c p=true) : score x c≤Nat.cast (referenceCost c) := by
  obtain ⟨cols,total⟩ := Bool.and_eq_true_iff.mp valid
  obtain ⟨legal,col⟩ := Bool.and_eq_true_iff.mp cols
  have raw := weakDual x nx rows (fun w => d*c w) p (d*referenceCost c)
    ⟨legal,col,Nat.le_of_eq (_root_.of_decide_eq_true total)⟩
  rw [scaleScore,Semiring.natCast_mul] at raw
  have lower := natMono (R:=R) (show 1≤d by omega)
  have one : (Nat.cast 1:R)=1 := by grind
  rw [one] at lower
  have pos : (0:R)<Nat.cast d := Std.lt_of_lt_of_le OrderedRing.zero_lt_one lower
  by_cases h : score x c≤Nat.cast (referenceCost c)
  · exact h
  · have m := OrderedRing.mul_pos pos (show 0<score x c-Nat.cast (referenceCost c) by grind)
    grind

/-- The ordinary 98-row packing bound for each of the 205 regular sorted
quartic gap monomials, measured against the physical computational reference. -/
theorem ordinaryForwardBound (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (m : Gap) (sorted : sortedGap m) (regular : exceptional m=false) :
    score x (forwardCost m)≤Nat.cast (referenceCost (forwardCost m)) := by
  let d := (ordinaryPrices (key m)).1
  let ps := (ordinaryPrices (key m)).2
  have h := ordinaryVerified m sorted regular
  change (decide (0<d) && dualOK d (forwardCost m) ps)=true at h
  have parts := Bool.and_eq_true_iff.mp h
  exact checkedScore x nx rows (forwardCost m) d ps (_root_.of_decide_eq_true parts.1) parts.2

private def cornerPrices : Nat → Prices
  | 264 => [(2,asRow 61)]
  | 265 => [(1,asRow 61)]
  | 266 => [(1,asRow 61)]
  | 267 => []
  | 268 => [(2,asRow 97)]
  | 269 => [(1,asRow 97)]
  | 270 => [(1,asRow 97)]
  | 271 => []
  | 272 => [(2,asRow 76)]
  | 273 => [(1,asRow 76)]
  | 274 => [(1,asRow 76)]
  | 275 => []
  | 292 => [(2,asRow 61)]
  | 293 => [(1,asRow 61)]
  | 294 => [(2,asRow 61)]
  | 295 => [(1,asRow 61)]
  | 296 => [(2,asRow 61),(2,asRow 97)]
  | 297 => [(1,asRow 61),(1,asRow 97)]
  | 298 => [(2,asRow 61),(2,asRow 97)]
  | 299 => [(1,asRow 61),(1,asRow 97)]
  | 300 => [(2,asRow 96),(2,asRow 97)]
  | 301 => [(1,asRow 96),(1,asRow 97)]
  | 302 => [(2,asRow 96),(2,asRow 97)]
  | 303 => [(1,asRow 96),(1,asRow 97)]
  | 304 => [(2,asRow 75),(2,asRow 76)]
  | 305 => [(1,asRow 75),(1,asRow 76)]
  | 306 => [(2,asRow 75),(2,asRow 76)]
  | 307 => [(1,asRow 75),(1,asRow 76)]
  | 324 => [(2,asRow 97)]
  | 325 => [(1,asRow 97)]
  | 326 => [(2,asRow 97)]
  | 327 => [(1,asRow 97)]
  | 328 => [(2,asRow 36),(2,asRow 97)]
  | 329 => [(1,asRow 36),(1,asRow 97)]
  | 330 => [(2,asRow 36),(2,asRow 97)]
  | 331 => [(1,asRow 36),(1,asRow 97)]
  | 332 => [(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 333 => [(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 334 => [(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 335 => [(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 356 => [(2,asRow 36)]
  | 357 => [(1,asRow 36)]
  | 358 => [(2,asRow 36)]
  | 359 => [(1,asRow 36)]
  | 360 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 361 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 362 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 363 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 460 => [(2,asRow 61)]
  | 461 => [(2,asRow 61)]
  | 462 => []
  | 463 => []
  | 464 => [(2,asRow 97)]
  | 465 => [(2,asRow 97)]
  | 466 => []
  | 467 => []
  | 468 => [(2,asRow 76)]
  | 469 => [(2,asRow 76)]
  | 470 => []
  | 471 => []
  | 488 => [(4,asRow 61)]
  | 489 => [(4,asRow 61)]
  | 490 => [(2,asRow 61)]
  | 491 => [(2,asRow 61)]
  | 492 => [(4,asRow 61),(4,asRow 97)]
  | 493 => [(4,asRow 61),(4,asRow 97)]
  | 494 => [(2,asRow 61),(2,asRow 97)]
  | 495 => [(2,asRow 61),(2,asRow 97)]
  | 496 => [(2,asRow 61),(2,asRow 76),(2,asRow 96),(2,asRow 97)]
  | 497 => [(2,asRow 61),(2,asRow 76),(2,asRow 96),(2,asRow 97)]
  | 498 => [(1,asRow 61),(1,asRow 76),(1,asRow 96),(1,asRow 97)]
  | 499 => [(1,asRow 61),(1,asRow 76),(1,asRow 96),(1,asRow 97)]
  | 500 => [(2,asRow 76),(2,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 501 => [(2,asRow 76),(2,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 502 => [(1,asRow 76),(1,asRow 95),(1,asRow 96),(1,asRow 97)]
  | 503 => [(1,asRow 76),(1,asRow 95),(1,asRow 96),(1,asRow 97)]
  | 520 => [(4,asRow 97)]
  | 521 => [(4,asRow 97)]
  | 522 => [(2,asRow 97)]
  | 523 => [(2,asRow 97)]
  | 524 => [(2,asRow 36),(4,asRow 76),(2,asRow 97)]
  | 525 => [(2,asRow 36),(4,asRow 76),(2,asRow 97)]
  | 526 => [(1,asRow 36),(2,asRow 76),(1,asRow 97)]
  | 527 => [(1,asRow 36),(2,asRow 76),(1,asRow 97)]
  | 528 => [(2,asRow 30),(2,asRow 36),(4,asRow 76)]
  | 529 => [(2,asRow 30),(2,asRow 36),(4,asRow 76)]
  | 530 => [(1,asRow 30),(1,asRow 36),(2,asRow 76)]
  | 531 => [(1,asRow 30),(1,asRow 36),(2,asRow 76)]
  | 552 => [(2,asRow 36),(2,asRow 76)]
  | 553 => [(2,asRow 36),(2,asRow 76)]
  | 554 => [(1,asRow 36),(1,asRow 76)]
  | 555 => [(1,asRow 36),(1,asRow 76)]
  | 556 => [(2,asRow 36),(2,asRow 76)]
  | 557 => [(2,asRow 36),(2,asRow 76)]
  | 558 => [(1,asRow 36),(1,asRow 76)]
  | 559 => [(1,asRow 36),(1,asRow 76)]
  | 1636 => [(2,asRow 61)]
  | 1637 => [(1,asRow 61)]
  | 1638 => [(2,asRow 61)]
  | 1639 => [(1,asRow 61)]
  | 1640 => [(2,asRow 97)]
  | 1641 => [(1,asRow 97)]
  | 1642 => [(2,asRow 97)]
  | 1643 => [(1,asRow 97)]
  | 1644 => [(2,asRow 76)]
  | 1645 => [(1,asRow 76)]
  | 1646 => [(2,asRow 76)]
  | 1647 => [(1,asRow 76)]
  | 1664 => [(2,asRow 61)]
  | 1665 => [(1,asRow 61)]
  | 1666 => [(2,asRow 61)]
  | 1667 => [(1,asRow 61)]
  | 1668 => [(2,asRow 61),(2,asRow 97)]
  | 1669 => [(1,asRow 61),(1,asRow 97)]
  | 1670 => [(2,asRow 61),(2,asRow 97)]
  | 1671 => [(1,asRow 61),(1,asRow 97)]
  | 1672 => [(2,asRow 96),(2,asRow 97)]
  | 1673 => [(1,asRow 96),(1,asRow 97)]
  | 1674 => [(2,asRow 96),(2,asRow 97)]
  | 1675 => [(1,asRow 96),(1,asRow 97)]
  | 1676 => [(2,asRow 75),(2,asRow 76)]
  | 1677 => [(1,asRow 75),(1,asRow 76)]
  | 1678 => [(2,asRow 75),(2,asRow 76)]
  | 1679 => [(1,asRow 75),(1,asRow 76)]
  | 1696 => [(2,asRow 97)]
  | 1697 => [(1,asRow 97)]
  | 1698 => [(2,asRow 97)]
  | 1699 => [(1,asRow 97)]
  | 1700 => [(2,asRow 36),(2,asRow 97)]
  | 1701 => [(1,asRow 36),(1,asRow 97)]
  | 1702 => [(2,asRow 36),(2,asRow 97)]
  | 1703 => [(1,asRow 36),(1,asRow 97)]
  | 1704 => [(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 1705 => [(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 1706 => [(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 1707 => [(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 1728 => [(2,asRow 36)]
  | 1729 => [(1,asRow 36)]
  | 1730 => [(2,asRow 36)]
  | 1731 => [(1,asRow 36)]
  | 1732 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 1733 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 1734 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(2,asRow 76)]
  | 1735 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(1,asRow 76)]
  | 1832 => [(4,asRow 61)]
  | 1833 => [(3,asRow 61)]
  | 1834 => [(4,asRow 61)]
  | 1835 => [(3,asRow 61)]
  | 1836 => [(4,asRow 97)]
  | 1837 => [(3,asRow 97)]
  | 1838 => [(4,asRow 97)]
  | 1839 => [(3,asRow 97)]
  | 1840 => [(4,asRow 76)]
  | 1841 => [(3,asRow 76)]
  | 1842 => [(4,asRow 76)]
  | 1843 => [(3,asRow 76)]
  | 1860 => [(8,asRow 61)]
  | 1861 => [(7,asRow 61)]
  | 1862 => [(8,asRow 61)]
  | 1863 => [(7,asRow 61)]
  | 1864 => [(8,asRow 95),(8,asRow 97)]
  | 1865 => [(7,asRow 95),(7,asRow 97)]
  | 1866 => [(8,asRow 95),(8,asRow 97)]
  | 1867 => [(7,asRow 95),(7,asRow 97)]
  | 1868 => [(2,asRow 75),(6,asRow 76),(4,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 1869 => [(1,asRow 75),(5,asRow 76),(4,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 1870 => [(2,asRow 75),(6,asRow 76),(4,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 1871 => [(1,asRow 75),(5,asRow 76),(4,asRow 95),(2,asRow 96),(2,asRow 97)]
  | 1872 => [(2,asRow 75),(6,asRow 76),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1873 => [(1,asRow 75),(5,asRow 76),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1874 => [(2,asRow 75),(6,asRow 76),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1875 => [(1,asRow 75),(5,asRow 76),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1892 => [(8,asRow 97)]
  | 1893 => [(7,asRow 97)]
  | 1894 => [(8,asRow 97)]
  | 1895 => [(7,asRow 97)]
  | 1896 => [(2,asRow 36),(2,asRow 37),(4,asRow 76),(8,asRow 97)]
  | 1897 => [(1,asRow 36),(1,asRow 37),(3,asRow 76),(1,asRow 94),(1,asRow 96),(8,asRow 97)]
  | 1898 => [(2,asRow 36),(2,asRow 37),(4,asRow 76),(8,asRow 97)]
  | 1899 => [(1,asRow 36),(1,asRow 37),(3,asRow 76),(1,asRow 94),(1,asRow 96),(8,asRow 97)]
  | 1900 => [(2,asRow 74),(2,asRow 75),(6,asRow 76),(2,asRow 93),(2,asRow 94),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1901 => [(1,asRow 74),(1,asRow 75),(5,asRow 76),(2,asRow 93),(2,asRow 94),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1902 => [(2,asRow 74),(2,asRow 75),(6,asRow 76),(2,asRow 93),(2,asRow 94),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1903 => [(1,asRow 74),(1,asRow 75),(5,asRow 76),(2,asRow 93),(2,asRow 94),(2,asRow 95),(2,asRow 96),(4,asRow 97)]
  | 1924 => [(2,asRow 36),(2,asRow 37),(4,asRow 76)]
  | 1925 => [(1,asRow 36),(1,asRow 37),(3,asRow 76),(1,asRow 94),(1,asRow 96),(1,asRow 97)]
  | 1926 => [(2,asRow 36),(2,asRow 37),(4,asRow 76)]
  | 1927 => [(1,asRow 36),(1,asRow 37),(3,asRow 76),(1,asRow 94),(1,asRow 96),(1,asRow 97)]
  | 1928 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(4,asRow 76),(2,asRow 92),(2,asRow 93),(4,asRow 94),(2,asRow 95),(4,asRow 96),(4,asRow 97)]
  | 1929 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(3,asRow 76),(2,asRow 92),(2,asRow 93),(4,asRow 94),(2,asRow 95),(4,asRow 96),(4,asRow 97)]
  | 1930 => [(2,asRow 73),(2,asRow 74),(2,asRow 75),(4,asRow 76),(2,asRow 92),(2,asRow 93),(4,asRow 94),(2,asRow 95),(4,asRow 96),(4,asRow 97)]
  | 1931 => [(1,asRow 73),(1,asRow 74),(1,asRow 75),(3,asRow 76),(2,asRow 92),(2,asRow 93),(4,asRow 94),(2,asRow 95),(4,asRow 96),(4,asRow 97)]
  | _ => []

private def weightedDen (m : Gap) (u y : Bool) := 4*key m+2*u.toNat+y.toNat

private def cornerOK (m : Gap) (u y : Bool) : Bool :=
  let ps := cornerPrices (weightedDen m u y)
  wedges.all (fun w => decide (subtractCost2 m u y w≤2*forwardCost m w)) && dualOK 1 (cornerCost2 m u y) ps

private def fourCorners (m : Gap) := cornerOK m false false && cornerOK m false true && cornerOK m true false && cornerOK m true true


private def adjustedChunk00 : List Gap := [((0,1),(2,3)),((0,1),(2,4)),((0,1),(2,5))]
private theorem cornerCheck00 : adjustedChunk00.all fourCorners=true := by decide
private def adjustedChunk01 : List Gap := [((0,1),(3,3)),((0,1),(3,4)),((0,1),(3,5))]
private theorem cornerCheck01 : adjustedChunk01.all fourCorners=true := by decide
private def adjustedChunk02 : List Gap := [((0,1),(3,6)),((0,1),(4,4)),((0,1),(4,5))]
private theorem cornerCheck02 : adjustedChunk02.all fourCorners=true := by decide
private def adjustedChunk03 : List Gap := [((0,1),(4,6)),((0,1),(5,5)),((0,1),(5,6))]
private theorem cornerCheck03 : adjustedChunk03.all fourCorners=true := by decide
private def adjustedChunk04 : List Gap := [((0,2),(2,3)),((0,2),(2,4)),((0,2),(2,5))]
private theorem cornerCheck04 : adjustedChunk04.all fourCorners=true := by decide
private def adjustedChunk05 : List Gap := [((0,2),(3,3)),((0,2),(3,4)),((0,2),(3,5))]
private theorem cornerCheck05 : adjustedChunk05.all fourCorners=true := by decide
private def adjustedChunk06 : List Gap := [((0,2),(3,6)),((0,2),(4,4)),((0,2),(4,5))]
private theorem cornerCheck06 : adjustedChunk06.all fourCorners=true := by decide
private def adjustedChunk07 : List Gap := [((0,2),(4,6)),((0,2),(5,5)),((0,2),(5,6))]
private theorem cornerCheck07 : adjustedChunk07.all fourCorners=true := by decide
private def adjustedChunk08 : List Gap := [((1,1),(2,3)),((1,1),(2,4)),((1,1),(2,5))]
private theorem cornerCheck08 : adjustedChunk08.all fourCorners=true := by decide
private def adjustedChunk09 : List Gap := [((1,1),(3,3)),((1,1),(3,4)),((1,1),(3,5))]
private theorem cornerCheck09 : adjustedChunk09.all fourCorners=true := by decide
private def adjustedChunk10 : List Gap := [((1,1),(3,6)),((1,1),(4,4)),((1,1),(4,5))]
private theorem cornerCheck10 : adjustedChunk10.all fourCorners=true := by decide
private def adjustedChunk11 : List Gap := [((1,1),(4,6)),((1,1),(5,5)),((1,1),(5,6))]
private theorem cornerCheck11 : adjustedChunk11.all fourCorners=true := by decide
private def adjustedChunk12 : List Gap := [((1,2),(2,3)),((1,2),(2,4)),((1,2),(2,5))]
private theorem cornerCheck12 : adjustedChunk12.all fourCorners=true := by decide
private def adjustedChunk13 : List Gap := [((1,2),(3,3)),((1,2),(3,4)),((1,2),(3,5))]
private theorem cornerCheck13 : adjustedChunk13.all fourCorners=true := by decide
private def adjustedChunk14 : List Gap := [((1,2),(3,6)),((1,2),(4,4)),((1,2),(4,5))]
private theorem cornerCheck14 : adjustedChunk14.all fourCorners=true := by decide
private def adjustedChunk15 : List Gap := [((1,2),(4,6)),((1,2),(5,5)),((1,2),(5,6))]
private theorem cornerCheck15 : adjustedChunk15.all fourCorners=true := by decide
def adjustedGaps : List Gap := ([adjustedChunk00,adjustedChunk01,adjustedChunk02,adjustedChunk03,adjustedChunk04,adjustedChunk05,adjustedChunk06,adjustedChunk07,adjustedChunk08,adjustedChunk09,adjustedChunk10,adjustedChunk11,adjustedChunk12,adjustedChunk13,adjustedChunk14,adjustedChunk15] : List (List Gap)).flatten
private theorem checkedAdjusted : adjustedGaps.all fourCorners=true := by
  simp only [adjustedGaps,List.flatten_cons,List.flatten_nil,List.all_append,List.all_nil,cornerCheck00,cornerCheck01,cornerCheck02,cornerCheck03,cornerCheck04,cornerCheck05,cornerCheck06,cornerCheck07,cornerCheck08,cornerCheck09,cornerCheck10,cornerCheck11,cornerCheck12,cornerCheck13,cornerCheck14,cornerCheck15]
  rfl

theorem adjustedGapCount : adjustedGaps.length=48 ∧ adjustedGaps.Nodup := by decide

/-- All 192 uniform two-probe corner certificates, with the probe costs
deducted before comparison against the computational reference. -/
theorem weightedCornerBound (x : Wedge7 → R) (nx : ∀ w, 0≤x w) (rows : RowsHold x)
    (m : Gap) (hm : m∈adjustedGaps) (u y : Bool) :
    (∀ w, subtractCost2 m u y w≤2*forwardCost m w) ∧
    score x (cornerCost2 m u y)≤Nat.cast (referenceCost (cornerCost2 m u y)) := by
  have all := List.all_eq_true.mp checkedAdjusted m hm
  unfold fourCorners at all
  obtain ⟨h,d⟩ := Bool.and_eq_true_iff.mp all
  obtain ⟨h,c⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  have cr : cornerOK m u y=true := by
    cases u <;> cases y
    · exact a
    · exact b
    · exact c
    · exact d
  let ps := cornerPrices (weightedDen m u y)
  change (wedges.all (fun w => decide (subtractCost2 m u y w ≤ 2*forwardCost m w)) && dualOK 1 (cornerCost2 m u y) ps)=true at cr
  obtain ⟨valid,cert⟩ := Bool.and_eq_true_iff.mp cr
  exact ⟨fun w => _root_.of_decide_eq_true (List.all_eq_true.mp valid w (memWedges w)),checkedScore x nx rows (cornerCost2 m u y) 1 ps (by decide) cert⟩

end RankSeven.PackingDual
#print axioms RankSeven.PackingDual.weightedCornerBound

#print axioms RankSeven.PackingDual.ordinaryForwardBound
#print axioms RankSeven.PackingDual.uniformBlockBound
