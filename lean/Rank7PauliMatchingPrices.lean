import Rank7PauliPairContraction
import Rank7OddSkewContraction

/-! Continuous seven-label matching prices from six degree rows and four
odd-set rows. The quadratic polynomials use the seven nonnegative gaps. -/
namespace RankSeven.PauliMatchingPrices
open Lean.Grind Pauli JointProbePayment JointProbeGram
open SectorDefectAccounting (wedgePairs)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

attribute [local instance] Semiring.natCast

abbrev Edges := Fin 7 → Fin 7 → R
inductive OddSet | headThree | splitThree | headFive | allSeven

def OddSet.labels : OddSet → List (Fin 7)
  | .headThree => [0,1,2]
  | .splitThree => [0,1,3]
  | .headFive => [0,1,2,3,4]
  | .allSeven => [0,1,2,3,4,5,6]

def OddSet.cap : OddSet → R
  | .headThree => 1
  | .splitThree => 1
  | .headFive => 2
  | .allSeven => 3

def mass (x : Edges (R:=R)) (edges : List (Fin 7×Fin 7)) := sumOver edges (fun e => x e.1 e.2)

def OddRows (x : Edges (R:=R)) : Prop := ∀ s : OddSet, mass x (wedgePairs s.labels) ≤ s.cap

private def edges := wedgePairs (List.finRange 7)
private def S6 := (List.finRange 7).filter (fun i => i.val<6)

def score (x : Edges (R:=R)) (t : Fin 7 → R) := sumOver edges (fun e => t e.1*t e.2*x e.1 e.2)
def massSix (x : Edges (R:=R)) := mass x (wedgePairs S6)
def degree (x : Edges (R:=R)) (i : Fin 7) := mass x (edges.filter (fun e => e.1==i || e.2==i))
def SortedSpectrum (t : Fin 7 → R) : Prop :=
  t 1≤t 0 ∧ t 2≤t 1 ∧ t 3≤t 2 ∧ t 4≤t 3 ∧ t 5≤t 4 ∧ t 6≤t 5 ∧ 0≤t 6

private theorem listEdges : edges=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)] := by decide
private theorem sixEdges : wedgePairs S6=[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)] := by decide

set_option maxRecDepth 8000 in
private theorem degreeRows (x : Edges (R:=R)) (h : ∀ i, degree x i≤1) :
    x 0 1+x 0 2+x 0 3+x 0 4+x 0 5+x 0 6≤1 ∧
    x 0 1+x 1 2+x 1 3+x 1 4+x 1 5+x 1 6≤1 ∧
    x 0 2+x 1 2+x 2 3+x 2 4+x 2 5+x 2 6≤1 ∧
    x 0 3+x 1 3+x 2 3+x 3 4+x 3 5+x 3 6≤1 ∧
    x 0 4+x 1 4+x 2 4+x 3 4+x 4 5+x 4 6≤1 ∧
    x 0 5+x 1 5+x 2 5+x 3 5+x 4 5+x 5 6≤1 := by
  have d0 := h 0
  have n0 : edges.filter (fun e => e.1==0 || e.2==0)=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)] := by decide
  simp only [degree,n0,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d0
  have d1 := h 1
  have n1 : edges.filter (fun e => e.1==1 || e.2==1)=[(0,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by decide
  simp only [degree,n1,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d1
  have d2 := h 2
  have n2 : edges.filter (fun e => e.1==2 || e.2==2)=[(0,2),(1,2),(2,3),(2,4),(2,5),(2,6)] := by decide
  simp only [degree,n2,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d2
  have d3 := h 3
  have n3 : edges.filter (fun e => e.1==3 || e.2==3)=[(0,3),(1,3),(2,3),(3,4),(3,5),(3,6)] := by decide
  simp only [degree,n3,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d3
  have d4 := h 4
  have n4 : edges.filter (fun e => e.1==4 || e.2==4)=[(0,4),(1,4),(2,4),(3,4),(4,5),(4,6)] := by decide
  simp only [degree,n4,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d4
  have d5 := h 5
  have n5 : edges.filter (fun e => e.1==5 || e.2==5)=[(0,5),(1,5),(2,5),(3,5),(4,5),(5,6)] := by decide
  simp only [degree,n5,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at d5
  exact ⟨by have := d0; grind only,by have := d1; grind only,by have := d2; grind only,by have := d3; grind only,by have := d4; grind only,by have := d5; grind only⟩

private theorem oddRows (x : Edges (R:=R)) (h : OddRows x) :
    x 0 1+x 0 2+x 1 2≤1 ∧
    x 0 1+x 0 3+x 1 3≤1 ∧
    x 0 1+x 0 2+x 0 3+x 0 4+x 1 2+x 1 3+x 1 4+x 2 3+x 2 4+x 3 4≤2 ∧
    x 0 1+x 0 2+x 0 3+x 0 4+x 0 5+x 0 6+x 1 2+x 1 3+x 1 4+x 1 5+x 1 6+x 2 3+x 2 4+x 2 5+x 2 6+x 3 4+x 3 5+x 3 6+x 4 5+x 4 6+x 5 6≤3 := by
  have r0 := h .headThree
  have t0 : wedgePairs OddSet.headThree.labels=[(0,1),(0,2),(1,2)] := by decide
  simp only [t0,OddSet.cap,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at r0
  have r1 := h .splitThree
  have t1 : wedgePairs OddSet.splitThree.labels=[(0,1),(0,3),(1,3)] := by decide
  simp only [t1,OddSet.cap,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at r1
  have r2 := h .headFive
  have t2 : wedgePairs OddSet.headFive.labels=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] := by decide
  simp only [t2,OddSet.cap,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at r2
  have r3 := h .allSeven
  have t3 : wedgePairs OddSet.allSeven.labels=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)] := by decide
  simp only [t3,OddSet.cap,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at r3
  exact ⟨by have := r0; grind only,by have := r1; grind only,by have := r2; grind only,by have := r3; grind only⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem highestBound (x : Edges (R:=R)) (t : Fin 7 → R) (sort : SortedSpectrum t)
    (nonneg : ∀ i j, 0≤x i j) (deg : ∀ i, degree x i≤1) (odd : OddRows x) :
    score x t≤highPrice t-leadingGap t*(1-x 0 1) := by
  obtain ⟨d0,d1,d2,d3,d4,d5⟩ := degreeRows x deg
  obtain ⟨oheadThree,osplitThree,oheadFive,oallSeven⟩ := oddRows x odd
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := sort
  let g0 := t 0-t 1
  have n0 : 0≤g0 := by dsimp only [g0]; grind only
  let g1 := t 1-t 2
  have n1 : 0≤g1 := by dsimp only [g1]; grind only
  let g2 := t 2-t 3
  have n2 : 0≤g2 := by dsimp only [g2]; grind only
  let g3 := t 3-t 4
  have n3 : 0≤g3 := by dsimp only [g3]; grind only
  let g4 := t 4-t 5
  have n4 : 0≤g4 := by dsimp only [g4]; grind only
  let g5 := t 5-t 6
  have n5 : 0≤g5 := by dsimp only [g5]; grind only
  let g6 := t 6
  have n6 : 0≤g6 := by dsimp only [g6]; grind only
  let c02 := 1-x 0 1-x 0 2
  have h02 : 0≤c02 := by
    dsimp only [c02]
    have := nonneg 0 3
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    grind only
  let c03 := 1-x 0 1-x 0 2-x 0 3
  have h03 : 0≤c03 := by
    dsimp only [c03]
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    grind only
  let c04 := 1-x 0 1-x 0 2-x 0 3-x 0 4
  have h04 : 0≤c04 := by
    dsimp only [c04]
    have := nonneg 0 5
    have := nonneg 0 6
    grind only
  let c05 := 1-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5
  have h05 : 0≤c05 := by
    dsimp only [c05]
    have := nonneg 0 6
    grind only
  let c06 := 1-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6
  have h06 : 0≤c06 := by
    dsimp only [c06]
    grind only
  let c12 := 1-x 0 1-x 0 2-x 1 2
  have h12 : 0≤c12 := by
    dsimp only [c12]
    grind only
  let c13 := 2-2*x 0 1-x 0 2-x 0 3-x 1 2-x 1 3
  have h13 : 0≤c13 := by
    dsimp only [c13]
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 4
    have := nonneg 1 5
    have := nonneg 1 6
    grind only
  let c14 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4
  have h14 : 0≤c14 := by
    dsimp only [c14]
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 5
    have := nonneg 1 6
    grind only
  let c15 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 1 2-x 1 3-x 1 4-x 1 5
  have h15 : 0≤c15 := by
    dsimp only [c15]
    have := nonneg 0 6
    have := nonneg 1 6
    grind only
  let c16 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-x 1 2-x 1 3-x 1 4-x 1 5-x 1 6
  have h16 : 0≤c16 := by
    dsimp only [c16]
    grind only
  let c22 := 1-x 0 1-x 0 2-x 1 2
  have h22 : 0≤c22 := by
    dsimp only [c22]
    grind only
  let c23 := 3-2*x 0 1-2*x 0 2-x 0 3-2*x 1 2-x 1 3-x 2 3
  have h23 : 0≤c23 := by
    dsimp only [c23]
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 4
    have := nonneg 1 5
    have := nonneg 1 6
    have := nonneg 2 4
    have := nonneg 2 5
    have := nonneg 2 6
    grind only
  let c24 := 3-2*x 0 1-2*x 0 2-x 0 3-x 0 4-2*x 1 2-x 1 3-x 1 4-x 2 3-x 2 4
  have h24 : 0≤c24 := by
    dsimp only [c24]
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 5
    have := nonneg 1 6
    have := nonneg 2 5
    have := nonneg 2 6
    grind only
  let c25 := 3-2*x 0 1-2*x 0 2-x 0 3-x 0 4-x 0 5-2*x 1 2-x 1 3-x 1 4-x 1 5-x 2 3-x 2 4-x 2 5
  have h25 : 0≤c25 := by
    dsimp only [c25]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    grind only
  let c26 := 3-2*x 0 1-2*x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-2*x 1 2-x 1 3-x 1 4-x 1 5-x 1 6-x 2 3-x 2 4-x 2 5-x 2 6
  have h26 : 0≤c26 := by
    dsimp only [c26]
    grind only
  let c33 := 2-x 0 1-x 0 2-x 0 3-x 1 2-x 1 3-x 2 3
  have h33 : 0≤c33 := by
    dsimp only [c33]
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 4
    have := nonneg 1 5
    have := nonneg 1 6
    have := nonneg 2 4
    have := nonneg 2 5
    have := nonneg 2 6
    have := nonneg 3 4
    have := nonneg 3 5
    have := nonneg 3 6
    grind only
  let c34 := 4-2*x 0 1-2*x 0 2-2*x 0 3-x 0 4-2*x 1 2-2*x 1 3-x 1 4-2*x 2 3-x 2 4-x 3 4
  have h34 : 0≤c34 := by
    dsimp only [c34]
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 5
    have := nonneg 1 6
    have := nonneg 2 5
    have := nonneg 2 6
    have := nonneg 3 5
    have := nonneg 3 6
    grind only
  let c35 := 4-2*x 0 1-2*x 0 2-2*x 0 3-x 0 4-x 0 5-2*x 1 2-2*x 1 3-x 1 4-x 1 5-2*x 2 3-x 2 4-x 2 5-x 3 4-x 3 5
  have h35 : 0≤c35 := by
    dsimp only [c35]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    have := nonneg 3 6
    grind only
  let c36 := 4-2*x 0 1-2*x 0 2-2*x 0 3-x 0 4-x 0 5-x 0 6-2*x 1 2-2*x 1 3-x 1 4-x 1 5-x 1 6-2*x 2 3-x 2 4-x 2 5-x 2 6-x 3 4-x 3 5-x 3 6
  have h36 : 0≤c36 := by
    dsimp only [c36]
    grind only
  let c44 := 2-x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4-x 2 3-x 2 4-x 3 4
  have h44 : 0≤c44 := by
    dsimp only [c44]
    grind only
  let c45 := 5-2*x 0 1-2*x 0 2-2*x 0 3-2*x 0 4-x 0 5-2*x 1 2-2*x 1 3-2*x 1 4-x 1 5-2*x 2 3-2*x 2 4-x 2 5-2*x 3 4-x 3 5-x 4 5
  have h45 : 0≤c45 := by
    dsimp only [c45]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    have := nonneg 3 6
    have := nonneg 4 6
    grind only
  let c46 := 5-2*x 0 1-2*x 0 2-2*x 0 3-2*x 0 4-x 0 5-x 0 6-2*x 1 2-2*x 1 3-2*x 1 4-x 1 5-x 1 6-2*x 2 3-2*x 2 4-x 2 5-x 2 6-2*x 3 4-x 3 5-x 3 6-x 4 5-x 4 6
  have h46 : 0≤c46 := by
    dsimp only [c46]
    grind only
  let c55 := 3-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 1 2-x 1 3-x 1 4-x 1 5-x 2 3-x 2 4-x 2 5-x 3 4-x 3 5-x 4 5
  have h55 : 0≤c55 := by
    dsimp only [c55]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    have := nonneg 3 6
    have := nonneg 4 6
    have := nonneg 5 6
    grind only
  let c56 := 6-2*x 0 1-2*x 0 2-2*x 0 3-2*x 0 4-2*x 0 5-x 0 6-2*x 1 2-2*x 1 3-2*x 1 4-2*x 1 5-x 1 6-2*x 2 3-2*x 2 4-2*x 2 5-x 2 6-2*x 3 4-2*x 3 5-x 3 6-2*x 4 5-x 4 6-x 5 6
  have h56 : 0≤c56 := by
    dsimp only [c56]
    grind only
  let c66 := 3-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-x 1 2-x 1 3-x 1 4-x 1 5-x 1 6-x 2 3-x 2 4-x 2 5-x 2 6-x 3 4-x 3 5-x 3 6-x 4 5-x 4 6-x 5 6
  have h66 : 0≤c66 := by
    dsimp only [c66]
    grind only
  have total : 0≤
      g0*g2*c02+
      g0*g3*c03+
      g0*g4*c04+
      g0*g5*c05+
      g0*g6*c06+
      g1*g2*c12+
      g1*g3*c13+
      g1*g4*c14+
      g1*g5*c15+
      g1*g6*c16+
      g2*g2*c22+
      g2*g3*c23+
      g2*g4*c24+
      g2*g5*c25+
      g2*g6*c26+
      g3*g3*c33+
      g3*g4*c34+
      g3*g5*c35+
      g3*g6*c36+
      g4*g4*c44+
      g4*g5*c45+
      g4*g6*c46+
      g5*g5*c55+
      g5*g6*c56+
      g6*g6*c66 := by
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n2) h02
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n3) h03
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n4) h04
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n5) h05
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n6) h06
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n2) h12
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n3) h13
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n4) h14
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n5) h15
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n6) h16
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n2) h22
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n3) h23
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n4) h24
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n5) h25
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n6) h26
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n3) h33
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n4) h34
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n5) h35
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n6) h36
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n4) h44
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n5) h45
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n6) h46
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n5 n5) h55
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n5 n6) h56
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n6 n6) h66
    grind only
  dsimp only [c02,c03,c04,c05,c06,c12,c13,c14,c15,c16,c22,c23,c24,c25,c26,c33,c34,c35,c36,c44,c45,c46,c55,c56,c66,g0,g1,g2,g3,g4,g5,g6] at total
  simp only [score,listEdges,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,highPrice,leadingGap]
  grind only

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem sharedBound (x : Edges (R:=R)) (t : Fin 7 → R) (sort : SortedSpectrum t)
    (nonneg : ∀ i j, 0≤x i j) (deg : ∀ i, degree x i≤1) (odd : OddRows x) :
    score x t≤secondPrice t+leadingGap t*x 0 1-sharedGap t*(1-(x 0 1+x 0 2))-
      emptyGap t*(1-(x 0 1+x 0 2)-x 1 2)-tailGap t*(3-massSix x) := by
  obtain ⟨d0,d1,d2,d3,d4,d5⟩ := degreeRows x deg
  obtain ⟨oheadThree,osplitThree,oheadFive,oallSeven⟩ := oddRows x odd
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := sort
  let g0 := t 0-t 1
  have n0 : 0≤g0 := by dsimp only [g0]; grind only
  let g1 := t 1-t 2
  have n1 : 0≤g1 := by dsimp only [g1]; grind only
  let g2 := t 2-t 3
  have n2 : 0≤g2 := by dsimp only [g2]; grind only
  let g3 := t 3-t 4
  have n3 : 0≤g3 := by dsimp only [g3]; grind only
  let g4 := t 4-t 5
  have n4 : 0≤g4 := by dsimp only [g4]; grind only
  let g5 := t 5-t 6
  have n5 : 0≤g5 := by dsimp only [g5]; grind only
  let g6 := t 6
  have n6 : 0≤g6 := by dsimp only [g6]; grind only
  let c03 := 1-x 0 1-x 0 2-x 0 3
  have h03 : 0≤c03 := by
    dsimp only [c03]
    have := nonneg 0 4
    have := nonneg 0 5
    have := nonneg 0 6
    grind only
  let c04 := 1-x 0 1-x 0 2-x 0 3-x 0 4
  have h04 : 0≤c04 := by
    dsimp only [c04]
    have := nonneg 0 5
    have := nonneg 0 6
    grind only
  let c05 := 1-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5
  have h05 : 0≤c05 := by
    dsimp only [c05]
    have := nonneg 0 6
    grind only
  let c06 := 1-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6
  have h06 : 0≤c06 := by
    dsimp only [c06]
    grind only
  let c13 := 1-x 0 1-x 0 3-x 1 3
  have h13 : 0≤c13 := by
    dsimp only [c13]
    grind only
  let c14 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4
  have h14 : 0≤c14 := by
    dsimp only [c14]
    have := nonneg 0 5
    have := nonneg 0 6
    have := nonneg 1 5
    have := nonneg 1 6
    grind only
  let c15 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 1 2-x 1 3-x 1 4-x 1 5
  have h15 : 0≤c15 := by
    dsimp only [c15]
    have := nonneg 0 6
    have := nonneg 1 6
    grind only
  let c16 := 2-2*x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-x 1 2-x 1 3-x 1 4-x 1 5-x 1 6
  have h16 : 0≤c16 := by
    dsimp only [c16]
    grind only
  let c23 := 1-x 0 3-x 1 3-x 2 3
  have h23 : 0≤c23 := by
    dsimp only [c23]
    have := nonneg 3 4
    have := nonneg 3 5
    have := nonneg 3 6
    grind only
  let c24 := 2-x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4-x 2 3-x 2 4
  have h24 : 0≤c24 := by
    dsimp only [c24]
    have := nonneg 3 4
    grind only
  let c25 := 3-2*x 0 1-2*x 0 2-x 0 3-x 0 4-x 0 5-2*x 1 2-x 1 3-x 1 4-x 1 5-x 2 3-x 2 4-x 2 5
  have h25 : 0≤c25 := by
    dsimp only [c25]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    grind only
  let c26 := 3-2*x 0 1-2*x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-2*x 1 2-x 1 3-x 1 4-x 1 5-x 1 6-x 2 3-x 2 4-x 2 5-x 2 6
  have h26 : 0≤c26 := by
    dsimp only [c26]
    grind only
  let c33 := 1-x 0 3-x 1 3-x 2 3
  have h33 : 0≤c33 := by
    dsimp only [c33]
    have := nonneg 3 4
    have := nonneg 3 5
    have := nonneg 3 6
    grind only
  let c34 := 3-x 0 1-x 0 2-2*x 0 3-x 0 4-x 1 2-2*x 1 3-x 1 4-2*x 2 3-x 2 4-x 3 4
  have h34 : 0≤c34 := by
    dsimp only [c34]
    have := nonneg 3 4
    have := nonneg 3 5
    have := nonneg 3 6
    grind only
  let c35 := 4-2*x 0 1-2*x 0 2-2*x 0 3-x 0 4-x 0 5-2*x 1 2-2*x 1 3-x 1 4-x 1 5-2*x 2 3-x 2 4-x 2 5-x 3 4-x 3 5
  have h35 : 0≤c35 := by
    dsimp only [c35]
    have := nonneg 0 6
    have := nonneg 1 6
    have := nonneg 2 6
    have := nonneg 3 6
    grind only
  let c36 := 4-2*x 0 1-2*x 0 2-2*x 0 3-x 0 4-x 0 5-x 0 6-2*x 1 2-2*x 1 3-x 1 4-x 1 5-x 1 6-2*x 2 3-x 2 4-x 2 5-x 2 6-x 3 4-x 3 5-x 3 6
  have h36 : 0≤c36 := by
    dsimp only [c36]
    grind only
  let c44 := 2-x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4-x 2 3-x 2 4-x 3 4
  have h44 : 0≤c44 := by
    dsimp only [c44]
    grind only
  let c45 := 2-x 0 1-x 0 2-x 0 3-x 0 4-x 1 2-x 1 3-x 1 4-x 2 3-x 2 4-x 3 4
  have h45 : 0≤c45 := by
    dsimp only [c45]
    grind only
  let c46 := 5-2*x 0 1-2*x 0 2-2*x 0 3-2*x 0 4-x 0 5-x 0 6-2*x 1 2-2*x 1 3-2*x 1 4-x 1 5-x 1 6-2*x 2 3-2*x 2 4-x 2 5-x 2 6-2*x 3 4-x 3 5-x 3 6-x 4 5-x 4 6
  have h46 : 0≤c46 := by
    dsimp only [c46]
    grind only
  let c56 := 3-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-x 1 2-x 1 3-x 1 4-x 1 5-x 1 6-x 2 3-x 2 4-x 2 5-x 2 6-x 3 4-x 3 5-x 3 6-x 4 5-x 4 6-x 5 6
  have h56 : 0≤c56 := by
    dsimp only [c56]
    grind only
  let c66 := 3-x 0 1-x 0 2-x 0 3-x 0 4-x 0 5-x 0 6-x 1 2-x 1 3-x 1 4-x 1 5-x 1 6-x 2 3-x 2 4-x 2 5-x 2 6-x 3 4-x 3 5-x 3 6-x 4 5-x 4 6-x 5 6
  have h66 : 0≤c66 := by
    dsimp only [c66]
    grind only
  have total : 0≤
      g0*g3*c03+
      g0*g4*c04+
      g0*g5*c05+
      g0*g6*c06+
      g1*g3*c13+
      g1*g4*c14+
      g1*g5*c15+
      g1*g6*c16+
      g2*g3*c23+
      g2*g4*c24+
      g2*g5*c25+
      g2*g6*c26+
      g3*g3*c33+
      g3*g4*c34+
      g3*g5*c35+
      g3*g6*c36+
      g4*g4*c44+
      g4*g5*c45+
      g4*g6*c46+
      g5*g6*c56+
      g6*g6*c66 := by
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n3) h03
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n4) h04
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n5) h05
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n0 n6) h06
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n3) h13
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n4) h14
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n5) h15
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n1 n6) h16
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n3) h23
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n4) h24
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n5) h25
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n2 n6) h26
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n3) h33
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n4) h34
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n5) h35
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n3 n6) h36
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n4) h44
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n5) h45
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n4 n6) h46
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n5 n6) h56
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg n6 n6) h66
    grind only
  dsimp only [c03,c04,c05,c06,c13,c14,c15,c16,c23,c24,c25,c26,c33,c34,c35,c36,c44,c45,c46,c56,c66,g0,g1,g2,g3,g4,g5,g6] at total
  simp only [score,listEdges,massSix,mass,sixEdges,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,secondPrice,leadingGap,sharedGap,emptyGap,tailGap]
  grind only


private theorem seven : List.finRange 7=[0,1,2,3,4,5,6] := by decide

/-- The degree constraints used by the edge price are all satisfied by the
actual Pauli vector; the missing diagonal term is nonnegative. -/
theorem physicalEdgeDegrees {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (odd : p∈MixedDefect.oddWords n) (i : Fin 7) :
    degree (pairWeight A p) i≤1 := by
  let x := pairWeight A p
  have deg := PauliPairContraction.physicalDegree A orth p i
  change sumOver (List.finRange 7) (x i)≤1 at deg
  rw [seven] at deg
  simp only [sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at deg
  have sym (a b : Fin 7) : x a b=x b a := PauliPairContraction.pairWeightSymm A p odd a b
  have pos (a : Fin 7) : 0≤x a a := ComplexScalar.normSq_nonnegative _
  have ho : ∀ i : Fin 7,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by decide
  change degree x i≤1
  rcases ho i with h|h|h|h|h|h|h <;> subst i
  · have sub : edges.filter (fun e => e.1==0 || e.2==0)=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 0
    grind only
  · have sub : edges.filter (fun e => e.1==1 || e.2==1)=[(0,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 1
    rw [sym 1 0] at deg
    grind only
  · have sub : edges.filter (fun e => e.1==2 || e.2==2)=[(0,2),(1,2),(2,3),(2,4),(2,5),(2,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 2
    rw [sym 2 0,sym 2 1] at deg
    grind only
  · have sub : edges.filter (fun e => e.1==3 || e.2==3)=[(0,3),(1,3),(2,3),(3,4),(3,5),(3,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 3
    rw [sym 3 0,sym 3 1,sym 3 2] at deg
    grind only
  · have sub : edges.filter (fun e => e.1==4 || e.2==4)=[(0,4),(1,4),(2,4),(3,4),(4,5),(4,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 4
    rw [sym 4 0,sym 4 1,sym 4 2,sym 4 3] at deg
    grind only
  · have sub : edges.filter (fun e => e.1==5 || e.2==5)=[(0,5),(1,5),(2,5),(3,5),(4,5),(5,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 5
    rw [sym 5 0,sym 5 1,sym 5 2,sym 5 3,sym 5 4] at deg
    grind only
  · have sub : edges.filter (fun e => e.1==6 || e.2==6)=[(0,6),(1,6),(2,6),(3,6),(4,6),(5,6)] := by decide
    simp only [degree,sub,mass,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have := pos 6
    rw [sym 6 0,sym 6 1,sym 6 2,sym 6 3,sym 6 4,sym 6 5] at deg
    grind only

/-- For every sorted nonnegative spectrum, the highest and shared matching
prices require only the four named odd capacities for this one physical word. -/
theorem perWordBoundsOfOddRows {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n)
    (t : Fin 7 → R) (sort : SortedSpectrum t) (odd : OddRows (pairWeight A p)) :
    let u := pairWeight A p 0 1+pairWeight A p 0 2
    matchingScore A t p≤highPrice t-leadingGap t*(1-pairWeight A p 0 1) ∧
    matchingScore A t p≤secondPrice t+leadingGap t*pairWeight A p 0 1-sharedGap t*(1-u)-
      emptyGap t*(1-u-pairWeight A p 1 2)-tailGap t*(3-sixVertexMass A p) := by
  have deg := physicalEdgeDegrees A orth p hp
  have nx (i j : Fin 7) : 0≤pairWeight A p i j := ComplexScalar.normSq_nonnegative _
  exact ⟨highestBound _ _ sort nx deg odd,sharedBound _ _ sort nx deg odd⟩


omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem sumAppend {α : Type} (xs ys : List α) (f : α → R) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons a xs ih => simp only [sumOver,List.cons_append,List.map_cons,List.sum_cons] at *; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem doubleMass (xs : List (Fin 7)) (x : Edges (R:=R)) (sym : ∀ i j,x j i=x i j) (zero : ∀ i,x i i=0) :
    sumOver xs (fun i => sumOver xs (fun j => x j i))=2*mass x (wedgePairs xs) := by
  induction xs with
  | nil => simp [wedgePairs,mass,sumOver]; grind only
  | cons a xs ih =>
    change x a a+sumOver xs (fun j => x j a)+sumOver xs (fun i => x a i+sumOver xs (fun j => x j i))=_
    rw [sumOverAdd,ih,zero a]
    have t : sumOver xs (fun j => x j a)=sumOver xs (x a) := sumOverCongr _ (fun j => sym a j)
    change _=2*sumOver (wedgePairs (a::xs)) (fun e => x e.1 e.2)
    rw [wedgePairs,sumAppend,t]
    change _=2*(sumOver (xs.map (fun b => (a,b))) (fun e => x e.1 e.2)+mass x (wedgePairs xs))
    have e : sumOver (xs.map (fun b => (a,b))) (fun e => x e.1 e.2)=sumOver xs (x a) := by
      simp only [sumOver,List.map_map,Function.comp_def]
    rw [e]; grind only

/-- Every odd subset of the seven source labels obeys the matching capacity.
The kernel of its skew compression supplies the missing unit in its trace. -/
theorem physicalOddCapacity {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n)
    (keep : Fin 7 → Bool) (odd : ((List.finRange 7).filter keep).length%2=1) :
    let xs := (List.finRange 7).filter keep
    2*mass (pairWeight A p) (wedgePairs xs)≤(Nat.cast xs.length:R)-1 := by
  let xs := (List.finRange 7).filter keep
  let H (i j : Fin 7) := pairAmplitude A p j i
  have sym (i j : Fin 7) : H i j= -H j i := PauliPairContraction.amplitudeSkew A p hp i j
  have c := OddSkewContraction.massLeLengthSubOne xs ((List.nodup_finRange 7).filter _) odd H sym
    (fun v => PauliPairContraction.subsetContraction A orth p keep v)
  have diag (i : Fin 7) : pairWeight A p i i=0 := by
    have z := sym i i
    have x := congrArg ComplexScalar.re z; have y := congrArg ComplexScalar.im z
    change (H i i).re= -(H i i).re at x; change (H i i).im= -(H i i).im at y
    have zero (v : R) (h : v= -v) : v=0 := by grind
    change (H i i).re^2+(H i i).im^2=0
    rw [zero _ x,zero _ y]; grind only
  change sumOver xs (fun i => sumOver xs (fun j => pairWeight A p j i))≤_ at c
  rw [doubleMass xs _ (fun i j => PauliPairContraction.pairWeightSymm A p hp j i) diag] at c
  exact c

theorem physicalOddRows {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    OddRows (pairWeight A p) := by
  intro s
  let keep (i : Fin 7) := s.labels.contains i
  have labels : (List.finRange 7).filter keep=s.labels := by cases s <;> decide
  have odd : ((List.finRange 7).filter keep).length%2=1 := by rw [labels]; cases s <;> decide
  have e := physicalOddCapacity A orth p hp keep odd
  dsimp only at e; rw [labels] at e
  have cap : (Nat.cast s.labels.length:R)-1=2*s.cap := by cases s <;> dsimp [OddSet.labels,OddSet.cap] <;> grind only
  rw [cap] at e; grind only

/-- The actual skew Pauli matching score satisfies both conditional prices
on the whole sorted nonnegative seven-spectrum cone. -/
theorem physicalPerWordBounds {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n)
    (t : Fin 7 → R) (sort : SortedSpectrum t) :
    let u := pairWeight A p 0 1+pairWeight A p 0 2
    matchingScore A t p≤highPrice t-leadingGap t*(1-pairWeight A p 0 1) ∧
    matchingScore A t p≤secondPrice t+leadingGap t*pairWeight A p 0 1-sharedGap t*(1-u)-
      emptyGap t*(1-u-pairWeight A p 1 2)-tailGap t*(3-sixVertexMass A p) :=
  perWordBoundsOfOddRows A orth p hp t sort (physicalOddRows A orth p hp)

/-- Manuscript equations (3) and (4) on the same orthonormal physical
frame, with every per-word matching and packing premise discharged. -/
theorem physicalProbePayments (half third : R) (h2 : 2*half=1) (h3 : 3*third=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (mu : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (sort : SortedSpectrum (fun i => (mu i)^2)) :
    let os := MixedDefect.oddWords (k+3)
    let t := fun i => (mu i)^2
    let E := PhysicalCompressionEffect.physicalEntries half h2 k A
    let W i := ProjectedProbeOverlap.weightedFourWedge 0 i t (fun w => E.realPart w w)
    let P₁ := fun p => pairWeight A p 0 1
    let P := fun p => P₁ p+pairWeight A p 0 2
    let L := densityCoordinates half A mu
    W 1-referencePair t+leadingGap t*oddAverage half (fun p => P₁ p*(1-P₁ p))≤
      2*hs os (pairCoordinates half A 0 1) L ∧
    W 1+W 2-referenceShared t+sharedGap t*oddAverage half (fun p => P p*(1-P p))+
      leadingGap t*oddAverage half (fun p => P₁ p*(1-P p))+
      emptyGap t*oddAverage half (fun p => P p*(1-P p-pairWeight A p 1 2))-
      tailGap t*(oddAverage half (fun p => P p*sixVertexMass A p)-5)≤
      2*hs os (sharedProbe half A) L :=
  ⟨highestPayment half third h2 h3 k A mu orth (fun p hp => (physicalPerWordBounds A orth p hp _ sort).1),
    sharedPayment half third h2 h3 k A mu orth (fun p hp => (physicalPerWordBounds A orth p hp _ sort).2)⟩

end RankSeven.PauliMatchingPrices

#print axioms RankSeven.PauliMatchingPrices.highestBound
#print axioms RankSeven.PauliMatchingPrices.sharedBound
#print axioms RankSeven.PauliMatchingPrices.physicalEdgeDegrees
#print axioms RankSeven.PauliMatchingPrices.physicalOddCapacity
#print axioms RankSeven.PauliMatchingPrices.physicalOddRows
#print axioms RankSeven.PauliMatchingPrices.physicalPerWordBounds
#print axioms RankSeven.PauliMatchingPrices.physicalProbePayments
