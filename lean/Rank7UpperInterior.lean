import Rank7UpperEndpointPrices

/-! The two exterior estimates bound the same fixed-frame quantity at each
corner. Their convex weights may vary between corners. -/
namespace RankSeven.UpperInterior
open Lean.Grind Interval UpperEndpoint UpperEndpointPrices
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

def combineRay (a b : R) (s t : RayData R) : RayData R :=
  ⟨a*s.n+b*t.n,a*s.v+b*t.v,a*s.m+b*t.m,a*s.peak+b*t.peak,a*s.constant+b*t.constant,
    a*s.improvement+b*t.improvement,a*s.tail+b*t.tail,a*s.traceOne+b*t.traceOne,a*s.traceShared+b*t.traceShared⟩

def left (sector : Fin 6) : Fin 7 := ⟨sector.val,Nat.lt_trans sector.isLt (by decide : 6<7)⟩
def right (sector : Fin 6) : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
noncomputable def sectorRay (j : Fin 6) (a b : R) :=
  combineRay a b (rayAt realArithmetic (left j)) (rayAt realArithmetic (right j))

noncomputable def readRay (p : Inputs R) (wh ws c d : R) (r : RayData R) :=
  readAt realArithmetic p (P p) (K p wh ws c d) (B p wh ws c d) invRate r

private theorem readLinear (p : Inputs R) (wh ws c d : R) (a b : R) (s t : RayData R) :
    let U := readRay p wh ws c d
    (U (combineRay a b s t)).splitMargin=a*(U s).splitMargin+b*(U t).splitMargin ∧
    (U (combineRay a b s t)).singleMargin=a*(U s).singleMargin+b*(U t).singleMargin := by
  dsimp only [readRay,readAt,leaf,combineRay]
  constructor <;> grind only

/-- Positivity of a *fixed corner's* common blend extends to any nonzero
nonnegative combination of its two ray records, including the limiting axis. -/
theorem positiveChord {p : Inputs R} {wh ws : R} {j : Fin 6} (sector : RealSector p wh ws j)
    (a b : R) (ha : 0≤a) (hb : 0≤b) (nz : 0<a+b) (cHigh dHigh : Bool) :
    let z := readRay p wh ws (cAt p cHigh) (dAt p dHigh) (sectorRay j a b)
    0<z.splitMargin ∨ 0<z.singleMargin := by
  let U := readRay p wh ws (cAt p cHigh) (dAt p dHigh)
  let l := rayAt (realArithmetic (R:=R)) (left j)
  let r := rayAt (realArithmetic (R:=R)) (right j)
  obtain ⟨s,t,hs,ht,hl,hr⟩ := sector cHigh dHigh
  change 0<s*(U l).splitMargin+t*(U l).singleMargin at hl
  change 0<s*(U r).splitMargin+t*(U r).singleMargin at hr
  have positive : 0<a*(s*(U l).splitMargin+t*(U l).singleMargin)+b*(s*(U r).splitMargin+t*(U r).singleMargin) := by
    by_cases z : 0<a
    · have s₀ := OrderedRing.mul_pos z hl; have s₁ := OrderedRing.mul_nonneg hb (Std.le_of_lt hr); grind only
    · have s₀ := OrderedRing.mul_nonneg ha (Std.le_of_lt hl); have s₁ := OrderedRing.mul_pos (show 0<b by grind only) hr; grind only
  let z := U (sectorRay j a b)
  have eqs := readLinear p wh ws (cAt p cHigh) (dAt p dHigh) a b l r
  change z.splitMargin=_ ∧ z.singleMargin=_ at eqs
  have gain : 0<s*z.splitMargin+t*z.singleMargin := by rw [eqs.1,eqs.2]; grind only
  change 0<z.splitMargin ∨ 0<z.singleMargin
  by_cases pos : 0<z.splitMargin
  · exact Or.inl pos
  · right
    by_cases h : 0<z.singleMargin
    · exact h
    · have bad := OrderedRing.mul_le_mul_of_nonneg_left (show z.splitMargin≤0 by grind only) hs
      have worse := OrderedRing.mul_le_mul_of_nonneg_left (show z.singleMargin≤0 by grind only) ht
      grind only

noncomputable def splitBound (p : Inputs R) (wh ws c d : R) (r : RayData R) : R :=
  let e := K p wh ws c d
  let A := B p wh ws c d
  A.splitDebit*r.n+(P p).residual*(e.dsq*r.v-e.tailPrefix*r.tail)-e.cd*p.k*r.v

noncomputable def singleBound (p : Inputs R) (wh ws c d : R) (r : RayData R) : R :=
  let e := K p wh ws c d
  let A := B p wh ws c d
  A.singleDebit*r.n+(P p).residual*(e.dsq*r.v-e.tailPrefix*r.tail)
    -A.singleton*r.m-(e.dsq*e.dsq)*r.constant-A.increment*r.improvement

private theorem marginsDiffer (p : Inputs R) (wh ws c d : R) (r : RayData R) :
    (readRay p wh ws c d r).splitMargin=physicalPrice p wh ws c d r-splitBound p wh ws c d r ∧
    (readRay p wh ws c d r).singleMargin=physicalPrice p wh ws c d r-singleBound p wh ws c d r := by
  dsimp only [readRay,readAt,leaf,physicalPrice,splitBound,singleBound,realArithmetic]
  constructor <;> grind only

private theorem interpolateCoordinate (l x u : R) (h : l≤x) (k : x≤u) :
    ∃ t : R,0≤t ∧ t≤1 ∧ lerp t l u=x := by
  by_cases d : l=u
  · exact ⟨0,by grind,by grind,by unfold lerp; grind only⟩
  · have pos : 0<u-l := by grind only
    let t := (x-l)/(u-l)
    have eq : (u-l)*t=x-l := UpperContractor.quotientEq _ pos
    have lo : 0≤t := UpperContractor.cancelLe pos (by rw [Semiring.mul_zero,eq]; grind only)
    have hi : t≤1 := UpperContractor.cancelLe pos (by rw [Semiring.mul_one,eq]; grind only)
    exact ⟨t,lo,hi,by unfold lerp; grind only⟩

/-- The endpoint weights disappear before rectangular interpolation. F is the
same bilinear gain at all corners; each exterior estimate individually bounds it. -/
theorem rectangleOfCornerEstimates (p : Inputs R) (wh ws : R) (j : Fin 6) (a b : R)
    (ha : 0≤a) (hb : 0≤b) (nz : 0<a+b) (accept : RealSector p wh ws j)
    (F : Bilinear R)
    (upper : ∀ i k : Bool,
      F.eval (cAt p i) (dAt p k)≤splitBound p wh ws (cAt p i) (dAt p k) (sectorRay j a b) ∧
      F.eval (cAt p i) (dAt p k)≤singleBound p wh ws (cAt p i) (dAt p k) (sectorRay j a b))
    (c d : R) (cl : p.cl≤c) (ch : c≤p.ch) (dl : p.dl≤d) (dh : d≤p.dh) :
    F.eval c d<physicalPrice p wh ws c d (sectorRay j a b) := by
  let r := sectorRay j a b
  obtain ⟨price,poly⟩ := physicalPriceMultiaffine p wh ws r
  let M : Bilinear R := ⟨price.constant-F.constant,price.first-F.first,price.second-F.second,price.interaction-F.interaction⟩
  have eq (x y : R) : M.eval x y=physicalPrice p wh ws x y r-F.eval x y := by
    rw [←poly]; unfold Bilinear.eval M; grind only
  have good (i k : Bool) : 0<M.eval (cAt p i) (dAt p k) := by
    rw [eq]
    have z := positiveChord accept a b ha hb nz i k
    change 0<(readRay p wh ws (cAt p i) (dAt p k) r).splitMargin ∨ 0<(readRay p wh ws (cAt p i) (dAt p k) r).singleMargin at z
    rw [(marginsDiffer p wh ws _ _ r).1,(marginsDiffer p wh ws _ _ r).2] at z
    obtain ⟨h0,h1⟩ := upper i k
    rcases z with z|z <;> grind only
  obtain ⟨s,s0,s1,ce⟩ := interpolateCoordinate p.cl c p.ch cl ch
  obtain ⟨t,t0,t1,de⟩ := interpolateCoordinate p.dl d p.dh dl dh
  have all := M.positiveOnRectangle p.cl p.ch p.dl p.dh s t s0 s1 t0 t1 (good false false)
    (good true false) (good false true) (good true true)
  rw [ce,de,eq] at all; grind only

end RankSeven.UpperInterior
#print axioms RankSeven.UpperInterior.positiveChord
#print axioms RankSeven.UpperInterior.rectangleOfCornerEstimates
