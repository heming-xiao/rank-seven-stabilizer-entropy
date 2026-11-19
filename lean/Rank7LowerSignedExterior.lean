import Rank7LowerExteriorScale
namespace RankSeven.LowerSignedExterior
open Lean.Grind ExteriorCuts PackingDual UpperEndpoint UpperPhysicalInterior UpperFrameGain UpperFrameTrace LowerCorner
open LowerExteriorScale
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- In the real lower checker's units, the two last probabilities are c/b and 1/b. -/
noncomputable def gainAt (z y x b c w : R) (p : Prices R) (weights : Wedge7→R) :=
  (b*b)*corrected (spectrum z y x) weights p.lambda (LowerSignedPrices.mu z y x w)
    (LowerSignedPrices.cross z x) (c/b) (1/b)

theorem allTails (z y x b c f u w wa wb : R) (weights : Wedge7→R)
    (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4)
    (nx : ∀i,0≤weights i) (rows : RowsHold weights) (n0 : 0≤sharedExcess weights) (v0 : 0≤highExcess weights) :
    let p := realPrices z y x b f u w wa wb
    let m := LowerSignedPrices.mu z y x w
    let r := trueRay (sharedExcess weights) (highExcess weights) 0 0
    gainAt z y x b c w p weights≤lowerSplit z y x b c p.lambda m r ∧
    gainAt z y x b c w p weights≤lowerSingle z y x b c p.lambda m r := by
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have bp : 0<b := by grind only
  let p := realPrices z y x b f u w wa wb
  let m := LowerSignedPrices.mu z y x w
  let r := trueRay (sharedExcess weights) (highExcess weights) 0 0
  obtain ⟨ls,ys,ac⟩ := LowerSignedPrices.realCaps z y x b f u w wa wb z0 y0 xh (Std.le_trans cb.1 cb.2) fs us ws
  have es := LowerNormalizedSigned.normalizedBounds z y x p.lambda m (LowerSignedPrices.cross z x) weights (c/b) (1/b)
    z0 y0 xh (orderedRatios b c cb) nx rows n0 v0 ls ys ac
  have scal := rescaleBounds z y x b c p.lambda m r bp
  have sp := OrderedRing.mul_le_mul_of_nonneg_left es.1 (Std.le_of_lt (OrderedRing.mul_pos bp bp))
  have si := OrderedRing.mul_le_mul_of_nonneg_left es.2 (Std.le_of_lt (OrderedRing.mul_pos bp bp))
  exact ⟨Std.le_trans sp (Std.le_of_eq scal.1),Std.le_trans si (Std.le_of_eq scal.2)⟩

def endpoint (b : R) (right : Bool) : R := if right then b else 1
def payment (b : R) (p : Prices R) (right : Bool) (r : RealRay R) : R :=
  (p.shared+(if right then 0 else p.leftBonus))*r.peak+p.high*r.v+endpoint b right*p.cut*r.traceShared

theorem priceParts (z y x b f u w wa wb : R) (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (b1 : 1≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4) :
    let p := realPrices z y x b f u w wa wb
    let m := LowerSignedPrices.mu z y x w
    p.weightedDelta=y*(z+y+x)-m ∧
    p.completion=(z+y+x)*(y+x)*x-p.lambda*((y+x)+x)-m*x := by
  let p := realPrices z y x b f u w wa wb
  let m := LowerSignedPrices.mu z y x w
  let C := (z+y+x)*(y+x)*x-p.lambda*((y+x)+x)-m*x
  obtain ⟨ls,ys,_⟩ := LowerSignedPrices.realCaps z y x b f u w wa wb z0 y0 xh b1 fs us ws
  have one : (0:R)<1 := OrderedRing.zero_lt_one
  have xp : 0≤x := by grind only
  have g := OrderedRing.mul_nonneg z0 xp
  have d := OrderedRing.mul_nonneg y0 (show 0≤z+y+x by grind only)
  have cp : 0≤C := UpperCornerCompletion.completionPriceNonnegative z0 y0 xp
    (by change 2*p.lambda≤z*x; change 0≤p.lambda ∧ 707*p.lambda≤150*(z*x) at ls; grind only)
    (by change 2*m≤y*(z+y+x); change 0≤m ∧ 707*m≤175*(y*(z+y+x)) at ys; grind only)
  change (1-24*UpperEndpointPrices.invRate*w)*(y*(z+y+x))=y*(z+y+x)-m ∧
    UpperPrices.positivePart (x*(z+y+x)*(x+(1-24*UpperEndpointPrices.invRate*w)*y)-p.lambda*(y+2*x))=C
  have E : x*(z+y+x)*(x+(1-24*UpperEndpointPrices.invRate*w)*y)-p.lambda*(y+2*x)=C := by
    dsimp only [C,m,LowerSignedPrices.mu]; grind only
  rw [E]; refine ⟨?_,?_⟩
  · dsimp only [m,LowerSignedPrices.mu]; grind only
  · simp [UpperPrices.positivePart,cp]

omit [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- The literal two checker margins are payment minus their respective signed bounds. -/
theorem leafIdentity (z y x b w c tr n v : R) (p : Prices R) (right : Bool)
    (endpt : c=endpoint b right)
    (wd : p.weightedDelta=y*(z+y+x)-LowerSignedPrices.mu z y x w)
    (cp : p.completion=(z+y+x)*(y+x)*x-p.lambda*((y+x)+x)-LowerSignedPrices.mu z y x w*x)
    (head : p.h=z*(x-1)-3*x-5/2) (xb : p.xOverB=x/b) (bs : p.bSquare=b*b) :
    let m := LowerSignedPrices.mu z y x w
    let r := trueRay n v 0 0
    let r' := realRay n v tr
    let e := realLeafPair z y x b p right r'
    e.1=payment b p right r'-lowerSplit z y x b c p.lambda m r ∧
    e.2=payment b p right r'-lowerSingle z y x b c p.lambda m r := by
  let m := LowerSignedPrices.mu z y x w
  let r := trueRay n v 0 0
  let r' := realRay n v tr
  let endc := endpoint b right
  let S := p.shared+(if right then 0 else p.leftBonus)
  let G := UpperEndpoint.smaller p.xOverB (endc*b*p.completion)
  let common := S*r.peak+p.high*v+p.weightedDelta*((b-1)*(endc-1)*r.tail-v)+endc*p.lambda*n
  let costs := S*r.peak+p.high*v+endc*p.cut*tr
  change common+(endc*p.cut*tr+endc*(y*v-p.h*n))=costs-lowerSplit z y x b c p.lambda m r ∧
    common+(endc*p.cut*tr+endc*(z*(r.m-x*n)+(2*y+3*x)*r.m)+r.constant/p.bSquare)+G*r.improvement=
      costs-lowerSingle z y x b c p.lambda m r
  change c=endc at endpt; subst c
  dsimp only [common,costs,G,lowerSplit,lowerSingle]
  rw [wd,cp,head,xb,bs]
  have nv : r.n=n := rfl
  have vv : r.v=v := rfl
  rw [nv,vv]
  dsimp only [m]; constructor <;> grind only

theorem physicalLeaf (z y x b f u w wa wb tr : R) (right : Bool)
    (half : R) (unit : 2*half=1) (k : Nat) (A : Pauli.Basis (k+3)→Fin 7→ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤sharedExcess (PackingPolynomial.physicalWeights half unit k A))
    (v0 : 0≤highExcess (PackingPolynomial.physicalWeights half unit k A))
    (res : LowerContractor.Residual z y x b) (b1 : 1≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4) :
    let weights := PackingPolynomial.physicalWeights half unit k A
    let n := sharedExcess weights; let v := highExcess weights
    let p := realPrices z y x b f u w wa wb
    let r := realRay n v tr
    let margin := payment b p right r-gainAt z y x b (endpoint b right) w p weights
    let checked := realLeafPair z y x b p right r
    checked.1≤margin ∧ checked.2≤margin := by
  let weights := PackingPolynomial.physicalWeights half unit k A
  let p := realPrices z y x b f u w wa wb
  let r := realRay (sharedExcess weights) (highExcess weights) tr
  obtain ⟨nx,rows⟩ := PackingPolynomial.physicalRows half unit k A orth
  have cb : 1≤endpoint b right ∧ endpoint b right≤b := by cases right <;> dsimp [endpoint] <;> grind only
  have bound := allTails z y x b _ f u w wa wb weights res.zNonnegative res.yNonnegative res.xHead cb fs us ws nx rows n0 v0
  obtain ⟨wd,cp⟩ := priceParts z y x b f u w wa wb res.zNonnegative res.yNonnegative res.xHead b1 fs us ws
  have e := leafIdentity z y x b w _ tr (sharedExcess weights) (highExcess weights) p right rfl wd cp rfl rfl rfl
  have monotone (A B C : R) (h : A≤B) : C-B≤C-A := by grind only
  exact ⟨Std.le_trans (Std.le_of_eq e.1) (monotone _ _ _ bound.1),Std.le_trans (Std.le_of_eq e.2) (monotone _ _ _ bound.2)⟩

end RankSeven.LowerSignedExterior
#print axioms RankSeven.LowerSignedExterior.allTails
#print axioms RankSeven.LowerSignedExterior.priceParts
#print axioms RankSeven.LowerSignedExterior.leafIdentity
#print axioms RankSeven.LowerSignedExterior.physicalLeaf