import Rank7PhysicalOddLeakage

/-! The three-leg compressed Pauli bound for Fourier localization. -/
namespace RankSeven.ThreeLegFourier
open Lean.Grind Pauli ComplexScalar OddTensorUncertainty SlaterAlternant SlaterUnionBound
open PhysicalPairedReduction (dagger)
open PhysicalOddLeakage (word compression)
open PauliPairContraction (image normSum)
variable {R α β γ : Type} [CommRing R]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem determinantGramNonnegative {m : Nat} {H : Mx (Fin m) R} (gram : Gram H) :
    0≤(determinant m H).re := by
  let xs := indices (List.finRange m) m
  let z := slater (C:=ComplexScalar R) m
  let M := matrix H m
  let d := determinant m H
  have lifted : Gram M := by
    obtain ⟨a,rows,F,eq⟩ := gram
    refine ⟨Sites a m,indices rows m,matrix F m,?_⟩
    unfold M; rw [matrixDagger,matrixComp,eq]
  have n := energyNonnegative xs lifted z
  have v : energy xs M z=normSum xs z*d.re :=
    energyEigen xs M z d (fun i _ _ => topEigenvector m H i)
  rw [v] at n
  have pos : 0<normSum xs z := slaterMassPositive m
  apply Classical.byContradiction; intro bad
  have a := OrderedRing.mul_pos pos (show 0< -d.re by change ¬0≤d.re at bad; grind only); grind only

theorem determinantScale {m : Nat} (c : ComplexScalar R) (H : Mx (Fin m) R) :
    determinant m (fun i j => c*H i j)=c^m*determinant m H := by
  let xs := indices (List.finRange m) m
  let z := slater (C:=ComplexScalar R) m
  let a := canonical m
  have k := topEigenvector m (fun i j => c*H i j) a
  have h := topEigenvector m H a
  have ca : z a=1 := canonicalValue m
  change sumOver xs (fun j => matrix (fun i j => c*H i j) m a j*z j)=z a*_ at k
  change sumOver xs (fun j => matrix H m a j*z j)=z a*determinant m H at h
  rw [ca,Semiring.one_mul] at k h
  rw [←k,←h,sumOverMulLeft]; apply sumOverCongr; intro j; rw [matrixScale]; grind only

end Order

variable {C : Type} [CommRing C]

def detThree (A : Fin 3 → Fin 3 → C) := A 0 0*(A 1 1*A 2 2-A 1 2*A 2 1)-
  A 0 1*(A 1 0*A 2 2-A 1 2*A 2 0)+A 0 2*(A 1 0*A 2 1-A 1 1*A 2 0)

theorem determinantThree (A : Fin 3 → Fin 3 → C) : determinant 3 A=detThree A := by
  have L : List.finRange 3=[0,1,2] := by decide
  unfold determinant; rw [L]; simp only [push,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  let sign (i j : Fin 3) : C := if i<j then 1 else if j<i then -1 else 0
  have three (i j k : Fin 3) : orientation (C:=C) [i,j,k]=(sign i j*(sign i k*1))*((sign j k*1)*(1*1)) := rfl
  simp (config := {decide := true}) only [three,sign,ite_true,ite_false]
  unfold detThree; grind only

def shift (H : Mx (Fin m) R) (s : Bool) (i j : Fin m) : ComplexScalar R :=
  ident i j+(if s then 1 else -1)*H i j

private theorem identityLeft {m : Nat} (H : Mx (Fin m) R) :
    matMul (List.finRange m) ident H=H := by
  funext i j; change sumOver _ (fun k => ident i k*H k j)=_
  rw [←ExteriorPauliBase.sumOnIndex (List.finRange m) i (fun k => H k j) (List.nodup_finRange m) (List.mem_finRange i)]
  apply sumOverCongr; intro k; by_cases h : i=k <;> simp only [ident,h,ite_true,ite_false,Semiring.zero_mul,Semiring.one_mul]

private theorem identityRight {m : Nat} (H : Mx (Fin m) R) :
    matMul (List.finRange m) H ident=H := by
  funext i j; change sumOver _ (fun k => H i k*ident k j)=_
  rw [←ExteriorPauliBase.sumOnIndex (List.finRange m) j (H i) (List.nodup_finRange m) (List.mem_finRange j)]
  apply sumOverCongr; intro k; by_cases h : j=k
  · subst k; simp only [ident,ite_true,Semiring.mul_one]
  · have ne : k≠j := fun e => h e.symm
    simp only [ident,h,ne,ite_false,Semiring.mul_zero]

private theorem hermitianIdentity {m : Nat} : dagger (ident (R:=R) (α:=Fin m))=ident := by
  funext i j; change star (ident j i)=ident i j
  by_cases h : i=j
  · subst j; simp only [ident,ite_true]; apply ComplexScalar.ext <;> simp <;> grind only
  · have z : j≠i := fun e => h e.symm
    simp only [ident,h,z,ite_false]; apply ComplexScalar.ext <;> simp <;> grind only

theorem shiftGram {m : Nat} (H : Mx (Fin m) R) (herm : dagger H=H)
    (comp : Gram (fun i j => ident i j-matMul (List.finRange m) (dagger H) H i j)) (b : Bool) :
    Gram (fun i j => (2:ComplexScalar R)*shift H b i j) := by
  let xs := List.finRange m
  let S := shift H b
  let k : ComplexScalar R := if b then 1 else -1
  have realK : star k=k := by cases b <;> dsimp only [k] <;> apply ComplexScalar.ext <;> simp <;> grind only
  have ksq : k*k=1 := by cases b <;> dsimp only [k] <;> grind only
  have sh : dagger S=S := by
    funext i j
    have e := congrFun (congrFun herm i) j
    have id := congrFun (congrFun (hermitianIdentity (R:=R) (m:=m)) i) j
    change star (H j i)=H i j at e; change star (ident j i)=ident i j at id
    change star (ident j i+k*H j i)=ident i j+k*H i j
    rw [star_add,star_mul,realK,e,id]
  have sq : Gram (matMul xs (dagger S) S) := ⟨Fin m,xs,S,rfl⟩
  have add := gramAdd sq comp
  change Gram (fun i j => 2*S i j)
  apply Eq.mp (congrArg Gram (show (fun i j => matMul xs (dagger S) S i j+(ident i j-matMul xs (dagger H) H i j))=(fun i j => 2*S i j) from ?_)) add
  funext i j; rw [sh,herm]
  have expand (a) : S i a*S a j=ident i a*ident a j+k*(ident i a*H a j)+k*(H i a*ident a j)+H i a*H a j := by
    change (ident i a+k*H i a)*(ident a j+k*H a j)=_
    have v := congrArg (fun z => z*(H i a*H a j)) ksq; grind only
  change sumOver xs (fun a => S i a*S a j)+_=_
  rw [sumOverCongr xs expand]; simp only [sumOverAdd,←sumOverMulLeft]
  change matMul xs ident ident i j+k*matMul xs ident H i j+k*matMul xs H ident i j+matMul xs H H i j+(ident i j-matMul xs H H i j)=2*(ident i j+k*H i j)
  rw [identityLeft,identityLeft,identityRight]; grind only

section Physical
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem rankThreeTraceLoss (H : Mx (Fin 3) R) (herm : dagger H=H)
    (comp : Gram (fun i j => ident i j-matMul (List.finRange 3) (dagger H) H i j)) :
    1-(trace (List.finRange 3) H).re^2≤3-
      sumOver (List.finRange 3) (fun i => sumOver (List.finRange 3) (fun j => normSq (H i j))) := by
  let xs := List.finRange 3
  have non (b : Bool) : 0≤(determinant 3 (shift H b)).re := by
    have h := determinantGramNonnegative (shiftGram H herm comp b)
    rw [determinantScale] at h
    have e : (2:ComplexScalar R)^3=ofReal (8:R) := by
      have pure : (2:ComplexScalar R)=ofReal (2:R) := rfl
      rw [pure,←PhysicalPairedReduction.realEmbeddingPow]; apply congrArg ofReal; grind only
    rw [e] at h; simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul] at h; grind only
  let T := trace xs H
  let F := trace xs (matMul xs H H)
  have L : xs=[0,1,2] := by decide
  have traceId : determinant 3 (shift H true)+determinant 3 (shift H false)=2+T^2-F := by
    rw [determinantThree,determinantThree]
    unfold detThree T F trace matMul
    simp (config:={decide:=true}) only [shift,ident,ite_true,ite_false,L,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    grind only
  have trHerm : star T=T := by
    unfold T trace; rw [ComplexExterior.starSumOver]
    apply sumOverCongr; intro i; exact congrFun (congrFun herm i) i
  have ti := congrArg ComplexScalar.im trHerm; rw [im_star] at ti
  have im : T.im=0 := by grind only
  have tSq : (T^2).re=T.re^2 := by rw [Semiring.pow_two,re_mul,im]; grind only
  have fr : F.re=sumOver xs (fun i => sumOver xs (fun j => normSq (H i j))) := by
    unfold F trace matMul
    have reSum (f : Fin 3 → ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
      rw [L]; simp [sumOver]
    rw [reSum]; apply sumOverCongr; intro i; rw [reSum]; apply sumOverCongr; intro j
    have e := congrFun (congrFun herm j) i
    change star (H i j)=H j i at e
    rw [←e,show H i j*star (H i j)=star (H i j)*H i j by grind only,re_star_mul_self]
  have id := congrArg ComplexScalar.re traceId
  simp only [re_add,re_sub,tSq,fr] at id
  have c : (2:ComplexScalar R).re=(2:R) := rfl
  rw [c] at id
  have hp := non true; have hm := non false
  change 1-T.re^2≤3-sumOver xs (fun i => sumOver xs (fun j => normSq (H i j))); grind only

theorem physicalThreeTrace {n : Nat} (A : Basis n → Fin 3 → ComplexScalar R)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) (p : Word n) :
    let H := compression A p
    1-(trace (List.finRange 3) H).re^2≤3-sumOver (List.finRange 3)
      (fun i => sumOver (List.finRange 3) (fun j => normSq (H i j))) :=
  rankThreeTraceLoss _ (PhysicalOddLeakage.compressionHerm A p) (PhysicalOddLeakage.compressionComplement A p orth)

/-- For negative head/middle Pauli signs, x and y are the magnitudes
of their two traces. Outside the half-squared-expectation stabilizer
threshold, the rational coefficient 11/15 suffices for coarse rounding. -/
theorem negativeCrossBound (x y b a l : R) (xn : 0≤x) (yn : 0≤y) (bn : 0≤b) (an : 0≤a) (ln : 0≤l)
    (residual : a=1-x^2-b) (oddLoss : 1-(y-x)^2≤a+l) :
    let D := y^2*(b+a)+x^2*(b+l)
    10*x*y*b≤4*D ∧ (2*x^2≤1 → 30*x*y*b≤11*D) := by
  let D := y^2*(b+a)+x^2*(b+l)
  have x2 := squareNonnegative x; have y2 := squareNonnegative y
  have u := OrderedRing.mul_nonneg y2 an
  have v := OrderedRing.mul_nonneg x2 ln
  have base : (x^2+y^2)*b≤D := by unfold D; grind only
  by_cases low : y≤2*x
  · have q := OrderedRing.mul_nonneg yn (show 0≤2*x-y by grind only)
    have floor : b≤l := by grind only
    have extra := OrderedRing.mul_nonneg x2 (show 0≤l-b by grind only)
    have cost : (2*x^2+y^2)*b≤D := by unfold D; grind only
    have f := squareNonnegative (11*y-15*x)
    have m := OrderedRing.mul_nonneg (show 0≤11*(2*x^2+y^2)-30*x*y by grind only) bn
    have d0 := OrderedRing.mul_nonneg (show 0≤2*x^2+y^2 by grind only) bn
    change 10*x*y*b≤4*D ∧ (_ → 30*x*y*b≤11*D)
    exact ⟨by grind only,fun _ => by grind only⟩
  · have high : 2*x≤y := by grind only
    have q := OrderedRing.mul_nonneg (show 0≤2*y-x by grind only) (show 0≤2*y-4*x by grind only)
    have m := OrderedRing.mul_nonneg (show 0≤4*(x^2+y^2)-10*x*y by grind only) bn
    change 10*x*y*b≤4*D ∧ (2*x^2≤1 → 30*x*y*b≤11*D)
    refine ⟨by grind only,?_⟩; intro hx
    by_cases over : 7*x≤3*y
    · have f := OrderedRing.mul_nonneg (show 0≤3*y-7*x by grind only) (show 0≤33*y-13*x by grind only)
      have g := OrderedRing.mul_nonneg (show 0≤11*(x^2+y^2)-30*x*y by grind only) bn
      grind only
    · have yy := OrderedRing.mul_nonneg (show 0≤7*x-3*y by grind only) (show 0≤3*(y-x)+4*x by grind only)
      have order := OrderedRing.mul_nonneg yn (show 0≤y-2*x by grind only)
      have mod := OrderedRing.mul_nonneg (show 0≤1-2*x^2 by grind only) (show 0≤(y-x)^2-x^2 by grind only)
      have slack := OrderedRing.mul_nonneg (show 0≤2*x^2-(y-x)^2 by grind only) (show 0≤1-x^2-b by grind only)
      have odd := OrderedRing.mul_le_mul_of_nonneg_left oddLoss x2
      have monotone := OrderedRing.mul_nonneg (show 0≤y^2-x^2 by
        have m := OrderedRing.mul_nonneg (show 0≤y-x by grind only) (show 0≤y+x by grind only); grind only) an
      have strong : (2*x^2+2*x*y)*b≤D := by unfold D; grind only
      have ratio := OrderedRing.mul_nonneg xn (show 0≤22*x-8*y by grind only)
      have p := OrderedRing.mul_nonneg (show 0≤11*(2*x^2+2*x*y)-30*x*y by grind only) bn
      grind only

def head (H : Mx (Fin 3) R) := (H 0 0).re
def middle (H : Mx (Fin 3) R) := (H 1 1).re+(H 2 2).re
def crossWeight (H : Mx (Fin 3) R) := normSq (H 1 0)+normSq (H 2 0)
def middleLoss (H : Mx (Fin 3) R) :=
  2-(normSq (H 1 1)+normSq (H 1 2)+normSq (H 2 1)+normSq (H 2 2))
def localDefect (H : Mx (Fin 3) R) :=
  (middle H)^2*(1-(head H)^2)+(head H)^2*middleLoss H

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem reSum (xs : List α) (f : α → ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => change (f i+sumOver xs f).re=_; rw [re_add,ih]; rfl

theorem columnContraction {m : Nat} (H : Mx (Fin m) R)
    (comp : Gram (fun i j => ident i j-matMul (List.finRange m) (dagger H) H i j)) (i : Fin m) :
    sumOver (List.finRange m) (fun j => normSq (H j i))≤1 := by
  obtain ⟨a,xs,F,e⟩ := comp
  have q := congrArg ComplexScalar.re (congrFun (congrFun e i) i)
  change (ident i i-sumOver (List.finRange m) (fun j => star (H j i)*H j i)).re=
    (sumOver xs (fun j => star (F j i)*F j i)).re at q
  simp only [ident,ite_true,re_sub,re_one,reSum,re_star_mul_self] at q
  have nn := Compression.sumOverNonnegative xs (fun j => normSq (F j i)) (fun _ _ => normSq_nonnegative _)
  grind only

/-- Applied to the actual two middle legs and the true leading column,
the signed Fourier cross term has the global 4/5 loss bound and the
strictly better 11/15 bound off the commuting large-expectation set. -/
theorem physicalLocalPrices {n : Nat} (A : Basis n → Fin 3 → ComplexScalar R)
    (orth : matMul (qubitIndices n) (dagger A) A=ident) (p : Word n) :
    let H := compression A p
    let C := head H*middle H*crossWeight H
    0≤localDefect H ∧ -4*localDefect H≤10*C ∧ (2*(head H)^2≤1 → -11*localDefect H≤30*C) := by
  let H := compression A p
  let r := head H
  let u := middle H
  let b := crossWeight H
  let a := 1-r^2-b
  let l := middleLoss H-b
  let D := localDefect H
  have herm := PhysicalOddLeakage.compressionHerm A p
  change dagger H=H at herm
  have comp := PhysicalOddLeakage.compressionComplement A p orth
  have d (i : Fin 3) := columnContraction H comp i
  have N : List.finRange 3=[0,1,2] := by decide
  have sy (i j : Fin 3) : normSq (H i j)=normSq (H j i) := by
    have z := congrFun (congrFun herm j) i; change star (H i j)=H j i at z; rw [←z,normSq_star]
  have re (i : Fin 3) : (H i i).im=0 := by
    have z := congrArg ComplexScalar.im (congrFun (congrFun herm i) i)
    change (star (H i i)).im=(H i i).im at z; rw [im_star] at z; grind only
  have sq : normSq (H 0 0)=r^2 := by unfold normSq r head; rw [re]; grind only
  have d0 := d 0; have d1 := d 1; have d2 := d 2
  simp only [N,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,sq] at d0 d1 d2
  rw [sy 0 1] at d1; rw [sy 0 2] at d2
  have bn : 0≤b := by have := normSq_nonnegative (H 1 0); have := normSq_nonnegative (H 2 0); unfold b crossWeight; grind only
  have an : 0≤a := by unfold a b crossWeight; grind only
  have ln : 0≤l := by unfold l b crossWeight middleLoss; grind only
  have ht := rankThreeTraceLoss H herm comp
  simp only [trace,N,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,re_add,re_zero,sq] at ht
  rw [sy 0 1,sy 0 2] at ht
  have q : 1-(u+r)^2≤a+l := by dsimp only [a,l,b,r,u,head,middle,middleLoss,crossWeight,H] at ht ⊢; grind only
  have cost : D=u^2*(b+a)+r^2*(b+l) := by dsimp only [D,localDefect,r,u,l,a]; grind only
  have dx := OrderedRing.mul_nonneg (squareNonnegative u) (show 0≤b+a by grind only)
  have dy := OrderedRing.mul_nonneg (squareNonnegative r) (show 0≤b+l by grind only)
  have dn : 0≤D := by grind only
  have z (x y : R) (xn : 0≤x) (yn : 0≤y) (xx : x^2=r^2) (yy : y^2=u^2)
      (prod : x*y= -(r*u)) (loss : (y-x)^2=(u+r)^2) :
      -4*D≤10*(r*u*b) ∧ (2*r^2≤1 → -11*D≤30*(r*u*b)) := by
    have h := negativeCrossBound x y b a l xn yn bn an ln (by unfold a; grind only) (by grind only)
    have w := congrArg (fun k => k*b) prod
    simp only [xx,yy] at h; grind only
  change 0≤D ∧ -4*D≤10*(r*u*b) ∧ (2*r^2≤1 → -11*D≤30*(r*u*b))
  refine ⟨dn,?_⟩
  by_cases pos : 0≤r*u
  · have nn := OrderedRing.mul_nonneg pos bn; exact ⟨by grind only,fun _ => by grind only⟩
  · by_cases first : 0≤r
    · have t : 0≤ -u := by by_cases h : 0≤u; have := OrderedRing.mul_nonneg first h; grind only; grind only
      exact z r (-u) first t rfl (by grind only) (by grind only) (by grind only)
    · have xn : 0≤ -r := by grind only
      have yn : 0≤u := by
        by_cases h : 0≤u; exact h
        have := OrderedRing.mul_nonneg xn (show 0≤ -u by grind only); grind only
      exact z (-r) u xn yn (by grind only) rfl (by grind only) (by grind only)

end Physical

end RankSeven.ThreeLegFourier

#print axioms RankSeven.ThreeLegFourier.determinantGramNonnegative
#print axioms RankSeven.ThreeLegFourier.determinantThree
#print axioms RankSeven.ThreeLegFourier.shiftGram
#print axioms RankSeven.ThreeLegFourier.rankThreeTraceLoss
#print axioms RankSeven.ThreeLegFourier.physicalThreeTrace
#print axioms RankSeven.ThreeLegFourier.negativeCrossBound
#print axioms RankSeven.ThreeLegFourier.physicalLocalPrices

