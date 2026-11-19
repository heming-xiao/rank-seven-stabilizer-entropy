import Rank7EndpointReserveSlots

namespace RankSeven.SharedTwoSlotReserve

open Lean.Grind Pauli ComplexScalar PauliReserveSlots OddCutReserve
open HeadPauliFourier ThreeLegFourier PhysicalFourierDefect
open PhysicalCompressionEffect (OrthonormalFrame)
open PhysicalPairedReduction (dagger)
open WeightedProbeShift (physicalPayment)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sqLe {x y : R} (xx : 0≤x) (le : x≤y) : x^2≤y^2 := by
  have z := OrderedRing.mul_nonneg (show 0≤y-x by grind only) (show 0≤y+x by grind only); grind only

/-- A weighted bound on the signed rank-three Pauli Fourier summand. -/
theorem localWeighted (r p a b e h q : R) (a0 : 0≤a) (a1 : a≤1) (rr : r^2≤1) (b0 : 0≤b)
    (ba : b≤a) (e0 : 0≤e) (odd : 1-p^2≤e) :
    h^2*q^2*(p^2*a-r^2*(a-b)+r*p*b)≤
      h^4*r^2*a+2*h^2*q^2*p^2*a+q^4*p^2*e := by
  let z := r*p*b-p^2*a
  let H := h^2
  let Q := q^2
  have rp := squareNonnegative r; have pp := squareNonnegative p
  have hh : 0≤H := squareNonnegative h; have qq : 0≤Q := squareNonnegative q
  have loss := OrderedRing.mul_nonneg rp (show 0≤a-b by grind only)
  have high : 0≤H^2*(r^2*a) := OrderedRing.mul_nonneg (squareNonnegative _) (OrderedRing.mul_nonneg rp a0)
  have low : 0≤Q^2*(p^2*e) := OrderedRing.mul_nonneg (squareNonnegative _) (OrderedRing.mul_nonneg pp e0)
  have hg : 0≤H*Q := OrderedRing.mul_nonneg hh qq
  have bound : H*Q*z≤H^2*(r^2*a)+Q^2*(p^2*e) := by
    by_cases zp : 0≤z
    · by_cases big : p^2≤r*p
      · have rp0 : 0≤r*p := by grind only
        have ra := OrderedRing.mul_le_mul_of_nonneg_left ba rp0
        have up : z≤(r*p-p^2)*a := by dsimp only [z]; grind only
        have sq := sqLe zp up
        have rp2 := OrderedRing.mul_nonneg pp (show 0≤1-r^2 by grind only)
        have rx := OrderedRing.mul_le_mul_of_nonneg_left odd rp
        have de : (r-p)^2≤r^2*e := by grind only
        have d1 := OrderedRing.mul_le_mul_of_nonneg_left a1 (squareNonnegative (r-p))
        rw [Semiring.mul_one] at d1
        have d2 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_trans d1 de) (OrderedRing.mul_nonneg pp a0)
        have prod : z^2≤(r^2*a)*(p^2*e) := by grind only
        have hyp := OrderedRing.mul_le_mul_of_nonneg_left prod (squareNonnegative (H*Q))
        have pos := squareNonnegative (H^2*(r^2*a)-Q^2*(p^2*e))
        have mult := OrderedRing.mul_nonneg high low
        by_cases done : H*Q*z≤H^2*(r^2*a)+Q^2*(p^2*e)
        · exact done
        · have adv : 0<H*Q*z-(H^2*(r^2*a)+Q^2*(p^2*e)) := by grind only
          have back : 0<H*Q*z+(H^2*(r^2*a)+Q^2*(p^2*e)) := by grind only
          have absurd := OrderedRing.mul_pos adv back
          grind only
      · have p1 := OrderedRing.mul_le_mul_of_nonneg_right (show r*p≤p^2 by grind only) b0
        have p2 := OrderedRing.mul_le_mul_of_nonneg_left ba pp
        have zz : z=0 := by dsimp only [z]; grind only
        rw [zz]; grind only
    · have neg := OrderedRing.mul_nonneg hg (show 0≤ -z by grind only); grind only
  have neg := OrderedRing.mul_nonneg hg loss
  dsimp only [H,Q,z] at bound neg
  grind only

theorem reserveAsLoss {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : OrthonormalFrame A) (i j : Fin 7) :
    2*reserve half A (cut i) (cut j)=half^n*sumOver (words n) (fun v => (coeff A (cut i) v)^2*cutLeak A j v) := by
  let di := half^n
  let d := (2:R)^n
  let c := coeff A (cut i)
  let l := cutLeak A j
  let z := neighborhood A (cut j)
  let ws := words n
  have point (v : Word n) : 2*(c v^2*z v)=d*(c v^2*l v) := by
    have f := neighborhoodFourier A orth (cut j) v
    change 2*z v=d*l v at f; have sc := congrArg (fun x => (c v)^2*x) f; grind only
  have eq := sumOverCongr ws point
  rw [←sumOverMulLeft,←sumOverMulLeft] at eq
  have inv : d*di=1 := SectorDefectAccounting.dimensionInverse half h2 n
  have sc := congrArg (fun x => di^2*x) eq
  have inv' := congrArg (fun x => (di*sumOver ws (fun v => (c v)^2*l v))*x) inv
  change 2*(di^2*sumOver ws (fun v => (c v)^2*z v))=di*sumOver ws (fun v => (c v)^2*l v)
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem coefficients {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (v : Word n) :
    coeff A (cut 0) v=head (localH A v) ∧ coeff A (cut 2) v=head (localH A v)+middle (localH A v) := by
  let M := FrameExteriorSector.framedWord A v
  have sc (i : Fin 7) : coeff A (cut i) v=sumOver labels (fun j => cut i j*(M j j).re) := by
    unfold coeff SymmetricDefect.traceWord
    rw [traceMatMulSwap,PhysicalDefectAssembly.pauliTraceEqSource]
    unfold trace
    rw [sumOverCongr _ (g:=fun j => ofReal (cut i j)*M j j) (fun j => PhysicalPairedReduction.diagonalAction _ (List.nodup_finRange 7) _ _ _ _ (List.mem_finRange j))]
    let ss (xs : List (Fin 7)) := (sumOver xs (fun j => ofReal (cut i j)*M j j)).re
    have red (xs : List (Fin 7)) : ss xs=sumOver xs (fun j => cut i j*(M j j).re) := by
      induction xs with
      | nil => rfl
      | cons j js ih =>
        change (ofReal (cut i j)*M j j+sumOver js _).re=_+sumOver js _
        rw [re_add,re_mul,re_ofReal,im_ofReal]; change _+ss js=_; rw [ih]; grind only
    exact red labels
  have xs : labels=[0,1,2,3,4,5,6] := by decide
  rw [sc,sc,xs]
  change _=(M 0 0).re ∧ _=(M 0 0).re+((M 1 1).re+(M 2 2).re)
  simp (config:={decide:=true}) [cut,sumOver] <;> grind only

/-- The two rank-cut leakages in the compressed three-by-three physical Pauli matrix. -/
theorem cutData {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R) (orth : OrthonormalFrame A) (v : Word n) :
    let H := localH A v
    let r := head H
    let u := middle H
    let a := cutLeak A 0 v
    let e := cutLeak A 2 v
    let b := crossWeight H
    a=1-r^2 ∧ e=a+middleLoss H-2*b ∧ 1-(r+u)^2≤e ∧ 0≤b ∧ b≤a := by
  let H := localH A v
  let M := FrameExteriorSector.framedWord A v
  let r := head H
  let u := middle H
  let a := cutLeak A 0 v
  let e := cutLeak A 2 v
  let b := crossWeight H
  let T := firstThree A
  have herm : dagger H=H := PhysicalOddLeakage.compressionHerm T v
  have comp := PhysicalOddLeakage.compressionComplement T v (topThreeOrth A orth)
  have sy (i j : Fin 3) : normSq (H i j)=normSq (H j i) := by
    have z := congrFun (congrFun herm j) i; change star (H i j)=H j i at z; rw [←z,normSq_star]
  have real := congrArg ComplexScalar.im (congrFun (congrFun herm 0) 0)
  change (star (H 0 0)).im=(H 0 0).im at real; rw [im_star] at real
  have im : (H 0 0).im=0 := by grind only
  have h00 : normSq (H 0 0)=r^2 := by unfold normSq; rw [im]; change _=(H 0 0).re^2; grind only
  have n3 : List.finRange 3=[0,1,2] := by decide
  have n7 : labels=[0,1,2,3,4,5,6] := by decide
  have addZ (x : R) : 0+x=x := by grind only
  have aa : a=1-r^2 := by
    change crossLoss (fun i j => normSq (M i j)) (cut 0) (cut 0)=_
    simp (config:={decide:=true}) only [crossLoss,n7,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,cut,↓reduceIte,
      Semiring.one_mul,Semiring.zero_mul,addZ,Semiring.add_zero]
    change 1-normSq (H 0 0)=_; rw [h00]
  have raw : e=3-sumOver (List.finRange 3) (fun i => sumOver (List.finRange 3) (fun j => normSq (H i j))) := by
    change crossLoss (fun i j => normSq (M i j)) (cut 2) (cut 2)=_
    simp (config:={decide:=true}) only [crossLoss,n7,n3,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,cut,↓reduceIte,
      Semiring.one_mul,Semiring.zero_mul,addZ,Semiring.add_zero]
    change _=3-(normSq (M 0 0)+(normSq (M 0 1)+normSq (M 0 2))+
      (normSq (M 1 0)+(normSq (M 1 1)+normSq (M 1 2))+(normSq (M 2 0)+(normSq (M 2 1)+normSq (M 2 2)))))
    grind only
  have ee : e=a+middleLoss H-2*b := by
    rw [raw,aa]; simp only [n3,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [h00,sy 0 1,sy 0 2]
    unfold middleLoss b crossWeight; grind only
  have loss := rankThreeTraceLoss H herm comp
  rw [←raw] at loss
  simp only [trace,n3,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,re_add,re_zero] at loss
  have col := columnContraction H comp 0
  simp only [n3,sumOver,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,h00] at col
  change a=1-r^2 ∧ e=a+middleLoss H-2*b ∧ 1-(r+u)^2≤e ∧ 0≤b ∧ b≤a
  refine ⟨aa,ee,?_,?_,?_⟩
  · dsimp only [r,u,head,middle]; grind only
  · have := normSq_nonnegative (H 1 0); have := normSq_nonnegative (H 2 0); unfold b crossWeight; grind only
  · unfold b crossWeight; grind only

private def avg {n : Nat} (half : R) (f : Word n → R) := half^n*sumOver (words n) f
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgAdd {n : Nat} (half : R) (f g : Word n → R) :
    avg half (fun x => f x+g x)=avg half f+avg half g := by unfold avg; rw [sumOverAdd]; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgSub {n : Nat} (half : R) (f g : Word n → R) :
    avg half (fun x => f x-g x)=avg half f-avg half g := by unfold avg; rw [Compression.sumOverSub]; grind only
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem avgMul {n : Nat} (half c : R) (f : Word n → R) :
    avg half (fun x => c*f x)=c*avg half f := by unfold avg; rw [←sumOverMulLeft]; grind only
private theorem avgLe {n : Nat} (half : R) (h2 : 2*half=1) (f g : Word n → R) (le : ∀ v,f v≤g v) :
    avg half f≤avg half g := by
  have non := Compression.sumOverNonnegative (words n) (fun v => g v-f v) (fun v _ => by have := le v; grind only)
  rw [Compression.sumOverSub] at non
  have hn (k : Nat) : 0≤half^k := by
    induction k with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
    | succ m ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  exact OrderedRing.mul_le_mul_of_nonneg_left (by grind only) (hn n)

/-- Weighted two-cut polarization on every physical frame. The argument uses the
physical rank-three trace loss and the equality of the two orientations of J₁₃. -/
theorem physicalTwoSlots (half : R) (h2 : 2*half=1) (k : Nat) (A : Basis (k+3) → Fin 7 → ComplexScalar R)
    (mu : Fin 7 → R) (orth : OrthonormalFrame A) (h q : R) :
    let K := (physicalPayment half h2 k A mu).kappa
    let J i j := reserve half A (cut i) (cut j)
    h^2*q^2*K≤2*h^4*J 0 0+4*h^2*q^2*J 0 2+2*q^4*J 2 2 := by
  let H := localH A
  let r v := head (H v)
  let u v := middle (H v)
  let p v := r v+u v
  let a := cutLeak A 0
  let e := cutLeak A 2
  let b v := crossWeight (H v)
  let l v := middleLoss (H v)
  let G v := (p v)^2*a v-(r v)^2*(a v-b v)+r v*p v*b v
  let J (i j : Fin 7) := reserve half A (cut i) (cut j)
  let K := (physicalPayment half h2 k A mu).kappa
  let E := avg (n:=k+3) half
  let Ra := E (fun v => (r v)^2*a v)
  let Pa := E (fun v => (p v)^2*a v)
  let Re := E (fun v => (r v)^2*e v)
  let Pe := E (fun v => (p v)^2*e v)
  let Rl := E (fun v => (r v)^2*l v)
  let Ua := E (fun v => (u v)^2*a v)
  let C := E (fun v => r v*u v*b v)
  have da (v : Word (k+3)) := cutData A orth v
  change ∀v,a v=1-(r v)^2 ∧ e v=a v+l v-2*b v ∧ 1-(p v)^2≤e v ∧ 0≤b v ∧ b v≤a v at da
  have rr (v : Word (k+3)) : coeff A (cut 0) v=r v := (coefficients A v).1
  have pp (v : Word (k+3)) : coeff A (cut 2) v=p v := (coefficients A v).2
  have ja := reserveAsLoss half h2 A orth 0 0
  have jb := reserveAsLoss half h2 A orth 2 0
  have jc := reserveAsLoss half h2 A orth 0 2
  have jd := reserveAsLoss half h2 A orth 2 2
  simp only [rr,pp] at ja jb jc jd
  change 2*J 0 0=Ra at ja; change 2*J 2 0=Pa at jb
  change 2*J 0 2=Re at jc; change 2*J 2 2=Pe at jd
  have sym : J 2 0=J 0 2 := reserveSwap half A _ _
  have ua : Ua=diagonalDefect half A := by
    unfold Ua E avg diagonalDefect; apply congrArg (fun x => half^(k+3)*x)
    apply sumOverCongr; intro v; rw [(da v).1]
  have kk : K=Ua+C := by
    rw [ua]; exact physicalFourierIdentity half h2 k A mu orth
  have loc : E (fun v => localDefect (H v))=Ua+Rl := by
    have pt (v : Word (k+3)) : localDefect (H v)=(u v)^2*a v+(r v)^2*l v := by rw [(da v).1]; rfl
    unfold E; simp only [pt,avgAdd]; rfl
  have both := localDefectSum half h2 A orth
  change E (fun v => localDefect (H v))=2*diagonalDefect half A at both
  rw [loc,←ua] at both
  have pol : E G=K := by
    have pt (v : Word (k+3)) : G v=r v*u v*b v+(p v)^2*a v-(r v)^2*e v+(r v)^2*l v := by
      rw [(da v).2.1]; unfold G p; grind only
    have a1 := congrArg E (funext pt)
    change E G=avg half (fun v => r v*u v*b v+(p v)^2*a v-(r v)^2*e v+(r v)^2*l v) at a1
    simp only [avgAdd,avgSub] at a1
    change E G=C+Pa-Re+Rl at a1
    grind only
  have pt (v : Word (k+3)) : h^2*q^2*G v≤h^4*((r v)^2*a v)+(2*h^2*q^2)*((p v)^2*a v)+q^4*((p v)^2*e v) := by
    have D := da v
    have ra := squareNonnegative (r v)
    have an := cutLeakNonnegative A orth v 0
    change 0≤a v at an
    have en := cutLeakNonnegative A orth v 2
    have w := localWeighted (r v) (p v) (a v) (b v) (e v) h q an (by grind only) (by grind only)
      D.2.2.2.1 D.2.2.2.2 en D.2.2.1
    unfold G; grind only
  have raw := avgLe half h2 _ _ pt
  simp only [avgMul,avgAdd] at raw
  change h^2*q^2*E G≤h^4*Ra+(2*h^2*q^2)*Pa+q^4*Pe at raw
  rw [pol,←ja,←jb,←jd,sym] at raw
  change h^2*q^2*K≤2*h^4*J 0 0+4*h^2*q^2*J 0 2+2*q^4*J 2 2
  grind only

end RankSeven.SharedTwoSlotReserve

#print axioms RankSeven.SharedTwoSlotReserve.localWeighted
#print axioms RankSeven.SharedTwoSlotReserve.reserveAsLoss
#print axioms RankSeven.SharedTwoSlotReserve.cutData
#print axioms RankSeven.SharedTwoSlotReserve.physicalTwoSlots

