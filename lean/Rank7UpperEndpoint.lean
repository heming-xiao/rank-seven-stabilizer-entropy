import Rank7UpperSupportEnclosure
import Rank7UpperReplay

/-! Interval and real evaluations of the upper C++ corner table. Each
arithmetic expression is shared by the two evaluations. -/
namespace RankSeven.UpperEndpoint
open Lean.Grind Interval UpperCorner UpperContractor
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

structure Arithmetic (T : Type) where
  whole : Nat→T
  fraction : (n d : Nat)→0<d→T
  byNat : T→(d : Nat)→0<d→T
  square : T→T
  pos : T→T
  largest : T→T→T
  smallest : T→T→T
  support : T→T→T→T

def gridArithmetic : Arithmetic Bounds :=
  ⟨whole cppGrid,fun n d _ => Bounds.rational cppGrid n d,fun a d _ => Bounds.div cppGrid a (whole cppGrid d),
    Bounds.square cppGrid,Bounds.positivePart,Bounds.largest,Bounds.smallest,UpperSupportEnclosure.price⟩

noncomputable def smaller (a b : R) : R := by classical exact if a≤b then a else b

noncomputable def realArithmetic : Arithmetic R :=
  ⟨fun n => OfNat.ofNat n,fun n d _ => OfNat.ofNat n/OfNat.ofNat d,fun a d _ => a/OfNat.ofNat d,
    fun a => a*a,UpperPrices.positivePart,UpperWeighted.larger,smaller,UpperPrices.supportValue⟩

structure Tracked (R : Type) [Field R] [LE R] where
  interval : Bounds
  real : R
  encloses : interval.Contains cppGrid real

local instance : Add Bounds := ⟨Bounds.add⟩
local instance : Sub Bounds := ⟨Bounds.sub⟩
local instance : Mul Bounds := ⟨Bounds.mul cppGrid⟩

local instance : Add (Tracked R) := ⟨fun a b => ⟨a.interval+b.interval,a.real+b.real,Bounds.addSound a.encloses b.encloses⟩⟩
local instance : Sub (Tracked R) := ⟨fun a b => ⟨a.interval-b.interval,a.real-b.real,Bounds.subSound a.encloses b.encloses⟩⟩
local instance : Mul (Tracked R) := ⟨fun a b => ⟨a.interval*b.interval,a.real*b.real,Bounds.mulSound a.encloses b.encloses⟩⟩

noncomputable def trackedArithmetic : Arithmetic (Tracked R) where
  whole n := ⟨_,_,wholeSound cppGrid n⟩
  fraction n d hd := ⟨_,_,fractionSound cppGrid n d hd⟩
  byNat a d hd := ⟨_,_,divSound a.encloses (wholeSound cppGrid d) (by
    change 0<Int.ofNat d*cppGrid.scale
    exact Int.mul_pos (Int.ofNat_lt.mpr hd) cppGrid.positive)⟩
  square a := ⟨_,_,Bounds.squareSound a.encloses⟩
  pos a := ⟨_,_,UpperSupportEnclosure.clipped a.encloses⟩
  largest a b := ⟨_,_,UpperWeighted.largerSound a.encloses b.encloses⟩
  smallest a b := ⟨_,smaller a.real b.real,Bounds.smallestSound a.encloses b.encloses (by unfold smaller; split <;> grind only)⟩
  support a b w := ⟨_,_,UpperSupportEnclosure.priceEnclosed a.encloses b.encloses w.encloses⟩

private def checkedDiv (a b : Bounds) : Option Bounds :=
  if 0<b.lo then some (Bounds.div cppGrid a b) else none

def pick (a b : Bounds) : Option Bounds := do
  let result ← checkedDiv (a-b).positivePart (a+b)
  return Bounds.point result.lo

theorem pickChecked (a b : Bounds) : pick a b=UpperSupportEnclosure.checkedWeight a b := by
  unfold pick checkedDiv UpperSupportEnclosure.checkedWeight
  dsimp only
  by_cases hp : 0<(a.add b).lo
  · simp [show 0<(a+b).lo from hp,hp]; rfl
  · simp [show ¬0<(a+b).lo from hp,hp]

private theorem checkedQuotient {a b out : Bounds} {x y : R}
    (ha : a.Contains cppGrid x) (hb : b.Contains cppGrid y) (pass : checkedDiv a b=some out) :
    out.Contains cppGrid (x/y) := by
  unfold checkedDiv at pass; split at pass
  · obtain rfl := (Option.some.inj pass).symm; exact divSound ha hb ‹_›
  · contradiction

structure Head (T : Type) where
  y : T
  g : T
  delta : T
  linear : T
  pair : T
  highInside : T
  lowOutside : T
  k2 : T
  g2 : T
  d2 : T
  anti : T
  psi : T
  oddDen : T
  cubic : T
  headGap : T
  tax : T
  clipped : T
  den : T

def head {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T)
    (h k q cl ch dl dh f : T) : Head T :=
  let x := h + k + q
  let y := k + q
  let g := h * q
  let delta := k * x
  let linear := h + (op.whole 2) * k + (op.whole 3) * q
  let alpha := (op.whole 1) + x
  let beta := (op.whole 1) + y
  let gamma := (op.whole 1) + q
  let pair := alpha * gamma
  let highInside := alpha * beta
  let lowOutside := (op.largest alpha (beta * gamma))
  let h2 := (op.square h)
  let q2 := (op.square q)
  let k2 := (op.square k)
  let g2 := (op.square g)
  let d2 := (op.square delta)
  let anti := k2 * (k2 + (op.byNat (h2 + q2) 2 (by decide)))
  let psiTail := (op.largest (op.fraction 1 13 (by decide)) ((op.square (op.pos (cl - dh))) + (op.byNat ((op.square ((op.whole 1) - ch)) + (op.square dl)) 6 (by decide))))
  let psi := (op.byNat (h2 + q2) 6 (by decide)) + psiTail
  let oddDen := h2 + (op.whole 3) * q2
  let cubic := x * y * q
  let headGap := g - h - (op.whole 3) * q - (op.fraction 5 2 (by decide))
  let tax := ((op.whole 1) - f) * (op.fraction 200 11 (by decide))
  let clipped := (op.pos (g - tax * (ch - dl)))
  let den := psi + (op.whole 12) * (op.square f)
  ⟨y,g,delta,linear,pair,highInside,lowOutside,k2,g2,d2,anti,psi,oddDen,cubic,headGap,tax,clipped,den⟩

structure Common (T : Type) where
  shift : T
  lambda : T
  sharedQuad : T
  residual : T
  completion : T
  highQuad : T

def common {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T)
    (q u w invRate qinv clipped delta cubic y d2 anti : T) : Common T :=
  let shift := u * clipped * qinv
  let lambda := (op.whole 24) * invRate * shift
  let sharedQuad := (op.whole 12) * u * ((op.whole 2) - u) * (op.square clipped) * qinv
  let mu := (op.whole 24) * invRate * w * delta
  let residual := delta - mu
  let completion := (op.pos (cubic - lambda * (y + q) - mu * q))
  let highQuad := (op.whole 12) * w * ((op.whole 2) - w) * d2 + anti
  ⟨shift,lambda,sharedQuad,residual,completion,highQuad⟩

structure Corner (T : Type) where
  dsq : T
  cd : T
  odd : T
  tailPrefix : T
  spread : T
  one : T
  shared : T

def corner {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T)
    (c d ch dl highInside pair lowOutside wh ws : T) : Corner T :=
  let dsq := (op.square d)
  let cd := c * d
  let odd := ((op.whole 1) - ch) * ((op.whole 1) + ch - (op.whole 2) * c) + dl * ((op.whole 2) * d - dl)
  let tailPrefix := ((op.whole 1) - d) * (c - d)
  let spread := c - d
  let one := (op.support (highInside * cd) pair wh)
  let shared := c * (op.support (pair * d) lowOutside ws)
  ⟨dsq,cd,odd,tailPrefix,spread,one,shared⟩

structure Charges (T : Type) where
  physicalShared : T
  physicalHigh : T
  increment : T
  singleton : T
  splitDebit : T
  singleDebit : T

def charges {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T)
    (g2 sharedQuad shift tax ch dl spread oddShared invRate highQuad odd k2 invGeom dsq d q c completion cd linear headGap lambda g : T) : Charges T :=
  let physicalShared := (op.byNat ((g2 + sharedQuad + (op.whole 24) * shift * tax * (ch - dl - spread) + oddShared) * invRate) 12 (by decide))
  let physicalHigh := (highQuad + (op.byNat (odd * k2) 2 (by decide))) * invRate * invGeom
  let increment := (op.smallest (dsq * d * q) (c * completion))
  let singleton := cd * linear
  let splitDebit := cd * (headGap - lambda)
  let singleDebit := cd * (g - lambda)
  ⟨physicalShared,physicalHigh,increment,singleton,splitDebit,singleDebit⟩

structure Leaf (T : Type) where
  splitMargin : T
  singleMargin : T

def leaf {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T)
    (invRate one traceOne shared traceShared physicalShared peak physicalHigh v residual tailPrefix tail dsq cd k splitDebit n singleton m constant increment improvement singleDebit : T) : Leaf T :=
  let cuts := (op.whole 96) * invRate * (one * traceOne + shared * traceShared)
  let base := physicalShared * peak + physicalHigh * v + cuts + residual * (tailPrefix * tail - dsq * v)
  let splitMargin := base + cd * k * v - splitDebit * n
  let singleMargin := base + singleton * m + (op.square dsq) * constant + increment * improvement - singleDebit * n
  ⟨splitMargin,singleMargin⟩

structure Inputs (T : Type) where
  h : T
  k : T
  q : T
  cl : T
  ch : T
  dl : T
  dh : T
  f : T
  u : T
  w : T

def gridInputs (box : TailBox) (s : Shifts) : Inputs Bounds :=
  ⟨box.h,box.k,box.q,Bounds.point box.c.lo,Bounds.point box.c.hi,Bounds.point box.d.lo,Bounds.point box.d.hi,s.f,s.u,s.w⟩

def realInputs (box : TailBox) (h k q f u w : R) : Inputs R :=
  ⟨h,k,q,value cppGrid box.c.lo,value cppGrid box.c.hi,value cppGrid box.d.lo,value cppGrid box.d.hi,f,u,w⟩

def ends {T : Type} (p : Inputs T) : List (T×T) := [(p.cl,p.dl),(p.ch,p.dl),(p.cl,p.dh),(p.ch,p.dh)]

structure RayData (T : Type) where
  n : T
  v : T
  m : T
  peak : T
  constant : T
  improvement : T
  tail : T
  traceOne : T
  traceShared : T

def gridRay (r : Ray) : RayData Bounds :=
  ⟨r.n,r.v,r.m,r.peak,r.constant,r.improvement,r.tail,r.traceOne,r.traceShared⟩

section Arithmetic
variable {T : Type} [Add T] [Sub T] [Mul T]

def heads (op : Arithmetic T) (p : Inputs T) := head op p.h p.k p.q p.cl p.ch p.dl p.dh p.f

def prices (op : Arithmetic T) (p : Inputs T) (H : Head T) (invRate qinv : T) :=
  common op p.q p.u p.w invRate qinv H.clipped H.delta H.cubic H.y H.d2 H.anti

def supports (op : Arithmetic T) (p : Inputs T) (H : Head T) (wh ws c d : T) :=
  corner op c d p.ch p.dl H.highInside H.pair H.lowOutside wh ws

def chargeAt (op : Arithmetic T) (p : Inputs T) (H : Head T) (P : Common T) (K : Corner T)
    (invRate invGeom oddShared c d : T) :=
  charges op H.g2 P.sharedQuad P.shift H.tax p.ch p.dl K.spread oddShared invRate P.highQuad K.odd H.k2 invGeom
    K.dsq d p.q c P.completion K.cd H.linear H.headGap P.lambda H.g

def readAt (op : Arithmetic T) (p : Inputs T) (P : Common T) (K : Corner T) (B : Charges T)
    (invRate : T) (r : RayData T) :=
  leaf op invRate K.one r.traceOne K.shared r.traceShared B.physicalShared r.peak B.physicalHigh r.v P.residual
    K.tailPrefix r.tail K.dsq K.cd p.k B.splitDebit r.n B.singleton r.m r.constant B.increment r.improvement B.singleDebit

end Arithmetic

def row (p : Inputs Bounds) (H : Head Bounds) (P : Common Bounds) (wh ws invRate invGeom : Bounds)
    (c d : Bounds) : Option (List (Int×Int)) := do
  let K := supports gridArithmetic p H wh ws c d
  let oddShared ← checkedDiv (K.odd*H.g2) H.oddDen
  let B := chargeAt gridArithmetic p H P K invRate invGeom oddShared c d
  return rays.map fun r =>
    let M := readAt gridArithmetic p P K B invRate (gridRay r)
    (M.splitMargin.lo,M.singleMargin.lo)

def preparedMargins (box : TailBox) (s : Shifts) : Option (List (List (Int×Int))) := do
  let p := gridInputs box s
  let H := heads gridArithmetic p
  if box.c.lo<box.d.hi then none else
    let ws ← pick (H.pair*p.dl) H.lowOutside
    let wh ← pick (H.highInside*p.cl*p.dl) H.pair
    let invRate ← checkedDiv (whole cppGrid 1) (Bounds.rational cppGrid 4242 25)
    let invGeom ← checkedDiv (whole cppGrid 1) (Bounds.rational cppGrid 5 2)
    let qinv ← checkedDiv H.psi H.den
    let P := prices gridArithmetic p H invRate qinv
    (ends p).mapM (fun (c,d) => row p H P wh ws invRate invGeom c d)

/-- The shared preparation and leaf factorization computes the original table. -/
theorem originalMargins (box : TailBox) (s : Shifts) :
    UpperCorner.margins box s=preparedMargins box s := by cases box; cases s; rfl
def Inputs.map {T S : Type} (v : Inputs T) (f : T→S) : Inputs S :=
  ⟨f v.h,f v.k,f v.q,f v.cl,f v.ch,f v.dl,f v.dh,f v.f,f v.u,f v.w⟩

def RayData.map {T S : Type} (v : RayData T) (f : T→S) : RayData S :=
  ⟨f v.n,f v.v,f v.m,f v.peak,f v.constant,f v.improvement,f v.tail,f v.traceOne,f v.traceShared⟩

def Head.map {T S : Type} (v : Head T) (f : T→S) : Head S :=
  ⟨f v.y,f v.g,f v.delta,f v.linear,f v.pair,f v.highInside,f v.lowOutside,f v.k2,f v.g2,f v.d2,f v.anti,f v.psi,f v.oddDen,f v.cubic,f v.headGap,f v.tax,f v.clipped,f v.den⟩

def Common.map {T S : Type} (v : Common T) (f : T→S) : Common S :=
  ⟨f v.shift,f v.lambda,f v.sharedQuad,f v.residual,f v.completion,f v.highQuad⟩

def Corner.map {T S : Type} (v : Corner T) (f : T→S) : Corner S :=
  ⟨f v.dsq,f v.cd,f v.odd,f v.tailPrefix,f v.spread,f v.one,f v.shared⟩

def Charges.map {T S : Type} (v : Charges T) (f : T→S) : Charges S :=
  ⟨f v.physicalShared,f v.physicalHigh,f v.increment,f v.singleton,f v.splitDebit,f v.singleDebit⟩

def Leaf.map {T S : Type} (v : Leaf T) (f : T→S) : Leaf S :=
  ⟨f v.splitMargin,f v.singleMargin⟩

def rayFrom {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T) (n v tone tsh : T) : RayData T :=
  let m := op.largest n (op.byNat v 2 (by decide))
  let total := op.whole 2*n+v
  ⟨n,v,m,op.largest n v,op.largest (op.largest (op.fraction 5 2 (by decide)*n) (op.whole 2*v)) total,
    op.pos (total-op.whole 3*m),op.largest v (op.byNat n 2 (by decide)),tone,tsh⟩

def rayAt {T : Type} [Add T] [Sub T] [Mul T] (op : Arithmetic T) (j : Fin 7) : RayData T :=
  let N := op.whole
  let F := op.fraction
  let r := rayFrom op
  let rs := [r (N 1) (N 0) (N 0) (F 1 2 (by decide)),
    r (N 1) (F 1 2 (by decide)) (F 3 8 (by decide)) (F 1 2 (by decide)),
    r (N 1) (F 2 3 (by decide)) (F 4 9 (by decide)) (F 1 2 (by decide)),
    r (N 1) (N 1) (F 2 3 (by decide)) (F 2 3 (by decide)),
    r (N 1) (N 2) (F 4 3 (by decide)) (F 5 6 (by decide)),
    r (N 1) (N 4) (F 8 3 (by decide)) (F 11 12 (by decide)),
    r (N 0) (N 1) (F 2 3 (by decide)) (N 0)]
  rs[j.val]'j.isLt

private theorem rayCases : ∀ j : Fin 7,j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6 := by decide

private theorem rayToGrid (j : Fin 7) : (rayAt (trackedArithmetic (R:=R)) j).map Tracked.interval=
    gridRay (rays[j.val]'j.isLt) := by
  rcases rayCases j with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem rayToReal (j : Fin 7) : (rayAt (trackedArithmetic (R:=R)) j).map Tracked.real=
    rayAt realArithmetic j := by
  rcases rayCases j with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem trackedReadGrid (p : Inputs (Tracked R)) (P : Common (Tracked R)) (K : Corner (Tracked R))
    (B : Charges (Tracked R)) (i : Tracked R) (r : RayData (Tracked R)) :
    (readAt trackedArithmetic p P K B i r).map Tracked.interval=
    readAt gridArithmetic (p.map Tracked.interval) (P.map Tracked.interval) (K.map Tracked.interval)
      (B.map Tracked.interval) i.interval (r.map Tracked.interval) := rfl
private theorem trackedReadReal (p : Inputs (Tracked R)) (P : Common (Tracked R)) (K : Corner (Tracked R))
    (B : Charges (Tracked R)) (i : Tracked R) (r : RayData (Tracked R)) :
    (readAt trackedArithmetic p P K B i r).map Tracked.real=
    readAt realArithmetic (p.map Tracked.real) (P.map Tracked.real) (K.map Tracked.real)
      (B.map Tracked.real) i.real (r.map Tracked.real) := rfl

noncomputable def realRead (p : Inputs R) (wh ws c d : R) (j : Fin 7) : Leaf R :=
  let H := heads realArithmetic p
  let invRate : R := 1/(4242/25:R)
  let invGeom : R := 1/(5/2:R)
  let P := prices realArithmetic p H invRate (H.psi/H.den)
  let K := supports realArithmetic p H wh ws c d
  let B := chargeAt realArithmetic p H P K invRate invGeom (K.odd*H.g2/H.oddDen) c d
  readAt realArithmetic p P K B invRate (rayAt realArithmetic j)

def trackedInputs {box : TailBox} {s : Shifts} {h k q c d f u w : R}
    (inside : Inside cppGrid box h k q c d) (hf : s.f.Contains cppGrid f)
    (hu : s.u.Contains cppGrid u) (hw : s.w.Contains cppGrid w) : Inputs (Tracked R) :=
  ⟨⟨_,_,inside.hInside⟩,⟨_,_,inside.kInside⟩,⟨_,_,inside.qInside⟩,
    ⟨_,_,pointSound _ box.c.lo⟩,⟨_,_,pointSound _ box.c.hi⟩,⟨_,_,pointSound _ box.d.lo⟩,⟨_,_,pointSound _ box.d.hi⟩,
    ⟨_,_,hf⟩,⟨_,_,hu⟩,⟨_,_,hw⟩⟩

private theorem mapMRow {I J : Type} (f : I→Option J) (xs : List I) (rs : List J) (pass : xs.mapM f=some rs) :
    ∀(i : Nat) (a : I),xs[i]?=some a→∃ v,f a=some v ∧ rs[i]?=some v := by
  induction xs generalizing rs with
  | nil => intro i a hi; simp at hi
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [List.mapM_cons,ha] at pass
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,ha,ht] at pass
      | some ts =>
        have h := Option.some.inj (show some (b::ts)=some rs by simpa [List.mapM_cons,ha,ht] using pass)
        subst rs; intro i a' hi; cases i with
        | zero => have e : a=a' := Option.some.inj hi; exact ⟨b,e ▸ ha,rfl⟩
        | succ i => exact ih ts ht i a' hi

private theorem rowRead (p : Inputs (Tracked R)) (wh ws c d : Tracked R) (ir ig iq : Bounds)
    (hr : checkedDiv (whole cppGrid 1) (Bounds.rational cppGrid 4242 25)=some ir)
    (hg : checkedDiv (whole cppGrid 1) (Bounds.rational cppGrid 5 2)=some ig)
    (hq : checkedDiv (heads gridArithmetic (p.map Tracked.interval)).psi
      (heads gridArithmetic (p.map Tracked.interval)).den=some iq)
    {rs : List (Int×Int)}
    (computed : row (p.map Tracked.interval) (heads gridArithmetic (p.map Tracked.interval))
      (prices gridArithmetic (p.map Tracked.interval) (heads gridArithmetic (p.map Tracked.interval)) ir iq)
      wh.interval ws.interval ir ig c.interval d.interval=some rs) (j : Fin 7) :
    ∃ b : Leaf Bounds,rs[j.val]?=some (b.splitMargin.lo,b.singleMargin.lo) ∧
      b.splitMargin.Contains cppGrid (realRead (p.map Tracked.real) wh.real ws.real c.real d.real j).splitMargin ∧
      b.singleMargin.Contains cppGrid (realRead (p.map Tracked.real) wh.real ws.real c.real d.real j).singleMargin := by
  let H := heads trackedArithmetic p
  let rate : Tracked R := ⟨ir,1/(4242/25:R),checkedQuotient (wholeSound _ 1) (fractionSound _ 4242 25 (by decide)) hr⟩
  let geom : Tracked R := ⟨ig,1/(5/2:R),checkedQuotient (wholeSound _ 1) (fractionSound _ 5 2 (by decide)) hg⟩
  let qi : Tracked R := ⟨iq,H.psi.real/H.den.real,checkedQuotient H.psi.encloses H.den.encloses hq⟩
  let P := prices trackedArithmetic p H rate qi
  let K := supports trackedArithmetic p H wh ws c d
  let early (os : Bounds) (r : Ray) :=
    let B := chargeAt gridArithmetic (p.map Tracked.interval) (H.map Tracked.interval) (P.map Tracked.interval)
      (K.map Tracked.interval) ir ig os c.interval d.interval
    let M := readAt gridArithmetic (p.map Tracked.interval) (P.map Tracked.interval) (K.map Tracked.interval) B ir (gridRay r)
    (M.splitMargin.lo,M.singleMargin.lo)
  have step : (checkedDiv (K.odd.interval*H.g2.interval) H.oddDen.interval).bind
    (fun os => some (rays.map (early os)))=some rs := computed
  cases pass : checkedDiv (K.odd.interval*H.g2.interval) H.oddDen.interval with
  | none => simp [pass] at step
  | some os =>
    have shape : rays.map (early os)=rs := by simpa [pass] using step
    let share : Tracked R := ⟨os,K.odd.real*H.g2.real/H.oddDen.real,
      checkedQuotient (Bounds.mulSound K.odd.encloses H.g2.encloses) H.oddDen.encloses pass⟩
    let B := chargeAt trackedArithmetic p H P K rate geom share c d
    let rt := rayAt (trackedArithmetic (R:=R)) j
    let M := readAt trackedArithmetic p P K B rate rt
    have gx := trackedReadGrid p P K B rate rt
    rw [rayToGrid] at gx
    have rx := trackedReadReal p P K B rate rt
    rw [rayToReal] at rx
    have rowsAt : rs[j.val]?=some (early os (rays[j.val]'j.isLt)) := by
      rw [←shape,List.getElem?_map,List.getElem?_eq_getElem (show j.val<rays.length from j.isLt)]; rfl
    refine ⟨M.map Tracked.interval,?_,?_,?_⟩
    · rw [rowsAt]; change _=some ((M.map Tracked.interval).splitMargin.lo,(M.map Tracked.interval).singleMargin.lo)
      rw [show M.map Tracked.interval=_ from gx]; rfl
    · have hh := congrArg Leaf.splitMargin rx
      change M.splitMargin.real=(realRead (p.map Tracked.real) wh.real ws.real c.real d.real j).splitMargin at hh
      rw [←hh]; exact M.splitMargin.encloses
    · have hh := congrArg Leaf.singleMargin rx
      change M.singleMargin.real=(realRead (p.map Tracked.real) wh.real ws.real c.real d.real j).singleMargin at hh
      rw [←hh]; exact M.singleMargin.encloses

def cAt {T : Type} (p : Inputs T) (high : Bool) := if high then p.ch else p.cl
def dAt {T : Type} (p : Inputs T) (high : Bool) := if high then p.dh else p.dl
def cornerIndex (cHigh dHigh : Bool) : Nat := (if dHigh then 2 else 0)+(if cHigh then 1 else 0)

private theorem cornerLookup {T : Type} (p : Inputs T) (a b : Bool) :
    (ends p)[cornerIndex a b]?=some (cAt p a,dAt p b) := by cases a <;> cases b <;> rfl

structure WeightLimits (p : Inputs R) (wh ws : R) : Prop where
  highNonnegative : 0≤wh
  sharedNonnegative : 0≤ws
  highUpper : wh≤UpperPrices.supportRatio ((heads realArithmetic p).highInside*p.cl*p.dl) (heads realArithmetic p).pair
  sharedUpper : ws≤UpperPrices.supportRatio ((heads realArithmetic p).pair*p.dl) (heads realArithmetic p).lowOutside
  highDenPositive : 0<(heads realArithmetic p).highInside*p.cl*p.dl+(heads realArithmetic p).pair
  sharedDenPositive : 0<(heads realArithmetic p).pair*p.dl+(heads realArithmetic p).lowOutside

private theorem nextStep {A B : Type} {v : Option A} {f : A→Option B} {out : B}
    (pass : v.bind f=some out) : ∃ a,v=some a ∧ f a=some out := by
  cases v with | none => contradiction | some a => exact ⟨a,rfl,pass⟩

/-- All four stored rows, with both real margins for each of the seven rays.
A single pair of actual lower-grid support weights works across the whole table. -/
theorem marginsEnclosed {box : TailBox} {s : Shifts} {rows : List (List (Int×Int))}
    {h k q c d f u w : R} (inside : Inside cppGrid box h k q c d) (hf : s.f.Contains cppGrid f)
    (hu : s.u.Contains cppGrid u) (hw : s.w.Contains cppGrid w)
    (computed : UpperCorner.margins box s=some rows) :
    let p := realInputs box h k q f u w
    ∃ wh ws : R,WeightLimits p wh ws ∧ ∀ a b : Bool,∃ rs,rows[cornerIndex a b]?=some rs ∧
      ∀ j : Fin 7,∃ B : Leaf Bounds,rs[j.val]?=some (B.splitMargin.lo,B.singleMargin.lo) ∧
        B.splitMargin.Contains cppGrid (realRead p wh ws (cAt p a) (dAt p b) j).splitMargin ∧
        B.singleMargin.Contains cppGrid (realRead p wh ws (cAt p a) (dAt p b) j).singleMargin := by
  let p := trackedInputs inside hf hu hw
  let H := heads trackedArithmetic p
  rw [originalMargins] at computed
  unfold preparedMargins at computed
  split at computed
  · contradiction
  · obtain ⟨ws,wsp,one⟩ := nextStep computed
    obtain ⟨wh,whp,two⟩ := nextStep one
    obtain ⟨ir,hr,three⟩ := nextStep two
    obtain ⟨ig,hg,four⟩ := nextStep three
    obtain ⟨iq,hq,table⟩ := nextStep four
    rw [pickChecked] at wsp whp
    have ⟨sh,s0,sl,sd⟩ := UpperSupportEnclosure.checkedWeightSound
      (Bounds.mulSound H.pair.encloses p.dl.encloses) H.lowOutside.encloses wsp
    have ⟨hh,h0,hl,hd⟩ := UpperSupportEnclosure.checkedWeightSound
      (Bounds.mulSound (Bounds.mulSound H.highInside.encloses p.cl.encloses) p.dl.encloses) H.pair.encloses whp
    let ts : Tracked R := ⟨ws,value cppGrid ws.lo,sh⟩
    let th : Tracked R := ⟨wh,value cppGrid wh.lo,hh⟩
    refine ⟨th.real,ts.real,⟨h0,s0,hl,sl,hd,sd⟩,?_⟩
    intro a b
    obtain ⟨rs,hrow,lookup⟩ := mapMRow _ _ _ table (cornerIndex a b) _ (cornerLookup (gridInputs box s) a b)
    refine ⟨rs,lookup,?_⟩
    cases a <;> cases b <;> intro j
    · exact rowRead p th ts p.cl p.dl ir ig iq hr hg hq hrow j
    · exact rowRead p th ts p.cl p.dh ir ig iq hr hg hq hrow j
    · exact rowRead p th ts p.ch p.dl ir ig iq hr hg hq hrow j
    · exact rowRead p th ts p.ch p.dh ir ig iq hr hg hq hrow j

def PositivePair (s t : Leaf R) : Prop := ∃ a b : R,0≤a ∧ 0≤b ∧
  0<a*s.splitMargin+b*s.singleMargin ∧ 0<a*t.splitMargin+b*t.singleMargin

def RealSector (p : Inputs R) (wh ws : R) (sector : Fin 6) : Prop :=
  ∀ a b : Bool,
    let lo : Fin 7 := ⟨sector.val,Nat.lt_trans sector.isLt (by decide : 6<7)⟩
    let hi : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
    PositivePair (realRead p wh ws (cAt p a) (dAt p b) lo) (realRead p wh ws (cAt p a) (dAt p b) hi)

theorem acceptedRealSector {box : TailBox} {s : Shifts} {rows : List (List (Int×Int))}
    {h k q c d f u w : R} (inside : Inside cppGrid box h k q c d) (hf : s.f.Contains cppGrid f)
    (hu : s.u.Contains cppGrid u) (hw : s.w.Contains cppGrid w)
    (computed : UpperCorner.margins box s=some rows) (sector : Fin 6)
    (pass : UpperReplay.sectorPass rows sector=true) :
    let p := realInputs box h k q f u w
    ∃ wh ws : R,WeightLimits p wh ws ∧ RealSector p wh ws sector := by
  obtain ⟨wh,ws,valid,table⟩ := marginsEnclosed inside hf hu hw computed
  refine ⟨wh,ws,valid,?_⟩; intro a b
  let lo : Fin 7 := ⟨sector.val,Nat.lt_trans sector.isLt (by decide : 6<7)⟩
  let hi : Fin 7 := ⟨sector.val+1,Nat.succ_lt_succ sector.isLt⟩
  obtain ⟨rs,idx,all⟩ := table a b
  have mem := List.mem_of_getElem? idx
  obtain ⟨low,lowAt,ls,lt⟩ := all lo
  obtain ⟨high,highAt,hs,ht⟩ := all hi
  have every : (rows.all fun row => match row[sector.val]?,row[sector.val+1]? with
      | some (u,v),some (z,t) => blend u v z t | _,_ => false)=true :=
    (Bool.and_eq_true_iff.mp pass).2
  have worked := List.all_eq_true.mp every rs mem
  change rs[sector.val]?=some _ at lowAt
  change rs[sector.val+1]?=some _ at highAt
  rw [lowAt,highAt] at worked
  exact blendEnclosed (grid:=cppGrid) worked ls.1 lt.1 hs.1 ht.1

def ShiftValues (f u w : R) : Prop :=
  (f=0∨f=1/2∨f=1∨f=1/4∨f=3/4) ∧ (u=5/4∨u=1∨u=3/4∨u=3/2) ∧ (w=5/4∨w=3/2∨w=7/4∨w=1)

theorem shiftEnclosed (s : Shifts) (member : s∈UpperReplay.shifts) :
    ∃ f u w : R,ShiftValues f u w ∧ s.f.Contains cppGrid f ∧ s.u.Contains cppGrid u ∧ s.w.Contains cppGrid w := by
  obtain ⟨fb,fm,tailU⟩ := List.mem_flatMap.mp member
  obtain ⟨ub,um,tailW⟩ := List.mem_flatMap.mp tailU
  obtain ⟨wb,wm,rfl⟩ := List.mem_map.mp tailW
  let N := whole cppGrid
  let F := Bounds.rational cppGrid
  have fs : fb=N 0∨fb=F 1 2∨fb=N 1∨fb=F 1 4∨fb=F 3 4 := by simpa using fm
  have us : ub=F 5 4∨ub=N 1∨ub=F 3 4∨ub=F 3 2 := by simpa using um
  have ws : wb=F 5 4∨wb=F 3 2∨wb=F 7 4∨wb=N 1 := by simpa using wm
  have fChoice : ∃ f : R,(f=0∨f=1/2∨f=1∨f=1/4∨f=3/4) ∧ fb.Contains cppGrid f := by
    rcases fs with rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact ⟨_,by simp,wholeSound cppGrid 0⟩
      | exact ⟨_,by simp,wholeSound cppGrid 1⟩
      | exact ⟨_,by simp,fractionSound cppGrid 1 2 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 1 4 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 3 4 (by decide)⟩
  have uChoice : ∃ u : R,(u=5/4∨u=1∨u=3/4∨u=3/2) ∧ ub.Contains cppGrid u := by
    rcases us with rfl|rfl|rfl|rfl
    all_goals first
      | exact ⟨_,by simp,wholeSound cppGrid 1⟩
      | exact ⟨_,by simp,fractionSound cppGrid 5 4 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 3 4 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 3 2 (by decide)⟩
  have wChoice : ∃ w : R,(w=5/4∨w=3/2∨w=7/4∨w=1) ∧ wb.Contains cppGrid w := by
    rcases ws with rfl|rfl|rfl|rfl
    all_goals first
      | exact ⟨_,by simp,wholeSound cppGrid 1⟩
      | exact ⟨_,by simp,fractionSound cppGrid 5 4 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 3 2 (by decide)⟩
      | exact ⟨_,by simp,fractionSound cppGrid 7 4 (by decide)⟩
  obtain ⟨f,fc,hf⟩ := fChoice; obtain ⟨u,uc,hu⟩ := uChoice; obtain ⟨w,wc,hw⟩ := wChoice
  exact ⟨f,u,w,⟨fc,uc,wc⟩,hf,hu,hw⟩

/-- The actual upper shared-branch acceptor supplies the real shifts,
the common support weights, and a positive blend for both rays at each corner. -/
theorem acceptedSharedSector {box : TailBox} {h k q c d : R} (inside : Inside cppGrid box h k q c d)
    (accepted : UpperReplay.acceptsCorners box=true) (sector : Fin 6) :
    ∃ f u w wh ws : R,ShiftValues f u w ∧ WeightLimits (realInputs box h k q f u w) wh ws ∧
      RealSector (realInputs box h k q f u w) wh ws sector := by
  obtain ⟨s,sm,rs,hc,pass⟩ := UpperReplay.acceptedCornersWitness accepted sector
  obtain ⟨f,u,w,sv,hf,hu,hw⟩ := shiftEnclosed (R:=R) s sm
  obtain ⟨wh,ws,limits,blend⟩ := acceptedRealSector inside hf hu hw hc sector pass
  exact ⟨f,u,w,wh,ws,sv,limits,blend⟩

end RankSeven.UpperEndpoint
#print axioms RankSeven.UpperEndpoint.originalMargins
#print axioms RankSeven.UpperEndpoint.marginsEnclosed
#print axioms RankSeven.UpperEndpoint.acceptedSharedSector
