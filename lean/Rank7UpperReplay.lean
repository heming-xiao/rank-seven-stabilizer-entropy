import Rank7BoxTraversal
import Rank7UpperOldRegions
import Rank7UpperWeighted

namespace RankSeven.UpperReplay

open Lean.Grind Interval UpperCorner UpperContractor

def TailBox.toBox (box : TailBox) : Box 5 :=
  fun i => [box.h, box.k, box.q, box.c, box.d][i.val]'i.isLt

def fromBox (box : Box 5) : TailBox :=
  ⟨box 0, box 1, box 2, box 3, box 4⟩

theorem fromToBox (box : TailBox) : fromBox (TailBox.toBox box) = box := by
  cases box
  rfl

theorem toFromBox (box : Box 5) : TailBox.toBox (fromBox box) = box := by
  funext i
  obtain ⟨i, hi⟩ := i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl

private def axisWeight (i : Fin 5) : Int :=
  if i=3 then 4 else if i=4 then 6 else 1

/-- The same strict comparison and leftmost tie behavior as the C++ axis loop. -/
def axis (box : Box 5) : Fin 5 :=
  (List.finRange 5).foldl (fun best i =>
    let a := box i
    let b := box best
    if axisWeight i*(a.hi-a.lo)*(cppGrid.scale+b.lo) >
       axisWeight best*(b.hi-b.lo)*(cppGrid.scale+a.lo) then i else best) 0

def shifts : List Shifts :=
  let r := Bounds.rational cppGrid
  let whole := UpperContractor.whole cppGrid
  [whole 0, r 1 2, whole 1, r 1 4, r 3 4].flatMap fun f =>
    [r 5 4, whole 1, r 3 4, r 3 2].flatMap fun u =>
      [r 5 4, r 3 2, r 7 4, whole 1].map fun w => ⟨f,u,w⟩

def cornerRowsBy (evaluate : TailBox → Shifts → Option (List (List (Int × Int))))
    (box : TailBox) (shift : Shifts) : Option (List (List (Int × Int))) :=
  let product := Bounds.mul cppGrid
  let one := whole cppGrid 1
  let price := product (one.sub shift.f) (Bounds.rational cppGrid 200 11)
  let spread := (Bounds.point box.c.hi).sub (Bounds.point box.d.lo)
  let g := (product box.h box.q).sub (product price spread)
  if g.positivePart.hi = 0 ∧ shift.u.hi ≠ cppGrid.scale then none
  else evaluate box shift

def cornerRows := cornerRowsBy UpperCorner.margins

def adjacentSectorPass (endpoints : Nat) (rows : List (List (Int × Int))) (sector : Nat) : Bool :=
  rows.length == endpoints && (rows.all fun row =>
    match row[sector]?, row[sector+1]? with
    | some (s₁,t₁), some (s₂,t₂) => blend s₁ t₁ s₂ t₂
    | _, _ => false)

/-- Store the sectors whose corresponding C++ bit is still unset. -/
def remainingSectorsBy (endpoints : Nat) (evaluate : Shifts → Option (List (List (Int × Int)))) :
    List Shifts → List Nat → List Nat
  | _, [] => []
  | [], pending => pending
  | shift :: rest, pending => match evaluate shift with
    | none => remainingSectorsBy endpoints evaluate rest pending
    | some rows => remainingSectorsBy endpoints evaluate rest
      (pending.filter fun sector => !adjacentSectorPass endpoints rows sector)

theorem sectorWitnessBy {endpoints : Nat}
    {evaluate : Shifts → Option (List (List (Int × Int)))} {params : List Shifts} {pending : List Nat}
    {sector : Nat} (mem : sector ∈ pending) (complete : remainingSectorsBy endpoints evaluate params pending = []) :
    ∃ s ∈ params, ∃ rows, evaluate s = some rows ∧ adjacentSectorPass endpoints rows sector = true := by
  induction params generalizing pending with
  | nil => cases pending <;> simp_all [remainingSectorsBy]
  | cons shift rest ih =>
    cases pending with
    | nil => simp at mem
    | cons first tail =>
      simp only [remainingSectorsBy] at complete
      cases hr : evaluate shift with
      | none =>
        rw [hr] at complete
        obtain ⟨s,hs,rows,hrows,pass⟩ := ih mem complete
        exact ⟨s,List.mem_cons_of_mem shift hs,rows,hrows,pass⟩
      | some rows =>
        rw [hr] at complete
        cases pass : adjacentSectorPass endpoints rows sector with
        | true => exact ⟨shift,List.mem_cons_self,rows,hr,pass⟩
        | false =>
          have remains : sector ∈ (first :: tail).filter (fun j => !adjacentSectorPass endpoints rows j) :=
            List.mem_filter.mpr ⟨mem, by simp [pass]⟩
          obtain ⟨s,hs,other,hrows,passed⟩ := ih remains complete
          exact ⟨s,List.mem_cons_of_mem shift hs,other,hrows,passed⟩


abbrev sectorPass := adjacentSectorPass 4

def remainingSectors (box : TailBox) : List Shifts → List Nat → List Nat :=
  remainingSectorsBy 4 (cornerRows box)

def acceptsCorners (box : TailBox) : Bool :=
  (remainingSectors box shifts (List.range 6)).isEmpty

theorem sectorWitness {box : TailBox} {params : List Shifts} {pending : List Nat}
    {sector : Nat} (mem : sector ∈ pending) (complete : remainingSectors box params pending = []) :
    ∃ s ∈ params, ∃ rows, cornerRows box s = some rows ∧ sectorPass rows sector = true :=
  sectorWitnessBy mem complete

/-- A successful numeric corner search returns one common shift for both
boundary rays and all four corners of each sector. -/
theorem acceptedCornersWitness {box : TailBox} (accepted : acceptsCorners box = true)
    (sector : Fin 6) :
    ∃ s ∈ shifts, ∃ rows, UpperCorner.margins box s = some rows ∧
      sectorPass rows sector = true := by
  have h : remainingSectors box shifts (List.range 6) = [] :=
    List.isEmpty_iff.mp accepted
  obtain ⟨s,hm,rows,hr,pass⟩ := sectorWitness (List.mem_range.mpr sector.isLt) h
  refine ⟨s,hm,rows,?_,pass⟩
  unfold cornerRows cornerRowsBy at hr
  dsimp only at hr
  split at hr
  · contradiction
  · exact hr

theorem acceptedSectorRows {rows : List (List (Int × Int))} {sector : Nat}
    (accepted : sectorPass rows sector = true) :
    rows.length=4 ∧ ∀ row ∈ rows, ∃ (s₁ t₁ s₂ t₂ w v : Int),
      row[sector]? = some (s₁,t₁) ∧ row[sector+1]? = some (s₂,t₂) ∧
      0≤w ∧ 0≤v ∧ 0<w*s₁+v*t₁ ∧ 0<w*s₂+v*t₂ := by
  unfold sectorPass adjacentSectorPass at accepted
  have ⟨len, every⟩ := Bool.and_eq_true_iff.mp accepted
  refine ⟨by simpa using len,?_⟩
  intro row mem
  have pass := List.all_eq_true.mp every row mem
  cases first : row[sector]? with
  | none => simp [first] at pass
  | some a =>
    cases second : row[sector+1]? with
    | none => simp [first,second] at pass
    | some b =>
      obtain ⟨s₁,t₁⟩ := a
      obtain ⟨s₂,t₂⟩ := b
      simp only [first,second] at pass
      obtain ⟨w,v,hw,hv,h1,h2⟩ := blendSound pass
      exact ⟨s₁,t₁,s₂,t₂,w,v,rfl,rfl,hw,hv,h1,h2⟩

inductive Result where
  | oldRegion
  | weighted
  | corners
  | unresolved
  deriving DecidableEq, Repr

def compare (depth : Nat) (box : TailBox) : Result :=
  if UpperOldRegions.accepts cppGrid box then .oldRegion
  else if UpperWeighted.accepts cppGrid box then .weighted
  else if 9≤depth && acceptsCorners box then .corners
  else .unresolved

def verifier : BoxVerifier 5 where
  contract box := (UpperContractor.contract cppGrid (fromBox box)).map TailBox.toBox
  accept depth box := decide (compare depth (fromBox box) ≠ .unresolved)
  axis := axis

def initial (low high : Int) : TailBox :=
  UpperContractor.initialBox (Bounds.rational cppGrid low 256).lo (Bounds.rational cppGrid high 256).hi

def replay (low high : Int) : Bool :=
  verifier.replay 73 0 (TailBox.toBox (initial low high))

theorem splitLimits {d : Nat} {box left right : Box d} {i : Fin d}
    (split : box.trySplit i=some (left,right)) (j : Fin d) :
    (box j).lo≤(left j).lo ∧ (left j).hi≤(box j).hi ∧
      (box j).lo≤(right j).lo ∧ (right j).hi≤(box j).hi := by
  dsimp only [Box.trySplit] at split
  split at split
  · obtain ⟨a,b⟩ := Prod.mk.inj (Option.some.inj split)
    subst left
    subst right
    by_cases eq : j=i
    · subst j
      simpa [Box.left, Box.right] using
        (show (box i).lo≤(box i).lo ∧ box.midpoint i≤(box i).hi ∧
          (box i).lo≤box.midpoint i ∧ (box i).hi≤(box i).hi from by omega)
    · simp [Box.left, Box.right,eq]
  · contradiction

private theorem splitValid {box left right : Box 5} {i : Fin 5}
    (valid : Valid cppGrid (fromBox box)) (split : box.trySplit i=some (left,right)) :
    Valid cppGrid (fromBox left) ∧ Valid cppGrid (fromBox right) :=
  ⟨validSubbox valid (splitLimits split 3).1 (splitLimits split 0).1
    (splitLimits split 2).1 (splitLimits split 4).2.1,
   validSubbox valid (splitLimits split 3).2.2.1 (splitLimits split 0).2.2.1
    (splitLimits split 2).2.2.1 (splitLimits split 4).2.2.2⟩

section Ordered

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]


attribute [local instance] Ring.intCast

private theorem gridMonotone (a b : R) (order : a≤b) :
    (Int.cast cppGrid.scale : R)*a≤Int.cast cppGrid.scale*b := by
  have cast : Int.cast (R:=R) cppGrid.scale=134217728 := Ring.intCast_ofNat 134217728
  rw [cast]
  exact OrderedRing.mul_le_mul_of_nonneg_left order (by grind only)

private theorem exactSlabPoint (n : Nat) :
    (Bounds.rational cppGrid (Int.ofNat n) 256).lo=(Bounds.rational cppGrid (Int.ofNat n) 256).hi := by
  change (Int.ofNat n*134217728)/256 = -((- (Int.ofNat n*134217728))/256)
  omega

/-- Every point of the stated normalized starting domain is contained in
the actual C++ root box, including the rounded cap on the sixth probability. -/
theorem initialContains (low high : Nat) {h k q c d : R}
    (hLo : 3/5≤h) (hHi : h≤143) (kLo : 0≤k) (kHi : k≤33/8)
    (qLo : 1/2≤q) (qHi : q≤51/4)
    (dLo : (OfNat.ofNat low:R)/256≤d) (dHi : d≤(OfNat.ofNat high:R)/256)
    (ordered : d≤c) (unit : c≤1) (spread : c≤(9/5:R)*d) :
    Inside cppGrid (initial (Int.ofNat low) (Int.ofNat high)) h k q c d := by
  let hg := fractionSound (R:=R) cppGrid 3 5 (by decide)
  let kg := fractionSound (R:=R) cppGrid 33 8 (by decide)
  let qL := fractionSound (R:=R) cppGrid 1 2 (by decide)
  let qH := fractionSound (R:=R) cppGrid 51 4 (by decide)
  let dL := fractionSound (R:=R) cppGrid low 256 (by decide)
  let dH := fractionSound (R:=R) cppGrid high 256 (by decide)
  have hEnd := Std.le_trans (gridMonotone h 143 hHi) (wholeSound (R:=R) cppGrid 143).2
  have kStart := Std.le_trans (wholeSound (R:=R) cppGrid 0).1 (gridMonotone 0 k kLo)
  have cEnd1 := Std.le_trans (gridMonotone c 1 unit) (wholeSound (R:=R) cppGrid 1).2
  have dUpper : (Bounds.point ((Bounds.rational cppGrid (Int.ofNat high) 256).hi)).Contains
        cppGrid ((OfNat.ofNat high:R)/256) := by
    refine ⟨?_,dH.2⟩
    rw [Bounds.point,←exactSlabPoint]
    exact dH.1
  have ratio : (0:R)≤9/5 := by
    exact lowerEndpointNonnegative (fractionSound cppGrid 9 5 (by decide)) (by decide)
  have cBelow : c≤(9/5:R)*((OfNat.ofNat high:R)/256) :=
    Std.le_trans spread (OrderedRing.mul_le_mul_of_nonneg_left dHi ratio)
  have cCap := Bounds.mulSound (fractionSound (R:=R) cppGrid 9 5 (by decide)) dUpper
  have cEnd2 := Std.le_trans (gridMonotone _ _ cBelow) cCap.2
  refine ⟨⟨Std.le_trans hg.1 (gridMonotone _ _ hLo),hEnd⟩,
    ⟨kStart,Std.le_trans (gridMonotone _ _ kHi) kg.2⟩,
    ⟨Std.le_trans qL.1 (gridMonotone _ _ qLo),Std.le_trans (gridMonotone _ _ qHi) qH.2⟩,
    ⟨Std.le_trans dL.1 (gridMonotone _ _ (Std.le_trans dLo ordered)),?_⟩,
    ⟨Std.le_trans dL.1 (gridMonotone _ _ dLo),Std.le_trans (gridMonotone _ _ dHi) dH.2⟩⟩
  change (Int.cast cppGrid.scale:R)*c ≤ Int.cast
    (min ((Bounds.mul cppGrid (Bounds.rational cppGrid 9 5)
      (Bounds.point ((Bounds.rational cppGrid (Int.ofNat high) 256).hi))).hi) cppGrid.scale)
  rw [Int.min_def]
  split
  · exact cEnd2
  · exact cEnd1

/-- Contract and cover any scalar point that satisfies the residual
conditions. The premises are the three physical implications needed by
the leaf acceptor. The traversal consumes no independent coverage premise. -/
theorem replayRegion (x : Fin 5 → R) (P : Prop)
    (residual : Residual (x 0) (x 1) (x 2) (x 3) (x 4))
    (old : UpperOldRegions.OldCondition (x 0) (x 1) (x 2) (x 3) (x 4) → P)
    (weighted : ∀ u, (u=1 ∨ u=5/4 ∨ u=3/2) →
      0<UpperWeighted.margin (x 0) (x 1) (x 2) (x 3) (x 4) u → P)
    (corners : ∀ box, Inside cppGrid box (x 0) (x 1) (x 2) (x 3) (x 4) →
      (∀ sector : Fin 6, ∃ shift ∈ shifts, ∃ rows,
        UpperCorner.margins box shift=some rows ∧ sectorPass rows sector=true) → P)
    (fuel depth : Nat) (box : Box 5) (valid : Valid cppGrid (fromBox box))
    (inside : box.Contains cppGrid x) (success : verifier.replay fuel depth box=true) :
    P := by
  induction fuel generalizing depth box with
  | zero => simp [BoxVerifier.replay] at success
  | succ fuel ih =>
    have current : Inside cppGrid (fromBox box) (x 0) (x 1) (x 2) (x 3) (x 4) :=
      ⟨inside 0, inside 1, inside 2, inside 3, inside 4⟩
    obtain ⟨z,hz,zInside⟩ := contractPreserves residual valid current
    have contracted : verifier.contract box=some (TailBox.toBox z) := by simp [verifier,hz]
    rw [BoxVerifier.replay,contracted] at success
    have branch : verifier.accept depth (TailBox.toBox z)=true ↔ compare depth z≠.unresolved := by
      simp [verifier, fromToBox]
    cases accept : verifier.accept depth (TailBox.toBox z) with
    | true =>
      have passed := branch.mp accept
      unfold compare at passed
      split at passed
      · rename_i hOld
        exact old (UpperOldRegions.acceptedOldCondition zInside hOld)
      · split at passed
        · rename_i hWeighted
          obtain ⟨u, admissible, positive⟩ := UpperWeighted.acceptedMargin zInside hWeighted
          exact weighted u admissible positive
        · split at passed
          · rename_i hCorners
            exact corners z zInside (acceptedCornersWitness (Bool.and_eq_true_iff.mp hCorners).2)
          · exact False.elim (passed rfl)
    | false =>
      simp only [accept, Bool.false_eq_true, ite_false] at success
      have subValid : Valid cppGrid (fromBox (TailBox.toBox z)) :=
        (fromToBox z).symm ▸ contractValid valid hz
      have subInside : (TailBox.toBox z).Contains cppGrid x := by
        intro j
        have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by
          obtain ⟨j,hj⟩ := j
          have values : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
          rcases values with rfl | rfl | rfl | rfl | rfl <;> simp
        rcases cases with rfl | rfl | rfl | rfl | rfl
        · exact zInside.hInside
        · exact zInside.kInside
        · exact zInside.qInside
        · exact zInside.cInside
        · exact zInside.dInside
      cases cut : (TailBox.toBox z).trySplit (verifier.axis (TailBox.toBox z)) with
      | none => simp [cut] at success
      | some pair =>
        obtain ⟨left,right⟩ := pair
        simp only [cut,Bool.and_eq_true] at success
        obtain ⟨leftValid,rightValid⟩ := splitValid subValid cut
        rcases Box.coverBySplit cut subInside with inLeft | inRight
        · exact ih (depth+1) left leftValid inLeft success.1
        · exact ih (depth+1) right rightValid inRight success.2

end Ordered

end RankSeven.UpperReplay

#print axioms RankSeven.UpperReplay.acceptedCornersWitness
#print axioms RankSeven.UpperReplay.acceptedSectorRows
#print axioms RankSeven.UpperReplay.replayRegion

#print axioms RankSeven.UpperReplay.initialContains
