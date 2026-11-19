import Rank7UpperReplay
import Rank7UpperPointMargin

namespace RankSeven.HintReplay
open Interval UpperCorner UpperReplay

inductive Plan where
  | old
  | weighted (index : Nat)
  | corners (indices : List Nat)
  | split (left right : Plan)
  deriving Inhabited

def hintedParams (indices : List Nat) := indices.filterMap fun i => UpperReplay.shifts[i]?
def weightedPass (b : TailBox) (u : Bounds) : Bool := match UpperWeighted.price cppGrid b u with
  | some m => decide (0<m.lo)
  | none => false
def hintedWeighted (box : TailBox) (i : Nat) : Bool := match (UpperWeighted.shifts cppGrid)[i]? with
  | none => false
  | some u => weightedPass box u
def hintedCorners (box : TailBox) (ids : List Nat) : Bool :=
  (remainingSectorsBy 4 (cornerRowsBy PointMargin.point box)
    (hintedParams ids) (List.range 6)).isEmpty

theorem hintedCorners_eq (box : TailBox) (ids : List Nat) :
    hintedCorners box ids = (remainingSectors box (hintedParams ids) (List.range 6)).isEmpty := by
  have same : PointMargin.point = UpperCorner.margins :=
    funext fun b => funext fun s => PointMargin.point_eq b s
  unfold hintedCorners remainingSectors cornerRows
  rw [same]

private theorem lookupMember {A : Type} (xs : List A) (n : Nat) {x : A} (atN : xs[n]?=some x) : x∈xs := by
  induction xs generalizing n with
  | nil => simp at atN
  | cons a as ih =>
    cases n with
    | zero => simp at atN; simp [atN]
    | succ n => exact List.mem_cons_of_mem a (ih n atN)

private theorem absent {s : Nat} {pending : List Nat} {es : Nat}
    (evaluate : Shifts → Option (List (List (Int × Int)))) (ss : List Shifts)
    (shift : Shifts) (hs : shift∈ss) (rows : List (List (Int×Int))) (ev : evaluate shift=some rows)
    (ok : adjacentSectorPass es rows s=true) :
    s∉remainingSectorsBy es evaluate ss pending := by
  have subset (ts : List Shifts) (ps : List Nat) (i : Nat) :
      i∈remainingSectorsBy es evaluate ts ps → i∈ps := by
    induction ts generalizing ps with
    | nil => cases ps <;> exact fun h => h
    | cons t ts ih =>
      cases ps with
      | nil => simp [remainingSectorsBy]
      | cons j js =>
        simp only [remainingSectorsBy]; split
        · exact ih _
        · exact fun h => (List.mem_filter.mp (ih _ h)).1
  induction ss generalizing pending with
  | nil => simp at hs
  | cons t ts ih =>
    cases pending with
    | nil => simp [remainingSectorsBy]
    | cons j js =>
      simp only [remainingSectorsBy]; rcases List.mem_cons.mp hs with eq|mem
      · subst t; rw [ev]; intro h
        have bad := (List.mem_filter.mp (subset ts _ _ h)).2
        simp [ok] at bad
      · split <;> apply ih mem

theorem hintedCornersSound (b : TailBox) (ids : List Nat) (ok : hintedCorners b ids=true) :
    UpperReplay.acceptsCorners b=true := by
  rw [hintedCorners_eq] at ok
  have complete := List.isEmpty_iff.mp ok
  apply List.isEmpty_iff.mpr
  cases eq : remainingSectors b UpperReplay.shifts (List.range 6) with
  | nil => rfl
  | cons j js =>
    have jmem : j∈remainingSectors b UpperReplay.shifts (List.range 6) := by rw [eq]; exact List.mem_cons_self
    have inside : j∈List.range 6 := by
      by_cases hj : j∈List.range 6
      · exact hj
      · have sub (ts : List Shifts) (ps : List Nat) (miss : j∉ps) : j∉remainingSectors b ts ps := by
          induction ts generalizing ps with
          | nil => cases ps <;> exact miss
          | cons t ts ih =>
            cases ps with
            | nil => simp [remainingSectors,remainingSectorsBy]
            | cons k ks =>
              unfold remainingSectors; simp only [remainingSectorsBy]; split
              · exact ih _ miss
              · apply ih; exact fun h => miss (List.mem_filter.mp h).1
        exact False.elim (sub _ _ hj jmem)
    obtain ⟨shift,mem,rs,ev,pass⟩ := UpperReplay.sectorWitness (params:=hintedParams ids) inside complete
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp mem
    have hs : shift∈UpperReplay.shifts := lookupMember _ _ hi
    exact False.elim (absent (cornerRows b) _ shift hs rs ev pass jmem)

theorem hintedWeightedSound (b : TailBox) (i : Nat) (ok : hintedWeighted b i=true) :
    UpperWeighted.accepts cppGrid b=true := by
  unfold hintedWeighted at ok
  split at ok
  · contradiction
  · rename_i u eq; exact List.any_eq_true.mpr ⟨u,lookupMember _ _ eq,ok⟩

def check : Nat → Nat → Box 5 → Plan → Bool
  | 0, _, _, _ => false
  | fuel+1, depth, box, plan =>
    match verifier.contract box with
    | none => match plan with | .old => true | _ => false
    | some narrowed => match plan with
      | .old => UpperOldRegions.accepts cppGrid (fromBox narrowed)
      | .weighted id => hintedWeighted (fromBox narrowed) id
      | .corners ids => decide (9≤depth) && hintedCorners (fromBox narrowed) ids
      | .split left right => match narrowed.trySplit (verifier.axis narrowed) with
        | none => false
        | some (l,r) => check fuel (depth+1) l left && check fuel (depth+1) r right

/-- Kernel implication into the original exhaustive verifier. The sole C++
inputs are suggestions for branching, leaf kinds and candidate shifts. -/
theorem checkSound (fuel depth : Nat) (box : Box 5) (plan : Plan) (ok : check fuel depth box plan=true) :
    verifier.replay fuel depth box=true := by
  induction fuel generalizing depth box plan with
  | zero => simp [check] at ok
  | succ f ih =>
    unfold check at ok; simp only [BoxVerifier.replay]
    cases c : verifier.contract box with
    | none => simp
    | some narrowed =>
      simp only [c] at ok ⊢
      cases plan with
      | old =>
        have yes : verifier.accept depth narrowed=true := by
          change decide (UpperReplay.compare depth (fromBox narrowed)≠.unresolved)=true
          simp only [UpperReplay.compare,ok,ite_true]; decide
        simp [yes]
      | weighted i =>
        have paid := hintedWeightedSound _ _ ok
        have yes : verifier.accept depth narrowed=true := by
          change decide (UpperReplay.compare depth (fromBox narrowed)≠.unresolved)=true
          unfold UpperReplay.compare; rw [ite_eq_left paid]; split <;> decide
        simp [yes]
      | corners ids =>
        obtain ⟨dep,paid⟩ := Bool.and_eq_true_iff.mp ok
        have pass := hintedCornersSound _ _ paid
        have yes : verifier.accept depth narrowed=true := by
          change decide (UpperReplay.compare depth (fromBox narrowed)≠.unresolved)=true
          unfold UpperReplay.compare; simp only [dep,pass,Bool.and_self,ite_true]
          split
          · decide
          · split <;> decide
        simp [yes]
      | split a b =>
        cases accept : verifier.accept depth narrowed with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true,ite_false]
          cases sp : narrowed.trySplit (verifier.axis narrowed) with
          | none => simp [sp] at ok
          | some lr =>
            obtain ⟨l,r⟩ := lr
            simp only [sp,Bool.and_eq_true] at ok ⊢
            exact ⟨ih _ _ _ ok.1,ih _ _ _ ok.2⟩
end RankSeven.HintReplay
#print axioms RankSeven.HintReplay.hintedCorners_eq
#print axioms RankSeven.HintReplay.checkSound
