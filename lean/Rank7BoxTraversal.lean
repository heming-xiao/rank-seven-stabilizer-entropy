import Rank7Interval

namespace RankSeven.Interval

open Lean.Grind
attribute [local instance] Ring.intCast

abbrev Box (d : Nat) := Fin d → Bounds

def Box.Contains {d : Nat} {R : Type} [CommRing R] [LE R] (g : Grid) (box : Box d) (x : Fin d → R) : Prop :=
  ∀ i, (box i).Contains g (x i)

def Box.midpoint {d : Nat} (box : Box d) (i : Fin d) : Int :=
  (box i).lo + ((box i).hi - (box i).lo) / 2

def Box.left {d : Nat} (box : Box d) (i : Fin d) (mid : Int) : Box d :=
  fun j => if j=i then ⟨(box j).lo,mid⟩ else box j

def Box.right {d : Nat} (box : Box d) (i : Fin d) (mid : Int) : Box d :=
  fun j => if j=i then ⟨mid,(box j).hi⟩ else box j

/-- Both rounded children include the common endpoint. The exact midpoint
matches the C++ integer expression on boxes with ordered endpoints. -/
def Box.trySplit {d : Nat} (box : Box d) (i : Fin d) : Option (Box d × Box d) :=
  let mid := box.midpoint i
  if (box i).lo < mid ∧ mid < (box i).hi then some (box.left i mid,box.right i mid) else none

section Coverage
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem Box.coverBySplit {d : Nat} {g : Grid} {box left right : Box d} {i : Fin d} {x : Fin d → R}
    (split : box.trySplit i = some (left,right)) (inside : box.Contains g x) :
    left.Contains g x ∨ right.Contains g x := by
  dsimp only [Box.trySplit] at split
  split at split
  · have h := Option.some.inj split
    have l := congrArg Prod.fst h
    have r := congrArg Prod.snd h
    dsimp only at l r
    rw [←l,←r]
    let boundary := (Int.cast (box.midpoint i) : R)
    by_cases side : (Int.cast g.scale : R)*x i ≤ boundary
    · apply Or.inl
      intro j
      by_cases same : j=i
      · subst j
        simp only [Box.left]
        have lower := (inside i).1
        change (Int.cast (box i).lo : R) ≤ Int.cast g.scale * x i ∧
          Int.cast g.scale*x i ≤ boundary
        exact ⟨lower,side⟩
      · simpa only [Box.left,ite_eq_right same] using inside j
    · apply Or.inr
      intro j
      by_cases same : j=i
      · subst j
        simp only [Box.right]
        have upper := (inside i).2
        change boundary ≤ Int.cast g.scale * x i ∧
          Int.cast g.scale*x i ≤ Int.cast (box i).hi
        exact ⟨by grind,upper⟩
      · simpa only [Box.right,ite_eq_right same] using inside j
  · contradiction

end Coverage

theorem Box.midpointEqTruncation {d : Nat} (box : Box d) (i : Fin d)
    (ordered : (box i).lo ≤ (box i).hi) :
    box.midpoint i = (box i).lo + ((box i).hi-(box i).lo).tdiv 2 := by
  unfold Box.midpoint
  have width : 0 ≤ (box i).hi-(box i).lo := by omega
  have nonnegative := Int.tmod_nonneg (2:Int) width
  rw [←cppFloorEq _ 2 (by decide)]
  simp only [cppFloor,Int.not_lt.mpr nonnegative,ite_false]
  omega

/-- Deterministic traversal shared by the two C++ interval verifiers.
A contractor can remove an already justified part of a box. A leaf
acceptor evaluates the directed inequalities at the current depth. -/
structure BoxVerifier (d : Nat) where
  contract : Box d → Option (Box d)
  accept : Nat → Box d → Bool
  axis : Box d → Fin d

def BoxVerifier.replay {d : Nat} (verifier : BoxVerifier d) : Nat → Nat → Box d → Bool
  | 0, _, _ => false
  | fuel+1, depth, box =>
    match verifier.contract box with
    | none => true
    | some narrowed =>
      if verifier.accept depth narrowed then true
      else match narrowed.trySplit (verifier.axis narrowed) with
        | none => false
        | some (left,right) =>
          replay verifier fuel (depth+1) left && replay verifier fuel (depth+1) right

section Replay
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- A successful exhaustive traversal proves coverage, once the semantic
soundness of contraction and accepting leaves has been established.
The depth and selected axis have no independent mathematical premises. -/
theorem BoxVerifier.replaySound {d : Nat} (verifier : BoxVerifier d) (g : Grid)
    (P : (Fin d → R) → Prop)
    (contractSound : ∀ box x, box.Contains g x →
      match verifier.contract box with
      | none => P x
      | some narrowed => P x ∨ narrowed.Contains g x)
    (acceptSound : ∀ depth box x, verifier.accept depth box=true → box.Contains g x → P x)
    (fuel depth : Nat) (box : Box d) (accepted : verifier.replay fuel depth box=true)
    (x : Fin d → R) (inside : box.Contains g x) : P x := by
  induction fuel generalizing depth box with
  | zero => simp [BoxVerifier.replay] at accepted
  | succ fuel ih =>
    have sc := contractSound box x inside
    cases h : verifier.contract box with
    | none => simpa only [h] using sc
    | some narrowed =>
      rw [h] at sc
      rcases sc with solved | narrowedInside
      · exact solved
      simp only [BoxVerifier.replay,h] at accepted
      cases pass : verifier.accept depth narrowed
      case true => exact acceptSound depth narrowed x pass narrowedInside
      case false =>
        simp only [pass,Bool.false_eq_true,ite_false] at accepted
        cases sp : narrowed.trySplit (verifier.axis narrowed) with
        | none => simp [sp] at accepted
        | some children =>
          obtain ⟨left,right⟩ := children
          simp only [sp,Bool.and_eq_true] at accepted
          rcases Box.coverBySplit sp narrowedInside with inLeft | inRight
          · exact ih (depth+1) left accepted.1 inLeft
          · exact ih (depth+1) right accepted.2 inRight

end Replay

section Corner
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- A single accepted mix for the two boundary rays certifies the common
margin throughout that ray segment at the chosen tail corner. -/
theorem blendBetweenRays {g : Grid} {s₀ t₀ s₁ t₁ : Int}
    (accepted : blend s₀ t₀ s₁ t₁=true)
    (a₀ b₀ a₁ b₁ u margin : R) (uLo : 0 ≤ u) (uHi : u ≤ 1)
    (a₀Lo : Int.cast s₀ ≤ Int.cast g.scale*a₀) (b₀Lo : Int.cast t₀ ≤ Int.cast g.scale*b₀)
    (a₁Lo : Int.cast s₁ ≤ Int.cast g.scale*a₁) (b₁Lo : Int.cast t₁ ≤ Int.cast g.scale*b₁)
    (first : lerp u a₀ a₁ ≤ margin) (second : lerp u b₀ b₁ ≤ margin) : 0 < margin := by
  obtain ⟨w,v,w0,v0,left,right⟩ := blendEnclosed accepted a₀Lo b₀Lo a₁Lo b₁Lo
  have between := lerpPositive uLo uHi left right
  have mix : lerp u (w*a₀+v*b₀) (w*a₁+v*b₁) = w*lerp u a₀ a₁+v*lerp u b₀ b₁ := by
    unfold lerp
    grind
  rw [mix] at between
  by_cases good : 0 < margin
  · exact good
  · have firstNonpos : lerp u a₀ a₁ ≤ 0 := by grind
    have secondNonpos : lerp u b₀ b₁ ≤ 0 := by grind
    have firstTerm := OrderedRing.mul_nonneg w0 (show 0 ≤ -lerp u a₀ a₁ by grind)
    have secondTerm := OrderedRing.mul_nonneg v0 (show 0 ≤ -lerp u b₀ b₁ by grind)
    grind

/-- Each corner may use its own mixing witness. Only the common physical
margin is interpolated across the tail rectangle. -/
theorem blendedRectangle {g : Grid} (f : Bilinear R) (c₀ c₁ d₀ d₁ r s t : R)
    (rLo : 0 ≤ r) (rHi : r ≤ 1) (sLo : 0 ≤ s) (sHi : s ≤ 1) (tLo : 0 ≤ t) (tHi : t ≤ 1)
    (sa ta sb tb : Bool → Bool → Int) (a₀ b₀ a₁ b₁ : Bool → Bool → R)
    (accepted : ∀ i j, blend (sa i j) (ta i j) (sb i j) (tb i j)=true)
    (bounds : ∀ i j, Int.cast (sa i j) ≤ Int.cast g.scale*a₀ i j ∧
      Int.cast (ta i j) ≤ Int.cast g.scale*b₀ i j ∧
      Int.cast (sb i j) ≤ Int.cast g.scale*a₁ i j ∧
      Int.cast (tb i j) ≤ Int.cast g.scale*b₁ i j)
    (common : ∀ i j, let m := f.eval (if i then c₁ else c₀) (if j then d₁ else d₀)
      lerp r (a₀ i j) (a₁ i j) ≤ m ∧ lerp r (b₀ i j) (b₁ i j) ≤ m) :
    0 < f.eval (lerp s c₀ c₁) (lerp t d₀ d₁) := by
  have corner (i j : Bool) : 0 < f.eval (if i then c₁ else c₀) (if j then d₁ else d₀) := by
    obtain ⟨a,b,c,d⟩ := bounds i j
    exact blendBetweenRays (accepted i j) _ _ _ _ r _ rLo rHi a b c d
      (common i j).1 (common i j).2
  exact Bilinear.positiveOnRectangle f c₀ c₁ d₀ d₁ s t sLo sHi tLo tHi
    (corner false false) (corner true false) (corner false true) (corner true true)

end Corner
end RankSeven.Interval

#print axioms RankSeven.Interval.Box.coverBySplit
#print axioms RankSeven.Interval.Box.midpointEqTruncation
#print axioms RankSeven.Interval.BoxVerifier.replaySound
#print axioms RankSeven.Interval.blendedRectangle
