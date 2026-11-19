import Rank7UpperHintReplay
open RankSeven Interval UpperCorner UpperReplay

namespace RankSeven.HintShards
deriving instance DecidableEq for TailBox

def children (input : TailBox) : Option (TailBox×TailBox) := do
  let box ← verifier.contract (TailBox.toBox input)
  let (left,right) ← box.trySplit (verifier.axis box)
  return (fromBox left,fromBox right)

/-- The C++ endpoints of the two shard roots are checked against the
actual Lean contractor, axis and midpoint before child proofs are used. -/
theorem glue (fuel depth : Nat) (input left right : TailBox)
    (split : children input=some (left,right))
    (l : verifier.replay fuel (depth+1) (TailBox.toBox left)=true)
    (r : verifier.replay fuel (depth+1) (TailBox.toBox right)=true) :
    verifier.replay (fuel+1) depth (TailBox.toBox input)=true := by
  unfold children at split
  cases hc : verifier.contract (TailBox.toBox input) with
  | none => simp [hc] at split
  | some b =>
    cases sp : b.trySplit (verifier.axis b) with
    | none => simp [hc,sp] at split
    | some lr =>
      obtain ⟨a,c⟩ := lr
      have eq : (fromBox a,fromBox c)=(left,right) := by simpa [hc,sp] using split
      cases eq; rw [toFromBox] at l r
      simp [BoxVerifier.replay,hc,sp,l,r]
end RankSeven.HintShards
#print axioms RankSeven.HintShards.glue
