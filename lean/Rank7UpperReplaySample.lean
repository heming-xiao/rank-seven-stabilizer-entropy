import Rank7UpperReplay

namespace RankSeven.UpperReplaySample

open Interval UpperCorner UpperReplay

structure Node where
  depth : Nat
  input : TailBox
  contracted : Option TailBox
  result : Result

-- These endpoints come from the original C++ traversal on [144/256,145/256].
-- Regenerate with python lean/extract_rank7_replay_sample.py.
def rootNode : Node :=
  ⟨0,
    ⟨⟨80530636, 19193135104⟩, ⟨0, 553648128⟩, ⟨67108864, 1711276032⟩, ⟨75497472, 134217728⟩, ⟨75497472, 76021760⟩⟩,
    some ⟨⟨154118976, 9047274399⟩, ⟨0, 553648128⟩, ⟨102745984, 1711276032⟩, ⟨75497472, 134217728⟩, ⟨75497472, 76021760⟩⟩, .unresolved⟩

def prunedNode : Node :=
  ⟨31,
    ⟨⟨193620090, 195986427⟩, ⟨11365896, 13344432⟩, ⟨107343523, 111328074⟩, ⟨75497472, 75956224⟩, ⟨75497472, 76021760⟩⟩,
    none, .unresolved⟩

def cornerNode : Node :=
  ⟨33,
    ⟨⟨195986427, 199867367⟩, ⟨12389696, 13344432⟩, ⟨107505835, 109416954⟩, ⟨75956224, 76414976⟩, ⟨75497472, 75759616⟩⟩,
    some ⟨⟨196080472, 199867367⟩, ⟨12432567, 13344432⟩, ⟨107597945, 109416954⟩, ⟨75956224, 76414976⟩, ⟨75497472, 75759616⟩⟩, .corners⟩

def oldNode : Node :=
  ⟨35,
    ⟨⟨203824455, 204471694⟩, ⟨27546, 1101962⟩, ⟨132011900, 134162586⟩, ⟨75956224, 76414976⟩, ⟨75497472, 76021760⟩⟩,
    some ⟨⟨203824455, 204471694⟩, ⟨27546, 1101962⟩, ⟨132011901, 134162586⟩, ⟨75956224, 76414976⟩, ⟨75497472, 76021760⟩⟩, .oldRegion⟩

def weightedNode : Node :=
  ⟨34,
    ⟨⟨434677165, 442320063⟩, ⟨1081344, 2162688⟩, ⟨398062047, 404345368⟩, ⟨75956224, 76414976⟩, ⟨75497472, 75759616⟩⟩,
    some ⟨⟨434677165, 442320063⟩, ⟨1081344, 2162688⟩, ⟨398062047, 404345368⟩, ⟨75956224, 76414976⟩, ⟨75497472, 75759616⟩⟩, .weighted⟩

def agrees (node : Node) : Bool :=
  match UpperContractor.contract cppGrid node.input, node.contracted with
  | none, none => true
  | some actual, some expected =>
    (List.finRange 5).all (fun i => decide
      (TailBox.toBox actual i = TailBox.toBox expected i)) &&
      decide (UpperReplay.compare node.depth actual = node.result)
  | _, _ => false

theorem startingBox :
    ∀ i, TailBox.toBox (initial 144 145) i = TailBox.toBox rootNode.input i := by decide

theorem rootAndAxis : agrees rootNode = true ∧
    (rootNode.contracted.map (fun b => axis (TailBox.toBox b))) = some 0 := by decide

theorem prunedAndOld : agrees prunedNode = true ∧ agrees oldNode = true := by decide

theorem weightedPrice :
    (weightedNode.contracted.bind (fun b => UpperWeighted.price cppGrid b (Bounds.point 201326592))) =
      some (⟨940246, 395233029⟩ : Bounds) ∧ agrees weightedNode = true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem cornersAgree : agrees cornerNode = true := by decide

def subtreeRoot : TailBox :=
  ⟨⟨193620090, 195986427⟩, ⟨11434960, 13344432⟩, ⟨107505835, 109416954⟩, ⟨75956224, 76414976⟩, ⟨75497472, 76021760⟩⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
/-- Kernel evaluation of a C++ split with both children accepted. -/
theorem subtreePasses : verifier.replay 2 32 (TailBox.toBox subtreeRoot) = true := by decide

end RankSeven.UpperReplaySample

#print axioms RankSeven.UpperReplaySample.startingBox
#print axioms RankSeven.UpperReplaySample.rootAndAxis
#print axioms RankSeven.UpperReplaySample.prunedAndOld
#print axioms RankSeven.UpperReplaySample.weightedPrice
#print axioms RankSeven.UpperReplaySample.cornersAgree
#print axioms RankSeven.UpperReplaySample.subtreePasses
