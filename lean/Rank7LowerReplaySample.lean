import Rank7LowerReplay

namespace RankSeven.LowerReplaySample

open Interval LowerContractor LowerReplay

private structure Node where
  depth : Nat
  input : Region
  output : Region
  result : Result

-- Reproduced from the lower verifier using extract_rank7_lower_leaf_sample.py.
private def splitNode : Node :=
  ⟨0,
    ⟨⟨80530636, 25501368320⟩, ⟨1398101, 738197504⟩, ⟨67108864, 2281701376⟩, ⟨167772160, 178956971⟩⟩,
    ⟨⟨80530636, 25501368320⟩, ⟨1398101, 738197504⟩, ⟨67108864, 2281701376⟩, ⟨167772160, 178956971⟩⟩, .unresolved⟩

private def sharedNode : Node :=
  ⟨16,
    ⟨⟨80530636, 179830783⟩, ⟨1398101, 93498026⟩, ⟨67108864, 136314880⟩, ⟨167772160, 178956971⟩⟩,
    ⟨⟨80530636, 179830783⟩, ⟨1398101, 93498026⟩, ⟨67108864, 136314880⟩, ⟨167772160, 178956971⟩⟩, .shared⟩

private def weightedNode : Node :=
  ⟨22,
    ⟨⟨430106212, 477731224⟩, ⟨346772820, 369797802⟩, ⟨119013376, 136314880⟩, ⟨173364565, 178956971⟩⟩,
    ⟨⟨430106212, 453004279⟩, ⟨346772820, 369797802⟩, ⟨119013376, 136314880⟩, ⟨173364565, 178956971⟩⟩, .weighted⟩

private def oldNode : Node :=
  ⟨17,
    ⟨⟨206585772, 238488110⟩, ⟨415847764, 461897727⟩, ⟨194718213, 237254663⟩, ⟨167772160, 178956971⟩⟩,
    ⟨⟨206585772, 207537126⟩, ⟨415847764, 461897727⟩, ⟨194718213, 195669567⟩, ⟨167772160, 178956971⟩⟩, .oldRegion⟩

private def nodeMatches (node : Node) : Bool :=
  decide (reduce cppGrid node.input=some node.output) &&
    decide (LowerReplay.compare node.depth node.output=node.result)

theorem nonsharedMatches :
    [splitNode,oldNode,weightedNode].all nodeMatches=true := by decide

theorem weightedBoundsMatch :
    LowerLeaves.weightedPrice cppGrid weightedNode.output (Bounds.point 167772160) =
      (⟨654481051,169046262696⟩ : Bounds) := by decide

private def sharedRows : List (List (Int × Int)) :=
  [[(534070325, 390065885), (417314481, 272610991), (378395864, 246042269), (300558638, 192904833), (67056220, 80874778), (-399948616, 151895627), (-233502418, 58421138)],
   [(667625526, 440434056), (558345461, 330280179), (521932083, 306158442), (449105336, 257914976), (230634352, 163525484), (-206307614, 332502747), (-218470984, 108684725)]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem sharedBoundsMatch :
    LowerCorner.margins sharedNode.output
      ⟨Bounds.point 0,Bounds.point 167772160,Bounds.point 167772160⟩ = some sharedRows ∧
      nodeMatches sharedNode=true := by decide +kernel

end RankSeven.LowerReplaySample

#print axioms RankSeven.LowerReplaySample.nonsharedMatches
#print axioms RankSeven.LowerReplaySample.weightedBoundsMatch
#print axioms RankSeven.LowerReplaySample.sharedBoundsMatch
