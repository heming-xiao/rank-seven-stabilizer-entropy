import Rank7LowerSmallHeadData
namespace RankSeven.LowerSmallHeadData
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
def bothPlan0 : Plan := ⟨9,[(5,.directed 0 1),(2,.directed 0 3),(3,.directed 1 2),(2,.directed 1 4),(2,.directed 1 5),(2,.directed 1 6),(2,.directed 2 0),(1,.directed 2 3),(3,.directed 3 1),(2,.directed 4 0),(1,.directed 4 1),(2,.directed 5 0),(1,.directed 5 1),(2,.directed 6 0),(1,.directed 6 1),(1,.omitPair 2 3)]⟩
theorem bothOk0 : (bothPlan0).ok (cost .both 0)=true := by decide
def bothPlan1 : Plan := ⟨9,[(30,.directed 0 1),(21,.directed 0 3),(7,.directed 1 2),(37,.directed 1 5),(7,.directed 1 6),(7,.directed 2 0),(7,.directed 2 5),(2,.directed 3 0),(23,.directed 3 1),(21,.directed 3 5),(37,.directed 5 0),(7,.directed 5 2),(9,.directed 5 3),(7,.directed 5 4),(14,.directed 5 6),(14,.directed 6 0),(7,.omitPair 0 6),(23,.omitPair 2 4),(16,.omitPair 2 6),(7,.omitPair 3 4),(23,.omitPair 4 6)]⟩
theorem bothOk1 : (bothPlan1).ok (cost .both 1)=true := by decide
def bothPlan2 : Plan := ⟨6,[(36,.directed 0 1),(70,.directed 0 3),(32,.directed 1 0),(74,.directed 1 5),(4,.directed 3 0),(74,.directed 3 1),(35,.directed 3 5),(35,.directed 3 6),(74,.directed 5 0),(39,.directed 5 3),(35,.directed 5 6),(35,.directed 6 0),(35,.directed 6 1),(74,.omitPair 2 4),(39,.omitPair 2 6),(39,.omitPair 4 6)]⟩
theorem bothOk2 : (bothPlan2).ok (cost .both 2)=true := by decide
def bothPlan3 : Plan := ⟨1,[(12,.directed 0 1),(12,.directed 0 3),(4,.directed 1 0),(20,.directed 1 5),(8,.directed 3 0),(20,.directed 3 1),(6,.directed 3 5),(6,.directed 3 6),(20,.directed 5 0),(14,.directed 5 3),(6,.directed 5 6),(6,.directed 6 0),(6,.directed 6 1),(20,.omitPair 2 4),(14,.omitPair 2 6),(14,.omitPair 4 6)]⟩
theorem bothOk3 : (bothPlan3).ok (cost .both 3)=true := by decide
def bothPlan4 : Plan := ⟨1,[(12,.directed 0 1),(4,.directed 0 3),(4,.directed 0 4),(4,.directed 0 6),(4,.directed 1 2),(4,.directed 1 5),(12,.directed 2 0),(8,.directed 3 0),(4,.directed 3 1),(8,.directed 4 0),(4,.directed 4 1),(12,.directed 5 0),(8,.directed 6 0),(4,.directed 6 1)]⟩
theorem bothOk4 : (bothPlan4).ok (cost .both 4)=true := by decide
def bothPlan5 : Plan := ⟨3,[(8,.directed 0 1),(2,.directed 0 2),(5,.directed 0 3),(1,.directed 0 4),(2,.directed 1 2),(1,.directed 1 3),(3,.directed 1 5),(2,.directed 1 6),(4,.directed 2 0),(5,.directed 3 2),(5,.directed 4 0),(2,.directed 4 1),(7,.directed 5 0),(1,.directed 5 2),(1,.directed 5 4),(6,.directed 6 0),(1,.directed 6 5),(6,.omitPair 2 3),(1,.omitPair 3 4),(1,.omitPair 3 6)]⟩
theorem bothOk5 : (bothPlan5).ok (cost .both 5)=true := by decide
def bothPlan6 : Plan := ⟨6,[(99,.directed 0 1),(30,.directed 0 2),(80,.directed 0 3),(7,.directed 0 4),(13,.directed 1 2),(7,.directed 1 3),(31,.directed 1 5),(19,.directed 1 6),(56,.directed 2 0),(80,.directed 3 2),(85,.directed 4 0),(19,.directed 4 1),(104,.directed 5 0),(12,.directed 5 2),(12,.directed 5 4),(92,.directed 6 0),(12,.directed 6 5),(92,.omitPair 2 3),(12,.omitPair 3 4),(12,.omitPair 3 6)]⟩
theorem bothOk6 : (bothPlan6).ok (cost .both 6)=true := by decide
def bothPlan7 : Plan := ⟨3,[(99,.directed 0 1),(38,.directed 0 2),(92,.directed 0 3),(15,.directed 0 4),(25,.directed 1 5),(15,.directed 1 6),(64,.directed 2 0),(10,.directed 3 0),(87,.directed 3 2),(102,.directed 4 0),(15,.directed 4 1),(10,.directed 4 5),(137,.directed 5 0),(10,.directed 5 2),(117,.directed 6 0),(10,.directed 6 5),(10,.omitPair 0 5),(102,.omitPair 2 3),(15,.omitPair 3 4),(5,.omitPair 3 5),(15,.omitPair 3 6)]⟩
theorem bothOk7 : (bothPlan7).ok (cost .both 7)=true := by decide
def bothPlan8 : Plan := ⟨5,[(86,.directed 0 1),(16,.directed 0 2),(146,.directed 0 3),(18,.directed 0 4),(6,.directed 1 5),(114,.directed 2 0),(16,.directed 3 1),(154,.directed 3 2),(6,.directed 3 5),(128,.directed 4 0),(16,.directed 4 1),(20,.directed 4 2),(6,.directed 4 3),(6,.directed 4 5),(146,.directed 5 0),(10,.directed 5 1),(20,.directed 5 2),(140,.directed 6 0),(10,.directed 6 1),(14,.directed 6 2),(134,.omitPair 2 3)]⟩
theorem bothOk8 : (bothPlan8).ok (cost .both 8)=true := by decide
def bothPlan9 : Plan := ⟨5,[(19,.directed 0 1),(12,.directed 0 2),(25,.directed 0 3),(3,.directed 1 0),(1,.directed 1 3),(2,.directed 1 5),(2,.directed 1 6),(12,.directed 2 0),(29,.directed 3 2),(25,.directed 4 0),(1,.directed 4 1),(3,.directed 4 2),(27,.directed 5 0),(4,.directed 5 2),(26,.directed 6 0),(4,.directed 6 2),(1,.directed 6 5),(1,.omitPair 0 5),(26,.omitPair 2 3),(1,.omitPair 3 4)]⟩
theorem bothOk9 : (bothPlan9).ok (cost .both 9)=true := by decide
def bothPlan10 : Plan := ⟨12,[(174,.directed 0 1),(62,.directed 0 2),(265,.directed 0 3),(9,.directed 0 4),(29,.directed 1 5),(9,.directed 1 6),(174,.directed 2 0),(29,.directed 3 1),(323,.directed 3 2),(256,.directed 4 0),(29,.directed 4 1),(67,.directed 4 2),(285,.directed 5 0),(67,.directed 5 2),(265,.directed 6 0),(20,.directed 6 1),(67,.directed 6 2),(20,.omitPair 0 5),(256,.omitPair 2 3)]⟩
theorem bothOk10 : (bothPlan10).ok (cost .both 10)=true := by decide
def bothPlan11 : Plan := ⟨6,[(1,.directed 0 1),(28,.directed 0 3),(28,.directed 0 4),(57,.directed 1 5),(61,.directed 2 3),(28,.directed 3 1),(131,.directed 3 2),(28,.directed 4 1),(131,.directed 4 2),(191,.directed 5 0),(24,.directed 5 1),(50,.directed 5 2),(81,.directed 6 0),(81,.directed 6 1),(50,.directed 6 2),(53,.directed 6 5),(110,.omitPair 0 5),(195,.omitPair 2 3),(134,.omitPair 2 4),(53,.omitPair 3 4)]⟩
theorem bothOk11 : (bothPlan11).ok (cost .both 11)=true := by decide
def bothPlan12 : Plan := ⟨12,[(1,.directed 0 1),(10,.directed 0 3),(10,.directed 0 4),(21,.directed 1 5),(19,.directed 2 3),(10,.directed 3 1),(53,.directed 3 2),(10,.directed 4 1),(53,.directed 4 2),(65,.directed 5 0),(6,.directed 5 1),(26,.directed 5 2),(27,.directed 6 0),(27,.directed 6 1),(26,.directed 6 2),(17,.directed 6 5),(38,.omitPair 0 5),(63,.omitPair 2 3),(44,.omitPair 2 4),(17,.omitPair 3 4)]⟩
theorem bothOk12 : (bothPlan12).ok (cost .both 12)=true := by decide
def bothPlan13 : Plan := ⟨4,[(15,.directed 0 1),(23,.directed 0 3),(22,.directed 1 5),(8,.directed 2 0),(7,.directed 3 0),(22,.directed 3 1),(34,.directed 3 2),(30,.directed 4 0),(22,.directed 4 1),(11,.directed 4 2),(52,.directed 5 0),(11,.directed 5 2),(30,.directed 6 0),(22,.directed 6 1),(11,.directed 6 2),(3,.triple 0 1 2),(22,.omitPair 0 5),(23,.omitPair 2 3)]⟩
theorem bothOk13 : (bothPlan13).ok (cost .both 13)=true := by decide
def bothPlan14 : Plan := ⟨5,[(2,.directed 0 1),(6,.directed 0 3),(4,.directed 2 0),(2,.directed 3 1),(10,.directed 3 2),(6,.directed 4 0),(2,.directed 4 1),(4,.directed 4 2),(6,.directed 5 0),(2,.directed 5 1),(4,.directed 5 2),(6,.directed 6 0),(2,.directed 6 1),(4,.directed 6 2),(4,.triple 0 1 2),(6,.omitPair 2 3)]⟩
theorem bothOk14 : (bothPlan14).ok (cost .both 14)=true := by decide
def bothPlan15 : Plan := ⟨3,[(1,.directed 1 0),(1,.directed 2 0),(1,.directed 3 0),(1,.directed 4 0),(1,.directed 5 0),(1,.directed 6 0)]⟩
theorem bothOk15 : (bothPlan15).ok (cost .both 15)=true := by decide
def bothPlan16 : Plan := ⟨3,[(4,.directed 1 0),(7,.directed 2 0),(7,.directed 3 0),(7,.directed 4 0),(7,.directed 5 0),(7,.directed 6 0)]⟩
theorem bothOk16 : (bothPlan16).ok (cost .both 16)=true := by decide
def bothPlan17 : Plan := ⟨3,[(4,.directed 1 0),(16,.directed 2 0),(16,.directed 3 0),(16,.directed 4 0),(16,.directed 5 0),(16,.directed 6 0)]⟩
theorem bothOk17 : (bothPlan17).ok (cost .both 17)=true := by decide
def bothPlan18 : Plan := ⟨1,[(4,.directed 2 0),(4,.directed 3 0),(4,.directed 4 0),(4,.directed 5 0),(4,.directed 6 0)]⟩
theorem bothOk18 : (bothPlan18).ok (cost .both 18)=true := by decide
def bothPlan19 : Plan := ⟨3,[(2,.directed 1 0),(2,.directed 2 0),(5,.directed 3 0),(5,.directed 4 0),(5,.directed 5 0),(5,.directed 6 0)]⟩
theorem bothOk19 : (bothPlan19).ok (cost .both 19)=true := by decide
def bothPlan20 : Plan := ⟨3,[(2,.directed 1 0),(8,.directed 2 0),(23,.directed 3 0),(23,.directed 4 0),(23,.directed 5 0),(23,.directed 6 0),(3,.omitPair 1 2)]⟩
theorem bothOk20 : (bothPlan20).ok (cost .both 20)=true := by decide
def bothPlan21 : Plan := ⟨1,[(4,.directed 2 0),(8,.directed 3 0),(8,.directed 4 0),(8,.directed 5 0),(8,.directed 6 0),(2,.triple 0 1 2)]⟩
theorem bothOk21 : (bothPlan21).ok (cost .both 21)=true := by decide
def bothPlan22 : Plan := ⟨3,[(1,.directed 1 0),(1,.directed 2 0),(7,.directed 3 0),(7,.directed 4 0),(7,.directed 5 0),(7,.directed 6 0),(3,.triple 0 1 2)]⟩
theorem bothOk22 : (bothPlan22).ok (cost .both 22)=true := by decide
def bothPlan23 : Plan := ⟨1,[(1,.directed 2 0),(5,.directed 3 0),(5,.directed 4 0),(5,.directed 5 0),(5,.directed 6 0),(3,.triple 0 1 2)]⟩
theorem bothOk23 : (bothPlan23).ok (cost .both 23)=true := by decide
def bothPlan24 : Plan := ⟨1,[(1,.directed 3 0),(1,.directed 4 0),(1,.directed 5 0),(1,.directed 6 0),(1,.triple 0 1 2)]⟩
theorem bothOk24 : (bothPlan24).ok (cost .both 24)=true := by decide
theorem bothPlans (j : Nat) (hj : j∈tags) : ∃ p : Plan,p.ok (cost .both j)=true := by
  simp only [tags,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,bothOk0⟩
  · exact ⟨_,bothOk1⟩
  · exact ⟨_,bothOk2⟩
  · exact ⟨_,bothOk3⟩
  · exact ⟨_,bothOk4⟩
  · exact ⟨_,bothOk5⟩
  · exact ⟨_,bothOk6⟩
  · exact ⟨_,bothOk7⟩
  · exact ⟨_,bothOk8⟩
  · exact ⟨_,bothOk9⟩
  · exact ⟨_,bothOk10⟩
  · exact ⟨_,bothOk11⟩
  · exact ⟨_,bothOk12⟩
  · exact ⟨_,bothOk13⟩
  · exact ⟨_,bothOk14⟩
  · exact ⟨_,bothOk15⟩
  · exact ⟨_,bothOk16⟩
  · exact ⟨_,bothOk17⟩
  · exact ⟨_,bothOk18⟩
  · exact ⟨_,bothOk19⟩
  · exact ⟨_,bothOk20⟩
  · exact ⟨_,bothOk21⟩
  · exact ⟨_,bothOk22⟩
  · exact ⟨_,bothOk23⟩
  · exact ⟨_,bothOk24⟩
end RankSeven.LowerSmallHeadData
#print axioms RankSeven.LowerSmallHeadData.bothPlans
