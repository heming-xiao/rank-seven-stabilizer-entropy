import Rank7LowerSmallHeadData
namespace RankSeven.LowerSmallHeadData
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
def mixedPlan0 : Plan := ⟨1,[(1,.directed 5 0),(1,.directed 6 5),(1,.omitPair 0 5),(1,.omitPair 5 6)]⟩
theorem mixedOk0 : (mixedPlan0).ok (cost .mixed 0)=true := by decide
def mixedPlan1 : Plan := ⟨1,[(9,.directed 5 0),(1,.directed 5 1),(1,.directed 6 0),(1,.directed 6 1),(8,.directed 6 5),(8,.omitPair 0 5),(8,.omitPair 5 6)]⟩
theorem mixedOk1 : (mixedPlan1).ok (cost .mixed 1)=true := by decide
def mixedPlan2 : Plan := ⟨1,[(30,.directed 5 0),(6,.directed 5 1),(6,.directed 6 0),(6,.directed 6 1),(24,.directed 6 5),(1,.triple 0 1 4),(1,.triple 0 1 3),(1,.triple 0 1 2),(24,.omitPair 0 5),(24,.omitPair 5 6)]⟩
theorem mixedOk2 : (mixedPlan2).ok (cost .mixed 2)=true := by decide
def mixedPlan3 : Plan := ⟨1,[(44,.directed 5 0),(12,.directed 5 1),(12,.directed 6 0),(12,.directed 6 1),(32,.directed 6 5),(4,.triple 0 1 4),(4,.triple 0 1 3),(4,.triple 0 1 2),(32,.omitPair 0 5),(32,.omitPair 5 6)]⟩
theorem mixedOk3 : (mixedPlan3).ok (cost .mixed 3)=true := by decide
def mixedPlan4 : Plan := ⟨1,[(24,.directed 5 0),(8,.directed 5 1),(8,.directed 6 0),(8,.directed 6 1),(16,.directed 6 5),(4,.triple 0 1 4),(4,.triple 0 1 3),(4,.triple 0 1 2),(16,.omitPair 0 5),(16,.omitPair 5 6)]⟩
theorem mixedOk4 : (mixedPlan4).ok (cost .mixed 4)=true := by decide
def mixedPlan5 : Plan := ⟨1,[(5,.directed 5 0),(1,.directed 5 1),(1,.directed 5 2),(1,.directed 6 0),(1,.directed 6 1),(1,.directed 6 2),(4,.directed 6 5),(4,.omitPair 0 5),(4,.omitPair 5 6)]⟩
theorem mixedOk5 : (mixedPlan5).ok (cost .mixed 5)=true := by decide
def mixedPlan6 : Plan := ⟨1,[(33,.directed 5 0),(10,.directed 5 1),(7,.directed 5 2),(10,.directed 6 0),(10,.directed 6 1),(7,.directed 6 2),(23,.directed 6 5),(1,.triple 0 1 4),(1,.triple 0 1 3),(2,.triple 0 1 2),(23,.omitPair 0 5),(24,.omitPair 5 6)]⟩
theorem mixedOk6 : (mixedPlan6).ok (cost .mixed 6)=true := by decide
def mixedPlan7 : Plan := ⟨1,[(72,.directed 5 0),(28,.directed 5 1),(16,.directed 5 2),(28,.directed 6 0),(28,.directed 6 1),(16,.directed 6 2),(44,.directed 6 5),(6,.triple 0 1 4),(6,.triple 0 1 3),(16,.triple 0 1 2),(44,.omitPair 0 5),(44,.omitPair 5 6)]⟩
theorem mixedOk7 : (mixedPlan7).ok (cost .mixed 7)=true := by decide
def mixedPlan8 : Plan := ⟨1,[(52,.directed 5 0),(24,.directed 5 1),(12,.directed 5 2),(24,.directed 6 0),(24,.directed 6 1),(12,.directed 6 2),(28,.directed 6 5),(8,.triple 0 1 4),(8,.triple 0 1 3),(20,.triple 0 1 2),(28,.omitPair 0 5),(28,.omitPair 5 6)]⟩
theorem mixedOk8 : (mixedPlan8).ok (cost .mixed 8)=true := by decide
def mixedPlan9 : Plan := ⟨1,[(9,.directed 5 0),(4,.directed 5 1),(4,.directed 5 2),(4,.directed 6 0),(4,.directed 6 1),(4,.directed 6 2),(5,.directed 6 5),(2,.triple 0 1 2),(5,.omitPair 0 5),(5,.omitPair 5 6)]⟩
theorem mixedOk9 : (mixedPlan9).ok (cost .mixed 9)=true := by decide
def mixedPlan10 : Plan := ⟨1,[(39,.directed 5 0),(21,.directed 5 1),(18,.directed 5 2),(21,.directed 6 0),(21,.directed 6 1),(18,.directed 6 2),(18,.directed 6 5),(2,.triple 0 1 4),(2,.triple 0 1 3),(18,.triple 0 1 2),(18,.omitPair 0 5),(18,.omitPair 5 6)]⟩
theorem mixedOk10 : (mixedPlan10).ok (cost .mixed 10)=true := by decide
def mixedPlan11 : Plan := ⟨1,[(42,.directed 5 0),(26,.directed 5 1),(20,.directed 5 2),(26,.directed 6 0),(26,.directed 6 1),(20,.directed 6 2),(16,.directed 6 5),(5,.triple 0 1 4),(5,.triple 0 1 3),(31,.triple 0 1 2),(16,.omitPair 0 5),(16,.omitPair 5 6)]⟩
theorem mixedOk11 : (mixedPlan11).ok (cost .mixed 11)=true := by decide
def mixedPlan12 : Plan := ⟨1,[(7,.directed 5 0),(5,.directed 5 1),(5,.directed 5 2),(5,.directed 6 0),(5,.directed 6 1),(5,.directed 6 2),(2,.directed 6 5),(6,.triple 0 1 2),(2,.omitPair 0 5),(2,.omitPair 5 6)]⟩
theorem mixedOk12 : (mixedPlan12).ok (cost .mixed 12)=true := by decide
def mixedPlan13 : Plan := ⟨1,[(15,.directed 5 0),(12,.directed 5 1),(11,.directed 5 2),(12,.directed 6 0),(12,.directed 6 1),(11,.directed 6 2),(3,.directed 6 5),(1,.triple 0 1 4),(1,.triple 0 1 3),(19,.triple 0 1 2),(3,.omitPair 0 5),(3,.omitPair 5 6)]⟩
theorem mixedOk13 : (mixedPlan13).ok (cost .mixed 13)=true := by decide
def mixedPlan14 : Plan := ⟨1,[(2,.directed 5 0),(2,.directed 5 1),(2,.directed 5 2),(2,.directed 6 0),(2,.directed 6 1),(2,.directed 6 2),(4,.triple 0 1 2)]⟩
theorem mixedOk14 : (mixedPlan14).ok (cost .mixed 14)=true := by decide
def mixedPlan15 : Plan := ⟨1,[(1,.directed 5 0),(1,.directed 6 0)]⟩
theorem mixedOk15 : (mixedPlan15).ok (cost .mixed 15)=true := by decide
def mixedPlan16 : Plan := ⟨1,[(6,.directed 5 0),(6,.directed 6 0),(1,.triple 0 1 4),(1,.triple 0 1 3),(1,.triple 0 1 2)]⟩
theorem mixedOk16 : (mixedPlan16).ok (cost .mixed 16)=true := by decide
def mixedPlan17 : Plan := ⟨1,[(12,.directed 5 0),(12,.directed 6 0),(4,.triple 0 1 4),(4,.triple 0 1 3),(4,.triple 0 1 2)]⟩
theorem mixedOk17 : (mixedPlan17).ok (cost .mixed 17)=true := by decide
def mixedPlan18 : Plan := ⟨1,[(8,.directed 5 0),(8,.directed 6 0),(4,.triple 0 1 4),(4,.triple 0 1 3),(4,.triple 0 1 2)]⟩
theorem mixedOk18 : (mixedPlan18).ok (cost .mixed 18)=true := by decide
def mixedPlan19 : Plan := ⟨1,[(4,.directed 5 0),(4,.directed 6 0),(2,.triple 0 1 2)]⟩
theorem mixedOk19 : (mixedPlan19).ok (cost .mixed 19)=true := by decide
def mixedPlan20 : Plan := ⟨1,[(16,.directed 5 0),(16,.directed 6 0),(2,.triple 0 1 4),(2,.triple 0 1 3),(12,.triple 0 1 2)]⟩
theorem mixedOk20 : (mixedPlan20).ok (cost .mixed 20)=true := by decide
def mixedPlan21 : Plan := ⟨1,[(16,.directed 5 0),(16,.directed 6 0),(4,.triple 0 1 4),(4,.triple 0 1 3),(16,.triple 0 1 2)]⟩
theorem mixedOk21 : (mixedPlan21).ok (cost .mixed 21)=true := by decide
def mixedPlan22 : Plan := ⟨1,[(5,.directed 5 0),(5,.directed 6 0),(6,.triple 0 1 2)]⟩
theorem mixedOk22 : (mixedPlan22).ok (cost .mixed 22)=true := by decide
def mixedPlan23 : Plan := ⟨1,[(10,.directed 5 0),(10,.directed 6 0),(1,.triple 0 1 4),(1,.triple 0 1 3),(15,.triple 0 1 2)]⟩
theorem mixedOk23 : (mixedPlan23).ok (cost .mixed 23)=true := by decide
def mixedPlan24 : Plan := ⟨1,[(2,.directed 5 0),(2,.directed 6 0),(4,.triple 0 1 2)]⟩
theorem mixedOk24 : (mixedPlan24).ok (cost .mixed 24)=true := by decide
theorem mixedPlans (j : Nat) (hj : j∈tags) : ∃ p : Plan,p.ok (cost .mixed j)=true := by
  simp only [tags,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,mixedOk0⟩
  · exact ⟨_,mixedOk1⟩
  · exact ⟨_,mixedOk2⟩
  · exact ⟨_,mixedOk3⟩
  · exact ⟨_,mixedOk4⟩
  · exact ⟨_,mixedOk5⟩
  · exact ⟨_,mixedOk6⟩
  · exact ⟨_,mixedOk7⟩
  · exact ⟨_,mixedOk8⟩
  · exact ⟨_,mixedOk9⟩
  · exact ⟨_,mixedOk10⟩
  · exact ⟨_,mixedOk11⟩
  · exact ⟨_,mixedOk12⟩
  · exact ⟨_,mixedOk13⟩
  · exact ⟨_,mixedOk14⟩
  · exact ⟨_,mixedOk15⟩
  · exact ⟨_,mixedOk16⟩
  · exact ⟨_,mixedOk17⟩
  · exact ⟨_,mixedOk18⟩
  · exact ⟨_,mixedOk19⟩
  · exact ⟨_,mixedOk20⟩
  · exact ⟨_,mixedOk21⟩
  · exact ⟨_,mixedOk22⟩
  · exact ⟨_,mixedOk23⟩
  · exact ⟨_,mixedOk24⟩
end RankSeven.LowerSmallHeadData
#print axioms RankSeven.LowerSmallHeadData.mixedPlans
