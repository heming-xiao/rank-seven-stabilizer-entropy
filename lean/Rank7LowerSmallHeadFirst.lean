import Rank7LowerSmallHeadData
namespace RankSeven.LowerSmallHeadData
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
def firstPlan0 : Plan := ⟨1,[(1,.directed 6 0),(1,.omitPair 0 6)]⟩
theorem firstOk0 : (firstPlan0).ok (cost .first 0)=true := by decide
def firstPlan1 : Plan := ⟨1,[(9,.directed 6 0),(1,.directed 6 1),(8,.omitPair 0 6)]⟩
theorem firstOk1 : (firstPlan1).ok (cost .first 1)=true := by decide
def firstPlan2 : Plan := ⟨1,[(31,.directed 6 0),(6,.directed 6 1),(24,.omitPair 0 6)]⟩
theorem firstOk2 : (firstPlan2).ok (cost .first 2)=true := by decide
def firstPlan3 : Plan := ⟨1,[(48,.directed 6 0),(12,.directed 6 1),(32,.omitPair 0 6)]⟩
theorem firstOk3 : (firstPlan3).ok (cost .first 3)=true := by decide
def firstPlan4 : Plan := ⟨1,[(28,.directed 6 0),(8,.directed 6 1),(16,.omitPair 0 6)]⟩
theorem firstOk4 : (firstPlan4).ok (cost .first 4)=true := by decide
def firstPlan5 : Plan := ⟨1,[(5,.directed 6 0),(5,.omitPair 0 6),(1,.omitPair 3 6),(1,.omitPair 4 6),(1,.omitPair 5 6)]⟩
theorem firstOk5 : (firstPlan5).ok (cost .first 5)=true := by decide
def firstPlan6 : Plan := ⟨1,[(34,.directed 6 0),(4,.directed 6 1),(2,.triple 0 1 2),(30,.omitPair 0 6),(6,.omitPair 3 6),(6,.omitPair 4 6),(6,.omitPair 5 6)]⟩
theorem firstOk6 : (firstPlan6).ok (cost .first 6)=true := by decide
def firstPlan7 : Plan := ⟨1,[(78,.directed 6 0),(18,.directed 6 1),(11,.triple 0 1 2),(60,.omitPair 0 6),(10,.omitPair 3 6),(10,.omitPair 4 6),(10,.omitPair 5 6)]⟩
theorem firstOk7 : (firstPlan7).ok (cost .first 7)=true := by decide
def firstPlan8 : Plan := ⟨1,[(60,.directed 6 0),(20,.directed 6 1),(14,.triple 0 1 2),(40,.omitPair 0 6),(4,.omitPair 3 6),(4,.omitPair 4 6),(4,.omitPair 5 6)]⟩
theorem firstOk8 : (firstPlan8).ok (cost .first 8)=true := by decide
def firstPlan9 : Plan := ⟨1,[(9,.directed 6 0),(1,.triple 0 1 2),(9,.omitPair 0 6),(4,.omitPair 3 6),(4,.omitPair 4 6),(4,.omitPair 5 6)]⟩
theorem firstOk9 : (firstPlan9).ok (cost .first 9)=true := by decide
def firstPlan10 : Plan := ⟨1,[(41,.directed 6 0),(5,.directed 6 1),(10,.triple 0 1 2),(36,.omitPair 0 6),(16,.omitPair 3 6),(16,.omitPair 4 6),(16,.omitPair 5 6)]⟩
theorem firstOk10 : (firstPlan10).ok (cost .first 10)=true := by decide
def firstPlan11 : Plan := ⟨1,[(47,.directed 6 0),(11,.directed 6 1),(18,.triple 0 1 2),(36,.omitPair 0 6),(15,.omitPair 3 6),(15,.omitPair 4 6),(15,.omitPair 5 6)]⟩
theorem firstOk11 : (firstPlan11).ok (cost .first 11)=true := by decide
def firstPlan12 : Plan := ⟨1,[(7,.directed 6 0),(3,.triple 0 1 2),(7,.omitPair 0 6),(5,.omitPair 3 6),(5,.omitPair 4 6),(5,.omitPair 5 6)]⟩
theorem firstOk12 : (firstPlan12).ok (cost .first 12)=true := by decide
def firstPlan13 : Plan := ⟨1,[(16,.directed 6 0),(2,.directed 6 1),(10,.triple 0 1 2),(14,.omitPair 0 6),(10,.omitPair 3 6),(10,.omitPair 4 6),(10,.omitPair 5 6)]⟩
theorem firstOk13 : (firstPlan13).ok (cost .first 13)=true := by decide
def firstPlan14 : Plan := ⟨1,[(2,.directed 6 0),(2,.triple 0 1 2),(2,.omitPair 0 6),(2,.omitPair 3 6),(2,.omitPair 4 6),(2,.omitPair 5 6)]⟩
theorem firstOk14 : (firstPlan14).ok (cost .first 14)=true := by decide
def firstPlan15 : Plan := ⟨1,[(1,.directed 6 0)]⟩
theorem firstOk15 : (firstPlan15).ok (cost .first 15)=true := by decide
def firstPlan16 : Plan := ⟨1,[(7,.directed 6 0)]⟩
theorem firstOk16 : (firstPlan16).ok (cost .first 16)=true := by decide
def firstPlan17 : Plan := ⟨1,[(16,.directed 6 0)]⟩
theorem firstOk17 : (firstPlan17).ok (cost .first 17)=true := by decide
def firstPlan18 : Plan := ⟨1,[(12,.directed 6 0)]⟩
theorem firstOk18 : (firstPlan18).ok (cost .first 18)=true := by decide
def firstPlan19 : Plan := ⟨1,[(4,.directed 6 0),(1,.triple 0 1 2)]⟩
theorem firstOk19 : (firstPlan19).ok (cost .first 19)=true := by decide
def firstPlan20 : Plan := ⟨1,[(18,.directed 6 0),(5,.triple 0 1 2)]⟩
theorem firstOk20 : (firstPlan20).ok (cost .first 20)=true := by decide
def firstPlan21 : Plan := ⟨1,[(20,.directed 6 0),(6,.triple 0 1 2)]⟩
theorem firstOk21 : (firstPlan21).ok (cost .first 21)=true := by decide
def firstPlan22 : Plan := ⟨1,[(5,.directed 6 0),(3,.triple 0 1 2)]⟩
theorem firstOk22 : (firstPlan22).ok (cost .first 22)=true := by decide
def firstPlan23 : Plan := ⟨1,[(11,.directed 6 0),(7,.triple 0 1 2)]⟩
theorem firstOk23 : (firstPlan23).ok (cost .first 23)=true := by decide
def firstPlan24 : Plan := ⟨1,[(2,.directed 6 0),(2,.triple 0 1 2)]⟩
theorem firstOk24 : (firstPlan24).ok (cost .first 24)=true := by decide
theorem firstPlans (j : Nat) (hj : j∈tags) : ∃ p : Plan,p.ok (cost .first j)=true := by
  simp only [tags,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,firstOk0⟩
  · exact ⟨_,firstOk1⟩
  · exact ⟨_,firstOk2⟩
  · exact ⟨_,firstOk3⟩
  · exact ⟨_,firstOk4⟩
  · exact ⟨_,firstOk5⟩
  · exact ⟨_,firstOk6⟩
  · exact ⟨_,firstOk7⟩
  · exact ⟨_,firstOk8⟩
  · exact ⟨_,firstOk9⟩
  · exact ⟨_,firstOk10⟩
  · exact ⟨_,firstOk11⟩
  · exact ⟨_,firstOk12⟩
  · exact ⟨_,firstOk13⟩
  · exact ⟨_,firstOk14⟩
  · exact ⟨_,firstOk15⟩
  · exact ⟨_,firstOk16⟩
  · exact ⟨_,firstOk17⟩
  · exact ⟨_,firstOk18⟩
  · exact ⟨_,firstOk19⟩
  · exact ⟨_,firstOk20⟩
  · exact ⟨_,firstOk21⟩
  · exact ⟨_,firstOk22⟩
  · exact ⟨_,firstOk23⟩
  · exact ⟨_,firstOk24⟩
end RankSeven.LowerSmallHeadData
#print axioms RankSeven.LowerSmallHeadData.firstPlans
