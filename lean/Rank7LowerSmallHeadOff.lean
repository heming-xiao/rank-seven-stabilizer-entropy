import Rank7LowerSmallHeadData
namespace RankSeven.LowerSmallHeadData
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
def offPlan0 : Plan := ⟨1,[(1,.omitPair 5 6)]⟩
theorem offOk0 : (offPlan0).ok (cost .off 0)=true := by decide
def offPlan1 : Plan := ⟨1,[(10,.omitPair 5 6)]⟩
theorem offOk1 : (offPlan1).ok (cost .off 1)=true := by decide
def offPlan2 : Plan := ⟨1,[(37,.omitPair 5 6)]⟩
theorem offOk2 : (offPlan2).ok (cost .off 2)=true := by decide
def offPlan3 : Plan := ⟨1,[(60,.omitPair 5 6)]⟩
theorem offOk3 : (offPlan3).ok (cost .off 3)=true := by decide
def offPlan4 : Plan := ⟨1,[(36,.omitPair 5 6)]⟩
theorem offOk4 : (offPlan4).ok (cost .off 4)=true := by decide
def offPlan5 : Plan := ⟨1,[(7,.omitPair 5 6)]⟩
theorem offOk5 : (offPlan5).ok (cost .off 5)=true := by decide
def offPlan6 : Plan := ⟨1,[(52,.omitPair 5 6)]⟩
theorem offOk6 : (offPlan6).ok (cost .off 6)=true := by decide
def offPlan7 : Plan := ⟨1,[(127,.omitPair 5 6)]⟩
theorem offOk7 : (offPlan7).ok (cost .off 7)=true := by decide
def offPlan8 : Plan := ⟨1,[(102,.omitPair 5 6)]⟩
theorem offOk8 : (offPlan8).ok (cost .off 8)=true := by decide
def offPlan9 : Plan := ⟨1,[(18,.omitPair 5 6)]⟩
theorem offOk9 : (offPlan9).ok (cost .off 9)=true := by decide
def offPlan10 : Plan := ⟨1,[(88,.omitPair 5 6)]⟩
theorem offOk10 : (offPlan10).ok (cost .off 10)=true := by decide
def offPlan11 : Plan := ⟨1,[(106,.omitPair 5 6)]⟩
theorem offOk11 : (offPlan11).ok (cost .off 11)=true := by decide
def offPlan12 : Plan := ⟨1,[(20,.omitPair 5 6)]⟩
theorem offOk12 : (offPlan12).ok (cost .off 12)=true := by decide
def offPlan13 : Plan := ⟨1,[(48,.omitPair 5 6)]⟩
theorem offOk13 : (offPlan13).ok (cost .off 13)=true := by decide
def offPlan14 : Plan := ⟨1,[(8,.omitPair 5 6)]⟩
theorem offOk14 : (offPlan14).ok (cost .off 14)=true := by decide
def offPlan15 : Plan := ⟨1,[(1,.omitPair 5 6)]⟩
theorem offOk15 : (offPlan15).ok (cost .off 15)=true := by decide
def offPlan16 : Plan := ⟨1,[(7,.omitPair 5 6)]⟩
theorem offOk16 : (offPlan16).ok (cost .off 16)=true := by decide
def offPlan17 : Plan := ⟨1,[(16,.omitPair 5 6)]⟩
theorem offOk17 : (offPlan17).ok (cost .off 17)=true := by decide
def offPlan18 : Plan := ⟨1,[(12,.omitPair 5 6)]⟩
theorem offOk18 : (offPlan18).ok (cost .off 18)=true := by decide
def offPlan19 : Plan := ⟨1,[(5,.omitPair 5 6)]⟩
theorem offOk19 : (offPlan19).ok (cost .off 19)=true := by decide
def offPlan20 : Plan := ⟨1,[(23,.omitPair 5 6)]⟩
theorem offOk20 : (offPlan20).ok (cost .off 20)=true := by decide
def offPlan21 : Plan := ⟨1,[(26,.omitPair 5 6)]⟩
theorem offOk21 : (offPlan21).ok (cost .off 21)=true := by decide
def offPlan22 : Plan := ⟨1,[(8,.omitPair 5 6)]⟩
theorem offOk22 : (offPlan22).ok (cost .off 22)=true := by decide
def offPlan23 : Plan := ⟨1,[(18,.omitPair 5 6)]⟩
theorem offOk23 : (offPlan23).ok (cost .off 23)=true := by decide
def offPlan24 : Plan := ⟨1,[(4,.omitPair 5 6)]⟩
theorem offOk24 : (offPlan24).ok (cost .off 24)=true := by decide
theorem offPlans (j : Nat) (hj : j∈tags) : ∃ p : Plan,p.ok (cost .off j)=true := by
  simp only [tags,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,offOk0⟩
  · exact ⟨_,offOk1⟩
  · exact ⟨_,offOk2⟩
  · exact ⟨_,offOk3⟩
  · exact ⟨_,offOk4⟩
  · exact ⟨_,offOk5⟩
  · exact ⟨_,offOk6⟩
  · exact ⟨_,offOk7⟩
  · exact ⟨_,offOk8⟩
  · exact ⟨_,offOk9⟩
  · exact ⟨_,offOk10⟩
  · exact ⟨_,offOk11⟩
  · exact ⟨_,offOk12⟩
  · exact ⟨_,offOk13⟩
  · exact ⟨_,offOk14⟩
  · exact ⟨_,offOk15⟩
  · exact ⟨_,offOk16⟩
  · exact ⟨_,offOk17⟩
  · exact ⟨_,offOk18⟩
  · exact ⟨_,offOk19⟩
  · exact ⟨_,offOk20⟩
  · exact ⟨_,offOk21⟩
  · exact ⟨_,offOk22⟩
  · exact ⟨_,offOk23⟩
  · exact ⟨_,offOk24⟩
end RankSeven.LowerSmallHeadData
#print axioms RankSeven.LowerSmallHeadData.offPlans
