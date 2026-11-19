import Rank7UpperCornerDual
namespace RankSeven.UpperSignedData
open UpperCornerDual
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
def obj24 : Cert := ⟨#[6,6,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(4,(.row (.triple 0 1 2))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok24 : obj24.check=true := by decide
def obj25 : Cert := ⟨#[13,13,5,2,2,7,3,1,1,3,1,1,0,0,0,1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(8,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(3,(.row (.omitPair 5 6)))]⟩
theorem ok25 : obj25.check=true := by decide
def obj26 : Cert := ⟨#[12,12,4,2,2,6,2,1,1,2,1,1,0,0,0,6,2,1,1,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(5,(.row (.omitPair 5 6)))]⟩
theorem ok26 : obj26.check=true := by decide
def obj27 : Cert := ⟨#[7,7,3,1,1,7,3,1,1,3,1,1,0,0,0,1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok27 : obj27.check=true := by decide
def obj28 : Cert := ⟨#[12,12,4,2,2,12,4,2,2,4,2,2,0,0,0,6,2,1,1,2,1,1,0,0,0,2,1,1,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(6,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 4))),(1,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok28 : obj28.check=true := by decide
def obj29 : Cert := ⟨#[5,5,1,1,1,5,1,1,1,1,1,1,0,0,0,5,1,1,1,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 4))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok29 : obj29.check=true := by decide
def obj30 : Cert := ⟨#[3,3,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(3,(.row (.omitPair 5 6)))]⟩
theorem ok30 : obj30.check=true := by decide
def obj31 : Cert := ⟨#[28,28,19,9,9,10,7,3,3,7,3,3,2,2,0,1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(9,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(13,(.row (.omitPair 5 6)))]⟩
theorem ok31 : obj31.check=true := by decide
def obj32 : Cert := ⟨#[27,27,18,9,9,9,6,3,3,6,3,3,2,2,0,9,6,3,3,6,3,3,2,2,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(8,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(8,(.row (.omitPair 5 6)))]⟩
theorem ok32 : obj32.check=true := by decide
def obj33 : Cert := ⟨#[29,29,20,9,9,20,14,6,6,14,6,6,4,4,0,2,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(4,(.row (.directed 6 0))),(4,(.row (.directed 6 1))),(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(9,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(8,(.row (.omitPair 5 6)))]⟩
theorem ok33 : obj33.check=true := by decide
def obj34 : Cert := ⟨#[57,57,39,18,18,39,27,12,12,27,12,12,8,8,0,21,15,6,6,15,6,6,4,4,0,9,3,3,2,2,0,2,2,0,0],1,[(1,(.row (.directed 3 0))),(1,(.row (.directed 3 1))),(2,(.row (.directed 4 0))),(2,(.row (.directed 4 1))),(4,(.row (.directed 5 0))),(4,(.row (.directed 5 1))),(8,(.row (.directed 6 0))),(8,(.row (.directed 6 1))),(2,(.row (.triple 0 1 5))),(3,(.row (.triple 0 1 4))),(3,(.row (.triple 0 1 3))),(15,(.row (.triple 0 1 2))),(1,(.row (.omitPair 2 3))),(1,(.row (.omitPair 3 5))),(3,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(9,(.row (.omitPair 5 6)))]⟩
theorem ok34 : obj34.check=true := by decide
def obj35 : Cert := ⟨#[28,28,19,9,9,19,13,6,6,13,6,6,4,4,0,19,13,6,6,13,6,6,4,4,0,7,3,3,2,2,0,2,2,0,0],1,[(1,(.row (.directed 3 0))),(1,(.row (.directed 3 1))),(2,(.row (.directed 4 0))),(2,(.row (.directed 4 1))),(4,(.row (.directed 5 0))),(4,(.row (.directed 5 1))),(4,(.row (.directed 6 0))),(4,(.row (.directed 6 1))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(6,(.row (.triple 0 1 2))),(1,(.row (.omitPair 2 3))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok35 : obj35.check=true := by decide
def obj36 : Cert := ⟨#[10,10,7,3,3,10,7,3,3,7,3,3,2,2,0,1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(3,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok36 : obj36.check=true := by decide
def obj37 : Cert := ⟨#[30,30,21,9,9,30,21,9,9,21,9,9,6,6,0,12,9,3,3,9,3,3,2,2,0,9,3,3,2,2,0,2,2,0,0],2,[(1,(.row (.directed 2 0))),(1,(.row (.directed 2 1))),(3,(.row (.directed 3 0))),(3,(.row (.directed 3 1))),(3,(.row (.directed 4 0))),(3,(.row (.directed 4 1))),(3,(.row (.directed 5 0))),(3,(.row (.directed 5 1))),(11,(.row (.directed 6 0))),(11,(.row (.directed 6 1))),(4,(.row (.triple 0 1 5))),(4,(.row (.triple 0 1 4))),(4,(.row (.triple 0 1 3))),(14,(.row (.triple 0 1 2))),(4,(.row (.omitPair 3 6))),(4,(.row (.omitPair 4 6))),(4,(.row (.omitPair 5 6)))]⟩
theorem ok37 : obj37.check=true := by decide
def obj38 : Cert := ⟨#[30,30,21,9,9,30,21,9,9,21,9,9,6,6,0,21,15,6,6,15,6,6,4,4,0,15,6,6,4,4,0,4,4,0,0],1,[(4,(.row (.directed 3 0))),(4,(.row (.directed 3 1))),(2,(.row (.directed 4 0))),(2,(.row (.directed 4 1))),(2,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(5,(.row (.directed 6 0))),(5,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(5,(.row (.triple 0 1 2))),(2,(.row (.omitPair 2 4))),(2,(.row (.omitPair 2 5))),(1,(.row (.omitPair 2 6))),(2,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok38 : obj38.check=true := by decide
def obj39 : Cert := ⟨#[10,10,7,3,3,10,7,3,3,7,3,3,2,2,0,10,7,3,3,7,3,3,2,2,0,7,3,3,2,2,0,2,2,0,0],2,[(1,(.row (.directed 2 0))),(1,(.row (.directed 2 1))),(3,(.row (.directed 3 0))),(3,(.row (.directed 3 1))),(3,(.row (.directed 4 0))),(3,(.row (.directed 4 1))),(3,(.row (.directed 5 0))),(3,(.row (.directed 5 1))),(3,(.row (.directed 6 0))),(3,(.row (.directed 6 1))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok39 : obj39.check=true := by decide
def obj40 : Cert := ⟨#[9,9,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(7,(.row (.triple 0 1 2))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok40 : obj40.check=true := by decide
def obj41 : Cert := ⟨#[18,18,4,4,4,9,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(5,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(11,(.row (.omitPair 5 6)))]⟩
theorem ok41 : obj41.check=true := by decide
def obj42 : Cert := ⟨#[18,18,4,4,4,9,2,2,2,2,2,2,0,0,0,9,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(5,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(9,(.row (.omitPair 5 6)))]⟩
theorem ok42 : obj42.check=true := by decide
def obj43 : Cert := ⟨#[9,9,2,2,2,9,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(5,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok43 : obj43.check=true := by decide
def obj44 : Cert := ⟨#[18,18,4,4,4,18,4,4,4,4,4,4,0,0,0,9,2,2,2,2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0],1,[(8,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 4))),(2,(.row (.omitPair 3 5))),(4,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(4,(.row (.omitPair 4 6))),(4,(.row (.omitPair 5 6)))]⟩
theorem ok44 : obj44.check=true := by decide
def obj45 : Cert := ⟨#[9,9,2,2,2,9,2,2,2,2,2,2,0,0,0,9,2,2,2,2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0],1,[(3,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 4))),(2,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok45 : obj45.check=true := by decide
def obj46 : Cert := ⟨#[9,9,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(5,(.row (.triple 0 1 2))),(4,(.row (.omitPair 5 6)))]⟩
theorem ok46 : obj46.check=true := by decide
def obj47 : Cert := ⟨#[81,81,36,36,36,27,12,12,12,12,12,12,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(4,(.row (.directed 6 0))),(7,(.row (.triple 0 1 2))),(4,(.row (.omitPair 0 6))),(8,(.row (.omitPair 3 6))),(8,(.row (.omitPair 4 6))),(62,(.row (.omitPair 5 6)))]⟩
theorem ok47 : obj47.check=true := by decide
end RankSeven.UpperSignedData
#print axioms RankSeven.UpperSignedData.ok47
