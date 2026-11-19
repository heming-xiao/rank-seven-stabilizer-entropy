import Rank7UpperCornerDual
namespace RankSeven.UpperSignedData
open UpperCornerDual
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
def obj144 : Cert := ⟨#[8,8,6,6,0,8,6,6,0,6,6,0,4,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(6,(.row (.directed 6 0))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok144 : obj144.check=true := by decide
def obj145 : Cert := ⟨#[14,14,10,10,0,14,10,10,0,10,10,0,6,0,0,5,4,4,0,4,4,0,2,0,0,4,4,0,2,0,0,2,0,0,0],1,[(2,(.row (.directed 3 0))),(2,(.row (.directed 4 0))),(2,(.row (.directed 5 0))),(8,(.row (.directed 6 0))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok145 : obj145.check=true := by decide
def obj146 : Cert := ⟨#[32,32,22,22,0,32,22,22,0,22,22,0,12,0,0,23,16,16,0,16,16,0,8,0,0,16,16,0,8,0,0,8,0,0,0],1,[(8,(.row (.directed 3 0))),(8,(.row (.directed 4 0))),(8,(.row (.directed 5 0))),(14,(.row (.directed 6 0))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok146 : obj146.check=true := by decide
def obj147 : Cert := ⟨#[3,3,2,2,0,3,2,2,0,2,2,0,1,0,0,3,2,2,0,2,2,0,1,0,0,2,2,0,1,0,0,1,0,0,0],1,[(1,(.row (.directed 3 0))),(1,(.row (.directed 4 0))),(1,(.row (.directed 5 0))),(1,(.row (.directed 6 0)))]⟩
theorem ok147 : obj147.check=true := by decide
def obj148 : Cert := ⟨#[11,11,5,2,2,5,3,1,1,3,1,1,0,0,0,-1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(6,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(3,(.row (.omitPair 5 6)))]⟩
theorem ok148 : obj148.check=true := by decide
def obj149 : Cert := ⟨#[10,10,4,2,2,4,2,1,1,2,1,1,0,0,0,4,2,1,1,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(5,(.row (.omitPair 5 6)))]⟩
theorem ok149 : obj149.check=true := by decide
def obj150 : Cert := ⟨#[5,5,3,1,1,5,3,1,1,3,1,1,0,0,0,-1,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok150 : obj150.check=true := by decide
def obj151 : Cert := ⟨#[8,8,4,2,2,8,4,2,2,4,2,2,0,0,0,2,2,1,1,2,1,1,0,0,0,2,1,1,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 4))),(1,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok151 : obj151.check=true := by decide
def obj152 : Cert := ⟨#[3,3,1,1,1,3,1,1,1,1,1,1,0,0,0,3,1,1,1,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,0],1,[(1,(.row (.omitPair 3 4))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok152 : obj152.check=true := by decide
def obj153 : Cert := ⟨#[27,27,19,9,9,9,7,3,3,7,3,3,2,2,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(8,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(13,(.row (.omitPair 5 6)))]⟩
theorem ok153 : obj153.check=true := by decide
def obj154 : Cert := ⟨#[26,26,18,9,9,8,6,3,3,6,3,3,2,2,0,8,6,3,3,6,3,3,2,2,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(7,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 5))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 5))),(1,(.row (.omitPair 4 6))),(8,(.row (.omitPair 5 6)))]⟩
theorem ok154 : obj154.check=true := by decide
def obj155 : Cert := ⟨#[27,27,20,9,9,18,14,6,6,14,6,6,4,4,0,0,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(4,(.row (.directed 6 0))),(4,(.row (.directed 6 1))),(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(7,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(8,(.row (.omitPair 5 6)))]⟩
theorem ok155 : obj155.check=true := by decide
def obj156 : Cert := ⟨#[59,59,41,22,18,41,29,16,12,29,16,12,8,8,0,23,17,10,6,17,10,6,4,4,0,11,7,3,2,2,0,2,2,0,0],1,[(2,(.row (.directed 2 1))),(2,(.row (.directed 3 0))),(2,(.row (.directed 4 0))),(4,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(8,(.row (.directed 6 0))),(6,(.row (.directed 6 1))),(2,(.row (.triple 0 1 5))),(3,(.row (.triple 0 1 4))),(3,(.row (.triple 0 1 3))),(11,(.row (.triple 0 1 2))),(3,(.row (.omitPair 3 4))),(4,(.row (.omitPair 3 5))),(6,(.row (.omitPair 3 6))),(4,(.row (.omitPair 4 5))),(6,(.row (.omitPair 4 6))),(13,(.row (.omitPair 5 6)))]⟩
theorem ok156 : obj156.check=true := by decide
def obj157 : Cert := ⟨#[32,32,21,13,9,23,15,10,6,15,10,6,4,4,0,23,15,10,6,15,10,6,4,4,0,9,7,3,2,2,0,2,2,0,0],1,[(2,(.row (.directed 2 1))),(2,(.row (.directed 3 0))),(2,(.row (.directed 4 0))),(4,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(4,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2))),(3,(.row (.omitPair 3 4))),(4,(.row (.omitPair 3 5))),(4,(.row (.omitPair 3 6))),(4,(.row (.omitPair 4 5))),(4,(.row (.omitPair 4 6))),(5,(.row (.omitPair 5 6)))]⟩
theorem ok157 : obj157.check=true := by decide
def obj158 : Cert := ⟨#[9,9,7,3,3,9,7,3,3,7,3,3,2,2,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2))),(1,(.row (.omitPair 3 6))),(1,(.row (.omitPair 4 6))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok158 : obj158.check=true := by decide
def obj159 : Cert := ⟨#[33,33,23,13,9,33,23,13,9,23,13,9,6,6,0,15,11,7,3,11,7,3,2,2,0,11,7,3,2,2,0,2,2,0,0],1,[(2,(.row (.directed 2 1))),(2,(.row (.directed 3 0))),(2,(.row (.directed 4 0))),(2,(.row (.directed 5 0))),(6,(.row (.directed 6 0))),(4,(.row (.directed 6 1))),(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2))),(3,(.row (.omitPair 3 4))),(3,(.row (.omitPair 3 5))),(5,(.row (.omitPair 3 6))),(3,(.row (.omitPair 4 5))),(5,(.row (.omitPair 4 6))),(5,(.row (.omitPair 5 6)))]⟩
theorem ok159 : obj159.check=true := by decide
def obj160 : Cert := ⟨#[39,39,25,17,9,39,25,17,9,25,17,9,6,6,0,30,19,14,6,19,14,6,4,4,0,19,14,6,4,4,0,4,4,0,0],1,[(4,(.row (.directed 2 1))),(4,(.row (.directed 3 0))),(4,(.row (.directed 4 0))),(4,(.row (.directed 5 0))),(6,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(1,(.row (.triple 0 1 5))),(1,(.row (.triple 0 1 4))),(1,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2))),(6,(.row (.omitPair 3 4))),(6,(.row (.omitPair 3 5))),(7,(.row (.omitPair 3 6))),(6,(.row (.omitPair 4 5))),(7,(.row (.omitPair 4 6))),(7,(.row (.omitPair 5 6)))]⟩
theorem ok160 : obj160.check=true := by decide
def obj161 : Cert := ⟨#[15,15,9,7,3,15,9,7,3,9,7,3,2,2,0,15,9,7,3,9,7,3,2,2,0,9,7,3,2,2,0,2,2,0,0],1,[(2,(.row (.directed 2 1))),(2,(.row (.directed 3 0))),(2,(.row (.directed 4 0))),(2,(.row (.directed 5 0))),(2,(.row (.directed 6 0))),(3,(.row (.omitPair 3 4))),(3,(.row (.omitPair 3 5))),(3,(.row (.omitPair 3 6))),(3,(.row (.omitPair 4 5))),(3,(.row (.omitPair 4 6))),(3,(.row (.omitPair 5 6)))]⟩
theorem ok161 : obj161.check=true := by decide
def obj162 : Cert := ⟨#[15,15,4,4,4,6,2,2,2,2,2,2,0,0,0,-3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(11,(.row (.omitPair 5 6)))]⟩
theorem ok162 : obj162.check=true := by decide
def obj163 : Cert := ⟨#[15,15,4,4,4,6,2,2,2,2,2,2,0,0,0,6,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(9,(.row (.omitPair 5 6)))]⟩
theorem ok163 : obj163.check=true := by decide
def obj164 : Cert := ⟨#[6,6,2,2,2,6,2,2,2,2,2,2,0,0,0,-3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 6))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok164 : obj164.check=true := by decide
def obj165 : Cert := ⟨#[12,12,4,4,4,12,4,4,4,4,4,4,0,0,0,3,2,2,2,2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 4))),(2,(.row (.omitPair 3 5))),(4,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(4,(.row (.omitPair 4 6))),(4,(.row (.omitPair 5 6)))]⟩
theorem ok165 : obj165.check=true := by decide
def obj166 : Cert := ⟨#[78,78,36,36,36,24,12,12,12,12,12,12,4,4,4,-3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(4,(.row (.directed 6 0))),(4,(.row (.directed 6 1))),(4,(.row (.directed 6 2))),(4,(.row (.triple 0 1 2))),(4,(.row (.omitPair 3 6))),(4,(.row (.omitPair 4 6))),(58,(.row (.omitPair 5 6)))]⟩
theorem ok166 : obj166.check=true := by decide
def obj167 : Cert := ⟨#[39,39,18,18,18,12,6,6,6,6,6,6,2,2,2,12,6,6,6,6,6,6,2,2,2,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.directed 5 0))),(2,(.row (.directed 5 1))),(2,(.row (.directed 5 2))),(2,(.row (.directed 6 0))),(2,(.row (.directed 6 1))),(2,(.row (.directed 6 2))),(13,(.row (.triple 0 1 2))),(2,(.row (.omitPair 3 5))),(2,(.row (.omitPair 3 6))),(2,(.row (.omitPair 4 5))),(2,(.row (.omitPair 4 6))),(10,(.row (.omitPair 5 6)))]⟩
theorem ok167 : obj167.check=true := by decide
end RankSeven.UpperSignedData
#print axioms RankSeven.UpperSignedData.ok167
