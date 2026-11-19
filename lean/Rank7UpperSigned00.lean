import Rank7UpperCornerDual
namespace RankSeven.UpperSignedData
open UpperCornerDual
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
def obj0 : Cert := ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[]⟩
theorem ok0 : obj0.check=true := by decide
def obj1 : Cert := ⟨#[1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 2)))]⟩
theorem ok1 : obj1.check=true := by decide
def obj2 : Cert := ⟨#[1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 2)))]⟩
theorem ok2 : obj2.check=true := by decide
def obj3 : Cert := ⟨#[1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.triple 0 1 2)))]⟩
theorem ok3 : obj3.check=true := by decide
def obj4 : Cert := ⟨#[3,3,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(3,(.row (.omitPair 5 6)))]⟩
theorem ok4 : obj4.check=true := by decide
def obj5 : Cert := ⟨#[8,8,6,0,0,5,4,0,0,4,0,0,0,0,0,2,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok5 : obj5.check=true := by decide
def obj6 : Cert := ⟨#[6,6,4,0,0,3,2,0,0,2,0,0,0,0,0,3,2,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2)))]⟩
theorem ok6 : obj6.check=true := by decide
def obj7 : Cert := ⟨#[5,5,4,0,0,5,4,0,0,4,0,0,0,0,0,2,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(3,(.row (.triple 0 1 2)))]⟩
theorem ok7 : obj7.check=true := by decide
def obj8 : Cert := ⟨#[6,6,4,0,0,6,4,0,0,4,0,0,0,0,0,3,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(4,(.row (.triple 0 1 2)))]⟩
theorem ok8 : obj8.check=true := by decide
def obj9 : Cert := ⟨#[3,3,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(3,(.row (.omitPair 5 6)))]⟩
theorem ok9 : obj9.check=true := by decide
def obj10 : Cert := ⟨#[6,6,2,2,0,3,1,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.directed 6 0))),(2,(.row (.triple 0 1 2))),(3,(.row (.omitPair 5 6)))]⟩
theorem ok10 : obj10.check=true := by decide
def obj11 : Cert := ⟨#[4242,4242,1414,1414,200,2121,707,707,0,707,707,0,0,0,0,2121,707,707,0,707,707,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(707,(.row (.directed 5 0))),(707,(.row (.directed 6 0))),(2628,(.row (.triple 0 1 2))),(200,(.row (.omitPair 5 6)))]⟩
theorem ok11 : obj11.check=true := by decide
def obj12 : Cert := ⟨#[3,3,1,1,0,3,1,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.directed 6 0))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok12 : obj12.check=true := by decide
def obj13 : Cert := ⟨#[4,4,1,1,0,4,1,1,0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.directed 6 0))),(3,(.row (.triple 0 1 2)))]⟩
theorem ok13 : obj13.check=true := by decide
def obj14 : Cert := ⟨#[3,3,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(3,(.row (.omitPair 5 6)))]⟩
theorem ok14 : obj14.check=true := by decide
def obj15 : Cert := ⟨#[27,27,18,18,0,9,6,6,0,6,6,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(6,(.row (.directed 6 0))),(9,(.row (.triple 0 1 2))),(12,(.row (.omitPair 5 6)))]⟩
theorem ok15 : obj15.check=true := by decide
def obj16 : Cert := ⟨#[19089,19089,12726,12726,1200,6363,4242,4242,0,4242,4242,0,2828,0,0,6363,4242,4242,0,4242,4242,0,2828,0,0,0,0,0,0,0,0,0,0,0,0],1,[(4242,(.row (.directed 5 0))),(4242,(.row (.directed 6 0))),(6363,(.row (.triple 0 1 2))),(4242,(.row (.omitPair 5 6)))]⟩
theorem ok16 : obj16.check=true := by decide
def obj17 : Cert := ⟨#[27,27,18,18,0,18,12,12,0,12,12,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(12,(.row (.directed 6 0))),(6,(.row (.triple 0 1 2))),(9,(.row (.omitPair 5 6)))]⟩
theorem ok17 : obj17.check=true := by decide
def obj18 : Cert := ⟨#[20503,20503,13433,13433,600,14140,9191,9191,0,9191,9191,0,5656,0,0,7777,4949,4949,0,4949,4949,0,2828,0,0,2828,2828,0,1414,0,0,1414,0,0,0],1,[(1414,(.row (.directed 3 0))),(1414,(.row (.directed 4 0))),(3535,(.row (.directed 5 0))),(7777,(.row (.directed 6 0))),(5656,(.row (.triple 0 1 2))),(2121,(.row (.omitPair 5 6)))]⟩
theorem ok18 : obj18.check=true := by decide
def obj19 : Cert := ⟨#[21917,21917,14140,14140,1200,15554,9898,9898,0,9898,9898,0,5656,0,0,15554,9898,9898,0,9898,9898,0,5656,0,0,5656,5656,0,2828,0,0,2828,0,0,0],1,[(2828,(.row (.directed 3 0))),(2828,(.row (.directed 4 0))),(7070,(.row (.directed 5 0))),(7070,(.row (.directed 6 0))),(3749,(.row (.triple 0 1 2))),(1200,(.row (.omitPair 5 6)))]⟩
theorem ok19 : obj19.check=true := by decide
def obj20 : Cert := ⟨#[9,9,6,6,0,9,6,6,0,6,6,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(6,(.row (.directed 6 0))),(3,(.row (.triple 0 1 2)))]⟩
theorem ok20 : obj20.check=true := by decide
def obj21 : Cert := ⟨#[31,31,20,20,0,31,20,20,0,20,20,0,12,0,0,13,8,8,0,8,8,0,4,0,0,8,8,0,4,0,0,4,0,0,0],1,[(4,(.row (.directed 3 0))),(4,(.row (.directed 4 0))),(4,(.row (.directed 5 0))),(12,(.row (.directed 6 0))),(3,(.row (.triple 0 1 2))),(4,(.row (.omitPair 3 6))),(4,(.row (.omitPair 4 6))),(4,(.row (.omitPair 5 6)))]⟩
theorem ok21 : obj21.check=true := by decide
def obj22 : Cert := ⟨#[35,35,22,22,0,35,22,22,0,22,22,0,12,0,0,26,16,16,0,16,16,0,8,0,0,16,16,0,8,0,0,8,0,0,0],1,[(8,(.row (.directed 3 0))),(8,(.row (.directed 4 0))),(8,(.row (.directed 5 0))),(14,(.row (.directed 6 0))),(5,(.row (.triple 0 1 2)))]⟩
theorem ok22 : obj22.check=true := by decide
def obj23 : Cert := ⟨#[13,13,8,8,0,13,8,8,0,8,8,0,4,0,0,13,8,8,0,8,8,0,4,0,0,8,8,0,4,0,0,4,0,0,0],1,[(4,(.row (.directed 3 0))),(4,(.row (.directed 4 0))),(4,(.row (.directed 5 0))),(4,(.row (.directed 6 0))),(1,(.row (.triple 0 1 2)))]⟩
theorem ok23 : obj23.check=true := by decide
end RankSeven.UpperSignedData
#print axioms RankSeven.UpperSignedData.ok23
