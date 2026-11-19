import Rank7UpperCornerDual
namespace RankSeven.UpperSignedData
open UpperCornerDual
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
def obj120 : Cert := ⟨#[19817,19817,13540,13540,0,19817,13540,13540,0,13540,13540,0,8484,0,0,8891,5656,5656,0,5656,5656,0,2828,0,0,5656,5656,0,2828,0,0,2828,0,0,0],1,[(2828,(.row (.directed 3 0))),(2828,(.row (.directed 4 0))),(2828,(.row (.directed 5 0))),(8484,(.row (.directed 6 0))),(1221,(.row (.triple 0 1 2))),(2228,(.row (.omitPair 3 6))),(2228,(.row (.omitPair 4 6))),(2228,(.row (.omitPair 5 6)))]⟩
theorem ok120 : obj120.check=true := by decide
def obj121 : Cert := ⟨#[23245,23245,15254,15254,0,23245,15254,15254,0,15254,15254,0,8484,0,0,17782,11312,11312,0,11312,11312,0,5656,0,0,11312,11312,0,5656,0,0,5656,0,0,0],1,[(5656,(.row (.directed 3 0))),(5656,(.row (.directed 4 0))),(5656,(.row (.directed 5 0))),(9598,(.row (.directed 6 0))),(2335,(.row (.triple 0 1 2)))]⟩
theorem ok121 : obj121.check=true := by decide
def obj122 : Cert := ⟨#[8891,8891,5656,5656,0,8891,5656,5656,0,5656,5656,0,2828,0,0,8891,5656,5656,0,5656,5656,0,2828,0,0,5656,5656,0,2828,0,0,2828,0,0,0],1,[(2828,(.row (.directed 3 0))),(2828,(.row (.directed 4 0))),(2828,(.row (.directed 5 0))),(2828,(.row (.directed 6 0))),(407,(.row (.triple 0 1 2)))]⟩
theorem ok122 : obj122.check=true := by decide
def obj123 : Cert := ⟨#[5356,5356,3535,707,0,3385,2121,707,0,2121,707,0,0,0,0,1414,707,707,0,707,707,0,0,0,0,707,707,0,0,0,0,0,0,0,0],1,[(707,(.row (.directed 6 0))),(707,(.row (.triple 0 2 6))),(707,(.row (.triple 0 1 5))),(707,(.row (.triple 0 1 4))),(707,(.row (.triple 0 1 3))),(2528,(.row (.triple 0 1 2))),(1414,(.row (.omitPair 5 6)))]⟩
theorem ok123 : obj123.check=true := by decide
def obj124 : Cert := ⟨#[3385,3385,2121,707,0,3385,2121,707,0,2121,707,0,0,0,0,1414,707,707,0,707,707,0,0,0,0,707,707,0,0,0,0,0,0,0,0],1,[(707,(.row (.directed 6 0))),(707,(.row (.triple 0 2 6))),(707,(.row (.triple 0 1 5))),(707,(.row (.triple 0 1 4))),(707,(.row (.triple 0 1 3))),(1971,(.row (.triple 0 1 2)))]⟩
theorem ok124 : obj124.check=true := by decide
def obj125 : Cert := ⟨#[723,723,532,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(723,(.row (.omitPair 5 6)))]⟩
theorem ok125 : obj125.check=true := by decide
def obj126 : Cert := ⟨#[1978,1978,1596,0,0,1255,1064,0,0,1064,0,0,0,0,0,532,532,0,0,532,0,0,0,0,0,532,0,0,0,0,0,0,0,0,0],1,[(532,(.row (.triple 0 1 5))),(532,(.row (.triple 0 1 4))),(532,(.row (.triple 0 1 3))),(914,(.row (.triple 0 1 2))),(532,(.row (.omitPair 5 6)))]⟩
theorem ok126 : obj126.check=true := by decide
def obj127 : Cert := ⟨#[1446,1446,1064,0,0,723,532,0,0,532,0,0,0,0,0,723,532,0,0,532,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(532,(.row (.triple 0 1 4))),(532,(.row (.triple 0 1 3))),(914,(.row (.triple 0 1 2)))]⟩
theorem ok127 : obj127.check=true := by decide
def obj128 : Cert := ⟨#[1255,1255,1064,0,0,1255,1064,0,0,1064,0,0,0,0,0,532,532,0,0,532,0,0,0,0,0,532,0,0,0,0,0,0,0,0,0],1,[(532,(.row (.triple 0 1 5))),(532,(.row (.triple 0 1 4))),(532,(.row (.triple 0 1 3))),(723,(.row (.triple 0 1 2)))]⟩
theorem ok128 : obj128.check=true := by decide
def obj129 : Cert := ⟨#[1446,1446,1064,0,0,1446,1064,0,0,1064,0,0,0,0,0,723,532,0,0,532,0,0,0,0,0,532,0,0,0,0,0,0,0,0,0],1,[(532,(.row (.triple 0 1 5))),(532,(.row (.triple 0 1 4))),(532,(.row (.triple 0 1 3))),(914,(.row (.triple 0 1 2)))]⟩
theorem ok129 : obj129.check=true := by decide
def obj130 : Cert := ⟨#[1978,1978,1330,266,0,1255,798,266,0,798,266,0,0,0,0,532,266,266,0,266,266,0,0,0,0,266,266,0,0,0,0,0,0,0,0],1,[(266,(.row (.directed 6 0))),(266,(.row (.triple 0 2 6))),(266,(.row (.triple 0 1 5))),(266,(.row (.triple 0 1 4))),(266,(.row (.triple 0 1 3))),(914,(.row (.triple 0 1 2))),(532,(.row (.omitPair 5 6)))]⟩
theorem ok130 : obj130.check=true := by decide
def obj131 : Cert := ⟨#[1255,1255,798,266,0,1255,798,266,0,798,266,0,0,0,0,532,266,266,0,266,266,0,0,0,0,266,266,0,0,0,0,0,0,0,0],1,[(266,(.row (.directed 6 0))),(266,(.row (.triple 0 2 6))),(266,(.row (.triple 0 1 5))),(266,(.row (.triple 0 1 4))),(266,(.row (.triple 0 1 3))),(723,(.row (.triple 0 1 2)))]⟩
theorem ok131 : obj131.check=true := by decide
def obj132 : Cert := ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[]⟩
theorem ok132 : obj132.check=true := by decide
def obj133 : Cert := ⟨#[7,7,6,0,0,4,4,0,0,4,0,0,0,0,0,1,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(3,(.row (.triple 0 1 2))),(2,(.row (.omitPair 5 6)))]⟩
theorem ok133 : obj133.check=true := by decide
def obj134 : Cert := ⟨#[5,5,4,0,0,2,2,0,0,2,0,0,0,0,0,2,2,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(3,(.row (.triple 0 1 2)))]⟩
theorem ok134 : obj134.check=true := by decide
def obj135 : Cert := ⟨#[4,4,4,0,0,4,4,0,0,4,0,0,0,0,0,1,2,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],1,[(2,(.row (.triple 0 1 5))),(2,(.row (.triple 0 1 4))),(2,(.row (.triple 0 1 3))),(2,(.row (.triple 0 1 2)))]⟩
theorem ok135 : obj135.check=true := by decide
def obj136 : Cert := ⟨#[5,5,2,2,0,2,1,1,0,1,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.directed 6 0))),(3,(.row (.triple 0 1 2))),(1,(.row (.omitPair 5 6)))]⟩
theorem ok136 : obj136.check=true := by decide
def obj137 : Cert := ⟨#[3535,3535,1414,1414,200,1414,707,707,0,707,707,0,0,0,0,1414,707,707,0,707,707,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(707,(.row (.directed 5 0))),(707,(.row (.directed 6 0))),(1921,(.row (.triple 0 1 2))),(200,(.row (.omitPair 5 6)))]⟩
theorem ok137 : obj137.check=true := by decide
def obj138 : Cert := ⟨#[2,2,1,1,0,2,1,1,0,1,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(1,(.row (.directed 6 0))),(1,(.row (.triple 0 1 2)))]⟩
theorem ok138 : obj138.check=true := by decide
def obj139 : Cert := ⟨#[26,26,18,18,0,8,6,6,0,6,6,0,4,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(6,(.row (.directed 6 0))),(8,(.row (.triple 0 1 2))),(12,(.row (.omitPair 5 6)))]⟩
theorem ok139 : obj139.check=true := by decide
def obj140 : Cert := ⟨#[9191,9191,6363,6363,600,2828,2121,2121,0,2121,2121,0,1414,0,0,2828,2121,2121,0,2121,2121,0,1414,0,0,0,0,0,0,0,0,0,0,0,0],1,[(2121,(.row (.directed 5 0))),(2121,(.row (.directed 6 0))),(2828,(.row (.triple 0 1 2))),(2121,(.row (.omitPair 5 6)))]⟩
theorem ok140 : obj140.check=true := by decide
def obj141 : Cert := ⟨#[25,25,18,18,0,16,12,12,0,12,12,0,8,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1,[(12,(.row (.directed 6 0))),(7,(.row (.triple 0 1 2))),(6,(.row (.omitPair 5 6)))]⟩
theorem ok141 : obj141.check=true := by decide
def obj142 : Cert := ⟨#[19089,19089,13433,13433,600,12726,9191,9191,0,9191,9191,0,5656,0,0,6363,4949,4949,0,4949,4949,0,2828,0,0,2828,2828,0,1414,0,0,1414,0,0,0],1,[(1414,(.row (.directed 3 0))),(1414,(.row (.directed 4 0))),(3535,(.row (.directed 5 0))),(7777,(.row (.directed 6 0))),(4242,(.row (.triple 0 1 2))),(2121,(.row (.omitPair 5 6)))]⟩
theorem ok142 : obj142.check=true := by decide
def obj143 : Cert := ⟨#[20503,20503,14140,14140,1200,14140,9898,9898,0,9898,9898,0,5656,0,0,14140,9898,9898,0,9898,9898,0,5656,0,0,5656,5656,0,2828,0,0,2828,0,0,0],1,[(2828,(.row (.directed 3 0))),(2828,(.row (.directed 4 0))),(7070,(.row (.directed 5 0))),(7070,(.row (.directed 6 0))),(2335,(.row (.triple 0 1 2))),(1200,(.row (.omitPair 5 6)))]⟩
theorem ok143 : obj143.check=true := by decide
end RankSeven.UpperSignedData
#print axioms RankSeven.UpperSignedData.ok143
