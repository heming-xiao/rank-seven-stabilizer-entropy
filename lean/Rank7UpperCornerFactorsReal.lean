import Rank7UpperCornerFactorEval0
import Rank7UpperCornerFactorEval1
import Rank7UpperCornerFactorEval2
import Rank7UpperCornerFactorEval3
import Rank7UpperCornerFactorEval4
import Rank7UpperCornerFactorEval5
import Rank7UpperCornerFactorEval6
import Rank7UpperCornerFactorEval7
import Rank7UpperCornerFactorEval8
namespace RankSeven.UpperCornerFactors
open Lean.Grind Pauli UpperCornerExpansion
attribute [local instance] Ring.intCast
theorem realExpansion {R : Type} [CommRing R] (v : Var→R) (i : Nat) (hi : i<54) :
    eval v (pattern i)=sumOver keys (fun m => Int.cast (fast i m)*mon v m) := by
  have cases54 : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9∨i=10∨i=11∨i=12∨i=13∨i=14∨i=15∨i=16∨i=17∨i=18∨i=19∨i=20∨i=21∨i=22∨i=23∨i=24∨i=25∨i=26∨i=27∨i=28∨i=29∨i=30∨i=31∨i=32∨i=33∨i=34∨i=35∨i=36∨i=37∨i=38∨i=39∨i=40∨i=41∨i=42∨i=43∨i=44∨i=45∨i=46∨i=47∨i=48∨i=49∨i=50∨i=51∨i=52∨i=53 := by omega
  rcases cases54 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact eval0 v
  · exact eval1 v
  · exact eval2 v
  · exact eval3 v
  · exact eval4 v
  · exact eval5 v
  · exact eval6 v
  · exact eval7 v
  · exact eval8 v
  · exact eval9 v
  · exact eval10 v
  · exact eval11 v
  · exact eval12 v
  · exact eval13 v
  · exact eval14 v
  · exact eval15 v
  · exact eval16 v
  · exact eval17 v
  · exact eval18 v
  · exact eval19 v
  · exact eval20 v
  · exact eval21 v
  · exact eval22 v
  · exact eval23 v
  · exact eval24 v
  · exact eval25 v
  · exact eval26 v
  · exact eval27 v
  · exact eval28 v
  · exact eval29 v
  · exact eval30 v
  · exact eval31 v
  · exact eval32 v
  · exact eval33 v
  · exact eval34 v
  · exact eval35 v
  · exact eval36 v
  · exact eval37 v
  · exact eval38 v
  · exact eval39 v
  · exact eval40 v
  · exact eval41 v
  · exact eval42 v
  · exact eval43 v
  · exact eval44 v
  · exact eval45 v
  · exact eval46 v
  · exact eval47 v
  · exact eval48 v
  · exact eval49 v
  · exact eval50 v
  · exact eval51 v
  · exact eval52 v
  · exact eval53 v
end RankSeven.UpperCornerFactors
#print axioms RankSeven.UpperCornerFactors.realExpansion
