import Rank7UpperCornerVector
namespace RankSeven.UpperCornerColumns
open Lean.Grind Pauli ExteriorCuts PackingDual UpperCornerExpansion UpperCornerFactors UpperCornerDual UpperPackedCoordinates UpperSignedData
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
private theorem packMap {α β : Type} (xs : List α) (f : α→β) (g : β→Int) :
    pack xs (fun i => g (f i))=pack (xs.map f) g := by
  induction xs with
  | nil => rfl
  | cons a as ih => change g (f a)+base*pack as _=g (f a)+base*pack (as.map f) g; rw [ih]
private theorem siteSlots : sites.map slot=List.range 35 := by decide
private theorem siteCost (c : Cert) (len : c.coeff.size=35) : pack sites c.cost=pack c.coeff.toList id := by
  change pack sites (fun w => c.coeff[slot w]?.getD 0)=_
  rw [packMap sites slot (fun i => c.coeff[i]?.getD 0),siteSlots]
  have ls : (List.range 35).map (fun i => c.coeff[i]?.getD 0)=c.coeff.toList := by
    apply List.ext_getElem
    · simp [len]
    · intro i h t
      simp at h; have g : i<c.coeff.size := len ▸ h
      simp [Array.getElem?_eq_getElem g]
  exact (packMap (List.range 35) (fun i => c.coeff[i]?.getD 0) id).trans (congrArg (fun xs => pack xs id) ls)
private theorem packedTable : allData.toList.map (fun c => pack c.val.coeff.toList id)=packedObj.toList := by decide
private theorem widths : allData.toList.all (fun c => c.val.coeff.size == 35)=true := by decide
theorem packedObject (j : Nat) (hj : j<286) : pack sites (objective j).cost=pObj j := by
  have ja : j<allData.size := hj
  have h := Array.getElem?_eq_getElem ja
  have member : allData[j] ∈ allData.toList := by simp
  have w := beq_iff_eq.mp (List.all_eq_true.mp widths _ member)
  change pack sites ((allData[j]?.getD ⟨obj0,ok0⟩).val.cost)=_
  rw [h]; change pack sites allData[j].val.cost=_
  rw [siteCost _ w]
  have eq := congrArg (fun l : List Int => l[j]?.getD 0) packedTable
  simpa only [List.getElem?_map,Array.getElem?_toList,h,Option.map_some,Option.getD_some,pObj] using eq
end RankSeven.UpperCornerColumns
#print axioms RankSeven.UpperCornerColumns.packedObject
