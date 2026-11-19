import Rank7UpperCornerReadout00
import Rank7UpperCornerReadout01
import Rank7UpperCornerReadout02
import Rank7UpperCornerReadout03
import Rank7UpperCornerReadout04
import Rank7UpperCornerReadout05
import Rank7UpperCornerReadout06
import Rank7UpperCornerReadout07
import Rank7UpperCornerReadout08
import Rank7UpperCornerReadout09
import Rank7UpperCornerReadout10
import Rank7UpperCornerReadout11
import Rank7UpperCornerReadout12
import Rank7UpperCornerSizes
import Rank7UpperCornerObjectivePacking
import Rank7UpperCornerPacking
import Rank7UpperCornerPolynomial
namespace RankSeven.UpperSignedCornerGain
open Lean.Grind Pauli ExteriorCuts PackingDual PackingInterpolation UpperCornerExpansion UpperCornerColumns UpperPackedCoordinates UpperCornerReadouts UpperCornerPolynomial UpperCornerDual UpperSignedData
attribute [local instance] Ring.intCast Semiring.natCast
def certifiedTags : Array {j : Nat // check j=true} := #[⟨0,checked0⟩,⟨1,checked1⟩,⟨2,checked2⟩,⟨3,checked3⟩,⟨4,checked4⟩,⟨5,checked5⟩,⟨6,checked6⟩,⟨7,checked7⟩,⟨8,checked8⟩,⟨9,checked9⟩,⟨10,checked10⟩,⟨11,checked11⟩,⟨12,checked12⟩,⟨13,checked13⟩,⟨14,checked14⟩,⟨15,checked15⟩,⟨16,checked16⟩,⟨17,checked17⟩,⟨18,checked18⟩,⟨19,checked19⟩,⟨20,checked20⟩,⟨21,checked21⟩,⟨22,checked22⟩,⟨23,checked23⟩,⟨24,checked24⟩,⟨25,checked25⟩,⟨26,checked26⟩,⟨27,checked27⟩,⟨28,checked28⟩,⟨29,checked29⟩,⟨30,checked30⟩,⟨31,checked31⟩,⟨32,checked32⟩,⟨33,checked33⟩,⟨34,checked34⟩,⟨35,checked35⟩,⟨36,checked36⟩,⟨37,checked37⟩,⟨38,checked38⟩,⟨39,checked39⟩,⟨40,checked40⟩,⟨41,checked41⟩,⟨42,checked42⟩,⟨43,checked43⟩,⟨44,checked44⟩,⟨45,checked45⟩,⟨46,checked46⟩,⟨47,checked47⟩,⟨48,checked48⟩,⟨49,checked49⟩,⟨50,checked50⟩,⟨51,checked51⟩,⟨52,checked52⟩,⟨53,checked53⟩,⟨54,checked54⟩,⟨55,checked55⟩,⟨56,checked56⟩,⟨57,checked57⟩,⟨58,checked58⟩,⟨59,checked59⟩,⟨60,checked60⟩,⟨61,checked61⟩,⟨62,checked62⟩,⟨63,checked63⟩,⟨64,checked64⟩,⟨65,checked65⟩,⟨66,checked66⟩,⟨67,checked67⟩,⟨68,checked68⟩,⟨69,checked69⟩,⟨70,checked70⟩,⟨71,checked71⟩,⟨72,checked72⟩,⟨73,checked73⟩,⟨74,checked74⟩,⟨75,checked75⟩,⟨76,checked76⟩,⟨77,checked77⟩,⟨78,checked78⟩,⟨79,checked79⟩,⟨80,checked80⟩,⟨81,checked81⟩,⟨82,checked82⟩,⟨83,checked83⟩,⟨84,checked84⟩,⟨85,checked85⟩,⟨86,checked86⟩,⟨87,checked87⟩,⟨88,checked88⟩,⟨89,checked89⟩,⟨90,checked90⟩,⟨91,checked91⟩,⟨92,checked92⟩,⟨93,checked93⟩,⟨94,checked94⟩,⟨95,checked95⟩,⟨96,checked96⟩,⟨97,checked97⟩,⟨98,checked98⟩,⟨99,checked99⟩,⟨100,checked100⟩,⟨101,checked101⟩,⟨102,checked102⟩,⟨103,checked103⟩]
theorem readAll (j : Nat) (hj : j<104) : check j=true := by
  have all : certifiedTags.toList.map Subtype.val=List.range 104 := by decide
  have hjj : j∈certifiedTags.toList.map Subtype.val := all.symm ▸ (List.mem_range.mpr hj)
  obtain ⟨a,_,e⟩ := List.mem_map.mp hjj; exact e ▸ a.property

theorem coefficient (j : Nat) (hj : j<104) (m : Key) (w : Wedge7) :
    term (tag j) m w=((sel j m).2:Int)*(objective (sel j m).1).cost w := by
  have e := readAt (readAll j hj) m
  rw [←packedTerm,←packedObject _ (UpperCornerSizes.selectionLimits j m).1,←packScale] at e
  have compare := inject sites _ _ (fun w _ => UpperCornerSizes.digitRange j m w) e
  exact compare w (List.contains_iff_mem.mp (List.all_eq_true.mp sitesFull w (memWedges w)))

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem scaleVal (x : Wedge7→R) (b : Int) (f : Wedge7→Int) :
    val x (fun w => b*f w)=Int.cast b*val x f := by
  unfold val; rw [sumOverMulLeft]; apply sumOverCongr; intro w
  rw [Ring.intCast_mul]; grind only

theorem signedCoefficient (j : Nat) (hj : j<104) (m : Key) (x : Wedge7→R) (nx : ∀w,0≤x w)
    (rows : RowsHold x) (n0 : 0≤UpperFrameTrace.sharedExcess x) (v0 : 0≤UpperFrameTrace.highExcess x) :
    gain x (fun w => Int.cast (term (tag j) m w))≤0 := by
  let b := (sel j m).2
  let o := objective (sel j m).1
  have point : term (tag j) m=fun w => (b:Int)*o.cost w := funext (coefficient j hj m)
  have dual := allObjectives (sel j m).1 x nx rows n0 v0
  change val x o.cost-val referenceWeight o.cost≤0 at dual
  have fact := OrderedRing.mul_le_mul_of_nonneg_left dual (OrderedRing.natCast_nonneg (R:=R) (a:=b))
  change val x (term (tag j) m)-val referenceWeight (term (tag j) m)≤0
  rw [point,scaleVal,scaleVal,Ring.intCast_natCast]; grind only

theorem signedPolynomial (j : Nat) (hj : j<104) (v : Var→R) (vn : ∀i,0≤v i) (x : Wedge7→R)
    (nx : ∀w,0≤x w) (rows : RowsHold x) (n0 : 0≤UpperFrameTrace.sharedExcess x) (v0 : 0≤UpperFrameTrace.highExcess x) :
    gain x (price (tag j) v)≤0 := by
  rw [gainExpansion]
  have each (m : Key) (_ : m∈keys) : mon v m * gain x (fun w => Int.cast (term (tag j) m w))≤0 := by
    have g := signedCoefficient j hj m x nx rows n0 v0
    have a := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (vn m.1.1) (vn m.1.2)) (vn m.2.1)) (vn m.2.2)
    exact Std.le_trans (OrderedRing.mul_le_mul_of_nonneg_left g a) (Std.le_of_eq (Semiring.mul_zero _))
  have eq {α : Type} (xs : List α) : sumOver xs (fun _ => (0:R))=0 := by
    induction xs with
    | nil => rfl
    | cons a as ih => change 0+sumOver as _=0; rw [ih]; grind only
  exact Std.le_trans (UpperOddCut.sumLe keys each) (Std.le_of_eq (eq keys))
end RankSeven.UpperSignedCornerGain
#print axioms RankSeven.UpperSignedCornerGain.coefficient
#print axioms RankSeven.UpperSignedCornerGain.signedPolynomial