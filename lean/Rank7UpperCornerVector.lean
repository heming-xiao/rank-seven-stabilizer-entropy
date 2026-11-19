import Rank7UpperCornerColumns
namespace RankSeven.UpperCornerVector
open Lean.Grind Pauli UpperCornerExpansion UpperCornerFactors UpperCornerColumns UpperCornerDual UpperPackedCoordinates
def add : List Int→List Int→List Int
  | [],v => v
  | u,[] => u
  | a::as,b::bs => (a+b)::add as bs

def scale (k : Int) (v : List Int) := v.map (fun a => k*a)
def get (v : List Int) (j : Nat) := v[j]?.getD 0

theorem addGet (a b : List Int) (j : Nat) : get (add a b) j=get a j+get b j := by
  induction a generalizing b j with
  | nil => change get b j=0+get b j; grind only
  | cons x xs ih =>
    cases b with
    | nil => change get (x::xs) j=get (x::xs) j+0; grind only
    | cons y ys => cases j with
      | zero => rfl
      | succ j => exact ih ys j

theorem scaleGet (k : Int) (a : List Int) (j : Nat) : get (scale k a) j=k*get a j := by
  induction a generalizing j with
  | nil => change 0=k*0; grind only
  | cons a as ih => cases j with
    | zero => rfl
    | succ j => exact ih j

def packRows {α : Type} : List α→(α→List Int)→List Int
  | [],_ => []
  | i::is,f => add (f i) (scale base (packRows is f))

theorem packRowsGet {α : Type} (xs : List α) (f : α→List Int) (k : Nat) :
    get (packRows xs f) k=pack xs (fun i => get (f i) k) := by
  induction xs with
  | nil => rfl
  | cons i is ih => change get (add (f i) (scale base (packRows is f))) k=get (f i) k+base*pack is _
                    rw [addGet,scaleGet,ih]
theorem arrayGet (v : Array Int) (j : Nat) : get v.toList j=v[j]?.getD 0 := by simp [get]

def row (id : Nat) := (precomputed[id]?.getD #[]).toList
def featureRow (j : Fin 4) (w : ExteriorCuts.Wedge7) :=
  let c := ground w
  match j.val with
  | 0 => row c.1.1
  | 1 => if high w=1 then row c.1.2 else []
  | 2 => if second w=1 then row c.2.1 else []
  | _ => if high w=1 then row c.2.2 else []

theorem featureGet (j : Fin 4) (m : Key) (w : ExteriorCuts.Wedge7) :
    get (featureRow j w) (index m)=feature j m w := by
  have cases4 : ∀a : Fin 4,a=0∨a=1∨a=2∨a=3 := by decide
  rcases cases4 j with rfl|rfl|rfl|rfl
  · exact arrayGet _ _
  · change get (if high w=1 then row _ else []) _=high w*fast _ _
    unfold high; split <;> simp [get,row,fast]
  · change get (if second w=1 then row _ else []) _=second w*fast _ _
    unfold second; split <;> simp [get,row,fast]
  · change get (if high w=1 then row _ else []) _=high w*fast _ _
    unfold high; split <;> simp [get,row,fast]
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
private theorem f0 : packRows sites (featureRow 0)=(packFeature[0]?.getD #[]).toList := by decide
private theorem f1 : packRows sites (featureRow 1)=(packFeature[1]?.getD #[]).toList := by decide
private theorem f2 : packRows sites (featureRow 2)=(packFeature[2]?.getD #[]).toList := by decide
private theorem f3 : packRows sites (featureRow 3)=(packFeature[3]?.getD #[]).toList := by decide
theorem featurePackedFast (j : Fin 4) (m : Key) : pack sites (feature j m)=feat j m := by
  have point : (fun w => get (featureRow j w) (index m))=feature j m := funext (featureGet j m)
  rw [←point,←packRowsGet]
  have cases4 : ∀a : Fin 4,a=0∨a=1∨a=2∨a=3 := by decide
  rcases cases4 j with rfl|rfl|rfl|rfl
  · rw [f0]; exact arrayGet _ _
  · rw [f1]; exact arrayGet _ _
  · rw [f2]; exact arrayGet _ _
  · rw [f3]; exact arrayGet _ _
end RankSeven.UpperCornerVector
#print axioms RankSeven.UpperCornerVector.featurePackedFast