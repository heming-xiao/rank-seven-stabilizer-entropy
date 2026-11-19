import Rank7FiveShuffleCAR

/-! Coordinate normal ordering and bilinear polarization for the two-hole
transport identity. The two repeated u coefficients are unconjugated. -/
namespace RankSeven.PhysicalTwoHoleTransport

open Pauli GenericExteriorKernel Lean.Grind
open PhysicalCutCapacities (Triple extend)
open FiveShuffleCAR (Five atSlot)
variable {C : Type} [CommRing C]
private def remove {α : Type} (v : Five α) (p : Fin 5) : Four α :=
  let k (i : Fin 4) : Fin 5 := ⟨if i.val<p.val then i.val else i.val+1,by split <;> omega⟩
  ((atSlot v (k 0),atSlot v (k 1)),(atSlot v (k 2),atSlot v (k 3)))

def boundary {n : Nat} (i half : C) (u : Triple (Basis n)) (v : Five (Basis n)) : C :=
  sumOver (List.finRange 5) (fun j => signed (j.val%2==1)
    (exteriorKernel i half (extend u (atSlot v j)) (remove v j)))

/-- Coefficient of the common-mode sum of the two-annihilator /
two-creator Pauli expression from grade three to grade two. -/
def commonMode {n : Nat} (i half : C) (b : Basis n × Basis n) (s : Triple (Basis n)) (j k l : Basis n) :=
   exteriorKernel i half ((j,s.1.1),b) ((k,l),(s.1.2,s.2)) -
   exteriorKernel i half ((j,s.1.2),b) ((k,l),(s.1.1,s.2)) +
   exteriorKernel i half ((j,s.2),b) ((k,l),s.1)

def direct {n : Nat} (i half : C) (b : Basis n × Basis n) (s : Triple (Basis n)) (j k l : Basis n) :=
  exteriorKernel i half ((j,l),b) ((k,s.1.1),(s.1.2,s.2))

private theorem swapBlocks {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (a b : Basis n × Basis n) (v : Four (Basis n)) :
    exteriorKernel i half (a,b) v=exteriorKernel i half (b,a) v := by
  have h := kernel_reorder_left i half hi hh (b,a) v ((2,3),(0,1)) (by decide)
  exact h

private theorem antiPair {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (b : Basis n × Basis n) (v : Four (Basis n)) (j k : Basis n) :
    exteriorKernel i half ((k,j),b) v= -exteriorKernel i half ((j,k),b) v := by
  exact kernel_reorder_left i half hi hh ((j,k),b) v ((1,0),(2,3)) (by decide)

/-- Exact normal ordering before exchanging j and k. Only the four-copy
Pauli determinant and its verified antisymmetry enter this equation. -/
theorem physicalNormalOrder {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (b : Basis n × Basis n) (s : Triple (Basis n)) (j k l : Basis n) :
    commonMode i half b s j k l - direct i half b s j k l =
    boundary i half (b,j) ((k,l),s) - exteriorKernel i half ((j,k),b) ((l,s.1.1),(s.1.2,s.2)) := by
  let K := exteriorKernel i half (n:=n)
  change commonMode i half b s j k l - direct i half b s j k l =
      (K (b,(j,k)) ((l,s.1.1),(s.1.2,s.2)) +
      (-(K (b,(j,l)) ((k,s.1.1),(s.1.2,s.2))) +
      (K (b,(j,s.1.1)) ((k,l),(s.1.2,s.2)) +
      (-(K (b,(j,s.1.2)) ((k,l),(s.1.1,s.2))) +
      (K (b,(j,s.2)) ((k,l),s.1) + 0))))) - K ((j,k),b) ((l,s.1.1),(s.1.2,s.2))
  dsimp only [K,commonMode,direct]
  rw [swapBlocks i half hi hh b (j,k),swapBlocks i half hi hh b (j,l),
    swapBlocks i half hi hh b (j,s.1.1),swapBlocks i half hi hh b (j,s.1.2),swapBlocks i half hi hh b (j,s.2)]
  grind only

private theorem constantZero {I : Type} (xs : List I) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with | nil => rfl | cons x xs ih => change 0+sumOver xs _=0; rw [ih]; grind

private theorem pairSumZero {I : Type} (half : C) (hh : 2*half=1) (xs : List I)
    (u : I → C) (f : I → I → C) (skew : ∀j k,f k j= -f j k) :
    sumOver xs (fun j => sumOver xs (fun k => (u j*u k)*f j k))=0 := by
  let w (j k : I) := (u j*u k)*f j k
  let Z := sumOver xs (fun j => sumOver xs (w j))
  have h : Z+Z=0 := by
    change sumOver xs (fun j => sumOver xs (w j)) + sumOver xs (fun j => sumOver xs (w j)) = 0
    conv => lhs; arg 2; rw [sumOverSwap]
    rw [←sumOverAdd]
    have row (j : I) : sumOver xs (w j)+sumOver xs (fun k => w k j)=0 := by
      rw [←sumOverAdd]
      have eq (k : I) : w j k+w k j=0 := by unfold w; rw [skew k j]; grind only
      rw [sumOverCongr xs eq]; exact constantZero xs
    rw [sumOverCongr xs row]; exact constantZero xs
  change Z=0
  have sc := congrArg (fun t => half*t) h; grind only

/-- Pointwise removal of the common mode against identical complex
coefficients in the two u slots. The remaining finite input is the
cross-boundary transposition on the physical eight-site kernel. -/
theorem transportFromCross {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (b : Basis n × Basis n) (s : Triple (Basis n)) (u : Basis n→C) (l : Basis n)
    (cross : ∀j k,boundary i half (b,k) ((j,l),s)= -boundary i half (b,j) ((k,l),s)) :
    sumOver (qubitIndices n) (fun j => sumOver (qubitIndices n) (fun k => (u j*u k)*commonMode i half b s j k l))=
    sumOver (qubitIndices n) (fun j => sumOver (qubitIndices n) (fun k => (u j*u k)*direct i half b s j k l)) := by
  let L := qubitIndices n
  let f (j k : Basis n) := commonMode i half b s j k l-direct i half b s j k l
  have skew (j k : Basis n) : f k j= -f j k := by
    unfold f; rw [physicalNormalOrder i half hi hh,physicalNormalOrder i half hi hh,cross,antiPair i half hi hh b _ j k]; grind only
  have d := pairSumZero half hh L u f skew
  have diff (j : Basis n) : sumOver L (fun k => (u j*u k)*f j k)=
    sumOver L (fun k => (u j*u k)*commonMode i half b s j k l)-sumOver L (fun k => (u j*u k)*direct i half b s j k l) := by
    rw [←Compression.sumOverSub]; apply sumOverCongr; intro k; unfold f; grind only
  rw [sumOverCongr L diff,Compression.sumOverSub] at d
  grind only

end RankSeven.PhysicalTwoHoleTransport
