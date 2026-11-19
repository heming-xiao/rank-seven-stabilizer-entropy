import Rank7UpperPairPfaffian
namespace RankSeven.UpperOddCut
open Lean.Grind Pauli ComplexScalar
open PauliPairContraction (image normSum)
open AnticommutingDefect (sumCongrMem)
variable {R α β γ : Type} [CommRing R] [DecidableEq α]
private theorem reSum {ι : Type} (xs : List ι) (f : ι→ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons u us ih => change (f u+sumOver us f).re=_; rw [re_add,ih]; rfl

def cutLine (N : R) (v : α→ComplexScalar R) (i j : α) :=
  (if i=j then ofReal N else 0)-star (v i)*v j

private theorem cutImage (ys : List α) (nd : ys.Nodup) (i : α) (hi : i∈ys)
    (N : R) (v : α→ComplexScalar R) (T : β→α→ComplexScalar R) (a : β) :
    image ys T (cutLine N v i) a=ofReal N*T a i-star (v i)*image ys T v a := by
  unfold image
  have eq (j : α) : T a j*cutLine N v i j=(if i=j then ofReal N*T a j else 0)-star (v i)*(T a j*v j) := by
    unfold cutLine; split <;> grind only
  rw [sumOverCongr ys eq,Compression.sumOverSub,←sumOverMulLeft,ExteriorPauliBase.sumOnIndex ys i _ nd hi]

private theorem cutRowEnergy (ys : List α) (nd : ys.Nodup) (v : α→ComplexScalar R) (T : β→α→ComplexScalar R) (a : β) :
    let N := normSum ys v
    sumOver ys (fun i => normSq (image ys T (cutLine N v i) a)) =
      N^2*sumOver ys (fun i => normSq (T a i))-N*normSq (image ys T v a) := by
  let N := normSum ys v
  let W := image ys T v a
  have each (i : α) (hi : i∈ys) :
      normSq (image ys T (cutLine N v i) a) =
      N^2*normSq (T a i)+normSq W*normSq (v i)-2*N*((T a i*v i)*star W).re := by
    rw [cutImage ys nd i hi]
    change normSq (ofReal N*T a i-star (v i)*W)=_
    simp only [normSq,re_sub,im_sub,re_mul,im_mul,re_star,im_star,re_ofReal,im_ofReal]; grind only
  have cross : sumOver ys (fun i => ((T a i*v i)*star W).re)=normSq W := by
    rw [←reSum,←sumOverMulRight]
    change (W*star W).re=normSq W
    rw [CommSemiring.mul_comm,re_star_mul_self]
  dsimp only
  change sumOver ys (fun i => normSq (image ys T (cutLine N v i) a)) = _
  rw [sumCongrMem ys _ _ each,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←sumOverMulLeft,←sumOverMulLeft,cross]
  change N^2*sumOver ys (fun i => normSq (T a i))+normSq W*N-2*N*normSq W=_
  change _=N^2*sumOver ys (fun i => normSq (T a i))-N*normSq W
  grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
theorem sumLe {ι : Type} (xs : List ι) {f g : ι→R} (h : ∀ i∈xs,f i≤g i) : sumOver xs f≤sumOver xs g := by
  have q := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at q; grind only

theorem oddLoss (ys : List α) (nd : ys.Nodup) (odd : ys.length%2=1) (xs : List β)
    (T : β→α→ComplexScalar R) (B : α→α→ComplexScalar R) (s : R)
    (skew : ∀ i j,B i j = -B j i)
    (project : ∀ z,normSum ys (image ys B z)≤normSum xs (image ys T z))
    (minimum : ∀ z,s*normSum ys z≤normSum xs (image ys T z)) :
    s+sumOver ys (fun j => sumOver ys (fun i => normSq (B j i)))≤
      sumOver xs (fun a => sumOver ys (fun i => normSq (T a i))) := by
  obtain ⟨v,⟨r,hr,vr⟩,kill⟩ := OddSkewContraction.oddKernel ys nd odd B skew
  let N := normSum ys v
  have pos : 0<N := by
    change 0<sumOver ys _
    rw [(columnSplit ys r _ nd hr).2]
    have rest := Compression.sumOverNonnegative (deleteColumn ys r) (fun i => normSq (v i)) (fun i _ => normSq_nonnegative (v i))
    have atR := normSq_positive (v r) vr; grind only
  have summed := sumLe ys (fun i _ => project (cutLine N v i))
  change sumOver ys (fun i => sumOver ys (fun j => normSq (image ys B (cutLine N v i) j)))≤
    sumOver ys (fun i => sumOver xs (fun a => normSq (image ys T (cutLine N v i) a))) at summed
  rw [sumOverSwap ys ys,sumOverSwap ys xs] at summed
  have left (j : α) (hj : j∈ys) : sumOver ys (fun i => normSq (image ys B (cutLine N v i) j))=
      N^2*sumOver ys (fun i => normSq (B j i)) := by
    rw [cutRowEnergy ys nd v B j]
    have z : image ys B v j=0 := kill j hj
    rw [z]; simp only [normSq,re_zero,im_zero]; grind only
  rw [sumCongrMem ys _ _ left,←sumOverMulLeft] at summed
  have right (a : β) : sumOver ys (fun i => normSq (image ys T (cutLine N v i) a))=
      N^2*sumOver ys (fun i => normSq (T a i))-N*normSq (image ys T v a) := cutRowEnergy ys nd v T a
  rw [sumOverCongr xs right,Compression.sumOverSub,←sumOverMulLeft,←sumOverMulLeft] at summed
  have minV := OrderedRing.mul_le_mul_of_nonneg_left (minimum v) (Std.le_of_lt pos)
  change N*(s*N)≤N*sumOver xs (fun a => normSq (image ys T v a)) at minV
  by_cases ok : s+sumOver ys (fun j => sumOver ys (fun i => normSq (B j i)))≤sumOver xs (fun a => sumOver ys (fun i => normSq (T a i)))
  · exact ok
  · have bad := OrderedRing.mul_pos (OrderedRing.mul_pos pos pos) (show 0<s+sumOver ys (fun j => sumOver ys (fun i => normSq (B j i)))-sumOver xs (fun a => sumOver ys (fun i => normSq (T a i))) by grind only)
    grind only
end Order
end RankSeven.UpperOddCut
#print axioms RankSeven.UpperOddCut.oddLoss
