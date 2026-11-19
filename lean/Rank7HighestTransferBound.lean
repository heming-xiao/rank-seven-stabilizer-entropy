import Rank7HighestOneHoleGram

namespace RankSeven.HighestTransferBound

open Lean.Grind Pauli ComplexScalar SymmetricDefect PhysicalCutCapacities HighestOneHoleGram HighestTailTransfer
open HighestCodeLocalization HighestExteriorOccupation HighestExteriorComponents
open PauliPairContraction (normSum)
open PhysicalCompressionEffect (OrthonormalFrame)
open UpperPairLoss (rest)
open MixedDefect (oddWords)
open WedgeSquareIntertwiner (wedgeSquareColumn)
variable {R α : Type} [CommRing R]

theorem factored {n : Nat} (half : R) (A : Basis n→Fin 7→ComplexScalar R) (w : Basis n×Basis n→ComplexScalar R) (i j : Fin 5) (p : Word n) :
    tailColumn half A w i j p=ofReal half*sumOver (qubitIndices n) (fun t => star (A t (rest j))*
      contracted half (tripleSource w (fun t => A t (rest i))) t p) := by
  let xs := qubitIndices n
  let ps := productIndices xs xs
  let F (t : Four (Basis n)) := wedgeSquareColumn half p t
  change ofReal half*sumOver (productIndices ps ps) (fun t => star (w t.1*(A t.2.1 (rest i)*A t.2.2 (rest j)))*F t)=
    ofReal half*sumOver xs (fun t => star (A t (rest j))*sumOver (productIndices ps xs) (fun u => star (w u.1*A u.2 (rest i))*F (extend u t)))
  congr 1
  rw [sumPairs]; simp only [sumPairs,sumOverMulLeft]
  rw [sumOverSwap xs ps]
  apply sumOverCongr; intro ab
  change sumOver (productIndices xs xs) _=_
  rw [sumPairs,sumOverSwap xs xs]
  apply sumOverCongr; intro t; apply sumOverCongr; intro c
  simp only [star_mul,extend]; grind only

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem sumLE (xs : List α) (f g : α→R) (h : ∀i∈xs,f i≤g i) : sumOver xs f≤sumOver xs g := by
  have e := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by have := h i hi; grind only)
  rw [Compression.sumOverSub] at e; grind only

theorem oneTail {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (w : Basis n×Basis n→ComplexScalar R) (sk : ∀i j,w (j,i)= -w (i,j)) (i : Fin 5) :
    2*sumOver (oddWords n) (fun p => sumOver (List.finRange 5) (fun j => normSq (tailColumn half A w i j p)))≤
      (3*(4*half^n))*HighestExteriorOccupation.measure half (qubitIndices n) w := by
  let xs := qubitIndices n
  let es := List.finRange 5
  let os := oddWords n
  let B t j := A t (rest j)
  let V t p := contracted half (tripleSource w (fun t => B t i)) t p
  have ort (j l : Fin 5) : sumOver xs (fun t => star (B t j)*B t l)=if j=l then 1 else 0 := by
    change sumOver xs (fun t => star (A t (rest j))*A t (rest l))=_
    have inj (a b : Fin 5) : rest a=rest b ↔ a=b := by
      constructor
      · intro eq; apply Fin.ext; have g := congrArg Fin.val eq; dsimp only [rest] at g; omega
      · intro eq; rw [eq]
    rw [orth]; by_cases h : j=l <;> simp [h,inj]
  have u : normSum xs (fun t => B t i)=1 := by
    have e := ort i i
    change innerProduct xs (fun t => B t i) (fun t => B t i)=_ at e
    rw [selfProduct,ite_eq_left rfl] at e; simpa only [re_ofReal,re_one] using congrArg ComplexScalar.re e
  have cmp (p : Word n) : sumOver es (fun j => normSq (tailColumn half A w i j p))≤
      half^2*sumOver xs (fun t => normSq (V t p)) := by
    have bv := frameBessel es xs (List.nodup_finRange _) List.mem_finRange B ort (fun t => V t p)
    have fac (j : Fin 5) : normSq (tailColumn half A w i j p)=half^2*normSq (sumOver xs (fun t => star (B t j)*V t p)) := by
      rw [factored,normSq_mul,normSq_ofReal]
    rw [sumOverCongr _ fac,←sumOverMulLeft]; exact OrderedRing.mul_le_mul_of_nonneg_left bv (squareNonnegative half)
  have le := sumLE os _ _ (fun p _ => cmp p)
  rw [←sumOverMulLeft] at le
  have oh := oneHoleBound half h2 w sk (fun t => B t i) u
  change 2*sumOver os (fun p => sumOver xs (fun t => normSq (V t p)))≤(3*(4*half^n))*(2*normSum (productIndices xs xs) w) at oh
  have bound := OrderedRing.mul_le_mul_of_nonneg_left oh (squareNonnegative half)
  let M := sumOver os (fun p => sumOver es (fun j => normSq (tailColumn half A w i j p)))
  let T := sumOver os (fun p => sumOver xs (fun t => normSq (V t p)))
  let q := 3*(4*half^n)
  let N := normSum (productIndices xs xs) w
  change M≤half^2*T at le
  change half^2*(2*T)≤half^2*(q*(2*N)) at bound
  have id : half^2*(q*(2*N))=q*(half*N) := by grind only
  rw [id] at bound
  change 2*M≤q*(half*N)
  have dbl := OrderedRing.mul_le_mul_of_nonneg_left le (show (0:R)≤2 by have := OrderedRing.zero_lt_one (R:=R); grind only)
  exact Std.le_trans dbl (show 2*(half^2*T)≤q*(half*N) by rw [show 2*(half^2*T)=half^2*(2*T) by grind only]; exact bound)

theorem allTails {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    (w : Basis n×Basis n→ComplexScalar R) (sk : ∀i j,w (j,i)= -w (i,j)) :
    2*normSum (rows n) (transfer half A w)≤5*(3*(4*half^n))*HighestExteriorOccupation.measure half (qubitIndices n) w := by
  let es := List.finRange 5
  let os := oddWords n
  let m i j p := normSq (tailColumn half A w i j p)
  let C := (3*(4*half^n))*HighestExteriorOccupation.measure half (qubitIndices n) w
  have bound := sumLE es (fun i => 2*sumOver os (fun p => sumOver es (fun j => m i j p))) (fun _ => C)
    (fun i _ => oneTail half h2 A orth w sk i)
  have cross : normSum (rows n) (transfer half A w)=sumOver es (fun i => sumOver os (fun p => sumOver es (fun j => m i j p))) := by
    unfold normSum rows transfer; simp only [sumPairs]; rw [sumOverSwap es es]
    apply sumOverCongr; intro i; rw [sumOverSwap es os]
  rw [←sumOverMulLeft,←cross] at bound
  change 2*normSum (rows n) (transfer half A w)≤C+(C+(C+(C+(C+0)))) at bound
  change 2*normSum (rows n) (transfer half A w)≤5*(3*(4*half^n))*HighestExteriorOccupation.measure half (qubitIndices n) w
  unfold C at bound; grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem componentSkew (P : Fin 3→SlaterUnionBound.Mx α R) (xs : List α) (x y : α→ComplexScalar R) (r : Fin 4) (i j : α) :
    component P xs x y r (j,i)= -component P xs x y r (i,j) := by
  have neg := sumOverMulLeft (sectors r) (fun p => exterior (PauliPairContraction.image xs (P p.1) x) (PauliPairContraction.image xs (P p.2) y) (i,j)) (-1)
  unfold component; rw [show -(sumOver (sectors r) _)=(-1)*(sumOver (sectors r) (fun p => exterior (PauliPairContraction.image xs (P p.1) x) (PauliPairContraction.image xs (P p.2) y) (i,j))) by grind only,neg]
  apply sumOverCongr; intro p; unfold exterior; grind only

theorem componentUpper {n : Nat} (half : R) (h2 : 2*half=1) (A : Basis n→Fin 7→ComplexScalar R) (orth : OrthonormalFrame A)
    {G : HeavyPauliGroup.MaximalFamily n} (L : StabilizerCharacterBasis.Lift G) (c d : Word n) (apart : ¬StabilizerCosetTransform.equiv G c d)
    (a b f g : R) :
    let xs := qubitIndices n
    let v := component (HighestExteriorComponents.split half L c d) xs (fun t => A t 0) (fun t => A t 1)
    let m i := HighestExteriorOccupation.measure half xs (v i)
    let z t i := transfer half A (v i) t
    2*normSum (rows n) (HighestExteriorStability.output z a b f g)≤
      5*(3*(4*half^n))*HighestExteriorStability.diagonal (m 0) (m 1) (m 2) (m 3) a b f g := by
  let xs := qubitIndices n
  let P := HighestExteriorComponents.split half L c d
  let v := component P xs (fun t => A t 0) (fun t => A t 1)
  let w := HighestExteriorStability.output (fun t j => v j t) a b f g
  have sk (i j : Basis n) : w (j,i)= -w (i,j) := by
    have s (r : Fin 4) : v r (j,i)= -v r (i,j) := componentSkew _ _ _ _ _ _ _
    unfold w HighestExteriorStability.output; simp only [s]; grind only
  have e := allTails half h2 A orth w sk
  have src := componentMass half h2 xs P (splitOrthogonal half h2 L c d apart) (fun t => A t 0) (fun t => A t 1) a b f g
  change HighestExteriorOccupation.measure half xs w=_ at src
  rw [src] at e
  have t := funext (linear half A v a b f g)
  change transfer half A w=_ at t
  rwa [t] at e

end RankSeven.HighestTransferBound

#print axioms RankSeven.HighestTransferBound.oneTail
#print axioms RankSeven.HighestTransferBound.allTails
#print axioms RankSeven.HighestTransferBound.componentUpper

