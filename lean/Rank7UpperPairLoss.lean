import Rank7UpperOddCut
namespace RankSeven.UpperPairLoss
open Lean.Grind Pauli ComplexScalar UpperPairPfaffian PhysicalCutCapacities JointProbePayment
open PauliPairContraction (image normSum)
variable {R : Type} [CommRing R]
def rest (i : Fin 5) : Fin 7 := ⟨2+i.val, by omega⟩
private theorem restInj (i j : Fin 5) : rest i=rest j ↔ i=j := by
  constructor
  · intro h; have e := congrArg Fin.val h; apply Fin.ext; dsimp only [rest] at e; omega
  · intro h; rw [h]

theorem pauliLegNorm {n} (A : Basis n → Fin 7 → ComplexScalar R) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (p : Word n) (z : Fin 7 → ComplexScalar R) :
    normSum (qubitIndices n) (image (List.finRange 7) (pauliLeg A p) z)=normSum (List.finRange 7) z := by
  let L := qubitIndices n
  let Q := List.finRange 7
  let Z := fun i => star (z i)
  let V := image Q A Z
  let P := wordEntry (imaginaryUnit (R:=R)) p
  have conj (t : Basis n) : image Q (pauliLeg A p) z t = star (image L P V t) := by
    dsimp only [image,V,pauliLeg,Z]
    simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulLeft,sumOverMulRight]
    rw [sumOverSwap Q _]
    apply sumOverCongr; intro r; apply sumOverCongr; intro i
    unfold P; rw [ComplexPauliMoment.wordHermitian]; grind only
  have normalized := (PauliPairContraction.wordIsometry p V).trans
    (PauliPairContraction.imageNorm L Q (List.nodup_finRange 7) (fun i => List.mem_finRange i) A orth Z)
  change normSum L (image Q (pauliLeg A p) z)=normSum Q z
  simpa only [normSum,conj,normSq_star,Z] using (show normSum L (fun t => star (image L P V t))=normSum Q z by
    simpa only [normSum,Z,normSq_star] using normalized)

private def combine {C : Type} (a b : C) (v : Fin 5→C) (i : Fin 7) : C := match i.val with
  | 0 => a | 1 => b | 2 => v 0 | 3 => v 1 | 4 => v 2 | 5 => v 3 | _ => v 4

private theorem folded {C : Type} [CommRing C] (D : Fin 7→C) (h a : C) (b c z : Fin 5→C) :
    sumOver (List.finRange 5) (fun j => h*(a*D (rest j)-b j*D 1+c j*D 0)*z j) =
    sumOver (List.finRange 7) (fun i => D i*combine (h*sumOver (List.finRange 5) (fun j => c j*z j))
      (-(h*sumOver (List.finRange 5) (fun j => b j*z j))) (fun j => h*a*z j) i) := by
  change h*(a*D 2-b 0*D 1+c 0*D 0)*z 0+(h*(a*D 3-b 1*D 1+c 1*D 0)*z 1+(h*(a*D 4-b 2*D 1+c 2*D 0)*z 2+(h*(a*D 5-b 3*D 1+c 3*D 0)*z 3+(h*(a*D 6-b 4*D 1+c 4*D 0)*z 4+(0))))) =
    D 0*(h*(c 0*z 0+(c 1*z 1+(c 2*z 2+(c 3*z 3+(c 4*z 4+(0)))))))+
    (D 1*(-(h*(b 0*z 0+(b 1*z 1+(b 2*z 2+(b 3*z 3+(b 4*z 4+(0))))))))+
    (D 2*(h*a*z 0)+(D 3*(h*a*z 1)+(D 4*(h*a*z 2)+(D 5*(h*a*z 3)+(D 6*(h*a*z 4)+(0)))))))
  grind only

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem freePart (a b h : ComplexScalar R) (z : Fin 5→ComplexScalar R) :
    normSq h*normSum (List.finRange 5) z≤normSum (List.finRange 7) (combine a b (fun i => h*z i)) := by
  change normSq h*(normSq (z 0)+(normSq (z 1)+(normSq (z 2)+(normSq (z 3)+(normSq (z 4)+(0)))))) ≤
    normSq a+(normSq b+(normSq (h*z 0)+(normSq (h*z 1)+(normSq (h*z 2)+(normSq (h*z 3)+(normSq (h*z 4)+(0)))))))
  simp only [normSq_mul]; have := normSq_nonnegative a; have := normSq_nonnegative b; grind only

theorem legMinimum {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n) (z : Fin 5→ComplexScalar R) :
    (2*half^n)^2*pairWeight A p 0 1*normSum (List.finRange 5) z ≤
      normSum (qubitIndices n) (image (List.finRange 5) (fun t i => leg half A ((0,1),rest i) t p) z) := by
  let h := ofReal (2*half^n)
  let a := pair A p 0 1
  let b (i : Fin 5) := pair A p 0 (rest i)
  let c (i : Fin 5) := pair A p 1 (rest i)
  let s := h*sumOver (List.finRange 5) (fun i => c i*z i)
  let v := -(h*sumOver (List.finRange 5) (fun i => b i*z i))
  let Z := combine s v (fun i => (h*a)*z i)
  have coord (t : Basis n) : image (List.finRange 5) (fun t i => leg half A ((0,1),rest i) t p) z t =
      image (List.finRange 7) (pauliLeg A p) Z t := by
    unfold image; simp only [anchoredLeg half unit A p hp]
    exact folded (pauliLeg A p t) h a b c z
  have factor : normSq (h*a)=(2*half^n)^2*pairWeight A p 0 1 := by
    simp only [h,a,pair,pairWeight,normSq_mul,normSq_star,normSq_ofReal]
  rw [←factor]
  exact Std.le_trans (freePart s v (h*a) z) (Std.le_of_eq ((pauliLegNorm A orth p Z).symm.trans (congrArg (normSum (qubitIndices n)) (funext coord).symm)))

theorem perWordOddCut {n} (half : R) (unit : 2*half=1) (A : Basis n → Fin 7 → ComplexScalar R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) (p : Word n) (hp : p∈MixedDefect.oddWords n) :
    (2*half^n)^2*pairWeight A p 0 1+
      sumOver (List.finRange 5) (fun j => sumOver (List.finRange 5) (fun i => normSq (columnCoef half A ((0,1),rest i,rest j) p))) ≤
      sumOver (qubitIndices n) (fun t => sumOver (List.finRange 5) (fun i => normSq (leg half A ((0,1),rest i) t p))) := by
  let T t i := leg half A ((0,1),rest i) t p
  let B j i := columnCoef half A ((0,1),rest i,rest j) p
  let F t i := A t (rest i)
  have ort (i j : Fin 5) : sumOver (qubitIndices n) (fun t => star (F t i)*F t j)=if i=j then 1 else 0 := by
    change sumOver _ (fun t => star (A t (rest i))*A t (rest j)) = _
    rw [orth]; by_cases k : i=j <;> simp [k,restInj]
  apply UpperOddCut.oddLoss (List.finRange 5) (List.nodup_finRange 5) (by decide) (qubitIndices n) T B _
  · intro i j; exact anchoredSkew half unit A p hp (rest j) (rest i)
  · intro z
    have proj (j : Fin 5) : image (List.finRange 5) B z j=sumOver (qubitIndices n) (fun t => star (F t j)*image (List.finRange 5) T z t) := by
      unfold image B
      have c (i : Fin 5) : columnCoef half A ((0,1),rest i,rest j) p=sumOver (qubitIndices n) (fun t => star (F t j)*T t i) := coefficientFromLeg half A ((0,1),rest i) (rest j) p
      simp only [c,sumOverMulRight,sumOverMulLeft]
      rw [sumOverSwap]; apply sumOverCongr; intro t; apply sumOverCongr; intro i; grind only
    unfold normSum; simp only [proj]
    exact frameBessel (List.finRange 5) (qubitIndices n) (List.nodup_finRange 5) (fun i => List.mem_finRange i) F ort _
  · exact legMinimum half unit A orth p hp

end Order
end RankSeven.UpperPairLoss
#print axioms RankSeven.UpperPairLoss.legMinimum
#print axioms RankSeven.UpperPairLoss.perWordOddCut
