import Rank7PhysicalMixedFrame
import Rank7PhysicalDefectAssembly

namespace RankSeven.PhysicalMixedSpectrum
open Lean.Grind Pauli ComplexScalar PhysicalDefectAssembly
variable {R : Type} [CommRing R]

private theorem embedSum {α : Type} (xs : List α) (f : α → R) :
    ofReal (sumOver xs f)=sumOver xs (fun i => ofReal (f i)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ofReal (f a+sumOver xs f) = ofReal (f a)+sumOver xs _
    rw [←ih]; apply ComplexScalar.ext <;> simp <;> grind only

private theorem trOrbit {n : Nat} (A : Basis n → Fin 7 → ComplexScalar R)
    (f : Fin 7 → R) (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    trace (qubitIndices n) (pairedState A f)=ofReal (sumOver (List.finRange 7) f) := by
  unfold trace pairedState RectangularPairedReduction.rankSevenCoefficients
  rw [sumOverSwap,embedSum]
  apply sumOverCongr; intro j
  rw [←sumOverCongr _ (fun i => show ofReal (f j)*(ComplexScalar.star (A i j)*A i j)=
    ofReal (f j) * A i j * ComplexPauliMoment.conjugate A i j by unfold ComplexPauliMoment.conjugate; grind only)]
  rw [←sumOverMulLeft,orth j j]; simp only [ite_true]
  change ofReal (f j)*1=_; exact Semiring.mul_one _

theorem fourthTraceEqSpectrum (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (mu : Fin 7 → R)
    (orth : PhysicalCompressionEffect.OrthonormalFrame A) :
    let xs := MixedDefect.oddWords n
    let F := PhysicalMixedFrame.K half (pairedState A mu)
    MixedDefect.realTrace xs (MixedDefect.square xs (MixedDefect.square xs F)) =
      sumOver (SectorDefectAccounting.wedgePairs (List.finRange 7)) (fun ij => (mu ij.1*mu ij.2)^4) := by
  let sites := qubitIndices n
  let N := pairedState A mu
  let b (k : Nat) := pairedState A (fun i => (mu i)^k)
  have m (f g : Fin 7 → R) := (pairedState_mul A f g orth).symm
  have sq : MixedDefect.square sites N=b 2 := by
    rw [MixedDefect.square]; refine (m mu mu).trans ?_
    apply congrArg (pairedState A); funext i; grind only
  have twice (j : Nat) : MixedDefect.square sites (b j)=b (j+j) := by
    rw [MixedDefect.square]; refine (m _ _).trans ?_
    apply congrArg (pairedState A); funext i; exact (Semiring.pow_add ..).symm
  have e := PhysicalMixedFrame.KFourthTrace half unit N
  change 2*trace _ _=(trace sites (MixedDefect.square sites (MixedDefect.square sites N)))^2-
      trace sites (MixedDefect.square sites (MixedDefect.square sites (MixedDefect.square sites N))) at e
  rw [sq,twice,twice] at e
  have t4 := trOrbit A (fun i => (mu i)^4) orth
  have t8 := trOrbit A (fun i => (mu i)^8) orth
  change trace sites (b 4)=_ at t4
  change trace sites (b 8)=_ at t8
  rw [t4,t8,←PhysicalPairedReduction.realEmbeddingPow] at e
  have re := congrArg ComplexScalar.re e
  change (ofReal (2:R)*_).re=ComplexScalar.re (R:=R) (_-_) at re
  simp only [ComplexScalar.re_mul,ComplexScalar.re_sub,ofReal,Semiring.zero_mul] at re
  have spec := SectorDefectAccounting.wedgeFourthSpectrum (List.finRange 7) mu
  change 2*MixedDefect.realTrace _ _-0=_ at re
  dsimp only
  have eq : 2*MixedDefect.realTrace (MixedDefect.oddWords n) (MixedDefect.square (MixedDefect.oddWords n) (MixedDefect.square (MixedDefect.oddWords n) (PhysicalMixedFrame.K half N))) =
      2*sumOver (SectorDefectAccounting.wedgePairs (List.finRange 7)) (fun ij => (mu ij.1*mu ij.2)^4) := by
    rw [spec]; grind only
  have t := congrArg (fun z => (z:R)*half) eq
  change _ = _ at t
  rw [show ∀ a:R, (2*a)*half=(2*half)*a from fun a => by grind only,unit,Semiring.one_mul] at t
  rw [show ∀ a:R, (2*a)*half=(2*half)*a from fun a => by grind only,unit,Semiring.one_mul] at t
  exact t

end RankSeven.PhysicalMixedSpectrum
#print axioms RankSeven.PhysicalMixedSpectrum.fourthTraceEqSpectrum
