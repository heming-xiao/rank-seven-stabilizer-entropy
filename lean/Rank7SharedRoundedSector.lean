import Rank7SharedMiddleCosets

namespace RankSeven.SharedRoundedSector

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks
open StabilizerSmallCodes StabilizerPopulationRounding StabilizerPairedCharacters
open StabilizerOddSector
open PhysicalCompressionEffect (OrthonormalFrame)
open WeightedProbeShift (physicalPayment)
open SixPointRounding (headWeight RoundedSector)
open JointProbeGram (oddAverage)

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def error {n : Nat} {half : R} {A : Basis n→Fin 7→ComplexScalar R}
    (C : SmallCodes half A) : R :=
  (2-middlePop half C.L C.a A-middlePop half C.L C.b A)+
    2*(1-pairedHead half C.L C.T A (wordAdd C.a C.b) C.c)

/-- In the small shared-Gram range, there are two disjoint parallel character
codes with the sharp total head-and-middle error bound. -/
theorem physicalCodes (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (m : Fin 7→R) (orth : OrthonormalFrame A)
    (small : 24*(physicalPayment half unit k A m).kappa≤1) :
    ∃C : SmallCodes half A, 7*error C<1 := by
  obtain ⟨G,L,T,a,ha,b,hb,c,hc,ne,e0,f0,smallError⟩ :=
    SharedMiddleCosets.physicalSmallCodes half unit k A m orth small
  let t := wordAdd a b
  let e := 2-middlePop half L a A-middlePop half L b A
  let f := 1-pairedHead half L T A t c
  change 0≤e at e0
  change 0≤f at f0
  change 7*(e+2*f)<1 at smallError
  obtain ⟨ma,mb⟩ := mateSwaps T a b ha hb
  have bounded (i : Word (k+3)) : headPop half L A i+middlePop half L i A≤1 :=
    (middleBounds half unit L i A orth).2
  have apart : c≠a ∧ c≠b := by
    have hf : f=1-(headPop half L A c+headPop half L A (representative T (wordAdd c t))) := rfl
    constructor
    · intro he
      rw [he,ma] at hf
      have h := bounded a
      have j := bounded b
      unfold e at smallError
      grind only
    · intro he
      rw [he,mb] at hf
      have h := bounded a
      have j := bounded b
      unfold e at smallError
      grind only
  have tn : t∉G.labels := fun h => ne (T.separated a ha b hb h)
  let C : SmallCodes half A :=
    ⟨G,L,T,a,b,c,ha,hb,hc,⟨ne,apart⟩,?_,?_,⟨e0,f0⟩⟩
  · exact ⟨C,smallError⟩
  · intro v eq
    subst v
    have inv := mateInvol T t c hc
    change representative T (wordAdd c t)≠a ∧ representative T (wordAdd c t)≠b ∧
      representative T (wordAdd c t)≠c
    refine ⟨?_,?_,Ne.symm (mateDifferent T t tn c)⟩
    · intro h
      rw [h,ma] at inv
      exact apart.2 inv.symm
    · intro h
      rw [h,mb] at inv
      exact apart.1 inv.symm
  · change 5*(e+2*f)<3
    grind only

/-- The exact selected odd cosets have exterior head weight at most
seven elevenths of the physical shared Gram. -/
theorem oddOutsidePrice (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3)→Fin 7→ComplexScalar R) (m : Fin 7→R) (orth : OrthonormalFrame A)
    (C : SmallCodes half A) (small : 7*error C≤1) (z : TransposeOffset C.G) :
    let leak := oddAverage half (fun p => if member z C.c C.a C.b p then 0 else headWeight A p)
    0≤leak ∧ 11*leak≤7*(physicalPayment half unit k A m).kappa := by
  let delta := 3*half*error C
  let flag := member z C.c C.a C.b
  let leak := oddAverage half (fun p => if flag p then 0 else headWeight A p)
  have scale : 2*delta=3*error C := by
    have e := congrArg (fun x : R => 3*x*error C) unit
    unfold delta
    grind only
  have pts (p : Word (k+3)) := PhysicalProjectionAngles.pointwise half unit C.L C.T z C.c C.a C.b
    C.hc C.ha C.hb C.distinct.1 A orth p
  let P : RoundedSector half A delta :=
    ⟨flag, selectorMass half unit C.T z C.c C.a C.b C.hc C.ha C.hb C.distinct.2.1 C.distinct.2.2 C.distinct.1,
      CharacterFourOrbits.selectorTrace half unit C.L C.T z C.c C.a C.b C.hc C.ha C.hb
        C.distinct.2.1 C.distinct.2.2 C.distinct.1 A orth, ?_, ?_⟩
  · have paid := SixPointRounding.physicalLeakage half unit k A m orth delta P
    have nonnegative : 0≤leak := paid.2.1
    have debited : 2*(1-delta)*leak≤(physicalPayment half unit k A m).kappa := paid.2.2.1
    have scalar : 0≤14*(1-delta)-11 := by grind only
    have combined := OrderedRing.mul_nonneg scalar nonnegative
    change 0≤leak ∧ 11*leak≤7*(physicalPayment half unit k A m).kappa
    exact ⟨nonnegative,by grind only⟩
  · intro p _ hp
    have e := (pts p).1 hp
    change 2*(1-headWeight A p)≤3*error C at e
    grind only
  · intro p _ hp
    have e := (pts p).2 hp
    change 2*headWeight A p≤3*error C at e
    grind only

end RankSeven.SharedRoundedSector

#print axioms RankSeven.SharedRoundedSector.physicalCodes
#print axioms RankSeven.SharedRoundedSector.oddOutsidePrice

