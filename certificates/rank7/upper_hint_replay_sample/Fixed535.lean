import Rank7UpperNearCollar
namespace RankSeven.CollarBatch.Fixed
open Lean.Grind Interval UpperContractor UpperReplay UpperCorner HintReplay
def root : TailBox := ⟨⟨181399805,215925561⟩,⟨3147373,17301504⟩,⟨102745984,127879266⟩,⟨75497472,79167488⟩,⟨75497472,76021760⟩⟩
set_option maxHeartbeats 60000000
set_option maxRecDepth 65536
theorem oneRoot : batchCheck root [0] = true := by decide +kernel
theorem fixedValid : Valid cppGrid root := ⟨by decide,by decide,by decide,by decide⟩

theorem fixedCover {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {h k q c d : R} (res : Residual h k q c d) (ins : Inside cppGrid root h k q c d) :
    ∃ z, Inside cppGrid z h k q c d ∧
      ∀ sector : Fin 6, ∃ shift ∈ UpperReplay.shifts, ∃ rows,
        UpperCorner.margins z shift = some rows ∧ UpperReplay.sectorPass rows sector = true :=
  batchWitness res fixedValid ins oneRoot
end RankSeven.CollarBatch.Fixed
#print axioms RankSeven.CollarBatch.Fixed.oneRoot
#print axioms RankSeven.CollarBatch.Fixed.fixedCover
