import Rank7PhysicalEightTransport
import Rank7PhysicalTwoHoleTransport

namespace RankSeven.PhysicalTwoHoleTransport
open Lean.Grind Pauli
open PhysicalCutCapacities (Triple)
variable {C : Type} [CommRing C]

/-- The physical transport identity in each pair of output coordinates,
with two identical, unconjugated mode coefficients and an arbitrary
creation mode in the remaining slot. -/
theorem physicalTransportFixed {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (b : Basis n × Basis n) (s : Triple (Basis n)) (u : Basis n → C) (l : Basis n) :
    sumOver (qubitIndices n) (fun j => sumOver (qubitIndices n) (fun k => (u j*u k)*commonMode i half b s j k l))=
    sumOver (qubitIndices n) (fun j => sumOver (qubitIndices n) (fun k => (u j*u k)*direct i half b s j k l)) := by
  apply transportFromCross i half hi hh b s u l
  intro j k
  exact PhysicalEightTransport.transportCross i half hi hh b.1 b.2 j k l s.1.1 s.1.2 s.2

/-- Eq. (199) for arbitrary complex coefficient vectors u and v and
all three-input / two-output computational coordinates. -/
theorem physicalBilinearTransport {n : Nat} (i half : C) (hi : i^4=1) (hh : 2*half=1)
    (b : Basis n × Basis n) (s : Triple (Basis n)) (u v : Basis n → C) :
    sumOver (qubitIndices n) (fun l => v l*sumOver (qubitIndices n) (fun j =>
      sumOver (qubitIndices n) (fun k => (u j*u k)*commonMode i half b s j k l)))=
    sumOver (qubitIndices n) (fun l => v l*sumOver (qubitIndices n) (fun j =>
      sumOver (qubitIndices n) (fun k => (u j*u k)*direct i half b s j k l))) := by
  apply sumOverCongr; intro l; rw [physicalTransportFixed i half hi hh b s u l]

end RankSeven.PhysicalTwoHoleTransport

#print axioms RankSeven.PhysicalTwoHoleTransport.physicalBilinearTransport
