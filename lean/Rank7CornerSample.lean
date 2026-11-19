import Rank7UpperCorner

namespace RankSeven.Interval

def sampleBox : UpperCorner.TailBox :=
  ⟨⟨181399805, 319502832⟩, ⟨0, 34603008⟩, ⟨102745984, 203279112⟩,
    ⟨90177536, 104857600⟩, ⟨75497472, 76021760⟩⟩

def sampleShifts : UpperCorner.Shifts :=
  ⟨Bounds.point 0, Bounds.point 134217728, Bounds.point 167772160⟩

/-- Signed lower endpoints for the first upper-tail box in [144/256, 145/256]
    for which the corner branch needs mixed weights. The contracted box
    for (h,k,q,c,d), at grid scale 2^27, is
    [181399805, 319502832], [0, 34603008], [102745984, 203279112], [90177536, 104857600], [75497472, 76021760].
    Each row lists the two payments at each adjoining ray and one fixed tail
    corner. Regenerate the data with `python lean/extract_rank7_corner_sample.py`. -/
def cornerSample : List (List (Int × Int × Int × Int)) :=
  [
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (128444801, 35224961, 109756916, 16537076),
      (148833367, 34969687, 134191513, 20327833),
      (129367463, 36209868, 110183396, 17025801),
      (149907267, 35962471, 134733106, 20788310)
    ],
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (109756916, 16537076, 103324993, 12344640),
      (134191513, 20327833, 128905641, 17281448),
      (110183396, 17025801, 103595061, 12739812),
      (134733106, 20788310, 129280590, 17638140)
    ],
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (103324993, 12344640, 90461153, 3959777),
      (128905641, 17281448, 118333904, 11188688),
      (103595061, 12739812, 90418395, 4167841),
      (129280590, 17638140, 118375562, 11337807)
    ],
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (90461153, 3959777, 51942504, -2835367),
      (118333904, 11188688, 86691295, 11269584),
      (90418395, 4167841, 50961296, -2804977),
      (118375562, 11337807, 85733106, 11179632)
    ],
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (51942504, -2835367, -25094793, 140637115),
      (86691295, 11269584, 23406076, 198618342),
      (50961296, -2804977, -27952903, 141200657),
      (85733106, 11179632, 20448195, 199147948)
    ],
    -- Shift intervals (f.lo, f.hi, u.lo, u.hi, w.lo, w.hi): 0, 0, 134217728, 134217728, 167772160, 167772160
    [
      (-25094793, 140637115, -38518649, 80879529),
      (23406076, 198618342, -31642610, 102817667),
      (-27952903, 141200657, -39457100, 81337916),
      (20448195, 199147948, -32642456, 103319257)
    ]
  ]

def acceptsCorner : Int × Int × Int × Int → Bool
  | (s₁, t₁, s₂, t₂) => blend s₁ t₁ s₂ t₂

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The kernel independently recomputes the 96 C++ lower endpoints from
    the contracted box and the shifts. All six sectors used the same shifts. -/
theorem cornerSampleRecomputed :
    (List.range 6).mapM (UpperCorner.sectorMargins sampleBox sampleShifts) = some cornerSample := by
  decide

/-- Kernel computation of the exact C++ mix predicate on all 24 rows. -/
theorem cornerSampleAccepted :
    cornerSample.length = 6 ∧
      (cornerSample.all fun sector => sector.length == 4 && sector.all acceptsCorner) = true := by
  decide

theorem cornerSampleHasMixedWeights :
    (cornerSample.any fun sector => sector.any fun (s₁, t₁, s₂, t₂) =>
      decide (¬(0 < s₁ ∧ 0 < s₂) ∧ ¬(0 < t₁ ∧ 0 < t₂))) = true := by
  decide

theorem cornerSampleWeights {sector : List (Int × Int × Int × Int)} (inSample : sector ∈ cornerSample)
    {s₁ t₁ s₂ t₂ : Int} (inSector : (s₁, t₁, s₂, t₂) ∈ sector) :
    ∃ w v : Int, 0 ≤ w ∧ 0 ≤ v ∧
      0 < w * s₁ + v * t₁ ∧ 0 < w * s₂ + v * t₂ := by
  have accepted := List.all_eq_true.mp cornerSampleAccepted.2 sector inSample
  rw [Bool.and_eq_true] at accepted
  exact blendSound (List.all_eq_true.mp accepted.2 _ inSector)

end RankSeven.Interval

#print axioms RankSeven.Interval.cornerSampleAccepted
#print axioms RankSeven.Interval.cornerSampleRecomputed
#print axioms RankSeven.Interval.cornerSampleWeights
