import Rank7RealUpperCutPrice

namespace RankSeven.RealTiedCutPrice

open ExteriorCuts

private theorem posMax (x : ℝ) : pos x = max x 0 := by
  unfold pos
  split
  · exact (max_eq_left ‹_›).symm
  · exact (max_eq_right (le_of_not_ge ‹_›)).symm

private theorem errorWidth (lo up a : ℝ) :
    error lo up a ≤ 2*pos (up-lo)*pos (a-lo) := by
  rw [error, posMax, posMax (up-lo), posMax (up-a), posMax (a-lo)]
  let x := max (up-lo) 0
  let y := max (up-a) 0
  let z := max (a-lo) 0
  change max (x^2-y^2) 0≤2*x*z
  have x0 : 0≤x := le_max_right _ _
  have y0 : 0≤y := le_max_right _ _
  have z0 : 0≤z := le_max_right _ _
  have hxy : x≤y+z := max_le
    (by linarith only [le_max_left (up-a) 0, le_max_left (a-lo) 0])
    (add_nonneg y0 z0)
  apply max_le _ (by positivity)
  by_cases order : y≤x
  · have h := mul_le_mul (show x-y≤z by linarith) (show x+y≤2*x by linarith)
      (add_nonneg x0 y0) z0
    nlinarith only [h]
  · have yx : x≤y := le_of_not_ge order
    have sq := mul_le_mul yx yx x0 y0
    have rhs : 0≤2*x*z := by positivity
    linarith only [sq, rhs]

/-- Upper bound on the one shared-cut entering wedge. Here t is the
square root of the sixth probability and G is the head-gap budget. -/
theorem enteringError (lo up a t b G : ℝ) (a0 : 0≤a) (t0 : 0≤t) (t1 : t≤1)
    (G0 : 0≤G) (upEq : up=t*b) (loBound : t*a≤lo) (gap : b^2-a^2≤G) :
    error lo up a ≤ G*(1-t^2)/2 := by
  let u := pos (b-a)
  have u0 : 0≤u := by rw [show u=max (b-a) 0 from posMax _]; exact le_max_right _ _
  have tc : 0≤1-t := sub_nonneg.mpr t1
  have first : pos (up-lo)≤t*u := by
    rw [posMax, upEq]
    apply max_le _ (mul_nonneg t0 u0)
    have bound : b-a≤u := by rw [show u=max (b-a) 0 from posMax _]; exact le_max_left _ _
    nlinarith only [loBound, mul_le_mul_of_nonneg_left bound t0]
  have second : pos (a-lo)≤a*(1-t) := by
    rw [posMax]
    apply max_le _ (mul_nonneg a0 tc)
    nlinarith only [loBound]
  have cover : 2*a*u≤G := by
    change 2*a*pos (b-a)≤G
    rw [posMax]
    by_cases active : a≤b
    · rw [max_eq_left (sub_nonneg.mpr active)]
      nlinarith only [gap, sq_nonneg (b-a)]
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge active))]
      simpa using G0
  have width := mul_le_mul first second (by rw [posMax]; exact le_max_right _ _) (mul_nonneg t0 u0)
  have factor : t*(1-t)≤(1-t^2)/2 := by nlinarith only [sq_nonneg (1-t)]
  calc
    error lo up a ≤ 2*pos (up-lo)*pos (a-lo) := errorWidth _ _ _
    _ ≤ 2*(t*u)*(a*(1-t)) := by linarith only [width]
    _ = (2*a*u)*(t*(1-t)) := by ring
    _ ≤ G*((1-t^2)/2) := mul_le_mul cover factor (mul_nonneg t0 tc) G0
    _ = G*(1-t^2)/2 := by ring

/-- Exhaustive ordering of the three head values, the tied middle
probabilities, and the two tail probabilities. -/
def weights (α β γ c d : ℝ) (i : Fin 7) : ℝ :=
  if i=0 then α else if i=1 then β else if i=2 then γ else if i=5 then c else if i=6 then d else 1

private theorem weightsOrdered (α β γ c d : ℝ) (hg : 1≤γ) (gb : γ≤β) (ba : β≤α)
    (dc : d≤c) (c1 : c≤1) : ∀ i j, i≤j → weights α β γ c d j≤weights α β γ c d i := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num at h <;> norm_num [weights] <;> linarith

private theorem weightsNonnegative (α β γ c d : ℝ) (hg : 1≤γ) (gb : γ≤β) (ba : β≤α)
    (d0 : 0≤d) (dc : d≤c) : ∀ i, 0≤weights α β γ c d i := by
  intro i
  fin_cases i <;> norm_num [weights] <;> linarith

private theorem productOrder {s : Fin 7→ℝ} (nn : ∀ i,0≤s i)
    (order : ∀ i j, i≤j → s j≤s i)
    {i j k m I J K M : Fin 7}
    (hi : i≤I) (hj : j≤J) (hk : k≤K) (hm : m≤M) :
    product4 s I J K M≤product4 s i j k m := by
  unfold product4
  have pair := mul_le_mul (order _ _ hi) (order _ _ hj) (nn J) (nn i)
  have triple := mul_le_mul pair (order _ _ hk) (nn K) (mul_nonneg (nn i) (nn j))
  exact mul_le_mul triple (order _ _ hm) (nn M) (mul_nonneg (mul_nonneg (nn i) (nn j)) (nn k))

private theorem lowInside (w : Wedge7) (hin : w.level.low=true) : w.i=0 ∧ w.j≤2 := by
  unfold Wedge7.level at hin
  split at hin
  · omega
  · split at hin <;> simp_all [Level.low]

private theorem highInside (w : Wedge7) (hin : w.level.high=true) : w.i=0 ∧ w.j=1 := by
  unfold Wedge7.level at hin
  split at hin
  · assumption
  · split at hin <;> simp_all [Level.high]

private theorem highOutside (w : Wedge7) (hout : w.level.high=false) : (2:Fin 7)≤w.j := by
  have ij := w.ij
  unfold Wedge7.level at hout
  split at hout
  · simp [Level.high] at hout
  · omega

private theorem lowOutside (w : Wedge7) (hout : w.level.low=false) :
    (w.i=0 ∧ (3:Fin 7)≤w.j) ∨ (1:Fin 7)≤w.i := by
  unfold Wedge7.level at hout
  split at hout
  · simp [Level.low] at hout
  · split at hout
    · simp [Level.low] at hout
    · omega

private theorem amplitudeRoot {s : Fin 7→ℝ} (nn : ∀ i,0≤s i) (w : Wedge7) :
    amplitude (fun i => Real.sqrt (s i)) w = Real.sqrt (amplitude s w) := by
  have nonnegative : 0≤amplitude (fun i => Real.sqrt (s i)) w := by
    unfold amplitude product4
    positivity
  have squared : (amplitude (fun i => Real.sqrt (s i)) w)^2=amplitude s w := by
    unfold amplitude product4
    simp only [mul_pow, Real.sq_sqrt (nn _)]
  rw [←squared, Real.sqrt_sq nonnegative]

private theorem sumPoint (xs : List Wedge7) (nd : xs.Nodup) (a : Wedge7) (z : ℝ) :
    Pauli.sumOver xs (fun b => if b=a then z else 0) = if a ∈ xs then z else 0 := by
  induction xs with
  | nil => simp [Pauli.sumOver]
  | cons w ws ih =>
    have tail := ih (List.nodup_cons.mp nd).2
    by_cases e : w=a
    · subst w
      have notmem := (List.nodup_cons.mp nd).1
      simp [Pauli.sumOver, notmem] at tail ⊢
      exact tail
    · have neq : a≠w := Ne.symm e
      simp [Pauli.sumOver, e, neq] at tail ⊢
      exact tail

set_option maxHeartbeats 900000 in
/-- The upper tied chart has the true highest interval and the nominal shared
interval, with only the 1234 crossing charged in the latter. -/
theorem chartGeometry (α β γ c d : ℝ) (hg : 1≤γ) (gb : γ≤β) (ba : β≤α)
    (d0 : 0≤d) (dc : d≤c) (c1 : c≤1) :
    let s := weights α β γ c d
    let a := amplitude (fun i => Real.sqrt (s i))
    let loS := Real.sqrt (c*max α (β*γ))
    let upS := Real.sqrt (α*γ*c*d)
    let loH := Real.sqrt (α*γ)
    let upH := Real.sqrt (α*β*c*d)
    let charge := γ*(α-β)*d*(1-c)/2
    upS≤loH ∧ (∀ w,insideBounds w.level upS upH (a w)) ∧
      ∀ w, outsideTax loS upS loH upH (a w) w.level ≤
        if w=UpperFrameGain.entering then charge else 0 := by
  dsimp only
  let s := weights α β γ c d
  have nn := weightsNonnegative α β γ c d hg gb ba d0 dc
  have ord := weightsOrdered α β γ c d hg gb ba dc c1
  have a0 : 0≤α := by linarith
  have b0 : 0≤β := by linarith
  have g0 : 0≤γ := by linarith
  have c0 : 0≤c := d0.trans dc
  have d1 : d≤1 := dc.trans c1
  have tail : c*d≤1 := by nlinarith [mul_nonneg c0 (sub_nonneg.mpr d1)]
  refine ⟨Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (mul_nonneg a0 g0) (sub_nonneg.mpr tail)]),?_,?_⟩
  · intro w
    rw [amplitudeRoot nn]
    refine ⟨?_,?_⟩
    · intro on
      obtain ⟨i, j⟩ := lowInside w on
      have hk := w.km
      apply Real.sqrt_le_sqrt
      have below := productOrder nn ord (i:=w.i) (j:=w.j) (k:=w.k) (m:=w.m)
        (I:=0) (J:=2) (K:=5) (M:=6) (by omega) j (by omega) (by omega)
      simpa [amplitude, product4, s, weights] using below
    · intro on
      obtain ⟨i, j⟩ := highInside w on
      have hk := w.km
      apply Real.sqrt_le_sqrt
      have below := productOrder nn ord (i:=w.i) (j:=w.j) (k:=w.k) (m:=w.m)
        (I:=0) (J:=1) (K:=5) (M:=6) (by omega) (by omega) (by omega) (by omega)
      simpa [amplitude, product4, s, weights] using below
  · intro w
    rw [amplitudeRoot nn]
    have highBound (off : w.level.high=false) :
        Real.sqrt (amplitude s w)≤Real.sqrt (α*γ) := by
      have j := highOutside w off
      have jk := w.jk
      have km := w.km
      apply Real.sqrt_le_sqrt
      have below := productOrder nn ord (i:=0) (j:=2) (k:=3) (m:=4)
        (I:=w.i) (J:=w.j) (K:=w.k) (M:=w.m) (by omega) j (by omega) (by omega)
      simpa [amplitude, product4, s, weights] using below
    by_cases enter : w=UpperFrameGain.entering
    · subst w
      have sq : Real.sqrt (amplitude s UpperFrameGain.entering)=Real.sqrt (β*γ) := by
        norm_num [amplitude, product4, s, weights, UpperFrameGain.entering]
      have outside : UpperFrameGain.entering.level=.outside := by rfl
      have zeroHigh := errorOfBelow (Real.sqrt (α*γ)) (Real.sqrt (α*β*c*d))
        (Real.sqrt (amplitude s UpperFrameGain.entering)) (highBound (by decide))
      simp only [outsideTax, outside, Level.low, Level.high, Bool.not_false,
        indicator, ite_true, mul_one]
      change error (Real.sqrt (c*max α (β*γ))) (Real.sqrt (α*γ*c*d))
          (Real.sqrt (amplitude s UpperFrameGain.entering)) +
        error (Real.sqrt (α*γ)) (Real.sqrt (α*β*c*d))
          (Real.sqrt (amplitude s UpperFrameGain.entering)) ≤ γ*(α-β)*d*(1-c)/2
      rw [zeroHigh, add_zero, sq]
      let t := Real.sqrt c
      let a := Real.sqrt (β*γ)
      let b := Real.sqrt (α*γ*d)
      have t2 : t^2=c := Real.sq_sqrt c0
      have t1 : t≤1 := by simpa [t] using Real.sqrt_le_sqrt c1
      have b2 : b^2=α*γ*d := Real.sq_sqrt (by positivity)
      have a2 : a^2=β*γ := Real.sq_sqrt (by positivity)
      have upEq : Real.sqrt (α*γ*c*d)=t*b := by
        rw [show α*γ*c*d=c*(α*γ*d) by ring, Real.sqrt_mul c0]
      have loBound : t*a≤Real.sqrt (c*max α (β*γ)) := by
        rw [← Real.sqrt_mul c0]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_max_right _ _) c0)
      have gap : b^2-a^2≤γ*(α-β)*d := by
        rw [b2,a2]
        have left := mul_nonneg (mul_nonneg b0 g0) (sub_nonneg.mpr d1)
        nlinarith only [left]
      have price := enteringError _ _ a t b (γ*(α-β)*d)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) t1
        (mul_nonneg (mul_nonneg g0 (sub_nonneg.mpr ba)) d0) upEq loBound gap
      simpa only [t2, a] using price
    · rw [ite_eq_right enter]
      have lowBound (off : w.level.low=false) :
          Real.sqrt (amplitude s w)≤Real.sqrt (c*max α (β*γ)) := by
        apply Real.sqrt_le_sqrt
        have ij := w.ij
        have jk := w.jk
        have km := w.km
        rcases lowOutside w off with ⟨i,j⟩|i
        · have below := productOrder nn ord (i:=0) (j:=3) (k:=4) (m:=5)
            (I:=w.i) (J:=w.j) (K:=w.k) (M:=w.m) (by omega) j (by omega) (by omega)
          have cmp : amplitude s w≤α*c := by simpa [amplitude, product4, s, weights] using below
          linarith only [cmp, mul_le_mul_of_nonneg_left (le_max_left α (β*γ)) c0]
        · have m : (5:Fin 7)≤w.m := by
            by_contra! small
            have e : w=UpperFrameGain.entering := by
              rcases w with ⟨wi,wj,wk,wm,ij,jk,km⟩
              change (1:Fin 7)≤wi at i
              change wm<5 at small
              have e1 : wi=1 := by omega
              have e2 : wj=2 := by omega
              have e3 : wk=3 := by omega
              have e4 : wm=4 := by omega
              subst wi
              subst wj
              subst wk
              subst wm
              rfl
            exact enter e
          have below := productOrder nn ord (i:=1) (j:=2) (k:=3) (m:=5)
            (I:=w.i) (J:=w.j) (K:=w.k) (M:=w.m) i (by omega) (by omega) m
          have cmp : amplitude s w≤β*γ*c := by simpa [amplitude, product4, s, weights] using below
          linarith only [cmp, mul_le_mul_of_nonneg_left (le_max_right α (β*γ)) c0]
      exact le_of_eq (outsideTaxOfSeparated _ _ _ _ _ _ lowBound highBound)

set_option maxHeartbeats 900000 in
/-- Both numerical affine support prices are available simultaneously in
the actual tied chart, after the explicitly bounded 1234 crossing. -/
theorem tiedSupportedCompression (E : Compression.HermitianEntries Wedge7 ℝ)
    (effect : E.IsCoordinateEffect wedges)
    (half s v α β γ c d ws wh : ℝ) (unit : 2*half=1)
    (s0 : 0≤s) (v0 : 0≤v)
    (lowPrice : s≤cutCost wedges (fun w => w.level.low)
      (Compression.rowSlack wedges (fun w => E.realPart w w) E.mass) E.mass)
    (highPrice : v≤cutCost wedges (fun w => w.level.high)
      (Compression.rowSlack wedges (fun w => E.realPart w w) E.mass) E.mass)
    (hg : 1≤γ) (gb : γ≤β) (ba : β≤α) (d0 : 0≤d) (dc : d≤c) (c1 : c≤1)
    (ws0 : 0≤ws) (wh0 : 0≤wh) :
    c*UpperPrices.supportValue (α*γ*d) (max α (β*γ)) ws*s +
      UpperPrices.supportValue (α*β*c*d) (α*γ) wh*v -
      (γ*(α-β)*d*(1-c)/2)*E.realPart UpperFrameGain.entering UpperFrameGain.entering ≤
      SectorDefectAccounting.compressionLoss
        (amplitude (fun i => Real.sqrt (weights α β γ c d i))) E := by
  let amp := amplitude (fun i => Real.sqrt (weights α β γ c d i))
  let loS := Real.sqrt (c*max α (β*γ))
  let upS := Real.sqrt (α*γ*c*d)
  let loH := Real.sqrt (α*γ)
  let upH := Real.sqrt (α*β*c*d)
  let charge := γ*(α-β)*d*(1-c)/2
  let diag (w : Wedge7) := E.realPart w w
  have ⟨apart,inside,tax⟩ := chartGeometry α β γ c d hg gb ba d0 dc c1
  have a0 : 0≤α := by linarith
  have b0 : 0≤β := by linarith
  have g0 : 0≤γ := by linarith
  have c0 : 0≤c := d0.trans dc
  have charge0 : 0≤charge := by
    unfold charge
    positivity
  have max0 : 0≤max α (β*γ) := a0.trans (le_max_left _ _)
  let costs := fun w => outsideTax loS upS loH upH (amp w) w.level * (diag w*(1-diag w))
  let charged := fun w => if w=UpperFrameGain.entering then charge*diag w else 0
  have each (w : Wedge7) : costs w≤charged w := by
    obtain ⟨lower,upper⟩ := E.effectDiagonalBounds wedges wedgesNodup effect w (memWedges w)
    change 0≤diag w at lower
    change diag w≤1 at upper
    have paid := mul_le_mul_of_nonneg_right (tax w) (mul_nonneg lower (sub_nonneg.mpr upper))
    change outsideTax loS upS loH upH (amp w) w.level * (diag w*(1-diag w)) ≤
      (if w=UpperFrameGain.entering then charge else 0)*(diag w*(1-diag w)) at paid
    by_cases enter : w=UpperFrameGain.entering
    · rw [ite_eq_left enter] at paid
      have geometry : diag w*(1-diag w)≤diag w := by nlinarith only [sq_nonneg (diag w)]
      exact le_trans paid (by simpa only [charged, ite_eq_left enter] using mul_le_mul_of_nonneg_left geometry charge0)
    · simpa only [costs, charged, ite_eq_right enter, zero_mul] using paid
  have paidSum := Compression.sumOverNonnegative wedges (fun w => charged w-costs w)
    (fun w _ => sub_nonneg.mpr (each w))
  rw [Compression.sumOverSub] at paidSum
  have totalPaid : Pauli.sumOver wedges charged = charge*diag UpperFrameGain.entering := by
    have same : charged = fun w => if w=UpperFrameGain.entering then charge*diag UpperFrameGain.entering else 0 := by
      funext w
      by_cases e : w=UpperFrameGain.entering <;> simp [charged,e]
    rw [same, sumPoint wedges wedgesNodup, ite_eq_left (memWedges _)]
  rw [totalPaid] at paidSum
  have supported := RealUpperCutPrice.supportedCompression E effect half s v unit s0 v0
    lowPrice highPrice amp loS upS loH upH ws wh
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apart inside ws0 wh0
  have loS2 : loS^2=c*max α (β*γ) := Real.sq_sqrt (mul_nonneg c0 max0)
  have upS2 : upS^2=α*γ*c*d := Real.sq_sqrt (by positivity)
  have loH2 : loH^2=α*γ := Real.sq_sqrt (by positivity)
  have upH2 : upH^2=α*β*c*d := Real.sq_sqrt (by positivity)
  rw [loS2,upS2,loH2,upH2] at supported
  have scale : UpperPrices.supportValue (α*γ*c*d) (c*max α (β*γ)) ws =
      c*UpperPrices.supportValue (α*γ*d) (max α (β*γ)) ws := by
    unfold UpperPrices.supportValue
    ring
  rw [scale] at supported
  exact le_trans (sub_le_sub_left (sub_nonneg.mp paidSum) _) supported

private theorem highPriceNonnegative (x : ℝ) (cap : 3*x≤7) (nonnegative : 0≤x-2) :
    0≤(x-2)*(1-(x-2)) :=
  mul_nonneg nonnegative (by linarith only [cap])

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- The two checker supports and the single entering wedge on an actual
orthonormal rank-seven frame, with both cut prices proved internally. -/
theorem physicalTiedCompression (half : ℝ) (unit : 2*half=1) (k : Nat)
    (A : Pauli.Basis (k+3) → Fin 7 → ComplexScalar ℝ) (orth : PhysicalCompressionEffect.OrthonormalFrame A)
    (n0 : 0≤UpperFrameTrace.sharedExcess (PackingPolynomial.physicalWeights half unit k A))
    (v0 : 0≤UpperFrameTrace.highExcess (PackingPolynomial.physicalWeights half unit k A))
    (α β γ c d ws wh : ℝ) (hg : 1≤γ) (gb : γ≤β) (ba : β≤α) (d0 : 0≤d) (dc : d≤c) (c1 : c≤1)
    (ws0 : 0≤ws) (wh0 : 0≤wh) :
    let E := PhysicalCompressionEffect.physicalEntries half unit k A
    let x := PackingPolynomial.physicalWeights half unit k A
    let s := UpperFrameTrace.sharedFraction x
    let v := UpperFrameTrace.highExcess x
    c*UpperPrices.supportValue (α*γ*d) (max α (β*γ)) ws*(s*(1-s)) +
      UpperPrices.supportValue (α*β*c*d) (α*γ) wh*(v*(1-v)) -
      (γ*(α-β)*d*(1-c)/2)*x UpperFrameGain.entering ≤
      SectorDefectAccounting.compressionLoss
        (amplitude (fun i => Real.sqrt (weights α β γ c d i))) E := by
  let x := PackingPolynomial.physicalWeights half unit k A
  have bound := UpperFrameTrace.physicalSharedTrace half unit k A orth n0
  have nonnegS := mul_nonneg bound.2.1 (sub_nonneg.mpr bound.2.2.1)
  have nonnegV : 0≤UpperFrameTrace.highExcess x*(1-UpperFrameTrace.highExcess x) :=
    highPriceNonnegative _ (UpperPairCap.physicalPairCap half unit k A orth) v0
  have prices := RealUpperCutPrice.actualTracePrices half unit k A orth n0 v0
  exact tiedSupportedCompression _
    (PhysicalCompressionEffect.rankSevenPhysicalEffect half unit k A orth)
    half _ _ α β γ c d ws wh unit nonnegS nonnegV prices.1 prices.2 hg gb ba d0 dc c1 ws0 wh0

end RankSeven.RealTiedCutPrice

#print axioms RankSeven.RealTiedCutPrice.enteringError
#print axioms RankSeven.RealTiedCutPrice.chartGeometry
#print axioms RankSeven.RealTiedCutPrice.tiedSupportedCompression
#print axioms RankSeven.RealTiedCutPrice.physicalTiedCompression

