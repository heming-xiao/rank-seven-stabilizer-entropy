import Rank7RealLowerCutPrice
import Rank7LowerPhysicalPauliSlots

namespace RankSeven.RealLowerPauliPrice
open LowerCorner LowerSignedPrices LowerAffinePayment LowerPhysicalGainScale
open PauliReserveSlots PhysicalTailBlend JointProbeGram
open UpperEndpointPrices (invRate invGeom)
noncomputable section

def headNorm (z x : ℝ) := z*z+x*x
def tax (f : ℝ) := (1-f)*(200/11)
def clipped (z x b f : ℝ) := UpperPrices.positivePart (z*x-tax f*(1-1/b))
def inversePenalty (z x f : ℝ) := headNorm z x/(headNorm z x+72*(f*f))
def shift (z x b f u : ℝ) := u*(clipped z x b f*inversePenalty z x f)
def highestShift (z y x w : ℝ) := w*(y*(z+y+x))
def antiPrice (z y x : ℝ) := y*y*(y*y+(z*z+x*x)/2)
def rawPsi (z x b c : ℝ) := (c-1)^2+((b*z)^2+(b*x)^2+(b-c)^2+1)/6

theorem shiftRanges (z y x b f u w : ℝ) (z0 : 0≤z) (y0 : 0≤y) (xh : 1≤2*x) (b1 : 1≤b)
    (fs : f=0∨f=1/2∨f=1) (us : u=5/4∨u=3/2∨u=1∨u=3/4) (ws : w=5/4∨w=3/2∨w=1∨w=7/4) :
    0≤f ∧ f≤1 ∧ 0≤shift z x b f u ∧ 2*shift z x b f u≤3*(z*x) ∧
    0≤highestShift z y x w ∧ 4*highestShift z y x w≤7*(y*(z+y+x)) := by
  have caps := LowerSignedPrices.realCaps z y x b f u w 0 0 z0 y0 xh b1 fs us ws
  let r := (1/(4242/25):ℝ)
  change (0≤24*r*shift z x b f u ∧ 707*(24*r*shift z x b f u)≤150*(z*x)) ∧
    (0≤24*r*w*(y*(z+y+x)) ∧ 707*(24*r*w*(y*(z+y+x)))≤175*(y*(z+y+x))) ∧ _ at caps
  have nonneg : 0≤f ∧ f≤1 := by rcases fs with h|h|h <;> rw [h] <;> norm_num
  have e : r=25/4242 := by norm_num [r]
  rw [e] at caps; dsimp only [highestShift]
  obtain ⟨⟨sl,sc⟩,⟨hl,hc⟩,_⟩ := caps
  exact ⟨nonneg.1,nonneg.2,by linarith only [sl],by linarith only [sc],by linarith only [hl],by linarith only [hc]⟩

theorem chartParts (z y x b c half third : ℝ) (h2 : 2*half=1) (h3 : 3*third=1) :
    let w := rawSpectrum z y x b c
    sharedGap w=b^2*(z*x) ∧ leadingGap w=b^2*(y*(z+y+x)) ∧ tailGap w=b*(c-1) ∧
    w 4=b ∧ PauliReserveSlots.gap w 0=b*z ∧ PauliReserveSlots.gap w 2=b*x ∧
    spectralPsi half third w=rawPsi z x b c ∧ leadingCoefficient half third w=b^4*antiPrice z y x := by
  have h : half=1/2 := by linarith only [h2]
  have th : third=1/3 := by linarith only [h3]
  simp [sharedGap,leadingGap,tailGap,PauliReserveSlots.gap,spectralPsi,leadingCoefficient,rawSpectrum,
    UpperFrameGain.tail,UpperPhysicalInterior.spectrum,rawPsi,antiPrice,h,th]
  ring_nf
  trivial

theorem ordered (z y x b c : ℝ) (z0 : 0≤z) (y0 : 0≤y) (x0 : 0≤x) (cb : 1≤c ∧ c≤b) :
    PauliMatchingPrices.SortedSpectrum (rawSpectrum z y x b c) := by
  have b0 : 0≤b := by linarith only [cb.1,cb.2]
  have bz := mul_nonneg b0 z0; have byy := mul_nonneg b0 y0; have bx := mul_nonneg b0 x0
  norm_num [PauliMatchingPrices.SortedSpectrum,rawSpectrum,UpperFrameGain.tail,UpperPhysicalInterior.spectrum]
  exact ⟨by linarith only [bz],by linarith only [byy],by linarith only [bx],cb.2,cb.1⟩

private theorem paymentIdentity (u g0 I Q s G T lo hi v : ℝ) (made : s=u*(g0*I)) (unit : Q*I=1)
    (active : g0=0 ∨ g0=G-T*(hi-lo)) :
    u*(2-u)*(g0*g0*I)+2*s*T*(hi-v)=s*(2*(G-T*(v-lo))-Q*s) := by
  subst s
  rcases active with no|yes
  · rw [no]; ring
  · have eq := congrArg (fun j : ℝ => j*(u*u*g0*g0*I)) unit
    have eq' := congrArg (fun j : ℝ => j*(2*u*g0*I)) yes
    linarith only [eq,eq']

theorem sharedScaled (z y x b c f u w wa wb : ℝ) (xh : 1≤2*x) (cb : 1≤c ∧ c≤b) :
    let p := realPrices z y x b f u w wa wb
    let s := b^2*shift z x b f u
    let Q := 1+12*f^2*b^2/rawPsi z x b c
    12*b^2*(p.shared+bonusSlope z x b f u*(b-c))≤
      invRate*((b*z)^2*(b*x)^2+12*s*(2*(b^2*(z*x)-tax f*(b*(c-1)))-Q*s)) := by
  let N := headNorm z x
  let ψ := rawPsi z x b c
  let G := z*x
  let g0 := clipped z x b f
  let T := tax f
  let I := inversePenalty z x f
  let s := shift z x b f u
  let Q₀ := 1+72*f^2/N
  let Q := 1+12*f^2*b^2/ψ
  let jr := invRate (R:=ℝ)
  have jp : 0≤jr := by norm_num [jr,invRate]
  have bp : 0<b := by linarith only [cb.1,cb.2]
  have np : 0<N := by
    have xp : 0<x := by linarith only [xh]
    dsimp [N,headNorm]; nlinarith only [mul_self_pos.mpr (ne_of_gt xp),sq_nonneg z]
  have extra : b^2*N≤6*ψ := by
    dsimp only [N,headNorm,ψ,rawPsi]; nlinarith only [sq_nonneg (c-1),sq_nonneg (b-c)]
  have pp : 0<ψ := by nlinarith only [extra,mul_pos (sq_pos_of_pos bp) np]
  have qi : Q₀*I=1 := by
    change (1+72*f^2/N)*(N/(N+72*(f*f)))=1
    have nz : N+72*(f*f)≠0 := by nlinarith only [np,sq_nonneg f]
    field_simp
  have qle : Q≤Q₀ := by
    change 1+12*f^2*b^2/ψ≤1+72*f^2/N
    have e := mul_le_mul_of_nonneg_left extra (show 0≤12*f^2 by positivity)
    apply add_le_add_right
    rw [div_le_div_iff₀ pp np]; linarith only [e]
  have active : g0=0 ∨ g0=G-T*(1-1/b) := by
    change UpperPrices.positivePart (G-T*(1-1/b))=0 ∨ UpperPrices.positivePart (G-T*(1-1/b))=_
    unfold UpperPrices.positivePart; split <;> simp
  have id := paymentIdentity u g0 I Q₀ s G T (1/b) 1 (c/b) rfl qi active
  have budget := mul_le_mul_of_nonneg_right qle (sq_nonneg s)
  have low : u*(2-u)*(g0*g0*I)+2*s*T*(1-c/b)≤s*(2*(G-T*((c/b)-(1/b)))-Q*s) := by
    rw [id]; linarith only [budget]
  have cleared := mul_le_mul_of_nonneg_left low (show 0≤12*jr*b^4 by positivity)
  have inv : b*(1/b)=1 := by field_simp
  have cv : b*(c/b)=c := by field_simp
  have cash : b^4*(1-c/b)=b^3*(b-c) := by field_simp
  have cost : b^4*(c/b-1/b)=b^3*(c-1) := by field_simp
  have cc := congrArg (fun t : ℝ => 24*jr*s*T*t) cash
  have vv := congrArg (fun t : ℝ => 24*jr*s*T*t) cost
  change 12*b^2*((((G*G)/12+u*(2-u)*(g0*g0*I))*(b*b)*jr)+2*s*T*b*jr*(b-c))≤
    jr*((b*z)^2*(b*x)^2+12*(b^2*s)*(2*(b^2*G-T*(b*(c-1)))-Q*(b^2*s)))
  dsimp only [G] at *
  linarith only [cleared,cc,vv]

end
end RankSeven.RealLowerPauliPrice
#print axioms RankSeven.RealLowerPauliPrice.sharedScaled