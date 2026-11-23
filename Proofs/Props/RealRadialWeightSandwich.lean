module

public import Props.RealSharpLowerEdges
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # The real radial cutoff weight

On the repaired positive radial domain for (12.4.1.22) and
(12.4.1.24), p. 518, the retained radial weight is Borel measurable.
Sharp indicator brackets on the two profiles also bound its values
and its pairing with the Fourier transform of an integrable test.
-/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform Topology

namespace Masullo

private noncomputable def radialBandDensity (B D r : ℝ) : ℝ → ℝ :=
  (Icc (r / D) B).indicator (fun s ↦ s⁻¹)

private theorem radialBandDensity_apply {B D r s : ℝ} (hD : 0 < D) (hs : 0 < s) :
    radialBandDensity B D r s =
      (Iic B).indicator (fun _ ↦ (1 : ℝ)) s *
        (Iic D).indicator (fun _ ↦ (1 : ℝ)) (r / s) * s⁻¹ := by
  have hd : r / s ≤ D ↔ r / D ≤ s := by
    rw [div_le_iff₀ hs, div_le_iff₀ hD, mul_comm D s]
  by_cases hb : s ≤ B <;> by_cases ha : r / D ≤ s <;>
    simp [radialBandDensity, hd, hb, ha]

private theorem integrable_radialBandDensity {B D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    Integrable (radialBandDensity B D r) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  refine (continuous_id.continuousOn.inv₀ ?_).integrableOn_Icc
  intro s hs
  exact ((div_pos hr hD).trans_le hs.1).ne'

private theorem integral_radialBandDensity {B D r : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hr : 0 < r) :
    (∫ s in Ioi 0, radialBandDensity B D r s) = max 0 (Real.log (B * D / r)) := by
  have hsub : Icc (r / D) B ⊆ Ioi 0 := fun _ hs ↦ (div_pos hr hD).trans_le hs.1
  rw [radialBandDensity, setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
  by_cases h : r ≤ B * D
  · have hvol := real_position_band_radial_volume (div_pos hr hD) ((div_le_iff₀ hD).2 h) hD hr
    have he : r / D * D = r := div_mul_cancel₀ _ hD.ne'
    have hlog := Real.log_nonneg ((le_div_iff₀ hr).2 (by simpa using h))
    rw [max_eq_right hlog, Real.log_div (hr.trans_le h).ne' hr.ne']
    simpa [he, h] using hvol
  · have hlt := lt_of_not_ge h
    have hlog := Real.log_nonpos (div_nonneg (mul_nonneg hB.le hD.le) hr.le)
      ((div_le_iff₀ hr).2 (by simpa using hlt.le))
    rw [Icc_eq_empty_of_lt ((lt_div_iff₀ hD).2 hlt), setIntegral_empty, max_eq_left hlog]

/-- For bracketed real profiles, the retained product is absolutely integrable
against `ds/s` at every positive radius and lies between the sharp log weights.
Measurability is required only on the positive ray, via zero extension. -/
public theorem real_radial_weight_sandwich {p q : ℝ → ℝ}
    (hp : Measurable ((Ioi (0 : ℝ)).indicator p))
    (hq : Measurable ((Ioi (0 : ℝ)).indicator q))
    {Blo Bhi Dlo Dhi r : ℝ} (hBlo : 0 < Blo) (hB : Blo ≤ Bhi)
    (hDlo : 0 < Dlo) (hD : Dlo ≤ Dhi) (hr : 0 < r)
    (hpB : ∀ s > 0, (Iic Blo).indicator (fun _ ↦ (1 : ℝ)) s ≤ p s ∧
      p s ≤ (Iic Bhi).indicator (fun _ ↦ (1 : ℝ)) s)
    (hqD : ∀ s > 0, (Iic Dlo).indicator (fun _ ↦ (1 : ℝ)) s ≤ q s ∧
      q s ≤ (Iic Dhi).indicator (fun _ ↦ (1 : ℝ)) s) :
    IntegrableOn (fun s ↦ p s * q (r / s) * s⁻¹) (Ioi 0) ∧
      max 0 (Real.log (Blo * Dlo / r)) ≤ (∫ s in Ioi 0, p s * q (r / s) * s⁻¹) ∧
      (∫ s in Ioi 0, p s * q (r / s) * s⁻¹) ≤ max 0 (Real.log (Bhi * Dhi / r)) := by
  let g (s : ℝ) := p s * q (r / s) * s⁻¹
  have hDhi := hDlo.trans_le hD
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    have hd : Measurable (fun s : ℝ ↦ r / s) := measurable_const.div measurable_id
    have hm := (hp.mul (hq.comp hd)).mul (measurable_id.inv : Measurable (fun s : ℝ ↦ s⁻¹))
    apply hm.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    change 0 < s at hs
    simp [g, indicator_of_mem (mem_Ioi.mpr hs), indicator_of_mem (mem_Ioi.mpr (div_pos hr hs))]
  have hcmp (s : ℝ) (hs : 0 < s) :
      0 ≤ g s ∧ radialBandDensity Blo Dlo r s ≤ g s ∧ g s ≤ radialBandDensity Bhi Dhi r s := by
    have hn (b t : ℝ) : 0 ≤ (Iic b).indicator (fun _ ↦ (1 : ℝ)) t :=
      indicator_nonneg (fun _ _ ↦ zero_le_one) t
    obtain ⟨hpl, hpu⟩ := hpB s hs
    obtain ⟨hql, hqu⟩ := hqD (r / s) (div_pos hr hs)
    have hpn := (hn Blo s).trans hpl
    have hqn := (hn Dlo (r / s)).trans hql
    rw [radialBandDensity_apply hDlo hs, radialBandDensity_apply hDhi hs]
    exact ⟨mul_nonneg (mul_nonneg hpn hqn) (inv_nonneg.mpr hs.le),
      mul_le_mul_of_nonneg_right (mul_le_mul hpl hql (hn Dlo (r / s)) hpn)
        (inv_nonneg.mpr hs.le),
      mul_le_mul_of_nonneg_right (mul_le_mul hpu hqu hqn (hn Bhi s)) (inv_nonneg.mpr hs.le)⟩
  have hlow := (integrable_radialBandDensity (B := Blo) (r := r) hDlo hr).integrableOn (s := Ioi 0)
  have hupp := (integrable_radialBandDensity (B := Bhi) (r := r) hDhi hr).integrableOn (s := Ioi 0)
  have hint : IntegrableOn g (Ioi 0) := by
    refine hupp.mono' hmeas ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    obtain ⟨hn, _, hu⟩ := hcmp s (mem_Ioi.mp hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hu
  change IntegrableOn g (Ioi 0) ∧
    max 0 (Real.log (Blo * Dlo / r)) ≤ (∫ s in Ioi 0, g s) ∧
    (∫ s in Ioi 0, g s) ≤ max 0 (Real.log (Bhi * Dhi / r))
  rw [← integral_radialBandDensity hBlo hDlo hr,
    ← integral_radialBandDensity (hBlo.trans_le hB) hDhi hr]
  exact ⟨hint, setIntegral_mono_on hlow hint measurableSet_Ioi fun s hs ↦ (hcmp s hs).2.1,
    setIntegral_mono_on hint hupp measurableSet_Ioi fun s hs ↦ (hcmp s hs).2.2⟩

/-- The retained radial weight, extended by zero at the origin, is Borel
measurable given measurable zero extensions of the profiles. No convergence
hypothesis is needed for this statement about the total Bochner integral. -/
public theorem measurable_real_radial_weight {p q : ℝ → ℝ}
    (hp : Measurable ((Ioi (0 : ℝ)).indicator p))
    (hq : Measurable ((Ioi (0 : ℝ)).indicator q)) :
    Measurable (fun w : ℝ ↦ if w = 0 then 0 else
      ∫ s in Ioi (0 : ℝ), p s * q (|w| / s) * s⁻¹) := by
  let g (ws : ℝ × ℝ) := (Ioi (0 : ℝ)).indicator p ws.2 *
    (Ioi (0 : ℝ)).indicator q (|ws.1| / ws.2) * ws.2⁻¹
  have hd : Measurable (fun ws : ℝ × ℝ ↦ |ws.1| / ws.2) :=
    (continuous_abs.measurable.comp measurable_fst).div measurable_snd
  have hg : Measurable g :=
    ((hp.comp measurable_snd).mul (hq.comp hd)).mul measurable_snd.inv
  have hi : Measurable (fun w : ℝ ↦ ∫ s in Ioi (0 : ℝ), g (w, s)) :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable
  convert hi using 1
  funext w
  by_cases hw : w = 0
  · subst w
    simp [g]
  · rw [ite_eq_right hw]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hqpos : |w| / s ∈ Ioi 0 := mem_Ioi.mpr (div_pos (abs_pos.mpr hw) hs)
    simp [g, indicator_of_mem hs, indicator_of_mem hqpos]

private theorem ae_real_radial_weight_brackets {p q : ℝ → ℝ}
    (hp : Measurable ((Ioi (0 : ℝ)).indicator p))
    (hq : Measurable ((Ioi (0 : ℝ)).indicator q))
    {Blo Bhi Dlo Dhi : ℝ} (hBlo : 0 < Blo) (hB : Blo ≤ Bhi)
    (hDlo : 0 < Dlo) (hD : Dlo ≤ Dhi)
    (hpB : ∀ s > 0, (Iic Blo).indicator (fun _ ↦ (1 : ℝ)) s ≤ p s ∧
      p s ≤ (Iic Bhi).indicator (fun _ ↦ (1 : ℝ)) s)
    (hqD : ∀ s > 0, (Iic Dlo).indicator (fun _ ↦ (1 : ℝ)) s ≤ q s ∧
      q s ≤ (Iic Dhi).indicator (fun _ ↦ (1 : ℝ)) s) :
    let W := fun w : ℝ ↦ if w = 0 then 0 else ∫ s in Ioi (0 : ℝ), p s * q (|w| / s) * s⁻¹
    ∀ᵐ w : ℝ ∂volume,
      max 0 (Real.log (Blo * Dlo / |w|)) ≤ W w ∧ W w ≤ max 0 (Real.log (Bhi * Dhi / |w|)) := by
  dsimp only
  filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
  simpa only [ite_eq_right hw] using
    (real_radial_weight_sandwich hp hq hBlo hB hDlo hD (abs_pos.mpr hw) hpB hqD).2

/-- Under upper-indicator brackets, the zero-extended real radial weight
pairs absolutely with the Fourier transform of an integrable test. Its
pairing differs from the sharp scalar at any intermediate cutoff product
by at most twice the product width times the test's `L¹` norm. -/
public theorem integrable_real_radial_pairing_and_norm_sub_le {p q : ℝ → ℝ}
    (hp : Measurable ((Ioi (0 : ℝ)).indicator p))
    (hq : Measurable ((Ioi (0 : ℝ)).indicator q))
    {Blo Bhi Dlo Dhi : ℝ} (hBlo : 0 < Blo) (hB : Blo ≤ Bhi)
    (hDlo : 0 < Dlo) (hD : Dlo ≤ Dhi)
    (hpB : ∀ s > 0, (Iic Blo).indicator (fun _ ↦ (1 : ℝ)) s ≤ p s ∧
      p s ≤ (Iic Bhi).indicator (fun _ ↦ (1 : ℝ)) s)
    (hqD : ∀ s > 0, (Iic Dlo).indicator (fun _ ↦ (1 : ℝ)) s ≤ q s ∧
      q s ≤ (Iic Dhi).indicator (fun _ ↦ (1 : ℝ)) s)
    {u : ℝ → ℂ} (hu : Integrable u) {K : ℝ} (hlo : Blo * Dlo ≤ K) (hhi : K ≤ Bhi * Dhi) :
    let W := fun w : ℝ ↦ if w = 0 then 0 else ∫ s in Ioi (0 : ℝ), p s * q (|w| / s) * s⁻¹
    Integrable (fun w ↦ (W w : ℂ) * 𝓕 u w) ∧
      ‖(∫ w, (W w : ℂ) * 𝓕 u w) - realSharpCutScalar u K‖ ≤
        2 * (Bhi * Dhi - Blo * Dlo) * ∫ x, ‖u x‖ := by
  dsimp only
  exact integrable_mul_fourier_and_norm_sub_le_of_sharp_cut_brackets
    (measurable_real_radial_weight hp hq).aestronglyMeasurable hu (mul_pos hBlo hDlo) hlo hhi
    (ae_real_radial_weight_brackets hp hq hBlo hB hDlo hD hpB hqD)

/-- Eventual upper-indicator brackets of vanishing product width transfer
 the real half-Haar limit to the retained profile-product pairing on the
 repaired radial domain. The brackets and width are not source conclusions. -/
public theorem real_log_profile_radial_pairing_tendsto {ι : Type*} {l : Filter ι}
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0)
    {p q : ι → ℝ → ℝ} {Blo Bhi Dlo Dhi K : ι → ℝ}
    (hprofiles : ∀ᶠ i in l, Measurable ((Ioi (0 : ℝ)).indicator (p i)) ∧
      Measurable ((Ioi (0 : ℝ)).indicator (q i)) ∧
      0 < Blo i ∧ Blo i ≤ Bhi i ∧ 0 < Dlo i ∧ Dlo i ≤ Dhi i ∧
      (∀ s > 0, (Iic (Blo i)).indicator (fun _ ↦ (1 : ℝ)) s ≤ p i s ∧
        p i s ≤ (Iic (Bhi i)).indicator (fun _ ↦ (1 : ℝ)) s) ∧
      (∀ s > 0, (Iic (Dlo i)).indicator (fun _ ↦ (1 : ℝ)) s ≤ q i s ∧
        q i s ≤ (Iic (Dhi i)).indicator (fun _ ↦ (1 : ℝ)) s) ∧
      Blo i * Dlo i ≤ K i ∧ K i ≤ Bhi i * Dhi i)
    (hwidth : Tendsto (fun i ↦ Bhi i * Dhi i - Blo i * Dlo i) l (𝓝 0))
    (hK : Tendsto K l atTop) :
    let u := realLogProfileAdditive (fun t ↦ f (-t))
    let W := fun i (w : ℝ) ↦ if w = 0 then 0 else
      ∫ s in Ioi (0 : ℝ), p i s * q i (|w| / s) * s⁻¹
    Tendsto (fun i ↦ ∫ w, (W i w : ℂ) * 𝓕 u w) l
      (𝓝 ((1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ))) := by
  intro u W
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test (hf.comp contDiff_neg)
    (hc.comp_homeomorph (Homeomorph.neg ℝ))
  refine tendsto_integral_mul_fourier_of_sharp_cut_brackets (W := W) (K := K)
    (hd.continuous.integrable_of_hasCompactSupport hk) ?_ hwidth ?_
  · filter_upwards [hprofiles] with i ⟨hp, hq, hBlo, hB, hDlo, hD, hpB, hqD, hlo, hhi⟩
    exact ⟨(measurable_real_radial_weight hp hq).aestronglyMeasurable, mul_pos hBlo hDlo, hlo, hhi,
      ae_real_radial_weight_brackets hp hq hBlo hB hDlo hD hpB hqD⟩
  · exact (real_log_profile_sharp_fourier_tendsto hf hc hzero).comp hK

/-- Measurability by zero extension and pointwise upper-indicator brackets
on the positive ray. Each endpoint interval belongs to one constituent
profile, not to the annulus obtained by subtraction. -/
@[expose] public def RealUpperProfileBracket (p : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  Measurable ((Ioi (0 : ℝ)).indicator p) ∧ 0 < lo ∧ lo ≤ hi ∧
    ∀ s > 0, (Iic lo).indicator (fun _ ↦ (1 : ℝ)) s ≤ p s ∧
      p s ≤ (Iic hi).indicator (fun _ ↦ (1 : ℝ)) s

/-- Decompose an annular profile on the positive ray into the difference of
upper-bracketed profiles. The lower support condition includes `aLo`, as
required by the closed lower indicator for the subtracted constituent. -/
public theorem exists_real_upper_profile_bracket_sub {ρ : ℝ → ℝ} {aLo aHi bLo bHi : ℝ}
    (hρ : Measurable ((Ioi (0 : ℝ)).indicator ρ))
    (haLo : 0 < aLo) (ha : aLo ≤ aHi) (hab : aHi ≤ bLo) (hb : bLo ≤ bHi)
    (hrange : ∀ s > 0, ρ s ∈ Icc (0 : ℝ) 1)
    (hlower : ∀ s > 0, s ≤ aLo → ρ s = 0)
    (hupper : ∀ s > bHi, ρ s = 0)
    (hplateau : ∀ s ∈ Icc aHi bLo, ρ s = 1) :
    ∃ pA pB : ℝ → ℝ, RealUpperProfileBracket pA aLo aHi ∧
      RealUpperProfileBracket pB bLo bHi ∧ ∀ s > 0, ρ s = pB s - pA s := by
  let ρ₀ := (Ioi (0 : ℝ)).indicator ρ
  let pA (s : ℝ) := if s ≤ aHi then 1 - ρ₀ s else 0
  let pB (s : ℝ) := if s ≤ aHi then 1 else ρ₀ s
  have hρ₀ (s : ℝ) (hs : 0 < s) : ρ₀ s = ρ s := indicator_of_mem hs _
  have hmA : Measurable pA :=
    Measurable.ite measurableSet_Iic (measurable_const.sub hρ) measurable_const
  have hmB : Measurable pB := Measurable.ite measurableSet_Iic measurable_const hρ
  refine ⟨pA, pB, ⟨hmA.indicator measurableSet_Ioi, haLo, ha, ?_⟩,
    ⟨hmB.indicator measurableSet_Ioi, (haLo.trans_le ha).trans_le hab, hb, ?_⟩, ?_⟩
  · intro s hs
    by_cases hslo : s ≤ aLo
    · simp [pA, hslo, hslo.trans ha, hρ₀ s hs, hlower s hs hslo]
    · by_cases hshi : s ≤ aHi
      · obtain ⟨h0, h1⟩ := hrange s hs
        simp [pA, hslo, hshi, hρ₀ s hs, sub_nonneg.mpr h1, sub_le_self 1 h0]
      · simp [pA, hslo, hshi]
  · intro s hs
    by_cases hsc : s ≤ aHi
    · simp [pB, hsc, hsc.trans hab, (hsc.trans hab).trans hb]
    · by_cases hslo : s ≤ bLo
      · have h1 := hplateau s ⟨(lt_of_not_ge hsc).le, hslo⟩
        simp [pB, hsc, hslo, hslo.trans hb, hρ₀ s hs, h1]
      · by_cases hshi : s ≤ bHi
        · simpa [pB, hsc, hslo, hshi, hρ₀ s hs] using hrange s hs
        · simp [pB, hsc, hslo, hshi, hρ₀ s hs, hupper s (lt_of_not_ge hshi)]
  · intro s hs
    by_cases hsc : s ≤ aHi <;> simp [pA, pB, hsc, hρ₀ s hs]

/-- The profile product integrated against `ds/s` on the positive radial
quotient, as a function of the additive frequency, extended by zero at zero. -/
@[expose] public noncomputable def realRadialWeight (p q : ℝ → ℝ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else ∫ s in Ioi (0 : ℝ), p s * q (|w| / s) * s⁻¹

/-- Pair the retained real radial weight with the additive Fourier transform. -/
@[expose] public noncomputable def realRadialPairing (u : ℝ → ℂ) (p q : ℝ → ℝ) : ℂ :=
  ∫ w, (realRadialWeight p q w : ℂ) * 𝓕 u w

private theorem radial_pairing_bound {u : ℝ → ℂ} (hu : Integrable u)
    {p q : ℝ → ℝ} {Blo Bhi Dlo Dhi K : ℝ}
    (hB : RealUpperProfileBracket p Blo Bhi) (hD : RealUpperProfileBracket q Dlo Dhi)
    (hlo : Blo * Dlo ≤ K) (hhi : K ≤ Bhi * Dhi) :
    Integrable (fun w ↦ (realRadialWeight p q w : ℂ) * 𝓕 u w) ∧
      ‖realRadialPairing u p q - realSharpCutScalar u K‖ ≤
        2 * (Bhi * Dhi - Blo * Dlo) * ∫ x, ‖u x‖ := by
  obtain ⟨hp, hBlo, hBord, hpB⟩ := hB
  obtain ⟨hq, hDlo, hDord, hqD⟩ := hD
  exact integrable_real_radial_pairing_and_norm_sub_le hp hq hBlo hBord hDlo hDord hpB hqD hu hlo hhi

/-- Split the smoothed two-annulus scalar into four upper-profile pairings.
Both the signed radial density at positive radii and the signed Fourier
integrand are absolutely integrable. No cutoff limit is needed. -/
public theorem real_radial_pairing_sub_sub {u : ℝ → ℂ} (hu : Integrable u)
    {pA pB qC qD : ℝ → ℝ} {Alo Ahi Blo Bhi Clo Chi Dlo Dhi : ℝ}
    (hA : RealUpperProfileBracket pA Alo Ahi) (hB : RealUpperProfileBracket pB Blo Bhi)
    (hC : RealUpperProfileBracket qC Clo Chi) (hD : RealUpperProfileBracket qD Dlo Dhi) :
    (∀ r > 0, IntegrableOn (fun s ↦ (pB s - pA s) * (qD (r / s) - qC (r / s)) * s⁻¹)
      (Ioi 0)) ∧
    Integrable (fun w ↦ (realRadialWeight (pB - pA) (qD - qC) w : ℂ) * 𝓕 u w) ∧
    realRadialPairing u (pB - pA) (qD - qC) =
      realRadialPairing u pB qD - realRadialPairing u pA qD -
        (realRadialPairing u pB qC - realRadialPairing u pA qC) := by
  let g (p q : ℝ → ℝ) (r s : ℝ) := p s * q (r / s) * s⁻¹
  have hg {p q : ℝ → ℝ} {lo hi lo' hi' r : ℝ} (hr : 0 < r)
      (hp : RealUpperProfileBracket p lo hi) (hq : RealUpperProfileBracket q lo' hi') :
      IntegrableOn (g p q r) (Ioi 0) := by
    obtain ⟨hp, hl, hh, hp'⟩ := hp
    obtain ⟨hq, hl', hh', hq'⟩ := hq
    exact (real_radial_weight_sandwich hp hq hl hh hl' hh' hr hp' hq').1
  have hs (r : ℝ) : g (pB - pA) (qD - qC) r =
      (g pB qD r - g pA qD r) - (g pB qC r - g pA qC r) := by
    funext s
    simp only [g, Pi.sub_apply]
    ring
  refine ⟨fun r hr ↦ ?_, ?_⟩
  · change IntegrableOn (g (pB - pA) (qD - qC) r) (Ioi 0)
    rw [hs]
    exact ((hg hr hB hD).sub (hg hr hA hD)).sub ((hg hr hB hC).sub (hg hr hA hC))
  have hw (w : ℝ) : realRadialWeight (pB - pA) (qD - qC) w =
      (realRadialWeight pB qD w - realRadialWeight pA qD w) -
        (realRadialWeight pB qC w - realRadialWeight pA qC w) := by
    by_cases hz : w = 0
    · simp [realRadialWeight, hz]
    simp only [realRadialWeight, ite_eq_right hz]
    change (∫ s in Ioi 0, g (pB - pA) (qD - qC) |w| s) =
      (∫ s in Ioi 0, g pB qD |w| s) - (∫ s in Ioi 0, g pA qD |w| s) -
        ((∫ s in Ioi 0, g pB qC |w| s) - (∫ s in Ioi 0, g pA qC |w| s))
    have hBD := hg (abs_pos.mpr hz) hB hD
    have hAD := hg (abs_pos.mpr hz) hA hD
    have hBC := hg (abs_pos.mpr hz) hB hC
    have hAC := hg (abs_pos.mpr hz) hA hC
    rw [hs]
    simpa only [Pi.sub_apply, integral_sub hBD hAD, integral_sub hBC hAC] using
      (integral_sub (hBD.sub hAD) (hBC.sub hAC))
  let F (p q : ℝ → ℝ) (w : ℝ) := (realRadialWeight p q w : ℂ) * 𝓕 u w
  have hF {p q : ℝ → ℝ} {lo hi lo' hi' : ℝ}
      (hp : RealUpperProfileBracket p lo hi) (hq : RealUpperProfileBracket q lo' hi') :
      Integrable (F p q) :=
    (radial_pairing_bound hu hp hq le_rfl
      (mul_le_mul hp.2.2.1 hq.2.2.1 hq.2.1.le (hp.2.1.trans_le hp.2.2.1).le)).1
  have hsplit : F (pB - pA) (qD - qC) = (F pB qD - F pA qD) - (F pB qC - F pA qC) := by
    funext w
    simp only [F, Pi.sub_apply, hw, Complex.ofReal_sub, sub_mul]
  change Integrable (F (pB - pA) (qD - qC)) ∧
    (∫ w, F (pB - pA) (qD - qC) w) =
      (∫ w, F pB qD w) - (∫ w, F pA qD w) - ((∫ w, F pB qC w) - (∫ w, F pA qC w))
  have hBD := hF hB hD
  have hAD := hF hA hD
  have hBC := hF hB hC
  have hAC := hF hA hC
  rw [hsplit]
  refine ⟨(hBD.sub hAD).sub (hBC.sub hAC), ?_⟩
  simpa only [Pi.sub_apply, integral_sub hBD hAD, integral_sub hBC hAC] using
    (integral_sub (hBD.sub hAD) (hBC.sub hAC))

/-- On any filter, the signed sharp limit transfers to the smoothed
annular pairing when each of the four product widths tends to zero.
The Boolean labels select the positive (`true`) or negative (`false`)
constituent of each profile. Only the ray brackets and intermediate
cutoff conditions are required eventually. -/
public theorem real_radial_pairing_sub_sub_tendsto {ι : Type*} {l : Filter ι}
    {u : ℝ → ℂ} (hu : Integrable u)
    {p q : ι → Bool → ℝ → ℝ} {Blo Bhi Dlo Dhi : ι → Bool → ℝ}
    {K : ι → Bool → Bool → ℝ} {L : ℂ}
    (hprofiles : ∀ᶠ i in l,
      (∀ b, RealUpperProfileBracket (p i b) (Blo i b) (Bhi i b)) ∧
      (∀ d, RealUpperProfileBracket (q i d) (Dlo i d) (Dhi i d)) ∧
      ∀ b d, Blo i b * Dlo i d ≤ K i b d ∧ K i b d ≤ Bhi i b * Dhi i d)
    (hwidth : ∀ b d, Tendsto (fun i ↦ Bhi i b * Dhi i d - Blo i b * Dlo i d) l (𝓝 0))
    (hsharp : Tendsto (fun i ↦ realSharpCutScalar u (K i true true) -
      realSharpCutScalar u (K i false true) -
        (realSharpCutScalar u (K i true false) - realSharpCutScalar u (K i false false))) l (𝓝 L)) :
    Tendsto (fun i ↦ realRadialPairing u (p i true - p i false) (q i true - q i false)) l (𝓝 L) := by
  have herr (b d : Bool) : Tendsto
      (fun i ↦ realRadialPairing u (p i b) (q i d) - realSharpCutScalar u (K i b d)) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun i ↦ 2 * (Bhi i b * Dhi i d - Blo i b * Dlo i d) * ∫ x, ‖u x‖)
    · filter_upwards [hprofiles] with i ⟨hp, hq, hK⟩
      exact (radial_pairing_bound hu (hp b) (hq d) (hK b d).1 (hK b d).2).2
    · simpa only [mul_zero, zero_mul] using
        (((hwidth b d).const_mul (2 : ℝ)).mul_const (∫ x, ‖u x‖))
  have hdiff := ((herr true true).sub (herr false true)).sub ((herr true false).sub (herr false false))
  have hsum := hdiff.add hsharp
  simp only [sub_zero, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hprofiles] with i ⟨hp, hq, _⟩
  rw [(real_radial_pairing_sub_sub hu (hp false) (hp true) (hq false) (hq true)).2.2]
  ring

end Masullo
