module

public import Props.RealSharpFourierCutoff
public import Lemmas.RealSharpLowerEdges
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Lower cutoff edges in the rational real scalar integral

In (12.4.1.12) and (12.4.1.15), p. 517, Masullo retains two
cutoff multipliers. Equation (12.4.1.22) replaces them with sharp upper
cutoffs. For an annular position cutoff, as proposed in p. 514 n. 2,
the lower edge subtracts another copy of the sharp scalar. The limits
below concern the scalar after extending the radial domain, not the
Paley–Wiener projection or its trace.
-/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- One annular position band `[A,B]` and an upper Fourier band of radius
`D` have scalar `S(B D) - S(A D)`, by integrating `ds/s` over
`max A (|w|/D) ≤ s ≤ B`. A vanishing lower product and a diverging lower
product yield different limits if the sharp half-Haar scalar is nonzero.
The filter is arbitrary to allow both independent paths and coupled limits. -/
public theorem real_log_profile_position_lower_edge_limits {ι : Type*} {l : Filter ι}
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0)
    {A B D : ι → ℝ} (hBD : Tendsto (fun i ↦ B i * D i) l atTop) :
    let u := realLogProfileAdditive (fun t ↦ f (-t))
    let S := realSharpCutScalar u
    (Tendsto (fun i ↦ A i * D i) l (𝓝[>] 0) →
      Tendsto (fun i ↦ S (B i * D i) - S (A i * D i)) l
        (𝓝 ((1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ)))) ∧
    (Tendsto (fun i ↦ A i * D i) l atTop →
      Tendsto (fun i ↦ S (B i * D i) - S (A i * D i)) l (𝓝 0)) := by
  intro u S
  have hlarge : Tendsto S atTop (𝓝 ((1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ))) :=
    real_log_profile_sharp_fourier_tendsto hf hc hzero
  exact ⟨fun hAD ↦ by simpa only [Function.comp_apply, sub_zero] using
      (hlarge.comp hBD).sub ((logProfile_sharpCut_tendsto_zero hf hc).comp hAD),
    fun hAD ↦ by simpa only [Function.comp_apply, sub_self] using
      (hlarge.comp hBD).sub (hlarge.comp hAD)⟩

/-- Adding an annular Fourier band `[C,D]` subtracts `S(B C) - S(A C)`.
When one cross-product diverges and the other vanishes, the sharp scalar
is erased even though both upper cutoffs exhaust and both lower edges
shrink. Reciprocal annuli with `B=t²`, `D=t` give this regime. -/
public theorem real_log_profile_two_annuli_erase {ι : Type*} {l : Filter ι}
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0)
    {A B C D : ι → ℝ} (hBD : Tendsto (fun i ↦ B i * D i) l atTop)
    (hAD : Tendsto (fun i ↦ A i * D i) l (𝓝[>] 0))
    (hBC : Tendsto (fun i ↦ B i * C i) l atTop)
    (hAC : Tendsto (fun i ↦ A i * C i) l (𝓝[>] 0)) :
    let S := realSharpCutScalar (realLogProfileAdditive (fun t ↦ f (-t)))
    Tendsto (fun i ↦ S (B i * D i) - S (A i * D i) -
      (S (B i * C i) - S (A i * C i))) l (𝓝 0) := by
  intro S
  have h₁ := (real_log_profile_position_lower_edge_limits hf hc hzero hBD).1 hAD
  have h₂ := (real_log_profile_position_lower_edge_limits hf hc hzero hBC).1 hAC
  simpa only [sub_self] using h₁.sub h₂

/-- Sharp radial volume of the retained position band and upper Fourier band.
The integrator is positive real multiplicative Haar (`ds/s`). The zero
frequency is omitted in the statement; it is a Lebesgue-null singleton. -/
public theorem real_position_band_radial_volume {A B D r : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hD : 0 < D) (hr : 0 < r) :
    (∫ s in Icc (max A (r / D)) B, s⁻¹) =
      (if r ≤ B * D then Real.log (B * D) - Real.log r else 0) -
      (if r ≤ A * D then Real.log (A * D) - Real.log r else 0) := by
  have hB := hA.trans_le hAB
  have hrd := div_pos hr hD
  have hADB := mul_le_mul_of_nonneg_right hAB hD.le
  have radial (a : ℝ) (ha : 0 < a) (hab : a ≤ B) :
      (∫ s in Icc a B, s⁻¹) = Real.log B - Real.log a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_inv (by simp [uIcc_of_le hab, ha.not_ge]), Real.log_div hB.ne' ha.ne']
  by_cases hb : r ≤ B * D
  · have hrdB := (div_le_iff₀ hD).2 hb
    rw [ite_eq_left hb, radial _ (hA.trans_le (le_max_left ..)) (max_le hAB hrdB)]
    by_cases ha : r ≤ A * D
    · rw [ite_eq_left ha, max_eq_left ((div_le_iff₀ hD).2 ha),
        Real.log_mul hB.ne' hD.ne', Real.log_mul hA.ne' hD.ne']
      ring
    · rw [ite_eq_right ha, max_eq_right (le_of_lt ((lt_div_iff₀ hD).2 (lt_of_not_ge ha))),
        Real.log_div hr.ne' hD.ne', Real.log_mul hB.ne' hD.ne']
      ring
  · rw [ite_eq_right hb, ite_eq_right (fun ha ↦ hb (ha.trans hADB)),
      Icc_eq_empty_of_lt (((lt_div_iff₀ hD).2 (lt_of_not_ge hb)).trans_le (le_max_right ..)),
      setIntegral_empty, sub_zero]

/-- The normalized sharp real scalar on the extended radial domain, with
position band `[A,B]` and Fourier band `|w|/s ≤ D`. -/
@[expose] public noncomputable def realPositionBandScalar (u : ℝ → ℂ) (A B D : ℝ) : ℂ :=
  ∫ w : ℝ, ((∫ s in Icc (max A (|w| / D)) B, s⁻¹ : ℝ) : ℂ) * 𝓕 u w

/-- Retaining the position lower edge subtracts a sharp scalar at `A D`.
This is an equality of scalar integrals, not a projected trace identity. -/
public theorem real_position_band_scalar_eq {u : ℝ → ℂ} (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun w ↦ (Real.log |w| : ℂ) * 𝓕 u w))
    {A B D : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hD : 0 < D) :
    realPositionBandScalar u A B D = realSharpCutScalar u (B * D) -
      realSharpCutScalar u (A * D) := by
  let s (K : ℝ) : Set ℝ := {w | |w| ≤ K}
  let g (K : ℝ) (w : ℝ) : ℂ := ((Real.log K - Real.log |w| : ℝ) : ℂ) * 𝓕 u w
  have hm (K : ℝ) : MeasurableSet (s K) := measurableSet_le (by fun_prop) measurable_const
  have hg (K : ℝ) : Integrable ((s K).indicator (g K)) := by
    apply Integrable.indicator _ (hm K)
    simpa only [g, Complex.ofReal_sub, sub_mul, Pi.sub_def] using
      (huf.const_mul (Real.log K : ℂ)).sub hlog
  have he (K : ℝ) : realSharpCutScalar u K = ∫ w, (s K).indicator (g K) w :=
    (integral_indicator (hm K)).symm
  rw [he, he, ← integral_sub (hg _) (hg _)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
  rw [real_position_band_radial_volume hA hAB hD (abs_pos.mpr hw), Complex.ofReal_sub, sub_mul]
  congr 1 <;> split_ifs <;> simp_all [s, g, indicator_apply]

private theorem annular_band_radial_volume {A B C D r : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D) (hr : 0 ≤ r) :
    (∫ s in Icc A B ∩ Icc (r / D) (r / C), s⁻¹) =
      (∫ s in Icc (max A (r / D)) B, s⁻¹) -
        (∫ s in Icc (max A (r / C)) B, s⁻¹) := by
  have hcut : r / D ≤ r / C := div_le_div_of_nonneg_left hr hC hCD
  have hsub : Icc (max A (r / C)) B ⊆ Icc (max A (r / D)) B :=
    Icc_subset_Icc_left (max_le_max le_rfl hcut)
  have hint : IntegrableOn (fun s : ℝ ↦ s⁻¹) (Icc (max A (r / D)) B) := by
    refine (continuous_id.continuousOn.inv₀ ?_).integrableOn_Icc
    intro s hs
    exact (hA.trans_le ((le_max_left ..).trans hs.1)).ne'
  rw [← setIntegral_sdiff measurableSet_Icc hint hsub]
  apply setIntegral_congr_set
  filter_upwards [volume.ae_ne (r / C)] with s hs
  simp only [mem_inter_iff, mem_Icc, Set.mem_sdiff, max_le_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hd, hc⟩
    exact ⟨⟨⟨ha, hd⟩, hb⟩, fun h ↦ hs (hc.antisymm h.1.2)⟩
  · rintro ⟨⟨⟨ha, hd⟩, hb⟩, hc⟩
    exact ⟨⟨ha, hb⟩, hd, (lt_of_not_ge (fun h ↦ hc ⟨⟨ha, h⟩, hb⟩)).le⟩

private theorem integrable_sharp_cut_pairing {u : ℝ → ℂ} (hu : Integrable u) (K : ℝ) :
    Integrable ({w : ℝ | |w| ≤ K}.indicator
      (fun w ↦ ((Real.log K - Real.log |w| : ℝ) : ℂ) * 𝓕 u w)) := by
  have hs : {w : ℝ | |w| ≤ K} = Icc (-K) K := by
    ext w
    change |w| ≤ K ↔ -K ≤ w ∧ w ≤ K
    exact abs_le
  have hl : IntegrableOn (fun w : ℝ ↦ Real.log K - Real.log |w|) {w : ℝ | |w| ≤ K} := by
    rw [hs, integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)]
    have hlog : IntervalIntegrable (fun w : ℝ ↦ Real.log K - Real.log w) volume (-K) K :=
      intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
    simpa only [Real.log_abs] using hlog.1
  have hm : MeasurableSet {w : ℝ | |w| ≤ K} := hs.symm ▸ measurableSet_Icc
  have hg : Integrable ({w : ℝ | |w| ≤ K}.indicator
      (fun w ↦ ((Real.log K - Real.log |w| : ℝ) : ℂ))) :=
    (integrable_indicator_iff hm).2 hl.ofReal
  have hf : Continuous (𝓕 u) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hu
  simpa only [← Set.indicator_mul_left] using
    hg.mul_bdd hf.aestronglyMeasurable (.of_forall (Real.norm_fourier_le_integral_norm u))

/-- The sharp scalar on the repaired positive radial quotient, retaining
both the position band `[A,B]` and the frequency band `[C,D]`. -/
@[expose] public noncomputable def realTwoAnnuliScalar (u : ℝ → ℂ) (A B C D : ℝ) : ℂ :=
  ∫ w : ℝ, ((∫ s in Icc A B ∩ Icc (|w| / D) (|w| / C), s⁻¹ : ℝ) : ℂ) * 𝓕 u w

/-- The finite sharp annular scalar is an alternating sum of upper
cutoff scalars. Only integrability of the test is needed: Each finite
log band is integrable and the Fourier transform is bounded. -/
public theorem real_two_annuli_scalar_eq {u : ℝ → ℂ} (hu : Integrable u) {A B C D : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D) :
    realTwoAnnuliScalar u A B C D = realSharpCutScalar u (B * D) - realSharpCutScalar u (A * D) -
      (realSharpCutScalar u (B * C) - realSharpCutScalar u (A * C)) := by
  let s (K : ℝ) : Set ℝ := {w | |w| ≤ K}
  let g (K : ℝ) (w : ℝ) : ℂ := ((Real.log K - Real.log |w| : ℝ) : ℂ) * 𝓕 u w
  let q (K : ℝ) := (s K).indicator (g K)
  have hq (K : ℝ) : Integrable (q K) := integrable_sharp_cut_pairing hu K
  have hJ (K : ℝ) : realSharpCutScalar u K = ∫ w, q K w :=
    (integral_indicator (measurableSet_le (by fun_prop) measurable_const)).symm
  have hqsub (K L : ℝ) : Integrable (fun w ↦ q K w - q L w) := (hq K).sub (hq L)
  simp only [realTwoAnnuliScalar, hJ]
  rw [← integral_sub (hq _) (hq _), ← integral_sub (hq _) (hq _),
    ← integral_sub (hqsub _ _) (hqsub _ _)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
  have hedge (E : ℝ) (hE : 0 < E) :
      ((∫ s in Icc (max A (|w| / E)) B, s⁻¹ : ℝ) : ℂ) * 𝓕 u w =
        q (B * E) w - q (A * E) w := by
    rw [real_position_band_radial_volume hA hAB hE (abs_pos.mpr hw), Complex.ofReal_sub, sub_mul]
    congr 1 <;> split_ifs <;> simp_all [s, g, q, indicator_apply]
  rw [annular_band_radial_volume hA hC hCD (abs_nonneg w), Complex.ofReal_sub, sub_mul,
    hedge D (hC.trans_le hCD), hedge C hC]

/-- The annular position repair proposed on p. 514 n. 2 does not have a
path-independent joint limit at the level of the retained sharp scalar.
In both paths `A → 0`, `B → ∞`, and `D → ∞`, but the comparison of `A`
with `1/D` differs. No assertion about smoothing or the global operator
is used. -/
public theorem real_position_band_scalar_path_dependence :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 0 ∧
      let u := realLogProfileAdditive (fun t ↦ f (-t))
      let H := (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ)
      H ≠ 0 ∧
      Tendsto (fun t : ℝ ↦ realPositionBandScalar u (t ^ 2)⁻¹ t t) atTop (𝓝 H) ∧
      Tendsto (fun t : ℝ ↦ realPositionBandScalar u t⁻¹ (t ^ 2) (t ^ 2)) atTop (𝓝 0) := by
  obtain ⟨f, hf, hc, hzero, hH⟩ := exists_nonzero_half_haar
  let u := realLogProfileAdditive (fun t ↦ f (-t))
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test (hf.comp contDiff_neg)
    (hc.comp_homeomorph (Homeomorph.neg ℝ))
  let v := hk.toSchwartzMap hd
  have he {A B D : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hD : 0 < D) :=
    real_position_band_scalar_eq (u := u) (𝓕 v).integrable
      (RealLogFourier.log_fourier_integrable v) hA hAB hD
  have hpow : Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop := tendsto_pow_atTop (by decide)
  have h₁ : Tendsto (fun t : ℝ ↦ (t ^ 2)⁻¹ * t) atTop (𝓝[>] 0) := by
    refine (tendsto_inv_atTop_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    field_simp [ne_of_gt (zero_lt_one.trans_le ht)]
  have h₂ : Tendsto (fun t : ℝ ↦ t⁻¹ * t ^ 2) atTop atTop := by
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    change t = t⁻¹ * t ^ 2
    field_simp [ne_of_gt (zero_lt_one.trans_le ht)]
  refine ⟨f, hf, hc, hzero, hH, ?_, ?_⟩
  · have hsq : Tendsto (fun t : ℝ ↦ t * t) atTop atTop :=
      tendsto_id.atTop_mul_atTop₀ tendsto_id
    refine ((real_log_profile_position_lower_edge_limits hf hc hzero hsq).1 h₁).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht' := zero_lt_one.trans_le ht
    exact (he (inv_pos.mpr (pow_pos ht' _))
      ((inv_le_one_of_one_le₀ (one_le_pow₀ ht)).trans ht) ht').symm
  · refine ((real_log_profile_position_lower_edge_limits hf hc hzero
      (hpow.atTop_mul_atTop₀ hpow)).2 h₂).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (he (inv_pos.mpr (zero_lt_one.trans_le ht))
      ((inv_le_one_of_one_le₀ ht).trans (one_le_pow₀ ht))
      (pow_pos (zero_lt_one.trans_le ht) _)).symm

end Masullo
