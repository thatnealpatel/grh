module

public import Props.RealSharpFourierCutoff
public import Lemmas.RealSharpLowerEdges
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
