module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The small missing-divisor probability witness on the circle

Sources: `fea7eb0b:.godel/alice/sharp-sparse-harmonics.md:9–13` and
`b825bc58:.godel/bob/noisy-sparse-harmonics.md:11–16` (scan `fa7259d`,
unchanged at the writing base). This is Bob's small branch with coefficient
`15/16`, on `ℝ / (2πℤ)` with Haar probability measure. The endpoint gives the
exact-zero inputs to `Masullo.exists_noisy_moment_witness`, including the
closed near-zero arcs. It does not assert a minimax bound.

Owning check session: `01a20eab-a304-7e57-9eec-1f7fc75e3637`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace Masullo.SparseSmallDensity

public abbrev AngularCircle := AddCircle (2 * Real.pi)

public instance twoPi_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The absolute half-sine on the circle, expressed using distance to zero. -/
@[expose] public noncomputable def envelope (s : AngularCircle) : ℝ :=
  Real.sin (‖s‖ / 2)

/-- `fourier` at period `2π` is the positive-sign complex harmonic. -/
public theorem fourier_coe (j : ℤ) (s : ℝ) :
    fourier j (s : AngularCircle) = Complex.exp (↑((j : ℝ) * s) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The observable is `|sin(s/2)|` on every real representative, not just a chosen lift. -/
public theorem envelope_coe (s : ℝ) :
    envelope (s : AngularCircle) = |Real.sin (s / 2)| := by
  have hnorm : ‖(s : AngularCircle)‖ ≤ Real.pi := by
    simpa [abs_of_pos Real.pi_pos] using
      (AddCircle.norm_le_half_period (2 * Real.pi) (by positivity : 2 * Real.pi ≠ 0)
        (x := (s : AngularCircle)))
  have hs : 0 ≤ envelope (s : AngularCircle) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  rw [← abs_of_nonneg hs, envelope, AddCircle.norm_eq]
  let k := round ((2 * Real.pi)⁻¹ * s)
  change |Real.sin (|s - (k : ℝ) * (2 * Real.pi)| / 2)| = _
  have h (x : ℝ) : |Real.sin (|x| / 2)| = |Real.sin (x / 2)| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, neg_div, Real.sin_neg, abs_neg]
  rw [h, show (s - (k : ℝ) * (2 * Real.pi)) / 2 = s / 2 + ((-k : ℤ) : ℝ) * Real.pi by
    push_cast; ring, Real.sin_add_int_mul_pi, abs_mul]
  simp

private theorem continuous_envelope : Continuous envelope := by
  unfold envelope
  fun_prop

/-- The real-valued density, packaged as nonnegative for `withDensity`. -/
@[expose] public noncomputable def density (n : ℕ) (s : AngularCircle) : ℝ≥0 :=
  ⟨1 - (15 / 16 : ℝ) * (fourier (n : ℤ) s).re,
    by
      have h : (fourier (n : ℤ) s).re ≤ 1 :=
        (Complex.re_le_norm _).trans_eq (Circle.norm_coe _)
      linarith⟩

private theorem continuous_density (n : ℕ) :
    Continuous fun s : AngularCircle ↦ (density n s : ℝ) := by
  change Continuous fun s ↦ 1 - (15 / 16 : ℝ) * (fourier (n : ℤ) s).re
  fun_prop

/-- The density on real representatives is exactly Bob's damped cosine. -/
public theorem density_coe (n : ℕ) (s : ℝ) :
    (density n (s : AngularCircle) : ℝ) = 1 - (15 / 16 : ℝ) * Real.cos ((n : ℝ) * s) := by
  change 1 - (15 / 16 : ℝ) * (fourier (n : ℤ) (s : AngularCircle)).re = _
  rw [fourier_coe, Int.cast_natCast, Complex.exp_ofReal_mul_I_re]

/-- The explicit law, relative to Haar normalized to mass one. -/
@[expose] public noncomputable def law (n : ℕ) : Measure AngularCircle :=
  AddCircle.haarAddCircle.withDensity (fun s ↦ (density n s : ℝ≥0∞))

private theorem density_measurable (n : ℕ) : Measurable (density n) :=
  (continuous_density n).measurable.subtype_mk

-- Integrate on the actual weighted circle, then transfer the weighted observable to [0, 2π].
private theorem integral_law_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (g : AngularCircle → E) :
    (∫ s, g s ∂law n) = (2 * Real.pi)⁻¹ •
      ∫ s in (0 : ℝ)..2 * Real.pi,
        (1 - (15 / 16 : ℝ) * Real.cos ((n : ℝ) * s)) • g (s : AngularCircle) := by
  rw [law, integral_withDensity_eq_integral_smul (density_measurable n),
    AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp only [zero_add, NNReal.smul_def, density_coe]

private noncomputable abbrev haar : Measure AngularCircle := AddCircle.haarAddCircle

private theorem mode_integrable (j : ℤ) : Integrable (fourier (T := 2 * Real.pi) j) haar :=
  Integrable.of_bound (fourier j).continuous.measurable.aestronglyMeasurable 1
    (ae_of_all _ fun s ↦ (Circle.norm_coe (AddCircle.toCircle (j • s))).le)

private theorem haar_mode_zero {j : ℤ} (hj : j ≠ 0) :
    (∫ s, fourier j s ∂haar) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hj (by positivity))

-- Multiplication by the density adds only the two frequencies `±n`.
private theorem weighted_mode (n : ℕ) (j : ℤ) (s : AngularCircle) :
    density n s • fourier j s = fourier j s - (15 / 32 : ℂ) *
      (fourier (j + (n : ℤ)) s + fourier (j - (n : ℤ)) s) := by
  rw [sub_eq_add_neg j, fourier_add, fourier_add, fourier_neg, ← mul_add, Complex.add_conj]
  change (1 - (15 / 16 : ℝ) * (fourier (n : ℤ) s).re) • fourier j s = _
  rw [Complex.real_smul]
  push_cast
  ring

private theorem integral_law_mode (n : ℕ) (j : ℤ)
    (hplus : j + (n : ℤ) ≠ 0) (hminus : j - (n : ℤ) ≠ 0) :
    (∫ s, fourier j s ∂law n) = ∫ s, fourier j s ∂haar := by
  rw [law, integral_withDensity_eq_integral_smul (density_measurable n)]
  simp_rw [weighted_mode]
  have hg : Integrable (fun s ↦ (15 / 32 : ℂ) *
      (fourier (j + (n : ℤ)) s + fourier (j - (n : ℤ)) s)) haar :=
    ((mode_integrable _).add (mode_integrable _)).const_mul _
  rw [integral_sub (mode_integrable j) hg,
    integral_const_mul, integral_add (mode_integrable _) (mode_integrable _),
    haar_mode_zero hplus, haar_mode_zero hminus]
  simp

/-- The cosine density has total mass one as a measure on the circle. -/
public theorem law_probability {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (law n) := by
  have h : (∫ s, ((density n s : ℝ) : ℂ) ∂haar) = 1 := by
    have hc := integral_law_mode n 0 (by omega) (by omega)
    rw [law, integral_withDensity_eq_integral_smul (density_measurable n)] at hc
    simpa only [fourier_zero, NNReal.smul_def, Complex.real_smul,
      mul_one, integral_const, probReal_univ, one_smul] using hc
  have hreal : (∫ s, (density n s : ℝ) ∂haar) = 1 :=
    Complex.ofReal_inj.mp (by simpa only [integral_complex_ofReal, Complex.ofReal_one] using h)
  exact ⟨by rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral _ ((continuous_density n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), hreal, ENNReal.ofReal_one]⟩

/-- All positive query modes other than the missing mode vanish, with no frequency cap. -/
public theorem law_mode_zero {n j : ℕ} (hj : 0 < j) (hjn : j ≠ n) :
    (∫ s, fourier (j : ℤ) s ∂law n) = 0 := by
  rw [integral_law_mode n j (by omega) (by omega)]
  exact haar_mode_zero (by omega)

/-- The closed arc about zero of radius `min(π, 16πt)` in radians. -/
@[expose] public noncomputable def arc (t : ℝ) : Set AngularCircle :=
  Metric.closedBall 0 (min Real.pi (16 * Real.pi * t))

private theorem law_ge_scaled_volume (n : ℕ) :
    ENNReal.ofReal ((32 * Real.pi)⁻¹) • (volume : Measure AngularCircle) ≤ law n := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
    ← ENNReal.ofReal_mul (by positivity),
    show (32 * Real.pi)⁻¹ * (2 * Real.pi) = 1 / 16 by
      field_simp [Real.pi_ne_zero]; norm_num,
    ← withDensity_const, law]
  apply withDensity_mono
  refine ae_of_all _ fun s ↦ ?_
  change ENNReal.ofReal (1 / 16) ≤ (density n s : ℝ≥0∞)
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  change 1 / 16 ≤ 1 - (15 / 16 : ℝ) * (fourier (n : ℤ) s).re
  have h : (fourier (n : ℤ) s).re ≤ 1 :=
    (Complex.re_le_norm _).trans_eq (Circle.norm_coe _)
  linarith

/-- The near-zero arc has at least the removable mass, including when it saturates. -/
public theorem law_arc_mass {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ≤ 1) :
    ENNReal.ofReal t ≤ law n (arc t) := by
  by_cases h : Real.pi ≤ 16 * Real.pi * t
  · have := law_probability hn
    rw [arc, min_eq_left h, AddCircle.closedBall_eq_univ_of_half_period_le
      (2 * Real.pi) (by positivity) 0 (by rw [abs_of_pos (by positivity)]; linarith), measure_univ]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht
  · have hr := le_of_not_ge h
    have hvol : volume (arc t) = ENNReal.ofReal (32 * Real.pi * t) := by
      rw [arc, AddCircle.volume_closedBall, min_eq_right hr,
        min_eq_right (by linarith : 2 * (16 * Real.pi * t) ≤ 2 * Real.pi)]
      congr 1
      ring
    calc
      ENNReal.ofReal t = (ENNReal.ofReal ((32 * Real.pi)⁻¹) •
          (volume : Measure AngularCircle)) (arc t) := by
        rw [smul_apply, smul_eq_mul, hvol, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [Real.pi_ne_zero]
      _ ≤ law n (arc t) := law_ge_scaled_volume n _

/-- On the whole arc the absolute half-sine is at most `8πt`. -/
public theorem envelope_le_on_arc {s : AngularCircle} {t : ℝ} (hs : s ∈ arc t) :
    envelope s ≤ 8 * Real.pi * t := by
  have h : ‖s‖ ≤ 16 * Real.pi * t :=
    (by simpa only [arc, Metric.mem_closedBall, dist_zero_right] using hs :
      ‖s‖ ≤ min Real.pi (16 * Real.pi * t)).trans (min_le_right _ _)
  exact (Real.sin_le (by positivity)).trans (by linarith)

-- Both half-integer frequencies in the cosine product have endpoint cosine `-1`.
private theorem integral_sin_half_int (k : ℤ) :
    (∫ s in (0 : ℝ)..2 * Real.pi, Real.sin (((k : ℝ) + 1 / 2) * s)) =
      2 / ((k : ℝ) + 1 / 2) := by
  have hk : (k : ℝ) + 1 / 2 ≠ 0 := by
    intro h
    have h' : ((2 * k + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have : 2 * k + 1 = 0 := by exact_mod_cast h'
    omega
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hk, integral_sin,
    mul_zero, Real.cos_zero,
    show ((k : ℝ) + 1 / 2) * (2 * Real.pi) = Real.pi + (k : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi, Real.cos_pi, smul_eq_mul]
  ring

private theorem integral_half_sine :
    (∫ s in (0 : ℝ)..2 * Real.pi, Real.sin (s / 2)) = 4 := by
  simpa only [Int.cast_zero, zero_add, one_div, div_eq_inv_mul, mul_one] using
    (integral_sin_half_int 0).trans (show (2 : ℝ) / ((0 : ℤ) + (1 / 2 : ℝ)) = 4 by norm_num)

private theorem integral_cos_half_sine {n : ℕ} (hn : 1 ≤ n) :
    (∫ s in (0 : ℝ)..2 * Real.pi, Real.cos ((n : ℝ) * s) * Real.sin (s / 2)) =
      -4 / (4 * (n : ℝ)^2 - 1) := by
  have hprod (s : ℝ) : Real.cos ((n : ℝ) * s) * Real.sin (s / 2) =
      (Real.sin (((n : ℝ) + 1 / 2) * s) + Real.sin ((-(n : ℝ) + 1 / 2) * s)) / 2 := by
    rw [show ((n : ℝ) + 1 / 2) * s = s / 2 + (n : ℝ) * s by ring,
      show (-(n : ℝ) + 1 / 2) * s = s / 2 - (n : ℝ) * s by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have h₁ := integral_sin_half_int (n : ℤ)
  have h₂ := integral_sin_half_int (-(n : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast] at h₁ h₂
  simp_rw [hprod]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add, h₁, h₂]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : 0 < 4 * (n : ℝ)^2 - 1 := by nlinarith
    field_simp (disch := first | positivity | linarith | nlinarith)
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Exact absolute half-sine mean of the normalized circle law. -/
public theorem law_mean {n : ℕ} (hn : 1 ≤ n) :
    (∫ s, envelope s ∂law n) =
      (2 / Real.pi) * (1 + (15 / 16 : ℝ) / (4 * (n : ℝ)^2 - 1)) := by
  have h (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) (2 * Real.pi)) :
      envelope (s : AngularCircle) = Real.sin (s / 2) := by
    rw [uIcc_of_le (by positivity)] at hs
    rw [envelope_coe, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
      (by linarith [hs.2]))]
  rw [integral_law_interval]
  simp_rw [smul_eq_mul]
  rw [intervalIntegral.integral_congr
    (fun s hs ↦ congrArg (fun x : ℝ ↦ (1 - (15 / 16 : ℝ) * Real.cos ((n : ℝ) * s)) * x) (h s hs))]
  simp_rw [sub_mul, one_mul, mul_assoc]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    integral_half_sine, integral_cos_half_sine hn]
  · field_simp [Real.pi_ne_zero]; ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

private theorem mean_comparison {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n) (hsmall : 4 * n ≤ 3 * N) :
    1 / ((N : ℝ) * Real.sin (Real.pi / (2 * (N : ℝ)))) ≤
      (2 / Real.pi) * (1 + (15 / 16 : ℝ) / (4 * (n : ℝ)^2 - 1)) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmallR : (4 : ℝ) * n ≤ 3 * (N : ℝ) := by exact_mod_cast hsmall
  let z : ℝ := Real.pi / (2 * (N : ℝ))
  let D : ℝ := 4 * (n : ℝ)^2
  let a : ℝ := 15 / 16
  have hz : 0 < z := by dsimp [z]; positivity
  have hzπ : z < Real.pi := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (N : ℝ))).2
    nlinarith only [mul_pos Real.pi_pos (show 0 < 2 * (N : ℝ) - 1 by linarith)]
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < D - 1 := by dsimp [D]; nlinarith
  have ha : 0 < a := by norm_num [a]
  have hq : z^2 / 6 ≤ a / D := by
    have hpi : Real.pi^2 ≤ 10 := by
      nlinarith only [pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2]
    calc
      z^2 / 6 = Real.pi^2 / (24 * (N : ℝ)^2) := by
        dsimp [z]
        field_simp
        ring
      _ ≤ 10 / (24 * (N : ℝ)^2) := div_le_div_of_nonneg_right hpi (by positivity)
      _ ≤ a / D := by
        apply (div_le_div_iff₀ (by positivity) hD).2
        dsimp [a, D]
        nlinarith only [pow_le_pow_left₀ (by positivity : 0 ≤ (4 : ℝ) * n) hsmallR 2]
  have hsinc : 1 - a / D ≤ Real.sin z / z := calc
    _ ≤ 1 - z^2 / 6 := sub_le_sub_left hq _
    _ ≤ _ := (le_div_iff₀ hz).2 (by nlinarith only [Real.sin_gt_sub_cube hz])
  have hproduct : 1 ≤ (1 + a / (D - 1)) * (1 - a / D) := calc
    _ ≤ 1 + a * (1 - a) / (D * (D - 1)) := by
      apply le_add_of_nonneg_right
      exact div_nonneg (mul_nonneg ha.le (by norm_num [a])) (mul_pos hD hd).le
    _ = _ := by field_simp [hD.ne', hd.ne']; ring
  change 1 / ((N : ℝ) * Real.sin z) ≤ (2 / Real.pi) * (1 + a / (D - 1))
  rw [div_le_iff₀ (mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi hz hzπ))]
  calc
    1 ≤ (1 + a / (D - 1)) * (1 - a / D) := hproduct
    _ ≤ (1 + a / (D - 1)) * (Real.sin z / z) :=
      mul_le_mul_of_nonneg_left hsinc (by positivity)
    _ = (2 / Real.pi) * (1 + a / (D - 1)) * ((N : ℝ) * Real.sin z) := by
      rw [show Real.sin z / z = (2 / Real.pi) * ((N : ℝ) * Real.sin z) by
        dsimp [z]; field_simp [Real.pi_ne_zero]]
      ring

/-- The actual small-branch law gives the exact-zero inputs to the generic
noisy-moment perturbation, for any family of positive queries omitting `n`.
The near-zero estimates are simultaneous for all `0 ≤ t ≤ 1`. -/
public theorem small_density_witness {ι : Type*} (query : ι → ℕ) {N n : ℕ}
    (hN : 2 ≤ N) (hn : 1 ≤ n) (hsmall : 4 * n ≤ 3 * N)
    (hquery : ∀ i, 0 < query i) (hmiss : ∀ i, query i ≠ n) :
    IsProbabilityMeasure (law n) ∧
      (∀ i, Measurable (fourier (T := 2 * Real.pi) (query i : ℤ))) ∧
      (∀ i (s : AngularCircle), ‖fourier (query i : ℤ) s‖ ≤ 1) ∧
      (∀ i, (∫ s, fourier (query i : ℤ) s ∂law n) = 0) ∧
      Integrable envelope (law n) ∧
      1 / ((N : ℝ) * Real.sin (Real.pi / (2 * (N : ℝ)))) ≤ (∫ s, envelope s ∂law n) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → MeasurableSet (arc t) ∧
        ENNReal.ofReal t ≤ law n (arc t) ∧ ∀ s ∈ arc t, envelope s ≤ 8 * Real.pi * t := by
  have hp := law_probability hn
  refine ⟨hp, fun i ↦ (fourier (query i : ℤ)).continuous.measurable,
    fun i s ↦ (Circle.norm_coe (AddCircle.toCircle ((query i : ℤ) • s))).le,
    fun i ↦ law_mode_zero (hquery i) (hmiss i),
    continuous_envelope.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    ?_, fun t _ ht ↦ ⟨measurableSet_closedBall, law_arc_mass hn ht, fun _ ↦ envelope_le_on_arc⟩⟩
  rw [law_mean hn]
  exact mean_comparison hN hn hsmall

end Masullo.SparseSmallDensity
