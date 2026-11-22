module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Local rational real level in log coordinates

The real level uses the two unit contributions, giving the factor `2` in
`profile` (see `.godel/obligations/trace-polar-free-q.md`). The convention
with `√2` instead of `2` gives the same closed complex span: the respective
profiles differ by a single nonzero scalar. This is a local level with
additive Fourier support constrained before passing to log coordinates.
-/

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace Masullo.OperatorTrace.RealLogLevel

noncomputable section

/-- The weight in the log coordinate, with nonnegative integral polynomial exponent. -/
@[expose] public def weight (α : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ r

public theorem weight_pos (α : ℝ) (r : ℕ) (x : ℝ) : 0 < weight α r x := by
  unfold weight
  positivity

public theorem continuous_weight (α : ℝ) (r : ℕ) : Continuous (weight α r) := by
  unfold weight
  fun_prop

/-- Weighted Lebesgue measure on the log line. -/
@[expose] public def μ (α : ℝ) (r : ℕ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (weight α r x))

public instance (α : ℝ) (r : ℕ) : IsFiniteMeasureOnCompacts (μ α r) where
  lt_top_of_isCompact K hK := by
    rw [μ, withDensity_apply _ hK.measurableSet,
      ← ofReal_integral_eq_lintegral_ofReal
        ((continuous_weight α r).continuousOn.integrableOn_compact hK)
        (ae_of_all _ fun x => (weight_pos α r x).le)]
    exact ENNReal.ofReal_lt_top

/-- Complex weighted log `L²`. -/
public abbrev H (α : ℝ) (r : ℕ) := Lp ℂ 2 (μ α r)

/-- The half-weighted rational real profile on the log line. -/
@[expose] public def profile (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (2 * Real.exp (x / 2) : ℝ) * f (Real.exp x)

private theorem continuous_profile (f : 𝓢(ℝ, ℂ)) : Continuous (profile f) :=
  (Complex.continuous_ofReal.comp (by fun_prop)).mul (f.continuous.comp Real.continuous_exp)

/-- On the negative half-line use boundedness. On the positive half-line,
use boundedness of `t * ‖f t‖` and take `t = exp x`. -/
private theorem profile_decay (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, ∀ x : ℝ, ‖profile f x‖ ≤ C * Real.exp (-(1 / 2) * |x|) := by
  let A := max (SchwartzMap.seminorm ℝ 0 0 f) (SchwartzMap.seminorm ℝ 1 0 f)
  refine ⟨2 * A, fun x => ?_⟩
  rw [profile, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rcases le_or_gt x 0 with hx | hx
  · have he : Real.exp (x / 2) = Real.exp (-(1 / 2) * |x|) := by
      rw [abs_of_nonpos hx]
      congr 1
      ring
    calc
      _ ≤ (2 * Real.exp (x / 2)) * A := by
        gcongr
        exact (SchwartzMap.norm_le_seminorm ℝ f _).trans (le_max_left ..)
      _ = _ := by rw [he]; ring
  · have hF : Real.exp x * ‖f (Real.exp x)‖ ≤ A := by
      simpa only [pow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using
        (SchwartzMap.norm_pow_mul_le_seminorm ℝ f 1 (Real.exp x)).trans (le_max_right ..)
    have hstep := mul_le_mul_of_nonneg_left hF (Real.exp_pos (-x)).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hstep
    have he : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(1 / 2) * |x|) := by
      rw [← Real.exp_add, abs_of_pos hx]
      congr 1
      ring
    calc
      _ ≤ (2 * Real.exp (x / 2)) * (Real.exp (-x) * A) := by gcongr
      _ = (2 * A) * (Real.exp (x / 2) * Real.exp (-x)) := by ring
      _ = _ := by rw [he]

private theorem polynomial_le_exp (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, (1 + x ^ 2) ^ r ≤ K * Real.exp (ε * |x|) := by
  let n := 2 * r
  refine ⟨((n.factorial : ℝ) / ε ^ n) * Real.exp ε, by positivity, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp (x := ε * (1 + |x|)) (by positivity) n
  rw [mul_pow, mul_add, mul_one, Real.exp_add] at h
  have hfact : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h' := (div_le_iff₀ hfact).mp h
  have h'' := (le_div_iff₀ (pow_pos hε n)).mpr (by simpa only [mul_comm (ε ^ n)] using h')
  calc
    (1 + x ^ 2) ^ r ≤ ((1 + |x|) ^ 2) ^ r := by
      gcongr
      rw [add_sq, sq_abs]
      nlinarith [abs_nonneg x]
    _ = (1 + |x|) ^ n := by rw [← pow_mul]
    _ ≤ Real.exp ε * Real.exp (ε * |x|) * (n.factorial : ℝ) / ε ^ n := h''
    _ = _ := by ring

private theorem integrable_exp_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => Real.exp (-ε * |x|)) := by
  have hlo := (integrableOn_exp_mul_Iic hε 0).congr_fun
    (g := fun x : ℝ => Real.exp (-ε * |x|))
    (fun x hx => by simp only [abs_of_nonpos (show x ≤ 0 from hx), neg_mul_neg]) measurableSet_Iic
  have hhi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).congr_fun
    (g := fun x : ℝ => Real.exp (-ε * |x|))
    (fun x hx => by simp only [abs_of_pos (show 0 < x from hx)]) measurableSet_Ioi
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hlo.union hhi

/-- Every Schwartz profile is in weighted `L²` when `α < 1/2`. The
estimate does not require the four local band constraints. -/
public theorem memLp_profile (α : ℝ) (r : ℕ) (hα : α < 1 / 2) (f : 𝓢(ℝ, ℂ)) :
    MemLp (profile f) 2 (μ α r) := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_profile f).aestronglyMeasurable).2
  rw [μ, integrable_withDensity_iff_integrable_smul'
    ((continuous_weight α r).measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (weight_pos α r _).le, smul_eq_mul]
  let ε : ℝ := 1 / 2 - α
  have hε : 0 < ε := sub_pos.mpr hα
  obtain ⟨C, hC⟩ := profile_decay f
  obtain ⟨K, hK, hpoly⟩ := polynomial_le_exp r hε
  refine ((integrable_exp_abs hε).const_mul (C ^ 2 * K)).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((continuous_weight α r).mul ((continuous_profile f).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (weight_pos α r x).le (sq_nonneg _)), weight]
    calc
      _ ≤ (Real.exp (2 * α * |x|) * (K * Real.exp (ε * |x|))) *
          (C * Real.exp (-(1 / 2) * |x|)) ^ 2 := by
        gcongr
        · exact hpoly x
        · exact hC x
      _ = (C ^ 2 * K) * (Real.exp (2 * α * |x|) * Real.exp (ε * |x|) *
          (Real.exp (-(1 / 2) * |x|)) ^ 2) := by ring
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 2
        dsimp [ε]
        ring

/-- The four constraints defining a local band witness. Mathlib's real
Fourier transform uses the additive `2π` convention. -/
@[expose] public def Admissible (Y : ℝ) (f : 𝓢(ℝ, ℂ)) : Prop :=
  Function.Even f ∧ Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Icc (-Y) Y ∧
    f 0 = 0 ∧ (∫ t, f t) = 0

/-- The concrete profiles that have weighted `L²` representatives. -/
@[expose] public def generators (α : ℝ) (r : ℕ) (Y : ℝ) : Set (H α r) :=
  {v | ∃ f : 𝓢(ℝ, ℂ), Admissible Y f ∧ (v : ℝ → ℂ) =ᵐ[μ α r] profile f}

/-- In the admissible weight range every local band witness gives a generator. -/
public theorem toLp_profile_mem_generators (α : ℝ) (r : ℕ) (hα : α < 1 / 2) {Y : ℝ}
    {f : 𝓢(ℝ, ℂ)} (hf : Admissible Y f) :
    (memLp_profile α r hα f).toLp (profile f) ∈ generators α r Y :=
  ⟨f, hf, (memLp_profile α r hα f).coeFn_toLp⟩

/-- The closed span of the local band profiles in weighted log `L²`. -/
@[expose] public def level (α : ℝ) (r : ℕ) (Y : ℝ) : ClosedSubmodule ℂ (H α r) :=
  (Submodule.span ℂ (generators α r Y)).closure

/-- Orthogonal projection onto the local real level. -/
@[expose] public def Q (α : ℝ) (r : ℕ) (Y : ℝ) : H α r →L[ℂ] H α r :=
  (level α r Y).toSubmodule.starProjection

public theorem range_Q (α : ℝ) (r : ℕ) (Y : ℝ) :
    (Q α r Y).range = (level α r Y).toSubmodule :=
  Submodule.range_starProjection _

/-- The pointwise representative of the reciprocal-weight window. -/
@[expose] public def window (α : ℝ) (r : ℕ) (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (fun y => ((weight α r y)⁻¹ : ℝ))

private theorem memLp_window (α : ℝ) (r : ℕ) (a b : ℝ) :
    MemLp (window α r a b) 2 (μ α r) := by
  let g : ℝ → ℂ := fun y => ((weight α r y)⁻¹ : ℝ)
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp ((continuous_weight α r).inv₀ fun y => (weight_pos α r y).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hg.norm.continuousOn
    (K := Icc a b)
  have : IsFiniteMeasure ((μ α r).restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top (μ := μ α r)).ne
  apply (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2
  apply MemLp.of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact hC (mem_image_of_mem _ hy)

/-- The reciprocal-weight interval window as a vector of the weighted `L²`. -/
public def q (α : ℝ) (r : ℕ) (a b : ℝ) : H α r := (memLp_window α r a b).toLp _

/-- The `L²` coercion agrees almost everywhere for the weighted measure with
`χ_[a,b] / w`, interpreted as a complex-valued function. -/
public theorem coe_q_ae (α : ℝ) (r : ℕ) (a b : ℝ) :
    (q α r a b : ℝ → ℂ) =ᵐ[μ α r] window α r a b :=
  (memLp_window α r a b).coeFn_toLp

private theorem weight_smul_mul_conj_window (α : ℝ) (r : ℕ) (a b : ℝ) (F : ℝ → ℂ) :
    (fun y => weight α r y • (F y * star (window α r a b y))) =
      (Icc a b).indicator F := by
  funext y
  by_cases hy : y ∈ Icc a b
  · rw [window, indicator_of_mem hy, indicator_of_mem hy, Complex.star_def,
      Complex.conj_ofReal, Complex.real_smul, mul_left_comm, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (weight_pos α r y).ne', Complex.ofReal_one, mul_one]
  · simp [window, hy]

/-- Weighted integrability of the window pairing requires only Lebesgue
integrability on the interval, not global integrability or an `L²` input. -/
public theorem integrable_mul_conj_q_iff (α : ℝ) (r : ℕ) (a b : ℝ) {F : ℝ → ℂ} :
    Integrable (fun y => F y * star (q α r a b y)) (μ α r) ↔
      IntegrableOn F (Icc a b) := by
  have h : (fun y => F y * star (q α r a b y)) =ᵐ[μ α r]
      (fun y => F y * star (window α r a b y)) :=
    (coe_q_ae α r a b).mono fun y hy => by simp only [hy]
  rw [integrable_congr h, μ, integrable_withDensity_iff_integrable_smul'
    ((continuous_weight α r).measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (weight_pos α r _).le]
  rw [weight_smul_mul_conj_window, integrable_indicator_iff measurableSet_Icc]

/-- Pairing with `q` cancels the weight and gives the Lebesgue integral over
`[a,b]`. The Bochner integral equality is unconditional; for integrability,
see `integrable_mul_conj_q_iff`. -/
public theorem integral_mul_conj_q (α : ℝ) (r : ℕ) (a b : ℝ) {F : ℝ → ℂ} :
    (∫ y, F y * star (q α r a b y) ∂μ α r) = ∫ y in Icc a b, F y := by
  calc
    _ = ∫ y, F y * star (window α r a b y) ∂μ α r :=
      integral_congr_ae ((coe_q_ae α r a b).mono fun y hy => by simp only [hy])
    _ = ∫ y, (Icc a b).indicator F y := by
      rw [μ, integral_withDensity_eq_integral_toReal_smul
        ((continuous_weight α r).measurable.ennreal_ofReal)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      simp_rw [ENNReal.toReal_ofReal (weight_pos α r _).le, weight_smul_mul_conj_window]
    _ = _ := integral_indicator measurableSet_Icc

end

end Masullo.OperatorTrace.RealLogLevel
