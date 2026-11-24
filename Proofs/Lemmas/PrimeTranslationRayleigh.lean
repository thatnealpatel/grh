module

public import Lemmas.PrimeTranslationProfileApproximation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The prime-translation Rayleigh quotient on the endpoint weight

Source: `bdd74f2a27ca:.godel/adhoc/prime-translation-norm.md`, lines 28–40,
§2 (the sharp endpoint comparison tested on the sum of the profiles).
Owning check session: `01a20db3-6987-747d-9d8d-903a502adedd`.

Scope: the window Rayleigh quotient of the actual untwisted, strict-cutoff
prime-translation sum on the sum of the two zero-extended profiles. This is
a test-vector result, not a statement about the whole-space operator norm,
signed characters, or compact corrections.
-/

open Filter MeasureTheory
open Real (exp log)
open scoped Topology

namespace Masullo

local notation "fₚ" => primeTranslationProfile
local notation "gₚ" => primeTranslationReflectedProfile

private noncomputable def weight (D x : ℝ) : ℝ := fₚ D x + gₚ D x

private theorem weight_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    weight D x = exp (-x / 2) + exp (-(D - x) / 2) := by
  have hy : D - x ∈ Set.Icc 0 D := ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩
  unfold weight primeTranslationReflectedProfile primeTranslationProfile
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]

private theorem weight_pos {D x : ℝ} (hx : x ∈ Set.Icc 0 D) : 0 < weight D x := by
  rw [weight_on hx]
  positivity

private theorem weight_continuousOn (D : ℝ) : ContinuousOn (weight D) (Set.Icc 0 D) :=
  (by fun_prop : Continuous (fun x : ℝ ↦ exp (-x / 2) + exp (-(D - x) / 2))).continuousOn.congr
    (fun _ hx ↦ weight_on hx)

private theorem weight_measurable (D : ℝ) : Measurable (weight D) := by
  have hf : Measurable (fₚ D) :=
    (by fun_prop : Measurable (fun x : ℝ ↦ exp (-x / 2))).indicator measurableSet_Icc
  exact hf.add (hf.comp (by fun_prop : Measurable (fun x : ℝ ↦ D - x)))

private theorem apply_measurable (D : ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (primeTranslationApply D u) := by
  unfold primeTranslationApply
  apply Finset.measurable_sum
  intro n _
  exact measurable_const.mul
    ((hu.comp (by fun_prop : Measurable (fun x : ℝ ↦ x + log n))).add
      (hu.comp (by fun_prop : Measurable (fun x : ℝ ↦ x - log n))))

-- Reflection swaps the two shifts term by term without changing the cutoff.
private theorem apply_weight (D x : ℝ) :
    primeTranslationApply D (weight D) x =
      primeTranslationApply D (fₚ D) x + primeTranslationApply D (fₚ D) (D - x) := by
  unfold primeTranslationApply
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [weight, primeTranslationReflectedProfile]
  rw [show D - (x + log n) = D - x - log n by ring,
    show D - (x - log n) = D - x + log n by ring]
  ring

private theorem weight_approximation_on {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ x ∈ Set.Ioo 0 D,
      |primeTranslationApply D (weight D) x - exp (D / 2) * weight D x| ≤
        η * exp (D / 2) * weight D x := by
  filter_upwards [primeTranslationProfileApproximationOn (half_pos hη)] with D hD
  intro x hx
  have hy : D - x ∈ Set.Ioo 0 D := ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩
  have hflip : gₚ D (D - x) = fₚ D x := by
    change fₚ D (D - (D - x)) = fₚ D x
    rw [show D - (D - x) = x by ring]
  have hr := hD (D - x) hy
  rw [hflip, show fₚ D (D - x) = gₚ D x from rfl, add_comm (gₚ D x) (fₚ D x)] at hr
  calc
    _ = |(primeTranslationApply D (fₚ D) x - exp (D / 2) * gₚ D x) +
          (primeTranslationApply D (fₚ D) (D - x) - exp (D / 2) * fₚ D x)| := by
      rw [apply_weight, weight]
      congr 1
      ring
    _ ≤ |primeTranslationApply D (fₚ D) x - exp (D / 2) * gₚ D x| +
          |primeTranslationApply D (fₚ D) (D - x) - exp (D / 2) * fₚ D x| :=
      abs_add_le _ _
    _ ≤ _ := (add_le_add (hD x hx) hr).trans_eq (by unfold weight; ring)

private theorem weight_sq_integral_pos {D : ℝ} (hD : 0 < D) :
    0 < ∫ x in Set.Icc 0 D, weight D x ^ 2 := by
  have hi := ((weight_continuousOn D).pow 2).integrableOn_Icc (μ := volume)
  refine (integral_pos_iff_support_of_nonneg_ae (.of_forall fun x ↦ sq_nonneg (weight D x)) hi).2 ?_
  have hs : Set.Icc 0 D ⊆ Function.support (fun x ↦ weight D x ^ 2) :=
    fun _ hx ↦ pow_ne_zero 2 (weight_pos hx).ne'
  calc
    0 < volume (Set.Icc 0 D) := by
      rw [Real.volume_Icc, sub_zero]
      exact ENNReal.ofReal_pos.mpr hD
    _ = volume.restrict (Set.Icc 0 D) (Set.Icc 0 D) := by
      rw [Measure.restrict_apply measurableSet_Icc, Set.inter_self]
    _ ≤ volume.restrict (Set.Icc 0 D) (Function.support (fun x ↦ weight D x ^ 2)) := measure_mono hs

/-- The window Rayleigh quotient on the sum of the two zero-extended endpoint
profiles, normalized by `exp (D / 2)`, tends to one as real `D → +∞`. -/
public theorem primeTranslationRayleigh :
    Tendsto (fun D : ℝ ↦
      let w : ℝ → ℝ := fun x ↦ primeTranslationProfile D x + primeTranslationReflectedProfile D x
      (∫ x in Set.Icc 0 D, primeTranslationApply D w x * w x) /
        (exp (D / 2) * ∫ x in Set.Icc 0 D, w x ^ 2)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [weight_approximation_on (half_pos hε), eventually_gt_atTop (0 : ℝ)] with D hT hD
  let w := weight D
  let μ := volume.restrict (Set.Icc 0 D)
  let n : ℝ → ℝ := fun x ↦ primeTranslationApply D w x * w x
  let b : ℝ → ℝ := fun x ↦ exp (D / 2) * w x ^ 2
  let e : ℝ → ℝ := fun x ↦ n x - b x
  have hb : Integrable b μ :=
    (continuousOn_const.mul ((weight_continuousOn D).pow 2)).integrableOn_Icc
  -- The cutoff is strict; the open-window estimate is enough for this integral.
  have ho : ∀ᵐ x ∂μ, x ∈ Set.Ioo 0 D := by
    dsimp only [μ]
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hpoint : ∀ᵐ x ∂μ, |e x| ≤ (ε / 2) * b x := by
    filter_upwards [ho] with x hx
    have hw₀ : 0 ≤ w x := (weight_pos ⟨hx.1.le, hx.2.le⟩).le
    have he : e x = (primeTranslationApply D w x - exp (D / 2) * w x) * w x := by
      dsimp only [e, n, b]
      ring
    rw [he, abs_mul, abs_of_nonneg hw₀]
    calc
      _ ≤ (ε / 2 * exp (D / 2) * w x) * w x := mul_le_mul_of_nonneg_right (hT x hx) hw₀
      _ = _ := by dsimp only [b]; ring
  have hmajor := hb.const_mul (ε / 2)
  have hw := weight_measurable D
  have he_meas : Measurable e :=
    ((apply_measurable D hw).mul hw).sub (measurable_const.mul (hw.pow_const (2 : ℕ)))
  have he : Integrable e μ :=
    hmajor.mono' he_meas.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hpoint)
  have hn : Integrable n μ := (he.add hb).congr (.of_forall fun x ↦
    show n x - b x + b x = n x from sub_add_cancel _ _)
  have herr : |(∫ x, n x ∂μ) - ∫ x, b x ∂μ| ≤ (ε / 2) * ∫ x, b x ∂μ := by
    rw [← integral_sub hn hb, ← integral_const_mul]
    exact abs_integral_le_integral_abs.trans (integral_mono_ae he.abs hmajor hpoint)
  have hB : (∫ x, b x ∂μ) = exp (D / 2) * ∫ x, w x ^ 2 ∂μ := integral_const_mul _ _
  have hBpos : 0 < ∫ x, b x ∂μ := by
    rw [hB]
    exact mul_pos (Real.exp_pos _) (weight_sq_integral_pos hD)
  change dist ((∫ x, n x ∂μ) / (exp (D / 2) * ∫ x, w x ^ 2 ∂μ)) 1 < ε
  rw [Real.dist_eq, ← hB]
  calc
    _ = |((∫ x, n x ∂μ) - ∫ x, b x ∂μ) / (∫ x, b x ∂μ)| := by
      rw [sub_div, div_self hBpos.ne']
    _ ≤ ε / 2 := by
      rw [abs_div, abs_of_pos hBpos]
      exact (div_le_iff₀ hBpos).mpr herr
    _ < ε := half_lt_self hε

end Masullo
