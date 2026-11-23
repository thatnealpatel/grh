module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Weighted Schur estimate for finitely many symmetric real shifts

The row bound controls the quadratic form on every zero-extended complex `L²` input,
not just smooth inputs or the trial weight. The estimate uses the two correlations per
symmetric pair with no additional factor of two. The support can be any measurable set
(in particular an interval), and the weight is bounded above and away from zero there.

Source: `bdd74f2:.godel/adhoc/prime-translation-norm.md`, lines 28–38.
Applications: `85842a8:.godel/alice/prime-conductor-window.md`, lines 54–62;
`fd044e1:.godel/alice/critical-conductor-window.md`, lines 60–70.
Owning check session: `01a208be-3e66-7cc4-8f5d-223682424036`.
-/

open MeasureTheory
open scoped ENNReal

namespace Masullo

private theorem weighted_two_mul_le (p q v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    2 * (p * q) ≤ p ^ 2 / v * w + q ^ 2 / w * v := by
  calc
    _ ≤ (p ^ 2 * w ^ 2 + q ^ 2 * v ^ 2) / (v * w) := by
      apply (le_div_iff₀ (mul_pos hv hw)).2
      nlinarith only [sq_nonneg (p * w - q * v)]
    _ = _ := by field_simp

/-- A Schur row bound on `I` bounds the norm correlations of every complex `L²`
input vanishing almost everywhere off `I`. The factor `2` accounts for the two shifts
in each symmetric pair; taking absolute values also bounds pairings with twists of
modulus at most one. -/
public theorem finiteShiftSchur {ι : Type*} (S : Finset ι) (s a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {I : Set ℝ} (hI : MeasurableSet I)
    {w : ℝ → ℝ} (hw : Measurable w) (hwzero : ∀ x ∉ I, w x = 0)
    {b B C : ℝ} (hb : 0 < b) (hlower : ∀ x ∈ I, b ≤ w x) (hupper : ∀ x ∈ I, w x ≤ B)
    (hrow : ∀ᵐ x ∂volume.restrict I,
      ∑ i ∈ S, a i * (w (x + s i) + w (x - s i)) ≤ C * w x)
    {u : ℝ → ℂ} (hu : MemLp u 2 volume) (huzero : ∀ᵐ x ∂volume, x ∉ I → u x = 0) :
    2 * (∑ i ∈ S, a i * ∫ x : ℝ, ‖u x‖ * ‖u (x + s i)‖) ≤
      C * ∫ x : ℝ, ‖u x‖ ^ 2 := by
  have hsq : Integrable (fun x ↦ ‖u x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      hu.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have hwpos (x : ℝ) (hx : x ∈ I) : 0 < w x := hb.trans_le (hlower x hx)
  have hwn (x : ℝ) : 0 ≤ w x := by
    by_cases hx : x ∈ I
    · exact (hwpos x hx).le
    · rw [hwzero x hx]
  have hwb (x : ℝ) : w x ≤ max B 0 := by
    by_cases hx : x ∈ I
    · exact (hupper x hx).trans (le_max_left B 0)
    · rw [hwzero x hx]
      exact le_max_right B 0
  -- Real division by zero makes this quotient zero off the support of the weight.
  let f (x : ℝ) : ℝ := ‖u x‖ ^ 2 / w x
  have hfzero (x : ℝ) (hx : x ∉ I) : f x = 0 := by simp [f, hwzero x hx]
  have hfn (x : ℝ) : 0 ≤ f x := div_nonneg (sq_nonneg _) (hwn x)
  have hf : Integrable f := by
    refine (hsq.div_const b).mono'
      (hsq.aestronglyMeasurable.aemeasurable.div hw.aemeasurable).aestronglyMeasurable ?_
    refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_of_nonneg (hfn x)]
    by_cases hx : x ∈ I
    · exact div_le_div_of_nonneg_left (sq_nonneg _) hb (hlower x hx)
    · rw [hfzero x hx]
      exact div_nonneg (sq_nonneg _) hb.le
  let g (t x : ℝ) : ℝ := f x * w (x + t)
  have hgn (t x : ℝ) : 0 ≤ g t x := mul_nonneg (hfn x) (hwn _)
  have hg (t : ℝ) : Integrable (g t) := by
    refine (hf.mul_const (max B 0)).mono'
      (hf.aestronglyMeasurable.mul
        (hw.comp (measurable_id.add_const t)).aestronglyMeasurable) ?_
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (hgn t x)]
      exact mul_le_mul_of_nonneg_left (hwb _) (hfn x)
  have hpair (t : ℝ) : (∫ x : ℝ, 2 * (‖u x‖ * ‖u (x + t)‖)) ≤
      ∫ x : ℝ, g t x + g (-t) x := by
    have ht := measurePreserving_add_right (volume : Measure ℝ) t
    have hshifted : Integrable (fun x ↦ g (-t) (x + t)) :=
      (ht.integrable_comp (hg (-t)).aestronglyMeasurable).2 (hg (-t))
    have hmajor : Integrable (fun x ↦ g t x + g (-t) (x + t)) := (hg t).add hshifted
    have hle : ∀ᵐ x ∂volume,
        2 * (‖u x‖ * ‖u (x + t)‖) ≤ g t x + g (-t) (x + t) := by
      -- Transport the support condition to the shifted argument before splitting cases.
      filter_upwards [huzero, ht.quasiMeasurePreserving.tendsto_ae.eventually huzero] with x hx hxt
      change x + t ∉ I → u (x + t) = 0 at hxt
      have hnonneg := add_nonneg (hgn t x) (hgn (-t) (x + t))
      by_cases hxi : x ∈ I
      · by_cases hxti : x + t ∈ I
        · simpa only [g, f, add_assoc, add_neg_cancel, add_zero] using
            weighted_two_mul_le ‖u x‖ ‖u (x + t)‖ (w x) (w (x + t))
              (hwpos x hxi) (hwpos (x + t) hxti)
        · simpa only [hxt hxti, norm_zero, mul_zero] using hnonneg
      · simpa only [hx hxi, norm_zero, zero_mul, mul_zero] using hnonneg
    have hleft : Integrable (fun x : ℝ ↦ 2 * (‖u x‖ * ‖u (x + t)‖)) := by
      have hu' := hu.aestronglyMeasurable.comp_quasiMeasurePreserving ht.quasiMeasurePreserving
      refine hmajor.mono'
        (aestronglyMeasurable_const.mul (hu.aestronglyMeasurable.norm.mul hu'.norm)) ?_
      filter_upwards [hle] with x hx
      rwa [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ∫ x : ℝ, g t x + g (-t) (x + t) := integral_mono_ae hleft hmajor hle
      _ = _ := by
        -- With y = x + t, the second term is f y * w (y - t).
        rw [integral_add (hg t) hshifted, integral_add_right_eq_self (μ := volume) (g (-t)) t,
          integral_add (hg t) (hg (-t))]
  have hterm (i : ι) : Integrable (fun x ↦ a i * (g (s i) x + g (-s i) x)) :=
    ((hg (s i)).add (hg (-s i))).const_mul _
  have hbound : ∀ᵐ x ∂volume, ∑ i ∈ S, a i * (g (s i) x + g (-s i) x) ≤ C * ‖u x‖ ^ 2 := by
    filter_upwards [(ae_restrict_iff' hI).1 hrow, huzero] with x hrowx hux
    calc
      _ = f x * (∑ i ∈ S, a i * (w (x + s i) + w (x - s i))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        dsimp only [g]
        rw [sub_eq_add_neg]
        ring
      _ ≤ C * ‖u x‖ ^ 2 := by
        by_cases hx : x ∈ I
        · have hfw : f x * w x = ‖u x‖ ^ 2 := div_mul_cancel₀ _ (hwpos x hx).ne'
          calc
            _ ≤ f x * (C * w x) := mul_le_mul_of_nonneg_left (hrowx hx) (hfn x)
            _ = C * (f x * w x) := by ring
            _ = _ := by rw [hfw]
        · simp [hfzero x hx, hux hx]
  calc
    _ = ∑ i ∈ S, a i * (∫ x : ℝ, 2 * (‖u x‖ * ‖u (x + s i)‖)) := by
      rw [Finset.mul_sum]
      simp_rw [integral_const_mul, mul_left_comm (2 : ℝ)]
    _ ≤ ∑ i ∈ S, a i * (∫ x : ℝ, g (s i) x + g (-s i) x) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hpair (s i)) (ha i hi)
    _ = ∫ x : ℝ, ∑ i ∈ S, a i * (g (s i) x + g (-s i) x) := by
      simp only [integral_finsetSum S (fun i _ ↦ hterm i), integral_const_mul]
    _ ≤ ∫ x : ℝ, C * ‖u x‖ ^ 2 :=
      integral_mono_ae (integrable_finsetSum S fun i _ ↦ hterm i) (hsq.const_mul C) hbound
    _ = _ := integral_const_mul C _

end Masullo
