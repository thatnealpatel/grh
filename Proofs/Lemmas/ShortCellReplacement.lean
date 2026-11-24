module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Short prime cells: replacement on spectral measures

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:39–53`, specifically
paragraph 43, which supplies the replacement error before applying the crossing bound.
Owning check session: `01a20f35-88fa-72a0-aedd-8c10c7068d1c`.

This is the measure-level estimate, not an operator-norm estimate or a Plancherel
identification of the spectral measure of an `L²` input. We use angular frequency
(`exp(i t ξ)`, with no `2π`) and Lebesgue measure on the original prime variable.
-/

open MeasureTheory Set

namespace ShortCellReplacement

public section

/-- The angular-frequency phase with the forward sign convention. -/
@[expose] noncomputable def phase (t ξ : ℝ) : ℂ :=
  Complex.exp (↑(t * ξ) * Complex.I)

/-- The correlation transform of a positive spectral measure on the frequency line. -/
@[expose] noncomputable def spectralTransform (μ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ ξ, phase t ξ ∂μ

private theorem norm_phase (t ξ : ℝ) : ‖phase t ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (t * ξ)

private theorem phase_continuous_freq (t : ℝ) : Continuous (phase t) := by
  unfold phase
  fun_prop

private theorem phase_continuous_shift (ξ : ℝ) : Continuous (fun t ↦ phase t ξ) := by
  unfold phase
  fun_prop

private theorem phase_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (phase t) μ :=
  (integrable_const (1 : ℝ)).mono' (phase_continuous_freq t).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ (norm_phase t ξ).le)

private theorem continuous_spectralTransform (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (spectralTransform μ) :=
  continuous_of_dominated
    (fun t ↦ (phase_continuous_freq t).aestronglyMeasurable)
    (fun t ↦ ae_of_all _ fun ξ ↦ (norm_phase t ξ).le)
    (integrable_const (1 : ℝ)) (ae_of_all _ phase_continuous_shift)

/-- Unit spectral mass bounds the correlation transform at every shift. -/
theorem norm_spectralTransform_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖spectralTransform μ t‖ ≤ 1 := by
  unfold spectralTransform
  simpa [Measure.real] using
    (norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (ae_of_all _ fun ξ ↦ (norm_phase t ξ).le))

private theorem norm_phase_sub_le_two (t s ξ : ℝ) : ‖phase t ξ - phase s ξ‖ ≤ 2 := by
  calc
    _ ≤ ‖phase t ξ‖ + ‖phase s ξ‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_phase, norm_phase]; norm_num

private theorem norm_phase_sub_le (t s ξ : ℝ) :
    ‖phase t ξ - phase s ξ‖ ≤ 2 * |t - s| * |ξ| := by
  let z : ℂ := ↑((t - s) * ξ) * Complex.I
  have hz : ‖z‖ = |t - s| * |ξ| := by
    change ‖(↑((t - s) * ξ) : ℂ) * Complex.I‖ = _
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    ‖phase t ξ - phase s ξ‖ ≤ 2 * ‖z‖ := by
      by_cases h : ‖z‖ ≤ 1
      · have he : phase t ξ = Complex.exp z * phase s ξ := by
          rw [phase, phase, ← Complex.exp_add]
          congr 1
          push_cast [z]
          ring
        rw [he, ← sub_one_mul, norm_mul, norm_phase, mul_one]
        exact Complex.norm_exp_sub_one_le h
      · exact (norm_phase_sub_le_two t s ξ).trans (by linarith)
    _ = 2 * |t - s| * |ξ| := by rw [hz, mul_assoc]

/-- Split the actual positive measure at the closed frequency band. The tail
contributes at most twice its mass; no moment assumption on the tail is needed. -/
theorem norm_spectralTransform_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T η : ℝ} (hT : 0 ≤ T) (htail : μ.real (Icc (-T) T)ᶜ ≤ η) (t s : ℝ) :
    ‖spectralTransform μ t - spectralTransform μ s‖ ≤ 2 * T * |t - s| + 2 * η := by
  let A : Set ℝ := Icc (-T) T
  let g : ℝ → ℂ := fun ξ ↦ phase t ξ - phase s ξ
  have hA : MeasurableSet A := measurableSet_Icc
  have hi : Integrable g μ := (phase_integrable μ t).sub (phase_integrable μ s)
  have hmain : ‖∫ ξ in A, g ξ ∂μ‖ ≤ 2 * T * |t - s| := by
    have hb : ∀ᵐ ξ ∂μ.restrict A, ‖g ξ‖ ≤ 2 * T * |t - s| := by
      filter_upwards [ae_restrict_mem (μ := μ) hA] with ξ hξ
      have hξ' : |ξ| ≤ T := abs_le.mpr hξ
      calc
        ‖g ξ‖ ≤ 2 * |t - s| * |ξ| := norm_phase_sub_le t s ξ
        _ ≤ 2 * |t - s| * T := mul_le_mul_of_nonneg_left hξ' (by positivity)
        _ = 2 * T * |t - s| := by ring
    have hm : (μ.restrict A).real univ ≤ 1 := by
      rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
      simpa [Measure.real] using (measureReal_mono (μ := μ) (subset_univ A))
    calc
      _ ≤ (2 * T * |t - s|) * (μ.restrict A).real univ :=
        norm_integral_le_of_norm_le_const hb
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hm
  have hrest : ‖∫ ξ in Aᶜ, g ξ ∂μ‖ ≤ 2 * η := by
    calc
      _ ≤ 2 * (μ.restrict Aᶜ).real univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun ξ ↦ norm_phase_sub_le_two t s ξ)
      _ ≤ _ := by
        rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
        exact mul_le_mul_of_nonneg_left htail (by norm_num)
  rw [spectralTransform, spectralTransform,
    ← integral_sub (phase_integrable μ t) (phase_integrable μ s), ← integral_add_compl hA hi]
  exact (norm_add_le _ _).trans (add_le_add hmain hrest)

private theorem abs_log_sub_le {L x y : ℝ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / L := by
  have ordered {a b : ℝ} (ha : L ≤ a) (hab : a ≤ b) :
      |Real.log b - Real.log a| ≤ |b - a| / L := by
    have ha₀ := hL.trans_le ha
    have hb₀ := ha₀.trans_le hab
    have hlog := Real.strictMonoOn_log.monotoneOn ha₀ hb₀ hab
    rw [abs_of_nonneg (sub_nonneg.mpr hlog), abs_of_nonneg (sub_nonneg.mpr hab),
      ← Real.log_div hb₀.ne' ha₀.ne']
    calc
      Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb₀ ha₀)
      _ = (b - a) / a := by rw [sub_div, div_self ha₀.ne']
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hL ha
  rcases le_total x y with h | h
  · rw [abs_sub_comm (Real.log x), abs_sub_comm x]
    exact ordered hx h
  · exact ordered hy h

private theorem abs_inv_sqrt_sub_le {L x y : ℝ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ (|x - y| / L) / Real.sqrt L := by
  have ordered {a b : ℝ} (ha : L ≤ a) (hab : a ≤ b) :
      |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| ≤ (|b - a| / L) / Real.sqrt L := by
    have ha₀ := hL.trans_le ha
    have hb₀ := ha₀.trans_le hab
    have hr := Real.sqrt_pos.mpr ha₀
    have hs := Real.sqrt_pos.mpr hb₀
    have hsa := Real.sqrt_le_sqrt ha
    have hab' := Real.sqrt_le_sqrt hab
    have he : (Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹ =
        (b - a) / (Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b)) := by
      apply (eq_div_iff (by positivity)).2
      calc
        _ = (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b) := by
          field_simp [hr.ne', hs.ne']
        _ = (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hb₀.le, Real.sq_sqrt ha₀.le]
    have hprod : L ≤ Real.sqrt a * Real.sqrt b := by
      calc
        L = Real.sqrt L * Real.sqrt L := (Real.mul_self_sqrt hL.le).symm
        _ ≤ _ := mul_le_mul hsa (hsa.trans hab') (Real.sqrt_nonneg _) hr.le
    have hden : L * Real.sqrt L ≤ Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) :=
      mul_le_mul hprod (hsa.trans (le_add_of_nonneg_right hs.le)) (Real.sqrt_nonneg _)
        (mul_nonneg hr.le hs.le)
    rw [abs_of_nonneg (sub_nonneg.mpr ((inv_le_inv₀ hs hr).2 hab')),
      abs_of_nonneg (sub_nonneg.mpr hab), he, div_div]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (by positivity) hden
  rcases le_total x y with h | h
  · rw [abs_sub_comm x]
    exact ordered hx h
  · rw [abs_sub_comm ((Real.sqrt x)⁻¹)]
    exact ordered hy h

/-- The sampled or integrated factor, including the reciprocal-square-root weight. -/
@[expose] noncomputable def weightedTransform (μ : Measure ℝ) (σ v : ℝ) : ℂ :=
  ((Real.sqrt v : ℂ)⁻¹) * spectralTransform μ (σ * Real.log v)

/-- Uniform cell oscillation budget for either direction. -/
@[expose] noncomputable def oscillationBudget (L h T η : ℝ) : ℝ :=
  (2 * T * (h / L) + 2 * η + h / L) / Real.sqrt L

private theorem weightedTransform_intervalIntegrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (σ : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (weightedTransform μ σ) volume l r := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlr]
  have hlog : ContinuousOn Real.log (Icc l r) :=
    Real.continuousOn_log.mono fun x hx ↦ (hl.trans_le hx.1).ne'
  unfold weightedTransform
  refine (((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn).inv₀ ?_).mul ?_
  · exact fun v hv ↦ Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hl.trans_le hv.1)).ne'
  · exact (continuous_spectralTransform μ).comp_continuousOn (continuousOn_const.mul hlog)

private theorem norm_weightedTransform_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L h T η σ x y : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (htail : μ.real (Icc (-T) T)ᶜ ≤ η)
    (hσ : |σ| ≤ 1) (hx : L ≤ x) (hy : L ≤ y) (hxy : |x - y| ≤ h) :
    ‖weightedTransform μ σ x - weightedTransform μ σ y‖ ≤ oscillationBudget L h T η := by
  have hlog : |σ * Real.log x - σ * Real.log y| ≤ h / L := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ 1 * |Real.log x - Real.log y| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact (abs_log_sub_le hL hx hy).trans (div_le_div_of_nonneg_right hxy hL.le)
  have hC := (norm_spectralTransform_sub_le μ hT htail (σ * Real.log x) (σ * Real.log y)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * T)) le_rfl)
  have hCx := norm_spectralTransform_le_one μ (σ * Real.log y)
  have hroot : ‖(Real.sqrt x : ℂ)⁻¹‖ ≤ (Real.sqrt L)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (Real.sqrt_pos.mpr (hL.trans_le hx)) (Real.sqrt_pos.mpr hL)).2
      (Real.sqrt_le_sqrt hx)
  have hinv : ‖(Real.sqrt x : ℂ)⁻¹ - (Real.sqrt y : ℂ)⁻¹‖ ≤ (h / L) / Real.sqrt L := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact (abs_inv_sqrt_sub_le hL hx hy).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hxy hL.le) (Real.sqrt_nonneg _))
  let a : ℂ := (Real.sqrt x : ℂ)⁻¹
  let b : ℂ := (Real.sqrt y : ℂ)⁻¹
  let c : ℂ := spectralTransform μ (σ * Real.log x)
  let d : ℂ := spectralTransform μ (σ * Real.log y)
  change ‖a * c - b * d‖ ≤ _
  rw [show a * c - b * d = a * (c - d) + (a - b) * d by ring]
  calc
    _ ≤ ‖a * (c - d)‖ + ‖(a - b) * d‖ := norm_add_le _ _
    _ ≤ (Real.sqrt L)⁻¹ * (2 * T * (h / L) + 2 * η) + (h / L) / Real.sqrt L := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul hroot hC (norm_nonneg _) (by positivity))
        ((mul_le_of_le_one_right (norm_nonneg _) hCx).trans hinv)
    _ = oscillationBudget L h T η := by
      unfold oscillationBudget
      simp only [div_eq_mul_inv]
      ring

/-- The coefficient `a(p) log p` before the reciprocal-square-root weight. -/
@[expose] noncomputable def primeLogCoefficient (a : ℕ → ℂ) (p : ℕ) : ℂ :=
  a p * (Real.log (p : ℝ) : ℂ)

/-- The cell mean is normalized by its length, not by its prime count or mass. -/
@[expose] noncomputable def primeCellMean (a : ℕ → ℂ) (P : Finset ℕ) (l r : ℝ) : ℂ :=
  (∑ p ∈ P, primeLogCoefficient a p) * ((r - l : ℝ) : ℂ)⁻¹

/-- The discrete contribution of the primes assigned to one cell. -/
@[expose] noncomputable def primeCellSum (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℂ)
    (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, primeLogCoefficient a p * weightedTransform μ σ p

/-- The forward or reverse smeared contribution of one cell. -/
@[expose] noncomputable def smearedCellSum (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℂ)
    (P : Finset ℕ) (l r : ℝ) : ℂ :=
  primeCellMean a P l r * ∫ v in l..r, weightedTransform μ σ v

private theorem norm_sub_average_le {f : ℝ → ℂ} {l r p B : ℝ} (hlr : l < r)
    (hf : IntervalIntegrable f volume l r) (hb : ∀ v ∈ Ioc l r, ‖f p - f v‖ ≤ B) :
    ‖f p - ((r - l : ℝ) : ℂ)⁻¹ * (∫ v in l..r, f v)‖ ≤ B := by
  have hd : 0 < r - l := sub_pos.mpr hlr
  have hd' : ((r - l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have he : f p - ((r - l : ℝ) : ℂ)⁻¹ * (∫ v in l..r, f v) =
      ((r - l : ℝ) : ℂ)⁻¹ * (∫ v in l..r, f p - f v) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf, intervalIntegral.integral_const,
      Complex.real_smul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hd', one_mul]
  rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hi : ‖∫ v in l..r, f p - f v‖ ≤ B * (r - l) := by
    simpa only [abs_of_pos hd] using (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun v ↦ f p - f v) (a := l) (b := r) (C := B) (by simpa [uIoc_of_le hlr.le] using hb))
  calc
    _ ≤ (r - l)⁻¹ * (B * (r - l)) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B := by rw [mul_left_comm, inv_mul_cancel₀ hd.ne', mul_one]

private theorem one_cell (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L h T η σ l r : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (htail : μ.real (Icc (-T) T)ᶜ ≤ η)
    (hσ : |σ| ≤ 1) (hLl : L ≤ l) (hlr : l < r) (hwidth : r - l ≤ h)
    (P : Finset ℕ) (a : ℕ → ℂ) (hcoeff : ∀ p, ‖a p‖ ≤ 1)
    (hprime : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ∈ Icc l r) :
    ‖primeCellSum μ σ a P - smearedCellSum μ σ a P l r‖ ≤
      oscillationBudget L h T η * ∑ p ∈ P, Real.log (p : ℝ) := by
  let f := weightedTransform μ σ
  let A : ℂ := ((r - l : ℝ) : ℂ)⁻¹ * ∫ v in l..r, f v
  have he : primeCellSum μ σ a P - smearedCellSum μ σ a P l r =
      ∑ p ∈ P, primeLogCoefficient a p * (f p - A) := by
    unfold primeCellSum smearedCellSum primeCellMean
    rw [mul_assoc, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [f, A, mul_sub]
  rw [he, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  obtain ⟨hpr, hpc⟩ := hprime p hp
  have hnlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
  have hnc : ‖primeLogCoefficient a p‖ ≤ Real.log (p : ℝ) := by
    rw [primeLogCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnlog]
    exact mul_le_of_le_one_left hnlog (hcoeff p)
  have ha : ‖f p - A‖ ≤ oscillationBudget L h T η := by
    apply norm_sub_average_le hlr (weightedTransform_intervalIntegrable μ σ (hL.trans_le hLl) hlr.le)
    intro v hv
    apply norm_weightedTransform_sub_le μ hL hT htail hσ (hLl.trans hpc.1)
      (hLl.trans hv.1.le)
    exact (abs_le.mpr ⟨by linarith [hpc.1, hv.2], by linarith [hpc.2, hv.1]⟩).trans hwidth
  rw [norm_mul, mul_comm (oscillationBudget L h T η)]
  exact (mul_le_mul_of_nonneg_right hnc (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left ha hnlog)

/-- In either direction, the replacement error is the common cell oscillation
budget times the total prime-log mass. The cells have positive length, all
lie above `L > 0`, and each assigned prime lies between its cell endpoints.
The interval integral uses Lebesgue measure, so either assignment of a shared
endpoint is allowed, provided it is counted only once when using the mass bound. -/
theorem norm_sum_primeCell_sub_smearedCell_le {ι : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L h T η σ : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (htail : μ.real (Icc (-T) T)ᶜ ≤ η)
    (hσ : |σ| ≤ 1) (cells : Finset ι) (l r : ι → ℝ) (P : ι → Finset ℕ)
    (a : ℕ → ℂ) (hcoeff : ∀ p, ‖a p‖ ≤ 1)
    (hcell : ∀ i ∈ cells, L ≤ l i ∧ l i < r i ∧ r i - l i ≤ h)
    (hprime : ∀ i ∈ cells, ∀ p ∈ P i, p.Prime ∧ (p : ℝ) ∈ Icc (l i) (r i)) :
    ‖(∑ i ∈ cells, primeCellSum μ σ a (P i)) -
      (∑ i ∈ cells, smearedCellSum μ σ a (P i) (l i) (r i))‖ ≤
      oscillationBudget L h T η * ∑ i ∈ cells, ∑ p ∈ P i, Real.log (p : ℝ) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  obtain ⟨hleft, hpos, hwidth⟩ := hcell i hi
  exact one_cell μ hL hT htail hσ hleft hpos hwidth (P i) a hcoeff (hprime i hi)

/-- The two shifts of the discrete form: `a(p)` forward and its conjugate in reverse. -/
@[expose] noncomputable def twoShiftPrimeForm {ι : Type*} (μ : Measure ℝ) (cells : Finset ι)
    (P : ι → Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  (∑ i ∈ cells, primeCellSum μ 1 a (P i)) +
    ∑ i ∈ cells, primeCellSum μ (-1) (fun p ↦ star (a p)) (P i)

/-- The two shifts of the smeared form over the same cells. -/
@[expose] noncomputable def twoShiftCellForm {ι : Type*} (μ : Measure ℝ) (cells : Finset ι)
    (l r : ι → ℝ) (P : ι → Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  (∑ i ∈ cells, smearedCellSum μ 1 a (P i) (l i) (r i)) +
    ∑ i ∈ cells, smearedCellSum μ (-1) (fun p ↦ star (a p)) (P i) (l i) (r i)

/-- Two-sided weighted correlation replacement, with the original complex
coefficients and their conjugates, and an explicit bound in terms of prime-log mass. -/
theorem norm_twoShiftPrimeForm_sub_twoShiftCellForm_le {ι : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L h T η : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (htail : μ.real (Icc (-T) T)ᶜ ≤ η)
    (cells : Finset ι) (l r : ι → ℝ) (P : ι → Finset ℕ)
    (a : ℕ → ℂ) (hcoeff : ∀ p, ‖a p‖ ≤ 1)
    (hcell : ∀ i ∈ cells, L ≤ l i ∧ l i < r i ∧ r i - l i ≤ h)
    (hprime : ∀ i ∈ cells, ∀ p ∈ P i, p.Prime ∧ (p : ℝ) ∈ Icc (l i) (r i)) :
    ‖twoShiftPrimeForm μ cells P a - twoShiftCellForm μ cells l r P a‖ ≤
      2 * oscillationBudget L h T η * ∑ i ∈ cells, ∑ p ∈ P i, Real.log (p : ℝ) := by
  have hf := norm_sum_primeCell_sub_smearedCell_le μ hL hT htail
    (σ := 1) (by norm_num) cells l r P a hcoeff hcell hprime
  have hr := norm_sum_primeCell_sub_smearedCell_le μ hL hT htail
    (σ := -1) (by norm_num) cells l r P (fun p ↦ star (a p))
    (fun p ↦ by simpa only [norm_star] using hcoeff p) hcell hprime
  unfold twoShiftPrimeForm twoShiftCellForm
  rw [show ∀ A B C D : ℂ, A + B - (C + D) = (A - C) + (B - D) by intros; ring]
  exact (norm_add_le _ _).trans (by simpa only [← two_mul, ← mul_assoc] using add_le_add hf hr)

private theorem primeLogMass_le {ι : Type*} (cells : Finset ι) (P : ι → Finset ℕ)
    {Y : ℝ} (hY : 0 ≤ Y) (hdisj : (cells : Set ι).PairwiseDisjoint P)
    (hprime : ∀ i ∈ cells, ∀ p ∈ P i, p.Prime ∧ (p : ℝ) ≤ Y) :
    (∑ i ∈ cells, ∑ p ∈ P i, Real.log (p : ℝ)) ≤ Real.log 4 * Y := by
  rw [← Finset.sum_biUnion hdisj]
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpP, hpY⟩ := hprime i hi p hpi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpP.pos, (Nat.le_floor_iff hY).2 hpY⟩, hpP⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)

/-- If each prime is counted at most once and all cells lie below `Y`,
Chebyshev's bound `θ(Y) ≤ (log 4)Y` suffices. No short-interval prime estimate is used. -/
theorem norm_twoShiftPrimeForm_sub_twoShiftCellForm_le_chebyshev {ι : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L h T η Y : ℝ} (hL : 0 < L) (hh : 0 ≤ h) (hT : 0 ≤ T)
    (htail : μ.real (Icc (-T) T)ᶜ ≤ η) (hY : 0 ≤ Y)
    (cells : Finset ι) (l r : ι → ℝ) (P : ι → Finset ℕ)
    (a : ℕ → ℂ) (hcoeff : ∀ p, ‖a p‖ ≤ 1)
    (hcell : ∀ i ∈ cells, L ≤ l i ∧ l i < r i ∧ r i - l i ≤ h ∧ r i ≤ Y)
    (hprime : ∀ i ∈ cells, ∀ p ∈ P i, p.Prime ∧ (p : ℝ) ∈ Icc (l i) (r i))
    (hdisj : (cells : Set ι).PairwiseDisjoint P) :
    ‖twoShiftPrimeForm μ cells P a - twoShiftCellForm μ cells l r P a‖ ≤
      2 * oscillationBudget L h T η * (Real.log 4 * Y) := by
  have hη : 0 ≤ η := measureReal_nonneg.trans htail
  refine (norm_twoShiftPrimeForm_sub_twoShiftCellForm_le μ hL hT htail cells l r P a hcoeff
    (fun i hi ↦ ⟨(hcell i hi).1, (hcell i hi).2.1, (hcell i hi).2.2.1⟩) hprime).trans ?_
  apply mul_le_mul_of_nonneg_left (primeLogMass_le cells P hY hdisj ?_)
  · unfold oscillationBudget
    positivity
  · intro i hi p hp
    obtain ⟨hpP, hpI⟩ := hprime i hi p hp
    exact ⟨hpP, hpI.2.trans (hcell i hi).2.2.2⟩

/-- The source scaling: cutoff `T = X^u`, cells in `[sX,Y]` of length at most
`d X^(1-α)`, and `Y ≤ KX`. For fixed positive `s` and fixed `d,K`, the three
terms are `O_s(√X (X^(u-α) + η + X^(-α)))` (with the width and cutoff comparison
constants fixed). Only the upper bounds of the two size comparisons are needed. -/
theorem norm_twoShiftPrimeForm_sub_twoShiftCellForm_le_at_scale {ι : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s X d K Y u α η : ℝ} (hs : 0 < s) (hX : 0 < X) (hd : 0 ≤ d)
    (hY : 0 ≤ Y) (hYmax : Y ≤ K * X) (htail : μ.real (Icc (-(X ^ u)) (X ^ u))ᶜ ≤ η)
    (cells : Finset ι) (l r : ι → ℝ) (P : ι → Finset ℕ)
    (a : ℕ → ℂ) (hcoeff : ∀ p, ‖a p‖ ≤ 1)
    (hcell : ∀ i ∈ cells, s * X ≤ l i ∧ l i < r i ∧ r i - l i ≤ d * X ^ (1 - α) ∧ r i ≤ Y)
    (hprime : ∀ i ∈ cells, ∀ p ∈ P i, p.Prime ∧ (p : ℝ) ∈ Icc (l i) (r i))
    (hdisj : (cells : Set ι).PairwiseDisjoint P) :
    ‖twoShiftPrimeForm μ cells P a - twoShiftCellForm μ cells l r P a‖ ≤
      (2 * Real.log 4 * K / Real.sqrt s) * Real.sqrt X *
        (2 * d / s * X ^ (u - α) + 2 * η + d / s * X ^ (-α)) := by
  have hη : 0 ≤ η := measureReal_nonneg.trans htail
  have hratio : d * X ^ (1 - α) / (s * X) = d / s * X ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hX, Real.rpow_one]
    field_simp
  have hband : 2 * X ^ u * (d / s * X ^ (-α)) = 2 * d / s * X ^ (u - α) := by
    rw [sub_eq_add_neg, Real.rpow_add hX]
    ring
  have hscl : X / (Real.sqrt s * Real.sqrt X) = Real.sqrt X / Real.sqrt s := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    calc
      X * Real.sqrt s = (Real.sqrt X * Real.sqrt X) * Real.sqrt s := by
        rw [Real.mul_self_sqrt hX.le]
      _ = _ := by ring
  let B := oscillationBudget (s * X) (d * X ^ (1 - α)) (X ^ u) η
  have hb : 0 ≤ B := by
    dsimp [B, oscillationBudget]
    positivity
  calc
    _ ≤ 2 * B * (Real.log 4 * Y) :=
      norm_twoShiftPrimeForm_sub_twoShiftCellForm_le_chebyshev μ (by positivity)
        (by positivity) (by positivity) htail hY cells l r P a hcoeff hcell hprime hdisj
    _ ≤ 2 * B * (Real.log 4 * (K * X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYmax (by positivity)) (by positivity)
    _ = _ := by
      dsimp only [B, oscillationBudget]
      rw [hratio, hband, Real.sqrt_mul hs.le]
      let b := 2 * d / s * X ^ (u - α) + 2 * η + d / s * X ^ (-α)
      change 2 * (b / (Real.sqrt s * Real.sqrt X)) * (Real.log 4 * (K * X)) = _
      calc
        _ = 2 * Real.log 4 * K * (X / (Real.sqrt s * Real.sqrt X)) * b := by ring
        _ = _ := by rw [hscl]; ring

end

end ShortCellReplacement
