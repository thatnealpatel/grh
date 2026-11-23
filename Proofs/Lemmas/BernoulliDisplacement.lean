module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Compact sums of Bernoulli displacements

The bit with value `true` contributes the full length of its displacement.
A two-point law cancels a specified nonreal frequency, and the expectation
on a finite set of coordinates factors into the one-coordinate expectations.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Masullo

/-- A bit selects whether the displacement of length `d` is taken. -/
@[expose] public def bitDisplacement (d : ℝ) (b : Bool) : ℝ := if b then d else 0

private theorem measurable_bitDisplacement (d : ℝ) : Measurable (bitDisplacement d) :=
  measurable_of_countable _

private theorem bitDisplacement_mem_Icc {d : ℝ} (hd : 0 ≤ d) (b : Bool) :
    bitDisplacement d b ∈ Icc 0 d := by
  cases b <;> simp [bitDisplacement, hd]

private noncomputable def displacementProbability (w : ℂ) (d : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / (1 + Real.exp (w.re * d)), by
    have h := Real.exp_pos (w.re * d)
    exact ⟨by positivity, (div_le_one (by positivity)).2 (by linarith)⟩⟩

/-- The probability of taking the displacement is `1 / (1 + exp (w.re * d))`. -/
public noncomputable def displacementLaw (w : ℂ) (d : ℝ) : Measure Bool :=
  bernoulliMeasure true false (displacementProbability w d)

public instance (w : ℂ) (d : ℝ) : IsProbabilityMeasure (displacementLaw w d) := by
  unfold displacementLaw
  infer_instance

private theorem exp_at_half_turn (w : ℂ) (hw : w.im ≠ 0) :
    Complex.exp (w * ((Real.pi / |w.im| : ℝ) : ℂ)) =
      -(Real.exp (w.re * (Real.pi / |w.im|)) : ℂ) := by
  let d := Real.pi / |w.im|
  have hre : (w * (d : ℂ)).re = w.re * d := by simp [Complex.mul_re]
  have him : (w * (d : ℂ)).im = d * w.im := by simp [Complex.mul_im, mul_comm]
  have hπ : d * w.im = Real.pi ∨ d * w.im = -Real.pi := by
    rcases lt_or_gt_of_ne hw with h | h
    · right
      rw [show d = Real.pi / |w.im| from rfl, abs_of_neg h, div_neg, neg_mul,
        div_mul_cancel₀ _ hw]
    · left
      rw [show d = Real.pi / |w.im| from rfl, abs_of_pos h, div_mul_cancel₀ _ hw]
  have hp : Complex.exp ((↑(d * w.im) : ℂ) * Complex.I) = -1 := by
    rcases hπ with h | h
    · rw [h, Complex.exp_pi_mul_I]
    · rw [h, Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      simp
  change Complex.exp (w * (d : ℂ)) = _
  rw [← Complex.re_add_im (w * (d : ℂ)), hre, him, Complex.exp_add, hp, mul_neg, mul_one,
    Complex.ofReal_exp]

/-- A half-turn displacement and the chosen probabilities cancel the two expectations. -/
public theorem integral_exp_displacementLaw (w : ℂ) (hw : w.im ≠ 0) :
    let d := Real.pi / |w.im|
    (∫ b, Complex.exp (w * (bitDisplacement d b : ℂ)) ∂displacementLaw w d) = 0 := by
  dsimp only
  let d := Real.pi / |w.im|
  change (∫ b, Complex.exp (w * (bitDisplacement d b : ℂ)) ∂displacementLaw w d) = 0
  rw [displacementLaw, integral_bernoulliMeasure]
  simp only [bitDisplacement, ite_true, Bool.false_eq_true, ite_false, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, Complex.real_smul]
  have hexp : Complex.exp (w * (d : ℂ)) = -(Real.exp (w.re * d) : ℂ) :=
    exp_at_half_turn w hw
  have hp : 1 - (displacementProbability w d : ℝ) =
      (displacementProbability w d : ℝ) * Real.exp (w.re * d) := by
    change 1 - 1 / (1 + Real.exp (w.re * d)) = 1 / (1 + Real.exp (w.re * d)) * _
    have hne : 1 + Real.exp (w.re * d) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp, hp, Complex.ofReal_mul, mul_neg, mul_one, neg_add_cancel]

/-- Sum the selected displacements over all coordinates. -/
@[expose] public noncomputable def displacementSum (d : ℕ → ℝ) (b : ℕ → Bool) : ℝ :=
  ∑' n, bitDisplacement (d n) (b n)

private def partialDisplacement (d : ℕ → ℝ) (m : ℕ) (b : ℕ → Bool) : ℝ :=
  ∑ i ∈ Finset.range m, bitDisplacement (d i) (b i)

public theorem measurable_displacementSum (d : ℕ → ℝ) : Measurable (displacementSum d) := by
  apply Measurable.tsum
  intro i
  exact (measurable_bitDisplacement (d i)).comp (measurable_pi_apply i)

private theorem summable_displacements {d : ℕ → ℝ} (hd : Summable d) (h0 : ∀ i, 0 ≤ d i)
    (b : ℕ → Bool) : Summable (fun i ↦ bitDisplacement (d i) (b i)) :=
  hd.of_nonneg_of_le (fun i ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).1)
    (fun i ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).2)

public theorem displacementSum_mem_Icc {d : ℕ → ℝ} (hd : Summable d) (h0 : ∀ i, 0 ≤ d i)
    (b : ℕ → Bool) : displacementSum d b ∈ Icc 0 (∑' n, d n) :=
  ⟨tsum_nonneg (fun i ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).1),
    (summable_displacements hd h0 b).tsum_le_tsum
      (fun i ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).2) hd⟩

private theorem partialDisplacement_mem_Icc {d : ℕ → ℝ} (hd : Summable d) (h0 : ∀ i, 0 ≤ d i)
    (m : ℕ) (b : ℕ → Bool) : partialDisplacement d m b ∈ Icc 0 (∑' n, d n) := by
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).1
  · exact (Finset.sum_le_sum fun i _ ↦ (bitDisplacement_mem_Icc (h0 i) (b i)).2).trans
      (hd.sum_le_tsum (Finset.range m) (fun i _ ↦ h0 i))

private theorem measurable_partialDisplacement (d : ℕ → ℝ) (m : ℕ) :
    Measurable (partialDisplacement d m) := by
  unfold partialDisplacement
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_bitDisplacement (d i)).comp (measurable_pi_apply i)

private theorem integral_exp_partialDisplacement (ν : ℕ → Measure Bool)
    [∀ i, IsProbabilityMeasure (ν i)] (z : ℂ) (d : ℕ → ℝ) (m : ℕ) :
    (∫ b, Complex.exp (z * (partialDisplacement d m b : ℂ)) ∂Measure.infinitePi ν) =
      ∏ i : Finset.range m, ∫ b, Complex.exp (z * (bitDisplacement (d i) b : ℂ)) ∂ν i := by
  let s := Finset.range m
  let f (i : s) (b : Bool) := Complex.exp (z * (bitDisplacement (d i) b : ℂ))
  have hf : Measurable (fun b : s → Bool ↦ ∏ i, f i (b i)) := by
    exact Finset.measurable_prod _ fun i _ ↦ (measurable_of_countable (f i)).comp
      (measurable_pi_apply i)
  calc
    _ = ∫ b, ∏ i : s, f i ((s.restrict b) i) ∂Measure.infinitePi ν := by
      apply integral_congr_ae (ae_of_all _ fun b ↦ ?_)
      simp only [partialDisplacement, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      exact (Finset.prod_coe_sort s
        (fun i ↦ Complex.exp (z * (bitDisplacement (d i) (b i) : ℂ)))).symm
    _ = ∫ b : s → Bool, ∏ i, f i (b i) ∂Measure.pi (fun i : s ↦ ν i) :=
      integral_restrict_infinitePi ν hf.aestronglyMeasurable
    _ = _ := integral_fintype_prod_eq_prod f

private theorem tendsto_integral_exp_partialDisplacement (ν : ℕ → Measure Bool)
    [∀ i, IsProbabilityMeasure (ν i)] (z : ℂ) {d : ℕ → ℝ} (hd : Summable d)
    (h0 : ∀ i, 0 ≤ d i) :
    Tendsto (fun m ↦ ∫ b, Complex.exp (z * (partialDisplacement d m b : ℂ)) ∂Measure.infinitePi ν)
      atTop (𝓝 (∫ b, Complex.exp (z * (displacementSum d b : ℂ)) ∂Measure.infinitePi ν)) := by
  have hz : Continuous (fun t : ℝ ↦ Complex.exp (z * (t : ℂ))) := by fun_prop
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ Real.exp (|z.re| * ∑' n, d n))
    (fun m ↦ (hz.measurable.comp (measurable_partialDisplacement d m)).aestronglyMeasurable)
    (integrable_const _) (fun m ↦ ae_of_all _ fun b ↦ ?_) (ae_of_all _ fun b ↦ ?_)
  · have hb := partialDisplacement_mem_Icc hd h0 m b
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr <| mul_le_mul (le_abs_self _) hb.2 hb.1 (abs_nonneg _)
  · exact (hz.tendsto _).comp (summable_displacements hd h0 b).hasSum.tendsto_sum_nat

/-- If one coordinate cancels a frequency, it cancels every partial sum containing it,
and hence also the sum of all the displacements. -/
public theorem integral_exp_displacementSum_eq_zero (ν : ℕ → Measure Bool)
    [∀ i, IsProbabilityMeasure (ν i)] (z : ℂ) {d : ℕ → ℝ} (hd : Summable d)
    (h0 : ∀ i, 0 ≤ d i) (n : ℕ)
    (hn : (∫ b, Complex.exp (z * (bitDisplacement (d n) b : ℂ)) ∂ν n) = 0) :
    (∫ b, Complex.exp (z * (displacementSum d b : ℂ)) ∂Measure.infinitePi ν) = 0 := by
  have he : (fun m ↦ ∫ b, Complex.exp (z * (partialDisplacement d m b : ℂ)) ∂Measure.infinitePi ν)
      =ᶠ[atTop] (fun _ ↦ 0) := by
    filter_upwards [eventually_gt_atTop n] with m hm
    rw [integral_exp_partialDisplacement]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨n, Finset.mem_range.mpr hm⟩ : Finset.range m)) hn
  exact tendsto_nhds_unique ((tendsto_integral_exp_partialDisplacement ν z hd h0).congr' he)
    tendsto_const_nhds

/-- A continuous function is integrable under a finite measure carried by a compact set. -/
public theorem integrable_of_carried_by_compact {μ : Measure ℝ} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ sᶜ = 0) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hs
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

/-- All real exponential moments of a compactly carried probability are strictly positive. -/
public theorem integral_real_exp_pos_of_carried_by_compact {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ sᶜ = 0) (r : ℝ) :
    0 < ∫ t : ℝ, Real.exp (r * t) ∂μ := by
  have hf : Integrable (fun t : ℝ ↦ Real.exp (r * t)) μ :=
    integrable_of_carried_by_compact (by fun_prop) hs hμ
  rw [integral_pos_iff_support_of_nonneg (fun t ↦ (Real.exp_pos (r * t)).le) hf]
  simp [Function.support, Real.exp_ne_zero]

end Masullo
