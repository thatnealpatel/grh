module

public import Lemmas.SignedBlockIntervalMoment
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact sampling on a translated centered-height mesh

Source: `554d2c816c8c:.godel/bob/centered-height-mesh.md:9–19`.
Owning check session: `01a209ce-61c0-7258-9ef8-09cad8ad12db`.

The consumer is the untruncated signed coefficient integral `J_r` in
`78091476b111:.godel/bob/balanced-height-reconstruction.md:5–23`, before
estimating the finite phase average of the retained samples. The identity
holds at every grid origin and at the no-alias cutoff itself. It does not
assert quadrature for the thresholded band weights or bound the phase average.
-/

open MeasureTheory Filter Asymptotics
open scoped BigOperators FourierTransform Topology

namespace Masullo.CenteredHeightMesh

open SignedBlockIntervalMoment (phase)

/-- The genuine-center kernel, of scale `t` and centered at `u = t`. -/
@[expose] public noncomputable def kernel (t u : ℝ) : ℝ :=
  t⁻¹ * Real.sinc (Real.pi * (u / t - 1)) ^ 2

/-- The angular Fourier triangle for the unshifted kernel. -/
@[expose] public noncomputable def triangle (t x : ℝ) : ℝ :=
  max (1 - t * |x| / (2 * Real.pi)) 0

/-- Finite complex exponential polynomial; labels need not have distinct frequencies. -/
@[expose] public noncomputable def expPolynomial {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ i ∈ s, c i * phase (u * ν i)

/-- Angular spacing of the Fourier aliases at mesh step `Δ`. -/
@[expose] public noncomputable def angularPeriod (Δ : ℝ) : ℝ := 2 * Real.pi / Δ

/-- The coefficient at the `m`-th Fourier alias, before multiplying by its grid phase. -/
@[expose] public noncomputable def aliasCoeff {ι : Type*} (t Δ : ℝ) (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) (m : ℤ) : ℂ :=
  ∑ i ∈ s, c i * phase (t * (ν i - (m : ℝ) * angularPeriod Δ)) *
    (triangle t (ν i - (m : ℝ) * angularPeriod Δ) : ℂ)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

private theorem kernel_eq_shift {t : ℝ} (ht : 0 < t) (u : ℝ) :
    kernel t u = SignedBlockIntervalMoment.sincKernel (40 * t / Real.pi) (u - t) := by
  unfold kernel SignedBlockIntervalMoment.sincKernel
  have hscale : 80 / (2 * Real.pi * (40 * t / Real.pi)) = t⁻¹ := by
    field_simp [ht.ne', Real.pi_ne_zero]
    ring
  have harg : 80 * (u - t) / (2 * (40 * t / Real.pi)) = Real.pi * (u / t - 1) := by
    field_simp [ht.ne', Real.pi_ne_zero]
    ring
  rw [hscale, harg]

private theorem triangle_eq_rescale {t : ℝ} (ht : 0 < t) (x : ℝ) :
    SignedBlockIntervalMoment.triangle (40 * t / Real.pi) x = triangle t x := by
  unfold SignedBlockIntervalMoment.triangle triangle
  congr 2
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

private theorem integrable_kernel {t : ℝ} (ht : 0 < t) : Integrable (kernel t) := by
  change Integrable (fun u ↦ kernel t u)
  simp_rw [kernel_eq_shift ht, sub_eq_add_neg]
  exact (SignedBlockIntervalMoment.integrable_sincKernel (by positivity)).comp_add_right (-t)

private theorem integrable_kernel_phase {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun u ↦ (kernel t u : ℂ) * phase (u * x)) :=
  (integrable_kernel ht).ofReal.mul_bdd
    (continuous_phase.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ (norm_phase (u * x)).le)

/-- The angular transform with the **positive** exponential has center phase `exp(i t x)`. -/
public theorem kernel_transform {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ u, (kernel t u : ℂ) * phase (u * x)) = phase (t * x) * (triangle t x : ℂ) := by
  calc
    _ = ∫ v, (kernel t (v + t) : ℂ) * phase ((v + t) * x) :=
      (integral_add_right_eq_self (fun u ↦ (kernel t u : ℂ) * phase (u * x)) t).symm
    _ = ∫ v, phase (t * x) *
        ((SignedBlockIntervalMoment.sincKernel (40 * t / Real.pi) v : ℂ) * phase (v * x)) := by
      congr 1
      funext v
      rw [kernel_eq_shift ht, add_sub_cancel_right, add_mul, phase_add]
      ring
    _ = _ := by
      rw [integral_const_mul, SignedBlockIntervalMoment.sincKernel_transform (by positivity),
        triangle_eq_rescale ht]

variable {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ)

private theorem norm_expPolynomial_le (u : ℝ) :
    ‖expPolynomial s c ν u‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  unfold expPolynomial
  simpa only [norm_mul, norm_phase, mul_one] using
    (norm_sum_le s fun i ↦ c i * phase (u * ν i))

private theorem continuous_expPolynomial : Continuous (expPolynomial s c ν) := by
  unfold expPolynomial phase
  fun_prop

/-- The untruncated continuous density in the sampling identity is integrable. -/
public theorem integrable_weighted_expPolynomial {t : ℝ} (ht : 0 < t) :
    Integrable (fun u ↦ (kernel t u : ℂ) * expPolynomial s c ν u) :=
  (integrable_kernel ht).ofReal.mul_bdd (continuous_expPolynomial s c ν).aestronglyMeasurable
    (Eventually.of_forall (norm_expPolynomial_le s c ν))

private theorem integral_modulated {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    (∫ u, phase (-(u * ξ)) * ((kernel t u : ℂ) * expPolynomial s c ν u)) =
      ∑ i ∈ s, c i * phase (t * (ν i - ξ)) * (triangle t (ν i - ξ) : ℂ) := by
  let F (i : ι) (u : ℝ) : ℂ := c i * ((kernel t u : ℂ) * phase (u * (ν i - ξ)))
  calc
    _ = ∫ u, ∑ i ∈ s, F i u := by
      congr 1
      funext u
      simp only [expPolynomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [F]
      rw [mul_sub, sub_eq_add_neg, phase_add]
      ring
    _ = ∑ i ∈ s, ∫ u, F i u :=
      integral_finsetSum _ (fun i _ ↦ (integrable_kernel_phase ht (ν i - ξ)).const_mul _)
    _ = _ := by simp only [F, integral_const_mul, kernel_transform ht, mul_assoc]

private theorem fourier_dilated {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (m : ℤ) :
    𝓕 (fun v ↦ (Δ : ℂ) * ((kernel t (Δ * v) : ℂ) * expPolynomial s c ν (Δ * v))) (m : ℝ) =
      aliasCoeff t Δ s c ν m := by
  let ξ := (m : ℝ) * angularPeriod Δ
  let A (u : ℝ) := phase (-(u * ξ)) * ((kernel t u : ℂ) * expPolynomial s c ν u)
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ v, (Δ : ℂ) * A (Δ * v) := by
      congr 1
      funext v
      have hangle : -2 * Real.pi * v * (m : ℝ) = -(Δ * v * ξ) := by
        dsimp [ξ, angularPeriod]
        field_simp [hΔ.ne']
      rw [hangle, smul_eq_mul]
      change phase (-(Δ * v * ξ)) * _ = _
      dsimp [A]
      ring
    _ = ∫ u, A u := by
      rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hΔ),
        Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hΔ.ne',
        Complex.ofReal_one, one_mul]
    _ = _ := integral_modulated s c ν ht ξ

private theorem triangle_eq_zero {t x : ℝ} (ht : 0 < t) (hx : 2 * Real.pi / t ≤ |x|) :
    triangle t x = 0 := by
  unfold triangle
  have hπ : 0 < 2 * Real.pi := by positivity
  have hx' : 2 * Real.pi ≤ t * |x| := by
    simpa only [mul_comm t] using (div_le_iff₀ ht).1 hx
  exact max_eq_right (sub_nonpos.mpr ((le_div_iff₀ hπ).2 (by simpa using hx')))

private theorem aliasCoeff_eq_zero_of_band {t Δ M : ℝ} (ht : 0 < t) {m : ℤ}
    (hν : ∀ i ∈ s, |ν i| ≤ M) (hm : M + 2 * Real.pi / t ≤ |(m : ℝ) * angularPeriod Δ|) :
    aliasCoeff t Δ s c ν m = 0 := by
  unfold aliasCoeff
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hsep := abs_sub_abs_le_abs_sub ((m : ℝ) * angularPeriod Δ) (ν i)
  rw [abs_sub_comm] at hsep
  rw [triangle_eq_zero ht (by linarith [hν i hi]), Complex.ofReal_zero, mul_zero]

/-- Only finitely many aliases can be nonzero, with no band assumption on the finite polynomial. -/
public theorem finite_support_aliasCoeff {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) :
    (Function.support (aliasCoeff t Δ s c ν)).Finite := by
  let M := ∑ i ∈ s, |ν i|
  have hp : 0 < angularPeriod Δ := by unfold angularPeriod; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((M + 2 * Real.pi / t) / angularPeriod Δ)
  refine (Set.finite_Icc (a := -(N : ℤ)) (b := (N : ℤ))).subset ?_
  intro m hm
  rw [Function.mem_support] at hm
  by_contra hout
  have habs : (N : ℝ) < |(m : ℝ)| := by
    have : (N : ℤ) < |m| := by simpa [Set.mem_Icc, ← abs_le] using hout
    exact_mod_cast this
  apply hm
  refine aliasCoeff_eq_zero_of_band s c ν ht
    (fun i hi ↦ Finset.single_le_sum (fun j _ ↦ abs_nonneg (ν j)) hi) ?_
  rw [abs_mul, abs_of_pos hp]
  exact ((div_lt_iff₀ hp).1 (hN.trans habs)).le

-- A positive affine rescaling of sinc squared has quadratic decay, regardless of its shift.
private theorem sinc_sq_affine_decay {a : ℝ} (ha : 0 < a) (d : ℝ) :
    (fun x : ℝ ↦ Real.sinc (a * x + d) ^ 2) =O[cocompact ℝ]
      (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
  have ha₂ : 0 < a / 2 := by positivity
  refine isBigO_iff.mpr ⟨((a / 2)⁻¹) ^ 2, ?_⟩
  have htail := (tendsto_norm_cocompact_atTop (E := ℝ)).eventually
    (eventually_ge_atTop (max 1 (|d| / (a / 2))))
  filter_upwards [htail] with x hx
  rw [Real.norm_eq_abs, max_le_iff] at hx
  have hxpos : 0 < |x| := zero_lt_one.trans_le hx.1
  have hd : |d| ≤ a / 2 * |x| := by
    simpa only [mul_comm (a / 2)] using (div_le_iff₀ ha₂).1 hx.2
  have hsep := abs_sub_abs_le_abs_sub (a * x) (-d)
  rw [abs_mul, abs_of_pos ha, abs_neg, sub_neg_eq_add] at hsep
  have harg : a / 2 * |x| ≤ |a * x + d| := by linarith
  have hargpos : 0 < |a * x + d| := (mul_pos ha₂ hxpos).trans_le harg
  have hprod : |Real.sinc (a * x + d)| * |x| ≤ (a / 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ ha₂]
    calc
      _ = |Real.sinc (a * x + d)| * (a / 2 * |x|) := by ring
      _ ≤ |Real.sinc (a * x + d)| * |a * x + d| := by gcongr
      _ = |Real.sin (a * x + d)| := by
        rw [Real.sinc_of_ne_zero (abs_pos.mp hargpos), abs_div, div_mul_cancel₀ _ hargpos.ne']
      _ ≤ 1 := Real.abs_sin_le_one _
  rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (by positivity : 0 ≤ (|x| ^ 2)⁻¹), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity : 0 < |x| ^ 2)]
  simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (by positivity) hprod 2

private theorem weighted_affine_decay {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (b : ℝ) :
    (fun x : ℝ ↦ (kernel t (b + Δ * x) : ℂ) * expPolynomial s c ν (b + Δ * x))
      =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
  let a := Real.pi * Δ / t
  let d := Real.pi * (b / t - 1)
  obtain ⟨C, hC⟩ := isBigO_iff.mp (sinc_sq_affine_decay (a := a) (by dsimp [a]; positivity) d)
  refine isBigO_iff.mpr ⟨‖t⁻¹‖ * C * (∑ i ∈ s, ‖c i‖), ?_⟩
  filter_upwards [hC] with x hx
  have heq : Real.pi * ((b + Δ * x) / t - 1) = a * x + d := by
    dsimp [a, d]
    ring
  rw [norm_mul, Complex.norm_real, kernel, heq, norm_mul]
  calc
    _ ≤ ‖t⁻¹‖ * (C * ‖|x| ^ (-(2 : ℝ))‖) * (∑ i ∈ s, ‖c i‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        (norm_expPolynomial_le s c ν _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hx))
    _ = _ := by ring

/-- The full, untruncated sample series converges absolutely at every real origin. -/
public theorem summable_norm_samples {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (b : ℝ) :
    Summable (fun j : ℤ ↦ ‖(kernel t (b + (j : ℝ) * Δ) : ℂ) *
      expPolynomial s c ν (b + (j : ℝ) * Δ)‖) := by
  have h := (weighted_affine_decay s c ν ht hΔ b).comp_tendsto Int.tendsto_coe_cofinite
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) h
  simpa only [Function.comp_def, mul_comm Δ] using hs.norm

/-- Exact Poisson alias identity for every origin `b`, with `P = 2π / Δ`.
The left series is absolutely summable and the right series is finitely supported. -/
public theorem discrete_alias {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (b : ℝ) :
    (Δ : ℂ) * (∑' j : ℤ, (kernel t (b + (j : ℝ) * Δ) : ℂ) *
      expPolynomial s c ν (b + (j : ℝ) * Δ)) =
    ∑' m : ℤ, phase ((m : ℝ) * angularPeriod Δ * b) * aliasCoeff t Δ s c ν m := by
  let f (v : ℝ) : ℂ := (Δ : ℂ) * ((kernel t (Δ * v) : ℂ) * expPolynomial s c ν (Δ * v))
  have hc : Continuous f := by
    unfold f kernel expPolynomial phase
    fun_prop
  have hd : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
    simpa only [f, zero_add] using
      (weighted_affine_decay s c ν ht hΔ 0).const_mul_left (Δ : ℂ)
  have hf (m : ℤ) : 𝓕 f (m : ℝ) = aliasCoeff t Δ s c ν m := fourier_dilated s c ν ht hΔ m
  have hsum : Summable (fun m : ℤ ↦ 𝓕 f (m : ℝ)) := by
    let S := (finite_support_aliasCoeff s c ν ht hΔ).toFinset
    refine summable_of_ne_finset_zero (s := S) ?_
    intro m hm
    rw [hf]
    by_contra hne
    exact hm (Set.Finite.mem_toFinset _ |>.mpr (Function.mem_support.mpr hne))
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc one_lt_two hd hsum (b / Δ)
  calc
    _ = ∑' j : ℤ, f (b / Δ + (j : ℝ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      have harg : Δ * (b / Δ + (j : ℝ)) = b + (j : ℝ) * Δ := by
        field_simp [hΔ.ne']
      simp only [f, harg]
    _ = ∑' m : ℤ, 𝓕 f (m : ℝ) * fourier m ((b / Δ : ℝ) : UnitAddCircle) := hp
    _ = _ := by
      apply tsum_congr
      intro m
      rw [hf, mul_comm, fourier_coe_apply, phase, angularPeriod]
      congr 1
      push_cast
      ring_nf

/-- When `P ≥ M + 2π/t` and `|ν i| ≤ M`, all nonzero aliases vanish,
including those incident to a triangle endpoint. No restriction on the origin is needed. -/
public theorem no_alias {t Δ M : ℝ} (ht : 0 < t) (hΔ : 0 < Δ)
    (hν : ∀ i ∈ s, |ν i| ≤ M) (hmesh : M + 2 * Real.pi / t ≤ angularPeriod Δ) (b : ℝ) :
    (Δ : ℂ) * (∑' j : ℤ, (kernel t (b + (j : ℝ) * Δ) : ℂ) *
      expPolynomial s c ν (b + (j : ℝ) * Δ)) =
    ∫ u, (kernel t u : ℂ) * expPolynomial s c ν u := by
  rw [discrete_alias s c ν ht hΔ b, tsum_eq_single (0 : ℤ)]
  · simpa [aliasCoeff, phase] using (integral_modulated s c ν ht 0).symm
  · intro m hm
    have hp : 0 < angularPeriod Δ := by unfold angularPeriod; positivity
    have habs : 1 ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hgate : M + 2 * Real.pi / t ≤ |(m : ℝ) * angularPeriod Δ| := by
      rw [abs_mul, abs_of_pos hp]
      exact hmesh.trans (le_mul_of_one_le_left hp.le habs)
    rw [aliasCoeff_eq_zero_of_band s c ν ht hν hgate, mul_zero]

end Masullo.CenteredHeightMesh
