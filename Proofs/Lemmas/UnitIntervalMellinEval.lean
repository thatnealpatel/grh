module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Mellin evaluation on the unit interval -/

open MeasureTheory Set
open scoped ComplexConjugate

namespace Masullo

/-- On `L²((0, 1), dx)`, Mellin evaluation at `ρ` with `1/2 < ρ.re` is a
continuous complex-linear functional. Its norm is the `L²` norm of the Mellin
kernel, and it takes the constant function `1` to `ρ⁻¹`. -/
public theorem exists_unitInterval_mellinEval (ρ : ℂ) (hρ : 1 / 2 < ρ.re) :
    let μ := (volume : Measure ℝ).restrict (Ioo 0 1)
    ∃ F : Lp ℂ 2 μ →L[ℂ] ℂ,
      ‖F‖ = (Real.sqrt (2 * ρ.re - 1))⁻¹ ∧
      (∀ (f : ℝ → ℂ) (hf : MemLp f 2 μ),
        Integrable (fun x ↦ f x * (x : ℂ) ^ (ρ - 1)) μ ∧
          F (hf.toLp f) = ∫ x, f x * (x : ℂ) ^ (ρ - 1) ∂μ) ∧
      F ((memLp_const (μ := μ) (p := 2) (1 : ℂ)).toLp (fun _ : ℝ ↦ 1)) = ρ⁻¹ := by
  intro μ
  let k := fun x : ℝ ↦ (x : ℂ) ^ (conj ρ - 1)
  have hpos : ∀ᵐ x ∂μ, 0 < x :=
    (ae_restrict_mem (μ := volume) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo).mono
      (fun _ hx ↦ hx.1)
  have hsq (x : ℝ) (hx : 0 < x) : ‖k x‖ ^ 2 = x ^ (2 * ρ.re - 2) := by
    dsimp only [k]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hx.le]
    congr 1
    simp only [Complex.sub_re, Complex.conj_re, Complex.one_re, Nat.cast_ofNat]
    ring
  have hmeas : AEStronglyMeasurable k μ := by
    refine ContinuousOn.aestronglyMeasurable (μ := volume) (s := Ioo 0 1) ?_ measurableSet_Ioo
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x (conj ρ - 1)
      (Or.inr (ne_of_gt hx.1))).continuousWithinAt
  have hexp : -1 < 2 * ρ.re - 2 := by linarith
  have hk : MemLp k 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    have hpow : Integrable (fun x : ℝ ↦ x ^ (2 * ρ.re - 2)) μ :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hexp
    exact hpow.congr (hpos.mono fun x hx ↦ (hsq x hx).symm)
  let K := hk.toLp k
  -- The first slot of the inner product conjugates the representing kernel.
  let F := innerSL ℂ K
  have hpair (f : ℝ → ℂ) (hf : MemLp f 2 μ) :
      Integrable (fun x ↦ f x * (x : ℂ) ^ (ρ - 1)) μ ∧
        F (hf.toLp f) = ∫ x, f x * (x : ℂ) ^ (ρ - 1) ∂μ := by
    have heq : (fun x : ℝ ↦ inner ℂ (K x) (hf.toLp f x)) =ᵐ[μ]
        (fun x ↦ f x * (x : ℂ) ^ (ρ - 1)) := by
      filter_upwards [hk.coeFn_toLp, hf.coeFn_toLp, hpos] with x hkx hfx hx
      change K x = k x at hkx
      change hf.toLp f x = f x at hfx
      rw [hkx, hfx, RCLike.inner_apply]
      have harg : (x : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hx.le]
        exact Real.pi_pos.ne
      have hconj : conj (k x) = (x : ℂ) ^ (ρ - 1) := by
        simpa only [k, map_sub, map_one, Complex.conj_ofReal] using
          (Complex.conj_cpow (x : ℂ) (ρ - 1) harg).symm
      change f x * conj (k x) = _
      rw [hconj]
    refine ⟨(L2.integrable_inner (𝕜 := ℂ) K (hf.toLp f)).congr heq, ?_⟩
    change innerSL ℂ K (hf.toLp f) = _
    rw [innerSL_apply_apply, L2.inner_def]
    exact integral_congr_ae heq
  have hμ : μ = (volume : Measure ℝ).restrict (Ioc 0 1) := restrict_Ioo_eq_restrict_Ioc
  refine ⟨F, ?_, hpair, ?_⟩
  · change ‖innerSL ℂ K‖ = _
    rw [innerSL_apply_norm, norm_eq_sqrt_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) K K)]
    have hself : (∫ x, RCLike.re (inner ℂ (K x) (K x)) ∂μ) =
        ∫ x : ℝ, x ^ (2 * ρ.re - 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hk.coeFn_toLp, hpos] with x hkx hx
      change K x = k x at hkx
      rw [inner_self_eq_norm_sq, hkx, hsq x hx]
    rw [hself, hμ, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hexp)]
    rw [show 2 * ρ.re - 2 + 1 = 2 * ρ.re - 1 by ring, Real.one_rpow,
      Real.zero_rpow (by linarith : 2 * ρ.re - 1 ≠ 0), sub_zero, one_div, Real.sqrt_inv]
  · have h := (hpair (fun _ ↦ 1) (memLp_const (μ := μ) (p := 2) (1 : ℂ))).2
    simp only [one_mul] at h
    have hexp' : -1 < (ρ - 1).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hρ₀ : ρ ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      rw [Complex.zero_re] at hre
      linarith
    rw [h, hμ, ← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hexp')]
    simp only [sub_add_cancel, Complex.ofReal_one, Complex.ofReal_zero,
      Complex.one_cpow, Complex.zero_cpow hρ₀, sub_zero, one_div]

end Masullo
