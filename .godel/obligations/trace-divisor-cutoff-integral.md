# Integrating the two-scale cutoff majorant

**Status: Lean draft, not elaborated.** This is the integration half of the
[Chapter 13 cutoff repair](trace-divisor-cutoff.md#uniform-weighted-bounds-for-the-cutoff-family).
The pointwise estimate in that handoff is an input here. No manuscript claim
or equality of the full and capped distributions is used.

The moving layer $[1/N,2/N]$ lies in the domain of integration for $N>0$.
Its Lebesgue mass is $1/N$, so the factor $N$ drops out exactly. The other
majorant term uses the exponential integral. The conclusion is a bound on
the sum of the two weighted integrals, matching the right-hand side of
[`norm_positiveLaplaceTest_mul_weight_le`](trace-divisor-compact-test.md).
Neither a common pointwise envelope for the differentiated family nor
nonnegativity of the two coefficients is needed for this integration step.

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

open MeasureTheory Set

namespace Masullo

/-- Integrating a moving layer of width `1 / N` and height `C₁ * N`
costs `C₁`, uniformly in the scale `N`. -/
theorem weightedCutoffIntegrals_le {f : ℝ → ℂ} {a δ C₀ C₁ N : ℝ}
    (hδ : 0 < δ) (hN : 0 < N)
    (hf : Continuous f) (hs : HasCompactSupport f)
    (hf₂ : Continuous (deriv (deriv f)))
    (hs₂ : HasCompactSupport (deriv (deriv f)))
    (hmajor : ∀ x > 0,
      Real.exp (a * x) * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
        C₀ * Real.exp (-δ * x) + (Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
        (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) ≤
      C₀ / δ + C₁ := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let I := Icc (1 / N) (2 / N)
  let p : ℝ → ℝ := fun x ↦ Real.exp (a * x) * ‖f x‖
  let q : ℝ → ℝ := fun x ↦ Real.exp (a * x) * ‖deriv (deriv f) x‖
  let g : ℝ → ℝ := fun x ↦ C₀ * Real.exp (-δ * x)
  let b : ℝ → ℝ := I.indicator (fun _ ↦ C₁ * N)
  have hI : MeasurableSet I := measurableSet_Icc
  have hsub : I ⊆ Ioi (0 : ℝ) := fun _ hx ↦ (one_div_pos.mpr hN).trans_le hx.1
  have hlen : 2 / N - 1 / N = 1 / N := by simp only [div_eq_mul_inv]; ring
  have hμI : μ I = ENNReal.ofReal (1 / N) := by
    rw [μ, Measure.restrict_apply hI, inter_eq_left.mpr hsub, I, Real.volume_Icc, hlen]
  have hw : Continuous (fun x : ℝ ↦ Real.exp (a * x)) := by fun_prop
  have hp : Integrable p μ :=
    (hw.mul hf.norm).integrable_of_hasCompactSupport
      (hs.comp_left (g := fun z : ℂ ↦ ‖z‖) norm_zero).mul_left |>.integrableOn
  have hq : Integrable q μ :=
    (hw.mul hf₂.norm).integrable_of_hasCompactSupport
      (hs₂.comp_left (g := fun z : ℂ ↦ ‖z‖) norm_zero).mul_left |>.integrableOn
  have hexp : Integrable (fun x : ℝ ↦ Real.exp (-δ * x)) μ :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hδ) 0
  have hg : Integrable g μ := hexp.const_mul C₀
  have hb : Integrable b μ := by
    apply (integrable_indicator_iff hI).mpr
    exact integrableOn_const (by rw [hμI]; exact ENNReal.ofReal_ne_top)
  have hgint : (∫ x, g x ∂μ) = C₀ / δ := by
    change (∫ x : ℝ in Ioi (0 : ℝ), C₀ * Real.exp (-δ * x)) = _
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hδ)]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, div_eq_mul_inv, one_mul]
  have hbint : (∫ x, b x ∂μ) = C₁ := by
    rw [b, integral_indicator_const _ hI, measureReal_def, hμI,
      ENNReal.toReal_ofReal (one_div_nonneg.mpr hN.le), smul_eq_mul]
    field_simp [hN.ne'] <;> ring
  have hle : (fun x ↦ p x + q x) ≤ᵐ[μ] (fun x ↦ g x + b x) := by
    have hpos : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem (μ := volume) hpos] with x hx
    simpa only [p, q, g, b, I, mul_add] using hmajor x (mem_Ioi.mp hx)
  change (∫ x, p x ∂μ) + (∫ x, q x ∂μ) ≤ _
  calc
    _ = ∫ x, (p x + q x) ∂μ := (integral_add hp hq).symm
    _ ≤ ∫ x, (g x + b x) ∂μ := integral_mono_ae (hp.add hq) (hg.add hb) hle
    _ = C₀ / δ + C₁ := by rw [integral_add hg hb, hgint, hbint]

end Masullo
```

In the family application, take $N=n+2$ and use the *same* $C_0,C_1,\delta$
for all $n$. Both weighted integrals are nonnegative, so the sum bound also
bounds each individually. Apply the compact-test estimate and divide by
$1+|w_i|^2$ before multiplying by $|d_i|$. This gives a uniform bound for
all pairs $(n,i)$, not a moving majorant for the spectral sum. The scalar
integral limits and zero-mean correction are separate steps.
