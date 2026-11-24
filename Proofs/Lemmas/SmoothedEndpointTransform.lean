module

public import Lemmas.LongCutoffSpline
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-!
# Smoothed, translated long-cutoff endpoint transform

Source: `daee96a9:.godel/bob/endpoint-convolution-lift.md`, “What a fixed
translated measurement sees,” lines 38–44. Half-tilt input: `247968e0`,
`Lemmas.LongCutoffSpline`. Owning session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.

This is the Fourier identity used in the Plancherel pairing, not the pairing
or the arithmetic matching argument itself. The source's bound by a constant
times `exp(-|v|/ε)`, with `1/ε > j+1`, implies the absolute integrability of
`k(v) exp(v/2)` used here. The kernel may be signed and the shift is arbitrary.
-/

open Complex MeasureTheory

namespace Masullo

noncomputable section

private def endpointParameter (x : ℝ) : ℂ := 1 / 2 + (x : ℂ) * I

private def endpointKernelTilt (k : ℝ → ℝ) (x v : ℝ) : ℂ :=
  (k v : ℂ) * exp (endpointParameter x * (v : ℂ))

private def endpointProfileTilt (j : ℕ) (x u : ℝ) : ℂ :=
  exp (-(x : ℂ) * I * (u : ℂ)) *
    ((Real.exp (-u / 2) * longCutoffProfile j u : ℝ) : ℂ)

private theorem endpointProfileTilt_eq_decay (j : ℕ) (x u : ℝ) :
    endpointProfileTilt j x u =
      exp (-endpointParameter x * (u : ℂ)) * (longCutoffProfile j u : ℂ) := by
  rw [endpointProfileTilt, Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  unfold endpointParameter
  ring

/-- The absolute half-exponential moment of the real signed kernel controls its complex tilt. -/
public theorem integrable_longCutoffKernel_halfTilt {k : ℝ → ℝ}
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) (x : ℝ) :
    let w : ℂ := 1 / 2 + (x : ℂ) * I
    Integrable (fun v : ℝ ↦ (k v : ℂ) * exp (w * (v : ℂ))) := by
  change Integrable (fun v : ℝ ↦ endpointKernelTilt k x v)
  have hsplit (v : ℝ) : endpointKernelTilt k x v =
      ((k v * Real.exp (v / 2) : ℝ) : ℂ) * exp ((x : ℂ) * I * (v : ℂ)) := by
    rw [endpointKernelTilt, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← exp_add]
    congr 2
    push_cast
    unfold endpointParameter
    ring
  simp_rw [hsplit]
  have hphase : Continuous (fun v : ℝ ↦ exp ((x : ℂ) * I * (v : ℂ))) := by fun_prop
  exact hk.ofReal.mul_bdd hphase.aestronglyMeasurable (c := 1) <|
    ae_of_all _ fun v ↦ by simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private def endpointIntegrand (k : ℝ → ℝ) (j : ℕ) (s x : ℝ) (p : ℝ × ℝ) : ℂ :=
  (exp (-(x : ℂ) * I * (p.1 : ℂ)) * (Real.exp (-(s + p.1) / 2) : ℂ)) *
    ((k p.2 * longCutoffProfile j (p.1 + s + p.2) : ℝ) : ℂ)

private theorem endpointIntegrand_factor (k : ℝ → ℝ) (j : ℕ) (s x z v : ℝ) :
    endpointIntegrand k j s x (z, v) =
      exp ((s : ℂ) * (x : ℂ) * I) * endpointKernelTilt k x v *
        endpointProfileTilt j x (z + s + v) := by
  have hweight : exp (-(x : ℂ) * I * (z : ℂ)) * (Real.exp (-(s + z) / 2) : ℂ) =
      exp ((s : ℂ) * (x : ℂ) * I) * exp (endpointParameter x * (v : ℂ)) *
        exp (-endpointParameter x * ((z + s + v : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    unfold endpointParameter
    ring
  simp only [endpointIntegrand, endpointKernelTilt, endpointProfileTilt_eq_decay,
    Complex.ofReal_mul, hweight]
  ring

private theorem integrable_endpointIntegrand {k : ℝ → ℝ}
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) (j : ℕ) (s x : ℝ) :
    Integrable (endpointIntegrand k j s x) (volume.prod volume) := by
  have hu : Integrable (fun u : ℝ ↦ endpointProfileTilt j x u) := by
    simp_rw [endpointProfileTilt_eq_decay]
    apply integrable_longCutoffProfile_decay
    norm_num [endpointParameter, Complex.mul_re]
  have hv : Integrable (endpointKernelTilt k x) := integrable_longCutoffKernel_halfTilt hk x
  -- First translate by `s`, then shear the profile coordinate by the kernel coordinate.
  have htranslate : MeasurePreserving (fun z : ℝ ↦ z + s) volume volume :=
    measurePreserving_add_right volume s
  have hshear : MeasurePreserving (fun p : ℝ × ℝ ↦ (p.1 + s + p.2, p.2))
      (volume.prod volume) (volume.prod volume) :=
    (measurePreserving_add_prod volume volume).comp (htranslate.prod (MeasurePreserving.id volume))
  have hprod := (hshear.integrable_comp_of_integrable (hu.mul_prod hv)).const_mul
    (exp ((s : ℂ) * (x : ℂ) * I))
  refine hprod.congr (ae_of_all _ fun ⟨z, v⟩ ↦ ?_)
  rw [endpointIntegrand_factor]
  change _ * (endpointProfileTilt j x (z + s + v) * endpointKernelTilt k x v) = _
  rw [mul_comm (endpointProfileTilt j x _)]
  exact (mul_assoc _ _ _).symm

private theorem integral_endpointIntegrand_right (k : ℝ → ℝ) (j : ℕ) (s x z : ℝ) :
    (∫ v : ℝ, endpointIntegrand k j s x (z, v)) =
      exp (-(x : ℂ) * I * (z : ℂ)) *
        ((Real.exp (-(s + z) / 2) *
          (∫ v : ℝ, k v * longCutoffProfile j (z + s + v)) : ℝ) : ℂ) := by
  simp only [endpointIntegrand, integral_const_mul]
  rw [show (∫ v : ℝ, ((k v * longCutoffProfile j (z + s + v) : ℝ) : ℂ)) =
      ((∫ v : ℝ, k v * longCutoffProfile j (z + s + v) : ℝ) : ℂ) from integral_ofReal (𝕜 := ℂ),
    Complex.ofReal_mul, mul_assoc]

/-- The convolution exists for a.e. shift coordinate and its real half-tilt is in `L¹`. -/
public theorem integrable_longCutoffProfile_smoothed_halfTilt {k : ℝ → ℝ}
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) (j : ℕ) (s : ℝ) :
    (∀ᵐ z : ℝ, Integrable (fun v ↦ k v * longCutoffProfile j (z + s + v))) ∧
      Integrable (fun z : ℝ ↦ Real.exp (-(s + z) / 2) *
        ∫ v : ℝ, k v * longCutoffProfile j (z + s + v)) := by
  have hprod := integrable_endpointIntegrand hk j s 0
  constructor
  · filter_upwards [hprod.prod_right_ae] with z hz
    have hw : Integrable (fun v ↦ Real.exp (-(s + z) / 2) *
        (k v * longCutoffProfile j (z + s + v))) := by
      have hre := hz.re
      change Integrable (fun v ↦ (endpointIntegrand k j s 0 (z, v)).re) at hre
      simpa only [endpointIntegrand, ofReal_zero, neg_zero, zero_mul, exp_zero, one_mul,
        ← Complex.ofReal_mul, Complex.ofReal_re] using hre
    simpa only [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul] using
      hw.const_mul (Real.exp (-(s + z) / 2))⁻¹
  · have hre := hprod.integral_prod_left.re
    change Integrable (fun z : ℝ ↦ (∫ v : ℝ, endpointIntegrand k j s 0 (z, v)).re) at hre
    simpa only [integral_endpointIntegrand_right, ofReal_zero, neg_zero, zero_mul, exp_zero,
      one_mul, Complex.ofReal_re] using hre

/-- The transform of the smoothed half-tilt has the translation phase and the full
signed kernel multiplier, at the Fourier convention `exp(-ixz)`. -/
public theorem integral_longCutoffProfile_smoothed_halfTilt {k : ℝ → ℝ}
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) {j : ℕ} (hj : 1 ≤ j) (s x : ℝ) :
    let w : ℂ := 1 / 2 + (x : ℂ) * I
    (∫ z : ℝ, exp (-(x : ℂ) * I * (z : ℂ)) *
      ((Real.exp (-(s + z) / 2) *
        (∫ v : ℝ, k v * longCutoffProfile j (z + s + v)) : ℝ) : ℂ)) =
      exp ((s : ℂ) * (x : ℂ) * I) * (∫ v : ℝ, (k v : ℂ) * exp (w * (v : ℂ))) *
        ((((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) w / w) ^ j) := by
  have hsection (v : ℝ) :
      (∫ z : ℝ, endpointIntegrand k j s x (z, v)) =
        exp ((s : ℂ) * (x : ℂ) * I) * endpointKernelTilt k x v *
          (∫ u : ℝ, endpointProfileTilt j x u) := by
    simp_rw [endpointIntegrand_factor, integral_const_mul]
    rw [show (∫ z : ℝ, endpointProfileTilt j x (z + s + v)) =
        ∫ u : ℝ, endpointProfileTilt j x u by
      simpa only [add_assoc] using integral_add_right_eq_self (endpointProfileTilt j x) (s + v)]
  change _ = exp ((s : ℂ) * (x : ℂ) * I) * (∫ v : ℝ, endpointKernelTilt k x v) * _
  rw [show _ = (∫ u : ℝ, endpointProfileTilt j x u) from
    (integral_longCutoffProfile_halfTilt hj x).symm]
  calc
    _ = ∫ z : ℝ, ∫ v : ℝ, endpointIntegrand k j s x (z, v) :=
      integral_congr_ae (ae_of_all _ fun z ↦ (integral_endpointIntegrand_right k j s x z).symm)
    _ = ∫ v : ℝ, ∫ z : ℝ, endpointIntegrand k j s x (z, v) :=
      integral_integral_swap (integrable_endpointIntegrand hk j s x)
    _ = _ := by simp_rw [hsection, integral_mul_const, integral_const_mul]

end

end Masullo
