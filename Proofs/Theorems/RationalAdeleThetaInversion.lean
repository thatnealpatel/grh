module

public import Theorems.RationalAdeleUnramifiedPoisson
public import Theorems.RationalThetaNormFiber

/-!
# Adelic theta inversion for the rational unramified tensor

This is the rational unramified case of Masullo's Theorem 2.2.3.2, p. 82.
The Fourier transform is the normalized adelic integral computed in
`integral_rationalAdeleUnramified_mul_conj_char`. We use pointwise adelic
Poisson summation for the dilated tensor, not real Poisson summation.
-/

open NumberField MeasureTheory
open scoped Classical FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

private theorem real_zero : rationalAdeleReal (0 : A) = 0 := by
  simpa only [map_zero, Rat.cast_zero] using rationalAdeleReal_algebraMap 0

private theorem unramified_zero (b : 𝓢(ℝ, ℂ)) : rationalAdeleUnramified b (0 : A) = b 0 := by
  rw [rationalAdeleUnramified, Set.indicator_of_mem rationalIntegralAdeles.zero_mem, real_zero]

private theorem thetaIdeleTerm_eq (b : 𝓢(ℝ, ℂ)) (g : J) (q : ℚˣ) :
    rationalThetaIdeleTerm b g q = rationalAdeleUnramified b ((ιˣ q * g : J) : A) := by
  rw [rationalThetaIdeleTerm, rationalAdeleUnramified, Set.indicator_apply, rationalAdeleReal_apply]
  rfl

/-- The nonzero rational sum of the unramified Schwartz tensor is absolutely
summable at every idele. This also applies to its Fourier transform. -/
public theorem summable_norm_rationalAdeleUnramified_idele (b : 𝓢(ℝ, ℂ)) (g : J) :
    Summable (fun q : ℚˣ ↦ ‖rationalAdeleUnramified b ((ιˣ q * g : J) : A)‖) := by
  simpa only [thetaIdeleTerm_eq] using (rationalTheta_eq_unramified_idele_sum b g).1

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

private theorem theta_inversion_from_adelic_poisson (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    rationalTheta b t = t⁻¹ • rationalTheta (𝓕 b) t⁻¹ + t⁻¹ • (𝓕 b) 0 - b 0 := by
  let bₜ := dilateSchwartz b t ht.ne'
  have hperiod := rationalAdeleComplexPeriodization_unramified_mk bₜ
    (a := (0 : A)) rationalIntegralAdeles.zero_mem
  simp only [rationalAdeleComplexPeriodization_mk, zero_add, real_zero] at hperiod
  have h := (hasSum_rationalAdeleUnramified_poisson bₜ (0 : A)).tsum_eq
  simp only [zero_add, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [hperiod] at h
  simp only [bₜ, dilateSchwartz_apply, fourier_dilateSchwartz b ht] at h
  have hs := (summable_norm_schwartz_int_mul (𝓕 b) (inv_ne_zero ht.ne')).of_norm
  rw [hs.tsum_const_smul t⁻¹, tsum_schwartz_int_mul_eq_zero_add b ht.ne',
    tsum_schwartz_int_mul_eq_zero_add (𝓕 b) (inv_ne_zero ht.ne'), smul_add] at h
  rw [eq_sub_iff_add_eq, add_comm (rationalTheta b t)]
  exact h.trans (add_comm _ _)

/-- On every rational idele `g`, the theta sum of the unramified tensor equals
`|g|⁻¹` times the theta sum of its Fourier transform at `g⁻¹`, with the
Fourier zero mode added and the original zero mode subtracted. -/
public theorem rationalAdeleUnramified_theta_inversion (b : 𝓢(ℝ, ℂ)) (g : J) :
    (∑' q : ℚˣ, rationalAdeleUnramified b ((ιˣ q * g : J) : A)) =
      (ideleNorm g)⁻¹ • (∑' q : ℚˣ, rationalAdeleUnramified (𝓕 b) ((ιˣ q * g⁻¹ : J) : A)) +
        (ideleNorm g)⁻¹ • rationalAdeleUnramified (𝓕 b) 0 - rationalAdeleUnramified b 0 := by
  have hg : 0 < ideleNorm g := ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g)
  simp only [← thetaIdeleTerm_eq, (rationalTheta_eq_unramified_idele_sum b g).2,
    (rationalTheta_eq_unramified_idele_sum (𝓕 b) g⁻¹).2, unramified_zero, map_inv]
  exact theta_inversion_from_adelic_poisson b hg

end Masullo
