module

public import Lemmas.ArchimedeanCompletionHaar
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Log-polar coordinates for complex multiplicative Haar

Definitions A.3.1.2(2), p. 556, and A.3.2.2(1), p. 560, supply
`2 dx dy` divided by the squared norm. To use the angular sector in
(A.2.3.21), p. 551, we compute the pushforward to weighted log-radius
and angle. This is a local calculation, not the construction or volume
of that fundamental domain. Principal argument gives the open interval
`(-π, π)` as the measure chart; the cut ray is null.
-/

open MeasureTheory NumberField InfinitePlace.Completion Set
open scoped ENNReal

namespace Masullo

private theorem lintegral_complexLogRadius (g : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 / r) * g (2 * Real.log r)) = ∫⁻ x, g x := by
  let e : ℝ → ℝ := fun x ↦ Real.exp (x / 2)
  have hderiv (x : ℝ) : HasDerivAt e (Real.exp (x / 2) / 2) x := by
    unfold e
    simpa only [id_eq, div_eq_mul_inv, one_mul] using ((hasDerivAt_id x).div_const 2).exp
  have hinj : Function.Injective e := Real.exp_injective.comp (fun x y hxy ↦ by linarith)
  have hcov : e '' univ = Ioi 0 := by
    rw [image_univ, ← Real.range_exp]
    ext y
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x / 2, hx⟩, fun ⟨t, ht⟩ ↦ ⟨t * 2, by simp [e, ht]⟩⟩
  rw [← hcov, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ ↦ (hderiv x).hasDerivWithinAt) hinj.injOn, Measure.restrict_univ]
  apply lintegral_congr
  intro x
  simp only [e, Real.log_exp, abs_of_pos (div_pos (Real.exp_pos _) (by norm_num : (0:ℝ) < 2))]
  rw [show 2 * (x / 2) = x by ring, ← mul_assoc, ← ENNReal.ofReal_mul]
  · rw [show Real.exp (x / 2) / 2 * (2 / Real.exp (x / 2)) = 1 by
      field_simp [Real.exp_ne_zero], ENNReal.ofReal_one, one_mul]
  · positivity

/-- Log-polar form of the complex multiplicative Tamagawa density. -/
public theorem complexTamagawaDensity_map_logPolar :
    Measure.map (fun z : ℂ ↦ (2 * Real.log ‖z‖, Complex.arg z)) complexTamagawaDensity =
      (volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  let e : ℂ → ℝ × ℝ := fun z ↦ (2 * Real.log ‖z‖, Complex.arg z)
  have he : Measurable e := (measurable_const.mul (Real.measurable_log.comp measurable_norm)).prodMk
    Complex.measurable_arg
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  change (∫⁻ p, f p ∂Measure.map e complexTamagawaDensity) = _
  rw [lintegral_map hf he, complexTamagawaDensity,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun z ↦ f (e z)) from hf.comp he),
    ← Complex.lintegral_comp_polarCoord_symm]
  let A : Set ℝ := Ioo (-Real.pi) Real.pi
  have hcoord :
      (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (ENNReal.ofReal (2 / ‖Complex.polarCoord.symm p‖ ^ 2) *
          f (e (Complex.polarCoord.symm p)))) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ A, ENNReal.ofReal (2 / p.1) * f (2 * Real.log p.1, p.2) := by
    rw [Complex.polarCoord_target]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp ↦ ?_)
    have hr : 0 < p.1 := hp.1
    have hangle := Complex.polarCoord.right_inv (show p ∈ Complex.polarCoord.target from hp)
    rw [Complex.polarCoord_apply] at hangle
    have hn := congrArg Prod.fst hangle
    have ha := congrArg Prod.snd hangle
    change ‖Complex.polarCoord.symm p‖ = p.1 at hn
    change (Complex.polarCoord.symm p).arg = p.2 at ha
    simp only [e, hn, ha, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hr.le]
    congr 2
    field_simp
  refine hcoord.trans ?_
  change (∫⁻ p, ENNReal.ofReal (2 / p.1) * f (2 * Real.log p.1, p.2)
    ∂((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ A)) = _
  rw [← Measure.prod_restrict, lintegral_prod_symm' _ (by fun_prop), lintegral_prod_symm' _ hf]
  congr 1
  funext a
  exact lintegral_complexLogRadius (fun x ↦ f (x, a))

/-- Log-polar form of multiplicative Tamagawa measure on actual complex completion units. -/
public theorem complexCompletionHaar_map_logPolar {K : Type*} [Field K] {v : InfinitePlace K}
    [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ] (hv : v.IsComplex) :
    Measure.map
      (fun u : v.Completionˣ ↦ (2 * Real.log ‖u.val‖, Complex.arg (extensionEmbedding v u.val)))
      (complexCompletionHaar hv) =
      (volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  rw [← complexTamagawaDensity_map_logPolar, ← complexCompletionHaar_map hv,
    Measure.map_map _ (complexCompletionEmbedding hv).measurable]
  · congr 1
    funext u
    have hn := (isometry_extensionEmbedding v).dist_eq u.val 0
    simp only [map_zero, dist_zero_right] at hn
    simp only [Function.comp_apply, hn]
  · exact (measurable_const.mul (Real.measurable_log.comp measurable_norm)).prodMk Complex.measurable_arg

end Masullo
