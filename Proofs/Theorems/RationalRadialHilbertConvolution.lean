module

public import Theorems.RationalRadialHilbertTranslation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Convolution on the rational radial theta quotient

This gives the bounded operator, for continuous compactly supported kernels in
the log coordinate, without a trace-class assertion. The integral is the
Bochner version of (9.3.1.2), with the norm-one Haar factor of mass one.
-/

open MeasureTheory NumberField

namespace Masullo

noncomputable section

local notation "negLe" h => (neg_le_self h)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ

private theorem continuous_translate_smul {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (u : rationalRadialHilbert (negLe hα) s) :
    Continuous (fun y ↦ φ y • rationalRadialHilbertTranslate hα hs y u) :=
  hφ.smul (continuous_rationalRadialHilbertTranslate hα hs u)

/-- The strongly continuous translates against a test kernel are Bochner integrable. -/
public theorem integrable_rationalRadialConvolution {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : rationalRadialHilbert (negLe hα) s) :
    Integrable (fun y ↦ φ y • rationalRadialHilbertTranslate hα hs y u) :=
  (continuous_translate_smul hα hs hφ u).integrable_of_hasCompactSupport hc.smul_right

private def convolutionLinear {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    rationalRadialHilbert (negLe hα) s →ₗ[ℂ] rationalRadialHilbert (negLe hα) s where
  toFun u := ∫ y, φ y • rationalRadialHilbertTranslate hα hs y u
  map_add' u v := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_rationalRadialConvolution hα hs hφ hc u)
      (integrable_rationalRadialConvolution hα hs hφ hc v)
  map_smul' c u := by
    simp only [RingHom.id_apply, map_smul, smul_comm (φ _) c, integral_smul]

private theorem bound_integral {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (u : rationalRadialHilbert (negLe hα) s) :
    ‖∫ y, φ y • rationalRadialHilbertTranslate hα hs y u‖ ≤
      (∫ y, ‖φ y‖ * rationalRadialTranslationBound α s y) * ‖u‖ := by
  rw [← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono
    (integrable_rationalRadialConvolution hα hs hφ hc u).norm ?_ ?_)
  · have hb : Continuous (rationalRadialTranslationBound α s) :=
      continuous_const.mul (continuous_symmetricStripWeightRoot α s)
    exact ((hφ.norm.mul hb).integrable_of_hasCompactSupport hc.norm.mul_right).mul_const _
  · intro y
    change ‖φ y • rationalRadialHilbertTranslate hα hs y u‖ ≤
      ‖φ y‖ * rationalRadialTranslationBound α s y * ‖u‖
    rw [norm_smul, mul_assoc]
    gcongr
    exact ((rationalRadialHilbertTranslate hα hs y).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_rationalRadialHilbertTranslate_le hα hs y) (norm_nonneg _))

/-- The bounded convolution of a rational radial profile by the log kernel `φ`. -/
public def rationalRadialHilbertConvolution {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    rationalRadialHilbert (negLe hα) s →L[ℂ] rationalRadialHilbert (negLe hα) s :=
  (convolutionLinear hα hs hφ hc).mkContinuous
    (∫ y, ‖φ y‖ * rationalRadialTranslationBound α s y) (bound_integral hα hs hφ hc)

/-- The ambient operator is the integral of genuine inverse left translations in `dx`. -/
public theorem rationalRadialHilbertConvolution_apply {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : rationalRadialHilbert (negLe hα) s) :
    rationalRadialHilbertConvolution hα hs hφ hc u =
      ∫ y, φ y • rationalRadialHilbertTranslate hα hs y u := by
  rw [rationalRadialHilbertConvolution]
  rfl

set_option linter.concreteInstances false

/-- The same operator is the normalized class-Haar integral for the radial test
`g ↦ φ(log |g|)`, with class translation acting through the log norm. -/
public theorem rationalRadialHilbertConvolution_haar [MeasurableSpace RationalIdeleClasses]
    [BorelSpace RationalIdeleClasses] {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : rationalRadialHilbert (negLe hα) s) :
    rationalRadialHilbertConvolution hα hs hφ hc u =
      ∫ g : RationalIdeleClasses, φ (Real.log (ideleClassNorm g)) •
        rationalRadialHilbertTranslate hα hs (Real.log (ideleClassNorm g)) u
          ∂rationalIdeleClassHaar := by
  rw [rationalRadialHilbertConvolution_apply]
  let h := measurePreserving_rationalIdeleClass_logNorm
  have hg := (continuous_translate_smul hα hs hφ u).aestronglyMeasurable (μ := volume)
  have hg' : AEStronglyMeasurable (fun y ↦ φ y • rationalRadialHilbertTranslate hα hs y u)
      (rationalIdeleClassHaar.map (fun g : RationalIdeleClasses ↦ Real.log (ideleClassNorm g))) :=
    h.map_eq.symm ▸ hg
  rw [← integral_map h.measurable.aemeasurable hg', h.map_eq]

variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

/-- The bounded quotient convolution on the completed global half-twisted theta quotient. -/
public def rationalRadialQuotientConvolution {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    rationalRadialHilbertQuotient (negLe hα) s →L[ℂ] rationalRadialHilbertQuotient (negLe hα) s :=
  (rationalRadialQuotientProjection (negLe hα) s).comp
    ((rationalRadialHilbertConvolution hα hs hφ hc).comp (rationalRadialHilbertQuotient (negLe hα) s).subtypeL)

/-- Projection intertwines on every ambient lift, not just on the orthogonal complement. -/
public theorem rationalRadialQuotientConvolution_projection {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : rationalRadialHilbert (negLe hα) s) :
    rationalRadialQuotientConvolution hα hs hφ hc (rationalRadialQuotientProjection (negLe hα) s u) =
      rationalRadialQuotientProjection (negLe hα) s (rationalRadialHilbertConvolution hα hs hφ hc u) := by
  let P := rationalRadialQuotientProjection (negLe hα) s
  let q := P u
  rw [rationalRadialQuotientConvolution]
  change P (rationalRadialHilbertConvolution hα hs hφ hc q.val) =
    P (rationalRadialHilbertConvolution hα hs hφ hc u)
  simp only [rationalRadialHilbertConvolution_apply,
    ← P.integral_comp_comm (integrable_rationalRadialConvolution hα hs hφ hc _), map_smul]
  congr 1
  funext y
  exact congrArg (φ y • ·) (rationalRadialQuotientTranslate_projection hα hs y u)

/-- In particular convolution preserves the actual closed global half-twisted theta image. -/
public theorem rationalRadialHilbertConvolution_mem_thetaClosure {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {u : rationalRadialHilbert (negLe hα) s} (hu : u ∈ rationalRadialThetaClosure (negLe hα) s) :
    rationalRadialHilbertConvolution hα hs hφ hc u ∈ rationalRadialThetaClosure (negLe hα) s := by
  rw [← (rationalRadialQuotientProjection_exact (negLe hα) s).1] at hu ⊢
  have h := rationalRadialQuotientConvolution_projection hα hs hφ hc u
  change rationalRadialQuotientProjection (negLe hα) s u = 0 at hu
  rw [hu, map_zero] at h
  exact LinearMap.mem_ker.mpr h.symm

end
end Masullo
