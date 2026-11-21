module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Theorems.RealMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp

/-! # Support and coordinate changes for the real logarithmic kernel -/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace Masullo

/-- The translated additive test in (B.4.4.2) for a radial real log profile.
The branch at `z = -1` extends the multiplicative test by zero. -/
@[expose] public noncomputable def realLogProfileAdditive (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  if 1 + z = 0 then 0 else ((|1 + z| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (Real.log |1 + z|)

namespace RealLogProfileHaar

public theorem additive_test {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (realLogProfileAdditive F) ∧ HasCompactSupport (realLogProfileAdditive F) := by
  let v (y : ℝ) : ℂ := if y = 0 then 0 else ((|y| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (Real.log |y|)
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  have hzero (y : ℝ) (hy : |y| < Real.exp a) : v y = 0 := by
    by_cases hy₀ : y = 0
    · simp [v, hy₀]
    have hloga : Real.log |y| < a := by simpa using Real.log_lt_log (abs_pos.mpr hy₀) hy
    have hz : F (Real.log |y|) = 0 := by
      by_contra hh
      exact (not_lt_of_ge (ha (subset_tsupport _ hh))) hloga
    simp only [v, hz, mul_zero, ite_self]
  have hvc : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y = 0
    · subst y
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.exp_pos a)] with t ht
      exact hzero t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
    · have hl : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hy
      have hw : ContDiffAt ℝ ∞ (fun t : ℝ ↦ (Real.exp (Real.log t * (-(1 / 2) : ℝ)) : ℂ)) y :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp y ((hl.mul contDiffAt_const).exp)
      apply (hw.mul (hF.contDiffAt.comp y hl)).congr_of_eventuallyEq
      filter_upwards [(isOpen_ne (x := (0 : ℝ))).mem_nhds hy] with t ht
      have ht' : t ≠ 0 := ht
      simp [v, ht', Real.rpow_def_of_pos (abs_pos.mpr ht'), Real.log_abs]
  have hv : HasCompactSupport v := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Real.exp b) (b := Real.exp b))
    intro y hy
    rw [mem_Icc, ← abs_le]
    by_contra! hyb
    have hlogb : b < Real.log |y| := by simpa using Real.log_lt_log (Real.exp_pos b) hyb
    have hz : F (Real.log |y|) = 0 := by
      by_contra hh
      exact (not_lt_of_ge (hb (subset_tsupport _ hh))) hlogb
    exact hy (by simp only [v, hz, mul_zero, ite_self])
  exact ⟨hvc.comp (contDiff_const.add contDiff_id), hv.comp_isClosedEmbedding (Homeomorph.addLeft (1 : ℝ)).isClosedEmbedding⟩

/-- Translate the density and integration set by `y = 1 + z`. -/
public theorem translate_set (u : ℝ → ℂ) (s : Set ℝ) :
    let e : ℝ → ℝ := fun z ↦ 1 + z
    (IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) (e ⁻¹' s) ↔
      IntegrableOn (fun y ↦ u (y - 1) / ((|1 - y| : ℝ) : ℂ)) s) ∧
    (∫ z in e ⁻¹' s, u z / ((|z| : ℝ) : ℂ)) =
      ∫ y in s, u (y - 1) / ((|1 - y| : ℝ) : ℂ) := by
  let e := MeasurableEquiv.addLeft (1 : ℝ)
  let g (y : ℝ) := u (y - 1) / ((|1 - y| : ℝ) : ℂ)
  have he : volume.map e = (volume : Measure ℝ) := (measurePreserving_add_left volume (1 : ℝ)).map_eq
  have hg : g ∘ e = fun z ↦ u z / ((|z| : ℝ) : ℂ) := by
    funext z
    have h₁ : 1 + z - 1 = z := by ring
    have h₂ : 1 - (1 + z) = -z := by ring
    simp [g, e, h₁, h₂]
  have hi := e.measurableEmbedding.integrableOn_map_iff (μ := volume) (f := g) (s := s)
  rw [he, hg] at hi
  have h := e.measurableEmbedding.setIntegral_map (μ := volume) g s
  change (∫ y in s, g y ∂volume.map e) = ∫ z in e ⁻¹' s, (g ∘ e) z at h
  rw [he, hg] at h
  exact ⟨hi.symm, h.symm⟩

/-- Translate both the test and the physical cutoff, preserving Lebesgue measure. -/
public theorem translate_cutoff (u : ℝ → ℂ) (ε : ℝ) :
    (IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) {z | ε ≤ |z|} ↔
      IntegrableOn (fun y ↦ u (y - 1) / ((|1 - y| : ℝ) : ℂ)) {y | ε ≤ |1 - y|}) ∧
    (∫ z in {z | ε ≤ |z|}, u z / ((|z| : ℝ) : ℂ)) =
      ∫ y in {y | ε ≤ |1 - y|}, u (y - 1) / ((|1 - y| : ℝ) : ℂ) := by
  simpa using translate_set u {y | ε ≤ |1 - y|}

/-- Push real local Haar to its density in the value coordinate. This works
on both sign components, and the additive measure ignores the null singleton. -/
public theorem density_set (F : ℝ → ℂ) {s : Set ℝ} (hs : MeasurableSet s) :
    let w (y : ℝ) := F (Real.log |y|) * ((|y| ^ (1 / 2 : ℝ) : ℝ) : ℂ) / ((|1 - y| : ℝ) : ℂ)
    let g (y : ℝ) := realLogProfileAdditive F (y - 1) / ((|1 - y| : ℝ) : ℂ)
    (IntegrableOn (w ∘ (Units.val : ℝˣ → ℝ)) (Units.val ⁻¹' s) realMultiplicativeHaar ↔ IntegrableOn g s) ∧
      (∫ y in Units.val ⁻¹' s, w y ∂realMultiplicativeHaar) = ∫ y in s, g y := by
  intro w g
  let j : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := Units.isOpenEmbedding_val.measurableEmbedding
  let ρ (y : ℝ) := ENNReal.ofReal |y|⁻¹
  have hρ : Measurable ρ := by dsimp [ρ]; fun_prop
  have hρtop : ∀ᵐ y ∂volume.restrict s, ρ y < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hη : (realMultiplicativeHaar.map Units.val) = volume.withDensity ρ := by
    rw [map_realMultiplicativeHaar_val, restrict_compl_singleton]
  have hg : (fun y ↦ (ρ y).toReal • w y) =ᵐ[volume.restrict s] g := by
    filter_upwards [(volume.ae_ne (0 : ℝ)).filter_mono (ae_mono Measure.restrict_le_self)] with y hy
    have hy' : 0 < |y| := abs_pos.mpr hy
    have h₁ : 1 + (y - 1) = y := by ring
    have h₂ : |y|⁻¹ * |y| ^ (1 / 2 : ℝ) = |y| ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hy']
      congr 1
      norm_num
    simp only [ρ, w, g, realLogProfileAdditive, h₁, ite_eq_right hy,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg y)), Complex.real_smul]
    push_cast [← h₂]
    ring
  constructor
  · rw [← j.integrableOn_map_iff, hη, IntegrableOn, restrict_withDensity hs,
      integrable_withDensity_iff_integrable_smul₀' hρ.aemeasurable hρtop]
    exact integrable_congr hg
  · rw [← j.setIntegral_map, hη, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      hρ.aemeasurable hρtop w hs]
    exact integral_congr_ae hg

/-- The pushforward density on the physical cutoff. -/
public theorem density_cutoff (F : ℝ → ℂ) (ε : ℝ) :
    let w (y : ℝ) := F (Real.log |y|) * ((|y| ^ (1 / 2 : ℝ) : ℝ) : ℂ) / ((|1 - y| : ℝ) : ℂ)
    let s : Set ℝ := {y | ε ≤ |1 - y|}
    let g (y : ℝ) := realLogProfileAdditive F (y - 1) / ((|1 - y| : ℝ) : ℂ)
    (IntegrableOn (w ∘ (Units.val : ℝˣ → ℝ)) (Units.val ⁻¹' s) realMultiplicativeHaar ↔ IntegrableOn g s) ∧
      (∫ y in Units.val ⁻¹' s, w y ∂realMultiplicativeHaar) = ∫ y in s, g y :=
  density_set F (measurableSet_le measurable_const (by fun_prop))

end RealLogProfileHaar
end Masullo
