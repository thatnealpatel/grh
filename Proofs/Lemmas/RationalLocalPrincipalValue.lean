module

public import Theorems.RationalLocalShiftedFourier
import Theorems.PadicLogFourier
import Lemmas.RationalLocalNormShell
import Lemmas.RationalLocalAdditiveModulus
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Unit subtraction and Fourier linearity in the rational finite completions -/

open Function NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Padic

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "ν[" v "]" => rationalLocalFieldAddHaar v

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

/-- The characteristic function of the integral unit group inside the field units. -/
@[expose]
public noncomputable def rationalLocalUnitIndicator (v : V) : K[v]ˣ → ℂ :=
  (range (rationalLocalUnitInclusion v)).indicator 1

public theorem rationalLocalUnitIndicator_properties (v : V) :
    IsLocallyConstant (rationalLocalUnitIndicator v) ∧
      HasCompactSupport (rationalLocalUnitIndicator v) ∧ rationalLocalUnitIndicator v 1 = 1 := by
  let U := range (rationalLocalUnitInclusion v)
  have hU := isCompact_range_rationalLocalUnitInclusion v
  have hcl : IsClopen U := ⟨hU.isClosed, (isOpenEmbedding_rationalLocalUnitInclusion v).isOpen_range⟩
  refine ⟨(LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.of_support_subset_isCompact hU ?_, ?_⟩
  · intro y hy
    by_contra h
    exact hy (indicator_of_notMem h _)
  · apply indicator_of_mem
    exact (RationalLocalNormShell.mem_unitRange_iff v 1).mpr (by simp)

private theorem shifted_unitIndicator (v : V) (x : K[v]) :
    rationalLocalShiftedTest v (rationalLocalUnitIndicator v) x =
      {y : K[v] | ‖1 + y‖ = 1}.indicator 1 x := by
  by_cases h : 1 + x = 0
  · have hz : ¬∃ y : K[v]ˣ, (y : K[v]) = 1 + x := fun ⟨y, hy⟩ ↦ y.ne_zero (hy.trans h)
    rw [rationalLocalShiftedTest, Function.extend_apply' _ _ _ hz,
      indicator_of_notMem (by simp [h])]
  · let z := Units.mk0 (1 + x) h
    have hz : (z : K[v]) = 1 + x := rfl
    unfold rationalLocalShiftedTest
    rw [← hz, Units.val_injective.extend_apply]
    have hmem : x ∈ {y : K[v] | ‖1 + y‖ = 1} ↔ ‖(z : K[v])‖ = 1 := by
      change ‖1 + x‖ = 1 ↔ ‖(z : K[v])‖ = 1
      rw [hz]
    by_cases hn : ‖(z : K[v])‖ = 1
    · rw [rationalLocalUnitIndicator, indicator_of_mem ((RationalLocalNormShell.mem_unitRange_iff v z).mpr hn),
        indicator_of_mem (hmem.mpr hn)]
      simp [hn]
    · rw [rationalLocalUnitIndicator, indicator_of_notMem (mt (RationalLocalNormShell.mem_unitRange_iff v z).mp hn),
        indicator_of_notMem (mt hmem.mp hn)]
      simp

/-- Transport the vanishing calibration from `ℚ_[p]` to the actual completion. -/
public theorem rationalLocalUnitIndicator_log_fourier (v : V) :
    let F := rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v (rationalLocalUnitIndicator v))
    Integrable F ν[v] ∧ (∫ ξ, F ξ ∂ν[v]) = 0 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let j : MeasurableEmbedding (e : K[v] → ℚ_[(p[v] : ℕ)]) := e.toHomeomorph.measurableEmbedding
  let μ := padicAddHaar (p[v] : ℕ)
  let χ := padicStdAddChar (p[v] : ℕ)
  let U : Set ℚ_[(p[v] : ℕ)] := {z | ‖1 + z‖ = 1}
  let F (η : ℚ_[(p[v] : ℕ)]) := (↑(Real.log ‖η‖ / Real.log ((p[v] : ℕ) : ℝ)) : ℂ) *
    ∫ z in U, star (χ (z * η)) ∂μ
  have he : MeasurePreserving e ν[v] μ := by
    refine ⟨j.measurable, ?_⟩
    change (μ.comap e).map e = μ
    rw [j.map_comap, e.surjective.range_eq, Measure.restrict_univ]
  have hU : MeasurableSet U := (isClosed_eq (continuous_norm.comp (by fun_prop)) continuous_const).measurableSet
  have hmem (x : K[v]) : x ∈ {y : K[v] | ‖1 + y‖ = 1} ↔ e x ∈ U := by
    change ‖1 + x‖ = 1 ↔ ‖1 + e x‖ = 1
    rw [← map_one e, ← map_add, norm_rationalLocal_padicEquiv]
  have hF : rationalLocalLogFourierIntegrand v
      (rationalLocalShiftedTest v (rationalLocalUnitIndicator v)) = F ∘ e := by
    funext ξ
    unfold rationalLocalLogFourierIntegrand F
    dsimp only [comp_apply]
    rw [norm_rationalLocal_padicEquiv, ← integral_indicator hU, ← he.integral_comp j]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      change rationalLocalShiftedTest v (rationalLocalUnitIndicator v) x * star (χ (e (x * ξ))) =
        U.indicator (fun z ↦ star (χ (z * e ξ))) (e x)
      rw [shifted_unitIndicator, map_mul]
      by_cases hx : x ∈ {y : K[v] | ‖1 + y‖ = 1}
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mp hx)]
        simp
      · rw [indicator_of_notMem hx, indicator_of_notMem (mt (hmem x).mpr hx)]
        simp
  dsimp only
  rw [hF]
  obtain ⟨hi, hzero⟩ := padicTranslatedUnits_log_fourier (p[v] : ℕ)
  exact ⟨(he.integrable_comp_emb j).mpr hi, (he.integral_comp j F).trans hzero⟩

private theorem shifted_add_mul (v : V) (f g : K[v]ˣ → ℂ) (c : ℂ) (x : K[v]) :
    rationalLocalShiftedTest v (fun y ↦ f y + c * g y) x =
      rationalLocalShiftedTest v f x + c * rationalLocalShiftedTest v g x := by
  unfold rationalLocalShiftedTest
  by_cases h : ∃ z : K[v]ˣ, (z : K[v]) = 1 + x
  · obtain ⟨z, hz⟩ := h
    simp only [← hz, Units.val_injective.extend_apply, add_div, mul_div_assoc]
  · simp only [Function.extend_apply' _ _ _ h, mul_zero, add_zero]

/-- Linearity of the weighted shifted transform, with separately integrable inner integrals. -/
public theorem rationalLocalShiftedFourier_add_mul (v : V) {f g : K[v]ˣ → ℂ} (c : ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) :
    rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v (fun y ↦ f y + c * g y)) =
      fun ξ ↦ rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v f) ξ +
        c * rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v g) ξ := by
  funext ξ
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let χ (x : K[v]) := star (padicStdAddChar (p[v] : ℕ) (e (x * ξ)))
  have hχ : Continuous χ :=
    ((continuous_padicStdAddChar (p[v] : ℕ)).comp
      (e.toHomeomorph.continuous.comp (continuous_id.mul continuous_const))).star
  have hi (b : K[v]ˣ → ℂ) (hb : IsLocallyConstant b) (hbc : HasCompactSupport b) :
      Integrable (fun x ↦ rationalLocalShiftedTest v b x * χ x) ν[v] := by
    obtain ⟨hu, huc, _⟩ := rationalLocalShiftedTest_properties v hb hbc
    exact (hu.continuous.mul hχ).integrable_of_hasCompactSupport (huc.mul_right (f' := χ))
  unfold rationalLocalLogFourierIntegrand
  set J : ℂ := (↑(Real.log ‖ξ‖ / Real.log ((p[v] : ℕ) : ℝ)) : ℂ)
  change J * (∫ x, rationalLocalShiftedTest v _ x * χ x ∂ν[v]) =
    J * (∫ x, rationalLocalShiftedTest v f x * χ x ∂ν[v]) +
      c * (J * ∫ x, rationalLocalShiftedTest v g x * χ x ∂ν[v])
  simp_rw [shifted_add_mul, add_mul, mul_assoc c]
  rw [integral_add (hi f hf hfc) ((hi g hg hgc).const_mul c), integral_const_mul]
  ring

end Masullo
