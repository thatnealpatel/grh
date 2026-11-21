module

public import Props.RationalAdeleStageCoordinates
import Lemmas.RationalIdeleReal

/-! # Support, phase, and Jacobian for Fourier on rational stage boxes -/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "W" => rationalFiniteIntegralAdeles
local notation "κ" => algebraMap ℚ F
local notation "eℝ" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The real scale of the stage box is one, so its norm is the finite box mass.
Multiplying by the diagonal `M⁻¹` preserves the norm and leaves only the real
coordinate `M⁻¹`. -/
public theorem ideleNorm_rationalAdeleStageScale {M : ℕ} (hM : 0 < M) :
    ideleNorm (rationalAdeleStageScale M hM) = (M : ℝ)⁻¹ := by
  have hq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  let r := (Units.mk0 (M : ℚ) hq)⁻¹
  let p := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r
  let g := rationalAdeleStageScale M hM
  have hp : ideleNorm p = 1 := by
    rw [ideleNorm_apply]
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero
  have hfin : ((p * g : IdeleGroup (𝓞 ℚ) ℚ) : A).2 = 1 := by
    change κ (M : ℚ)⁻¹ * κ (M : ℚ) = 1
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have habs := ideleNorm_eq_abs_rationalIdeleReal (p * g) (fun v ↦ by
    rw [hfin]
    exact map_one (Valued.v : Valuation (v.adicCompletion ℚ) _))
  have hreal : rationalIdeleReal g = 1 := by
    change eℝ 1 = 1
    exact map_one _
  rw [map_mul, hp, one_mul, rationalIdeleReal_principal_mul, hreal, mul_one] at habs
  change ideleNorm g = |(((M : ℚ)⁻¹ : ℚ) : ℝ)| at habs
  simpa only [Rat.cast_inv, Rat.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ)⁻¹)]
    using habs

/-- The unramified frequency factor scaled by the stage idele is supported on
`M⁻¹ ℤ̂` in the finite part, with unchanged real frequency. -/
public theorem rationalAdeleUnramified_stageScale {M : ℕ} (hM : 0 < M)
    (b : 𝓢(ℝ, ℂ)) (y : A) :
    rationalAdeleUnramified b ((rationalAdeleStageScale M hM : A) * y) =
      (rationalAdeleStageSupport M).indicator (fun x ↦ b (rationalAdeleReal x)) y := by
  let g := rationalAdeleStageScale M hM
  have hf : (g : A).2 = (M : F) := map_natCast κ M
  have hm : (g : A) * y ∈ rationalIntegralAdeles ↔ y ∈ rationalAdeleStageSupport M := by
    rw [rationalAdeleStageSupport_eq_preimage]
    change (g : A).2 * y.2 ∈ W ↔ (M : F) * y.2 ∈ W
    rw [hf]
  have hr : rationalAdeleReal ((g : A) * y) = rationalAdeleReal y := by
    rw [rationalAdeleReal_apply ((g : A) * y)]
    change eℝ (1 * y.1 Rat.infinitePlace) = _
    rw [one_mul, rationalAdeleReal_apply]
  rw [rationalAdeleUnramified]
  by_cases hy : y ∈ rationalAdeleStageSupport M
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hm.mpr hy), hr]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt hm.mp hy)]

/-- On a frequency cell the translation character is constant. Changing the
frequency representative by `M z` adds the integral adele `j z` to its finite
pairing with the center `j/M`. -/
public theorem rationalAdeleAddChar_stageCenter_mul {M : ℕ} (hM : 0 < M)
    (j k : Fin (M ^ 2)) {y : A} (hy : y ∈ rationalAdeleStageCell M k) :
    rationalAdeleAddChar (rationalAdeleStageCenter M j * y) = rationalFiniteAdeleAddChar
      (rationalAdeleStageRepresentative M j * rationalAdeleStageRepresentative M k) := by
  obtain ⟨z, hz, he⟩ := (mem_rationalAdeleStageCell_iff hM k y).mp hy
  have hn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : rationalAdeleReal (rationalAdeleStageCenter M j * y) = 0 := by
    rw [rationalAdeleReal_apply]
    change eℝ (0 * y.1 Rat.infinitePlace) = _
    rw [zero_mul, map_zero]
  have hM' : rationalAdeleStageRepresentative M j * (M : F) = (j.val : F) := by
    rw [rationalAdeleStageRepresentative, ← map_natCast κ M, ← map_mul,
      div_mul_cancel₀ _ hn, map_natCast]
  have hone : rationalFiniteAdeleAddChar ((j.val : F) * z) = 1 := by
    have hz' : (j.val : F) * z ∈ W := by
      simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hz j.val
    simpa using rationalFiniteAdeleAddChar_eq_prod _ ∅ (fun v _ ↦ hz' v)
  rw [rationalAdeleAddChar_eq_finite hr]
  change rationalFiniteAdeleAddChar (rationalAdeleStageRepresentative M j * y.2) = _
  rw [he, mul_add, ← mul_assoc _ (M : F) z, hM', AddChar.map_add_eq_mul, hone, mul_one]

end Masullo
