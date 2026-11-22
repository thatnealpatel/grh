module

public import Theorems.FiniteCompletionFourierSquare
public import Lemmas.FiniteHeckeReflectedShift
import Lemmas.FiniteLocalBallMass

/-! # The reflected Mellin integral of the finite integer-ring Fourier test -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "d" => finiteCompletionDifferentExponent v
attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree
local notation "Diff" => differentIdeal ℤ_[p] O
local notation "C" => ((Diff : FractionalIdeal O⁰ F)⁻¹ : FractionalIdeal O⁰ F)
set_option quotPrecheck false in
local notation "B" => (O : Set F).indicator (fun _ ↦ (1 : ℂ))

private theorem mem_codifferent_iff_shift (π : Fˣ) (hπ : Valued.v.IsUniformizer (π : F)) (x : Fˣ) :
    (x : F) ∈ C ↔ ‖((π ^ d * x : Fˣ) : F)‖ ≤ 1 := by
  let t : O := ⟨(π : F), hπ.val_lt_one.le⟩
  have ht : Ideal.span {t ^ d} = Diff := by
    rw [finiteCompletion_differentIdeal_eq_maximalIdeal_pow]
    exact (Valuation.pow_Uniformizer_is_pow_generator (v := Valued.v) ⟨t, hπ⟩ d).symm
  rw [finiteCompletion_mem_codifferent_iff v (t ^ d) ht, Valued.toNormedField.norm_le_one_iff]
  rfl

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]

/-- On the reflected half-plane the Mellin pairing of the actual normalized first
transform retains the multiplicative unit mass `u_v`. Its remaining multiplier is
`a_v ^ d * q ^ (d * (1/2 - s))`, with `a_v = χ_v(π)` at this unramified place. -/
public theorem finiteCompletionFourier_reflectedMellin (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hself : ∀ x : IdeleClassGroup (𝓞 K) K, (χ x)⁻¹ = χ x)
    (hu : χ.IsUnramifiedAt v) (μ : Measure Fˣ) [μ.IsHaarMeasure] {s : ℂ} (hs : s.re < 1) :
    let g := fun x : Fˣ ↦ finiteCompletionFourier v (finiteCompletionNormalizedHaar v) B (x : F) *
      (χ.restrict v (x : F))⁻¹ * (‖(x : F)‖ : ℂ) ^ (1 - s)
    Integrable g μ ∧ (∫ x, g x ∂μ) = (μ.real (finiteLocalUnitSet v) : ℂ) *
      finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v (1 - s) * finiteHeckeCoefficient χ v ^ d *
      (finitePlaceNorm v : ℂ) ^ ((d : ℂ) * (1 / 2 - s)) := by
  intro g
  obtain ⟨t, ht⟩ := (Valued.v : Valuation F (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (t : F) ht.ne_zero
  have he : g = finiteHeckeReflectedShiftIntegrand χ v π s := by
    funext x
    dsimp only [g, finiteHeckeReflectedShiftIntegrand]
    rw [finiteCompletionNormalizedHaar_fourier_integers]
    have h := mem_codifferent_iff_shift v π ht x
    by_cases hx : (x : F) ∈ C
    · rw [indicator_of_mem hx, indicator_of_mem (h.1 hx), mul_one]
      simp [finitePlaceNorm]
    · rw [indicator_of_notMem hx, indicator_of_notMem (mt h.2 hx)]
      simp
  rw [he]
  exact finiteHeckeReflectedShift_unramified χ hχ hself v μ
    (finiteLocalUnitSet_measure_bounds v μ).2.ne hu π ht hs

/-- The absolute-convergence half-plane is sharp for multiplicative Haar. At
its boundary and beyond, the integrand's norm is bounded below by the positive
additive integer mass on a punctured ball of infinite multiplicative mass. -/
public theorem finiteCompletionFourier_reflectedMellin_integrable_iff (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hself : ∀ x : IdeleClassGroup (𝓞 K) K, (χ x)⁻¹ = χ x)
    (hu : χ.IsUnramifiedAt v) (μ : Measure Fˣ) [μ.IsHaarMeasure] (s : ℂ) :
    Integrable (fun x : Fˣ ↦ finiteCompletionFourier v (finiteCompletionNormalizedHaar v) B (x : F) *
      (χ.restrict v (x : F))⁻¹ * (‖(x : F)‖ : ℂ) ^ (1 - s)) μ ↔ s.re < 1 := by
  refine ⟨fun hg ↦ ?_, fun hs ↦ (finiteCompletionFourier_reflectedMellin v χ hχ hself hu μ hs).1⟩
  by_contra! hs
  let U := {x : Fˣ | ‖(x : F)‖ ≤ 1}
  have hU : MeasurableSet U := (isClosed_le (continuous_norm.comp Units.continuous_val)
    continuous_const).measurableSet
  let m := (finiteCompletionNormalizedHaar v).real (O : Set F)
  have hm : 0 < m := finiteCompletionIntegers_measureReal_pos v _
  have hi : IntegrableOn (fun _ ↦ m) U μ := by
    apply Integrable.mono (hg.integrableOn (s := U)) aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem hU] with x hx
    have hx' : ‖(x : F)‖ ≤ 1 := hx
    have hxO : (x : F) ∈ O := Valued.toNormedField.norm_le_one_iff.mp hx'
    rw [finiteCompletionFourier_integers, indicator_of_mem (finiteCompletion_integers_subset_codifferent v hxO),
      mul_one, norm_mul, norm_mul, Complex.norm_real, norm_inv, norm_heckeRestrict_of_unitary χ hχ v x.ne_zero,
      inv_one, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr x.ne_zero)]
    change ‖m‖ ≤ ‖m‖ * _
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (norm_pos_iff.mpr x.ne_zero) hx' (by simpa using sub_nonpos.mpr hs))
  have hf := ((integrableOn_const_iff («C» := m)).mp hi).resolve_left (by simpa using hm.ne')
  exact hf.ne (finiteLocalBall_measure_top v μ)

end Masullo
