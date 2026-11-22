module

public import Theorems.FiniteCompletionDifferentScale
public import Theorems.FiniteHeckeLocalZeta
import Mathlib.MeasureTheory.Group.Integral

/-! # Reflected finite Hecke zeta integrals on the shifted unit ball -/

open NumberField IsDedekindDomain MeasureTheory Set
open scoped ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "G" v => (F v)ˣ

/-- The reflected weight supported where multiplication by `π ^ d` lands in the unit ball,
with `d` the local different exponent. -/
@[expose] public noncomputable def finiteHeckeReflectedShiftIntegrand
    (χ : HeckeCharacter (𝓞 K) K) (v : Places) (π : G v) (s : ℂ) : (G v) → ℂ :=
  {x : G v | ‖((π ^ finiteCompletionDifferentExponent v * x : G v) : F v)‖ ≤ 1}.indicator
    (fun x ↦ ((Real.sqrt (finitePlaceNorm v ^ finiteCompletionDifferentExponent v) : ℝ) : ℂ)⁻¹ *
      (χ.restrict v (x : F v))⁻¹ * (‖(x : F v)‖ : ℂ) ^ (1 - s))

private theorem reflectedShift_scale {q : ℝ} (hq : 0 < q) (d : ℕ) (s : ℂ) :
    (Real.sqrt (q ^ d) : ℂ)⁻¹ * ((q ^ d : ℝ) : ℂ) ^ (1 - s) =
      (q : ℂ) ^ ((d : ℂ) * (1 / 2 - s)) := by
  have hqd : 0 < q ^ d := pow_pos hq _
  have hqd₀ : ((q ^ d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqd.ne'
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hqd.le, hhalf, ← Complex.cpow_neg,
    ← Complex.cpow_add _ _ hqd₀,
    show -(1 / 2 : ℂ) + (1 - s) = 1 / 2 - s by ring,
    ← Complex.ofReal_natCast d, Complex.cpow_mul_ofReal_nonneg hq.le, Real.rpow_natCast]

/-- On `Re s < 1`, at an unramified place, the reflected shifted-ball integrand is integrable.
The substitution `y = π ^ d * x` preserves multiplicative measure and reduces the integral to
unit-ball local zeta at `1 - s`, with the different contributing `a_v ^ d * q ^ (d * (1/2 - s))`. -/
public theorem finiteHeckeReflectedShift_unramified (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hself : ∀ x : IdeleClassGroup (𝓞 K) K, (χ x)⁻¹ = χ x)
    (v : Places) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (μ : Measure (G v)) [Measure.IsMulLeftInvariant μ] (hμ : μ (finiteLocalUnitSet v) ≠ ∞)
    (hu : χ.IsUnramifiedAt v) (π : G v) (hπ : Valued.v.IsUniformizer (π : F v))
    {s : ℂ} (hs : s.re < 1) :
    Integrable (finiteHeckeReflectedShiftIntegrand χ v π s) μ ∧
      (∫ x, finiteHeckeReflectedShiftIntegrand χ v π s x ∂μ) =
        (μ.real (finiteLocalUnitSet v) : ℂ) *
          finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v (1 - s) *
          finiteHeckeCoefficient χ v ^ finiteCompletionDifferentExponent v *
          (finitePlaceNorm v : ℂ) ^ ((finiteCompletionDifferentExponent v : ℂ) * (1 / 2 - s)) := by
  classical
  let d := finiteCompletionDifferentExponent v
  let q := finitePlaceNorm v
  let a := finiteHeckeCoefficient χ v
  let b := π ^ d
  let B : Set (G v) := {y | ‖(y : F v)‖ ≤ 1}
  let f : (G v) → ℂ := B.indicator (fun y ↦ χ.restrict v (y : F v) * (‖(y : F v)‖ : ℂ) ^ (1 - s))
  let g := finiteHeckeReflectedShiftIntegrand χ v π s
  let c : ℂ := a ^ d * (q : ℂ) ^ ((d : ℂ) * (1 / 2 - s))
  have hq : 0 < q := (by norm_num : (0 : ℝ) < 2).trans_le (two_le_finitePlaceNorm v)
  have hs' : 0 < (1 - s).re := by simpa using sub_pos.mpr hs
  obtain ⟨hf, hval⟩ := finiteHeckeLocalZeta_unramified χ hχ v μ hμ hu hs'
  change Integrable f μ at hf
  change (∫ y, f y ∂μ) = (μ.real (finiteLocalUnitSet v) : ℂ) * finiteHeckeEulerFactor
    (finiteHeckeCoefficient χ) v (1 - s) at hval
  have ha : χ.restrict v (π : F v) = a := by
    dsimp only [a]
    rw [finiteHeckeCoefficient, ite_eq_left hu, hu.localValue_eq _ hπ]
  have hself' (y : G v) : (χ.restrict v (y : F v))⁻¹ = χ.restrict v (y : F v) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    exact hself (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v y)
  -- In the inverse substitution `x = b⁻¹ * y`, the inverse character contributes `a ^ d`.
  have hchar (y : G v) : (χ.restrict v ((b⁻¹ * y : G v) : F v))⁻¹ =
      a ^ d * χ.restrict v (y : F v) := by
    dsimp only [b]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      ← MulChar.inv_apply', MulChar.inv_apply_eq_inv', map_pow, mul_inv_rev, inv_inv,
      ha, hself', mul_comm]
  have hnorm (y : G v) : ‖((b⁻¹ * y : G v) : F v)‖ = q ^ d * ‖(y : F v)‖ := by
    dsimp only [b]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_mul,
      norm_inv, norm_pow, norm_uniformizer_eq_inv_finitePlaceNorm v _ hπ, inv_pow, inv_inv]
  have htranslate (y : G v) : g (b⁻¹ * y) = c * f y := by
    have hsupport : b⁻¹ * y ∈ {x : G v | ‖((b * x : G v) : F v)‖ ≤ 1} ↔ y ∈ B := by
      change ‖((b * (b⁻¹ * y) : G v) : F v)‖ ≤ 1 ↔ ‖(y : F v)‖ ≤ 1
      simp
    change {x : G v | ‖((b * x : G v) : F v)‖ ≤ 1}.indicator
      (fun x ↦ (Real.sqrt (q ^ d) : ℂ)⁻¹ * (χ.restrict v (x : F v))⁻¹ *
        (‖(x : F v)‖ : ℂ) ^ (1 - s)) (b⁻¹ * y) = c * B.indicator _ y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem (hsupport.mpr hy), indicator_of_mem hy, hchar, hnorm, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg hq.le d) (norm_nonneg _)]
      dsimp only [c]
      rw [← reflectedShift_scale hq d s]
      ring
    · rw [indicator_of_notMem (fun h ↦ hy (hsupport.mp h)), indicator_of_notMem hy, mul_zero]
  -- Express the original integrand as the scalar multiple pulled back along `y = b * x`.
  have hpull : g = fun x ↦ c * f (b * x) := by
    funext x
    simpa using htranslate (b * x)
  change Integrable g μ ∧ (∫ x, g x ∂μ) = _
  refine ⟨?_, ?_⟩
  · rw [hpull]
    exact (measurePreserving_mul_left μ b).integrable_comp_of_integrable (hf.const_mul c)
  · calc
      (∫ x, g x ∂μ) = ∫ y, g (b⁻¹ * y) ∂μ := (integral_mul_left_eq_self g b⁻¹).symm
      _ = c * (∫ y, f y ∂μ) := by simp_rw [htranslate, integral_const_mul]
      _ = _ := by rw [hval]; dsimp only [c, a, q, d]; ring

end Masullo
