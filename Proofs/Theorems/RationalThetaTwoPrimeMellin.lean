module

public import Theorems.RationalThetaMellinKernel
public import Theorems.RationalThetaPrimeMask
import all Theorems.RationalThetaRadialCore
import Lemmas.IdeleStageNormCoordinates
import Lemmas.SinglePlaceNorm
import Mathlib.MeasureTheory.Group.Integral

/-! # Raw idelic Mellin transform of the rational two-prime unit cut

For the repaired disjoint unit cut (Masullo, §1.3.2, p. 26), remove the
nonunit part of integral support by a uniformizer translation at each tested
prime. This argument uses the raw Haar integral, not class periodization.
-/

open NumberField IsDedekindDomain MeasureTheory Set
open scoped Classical RestrictedProduct SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "πᵥ" => rationalThetaRadialUniformizer

private theorem uniformizer_mul_real (v : V) (a : J) :
    rationalAdeleReal ((πᵥ v * a : J) : A) = rationalAdeleReal (a : A) := by
  rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
  congr 1
  change (1 : Rat.infinitePlace.Completion) * (a : A).1 Rat.infinitePlace = _
  rw [one_mul]

private theorem uniformizer_mul_finite_of_ne (v w : V) (a : J) (hw : w ≠ v) :
    ((πᵥ v * a : J) : A).2 w = (a : A).2 w := by
  change RestrictedProduct.mulSingle (fun p : V ↦ p.adicCompletionIntegers ℚ) v
    (rationalLocalUniformizer v : v.adicCompletion ℚ) w * (a : A).2 w = _
  rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, one_mul]

private theorem uniformizer_mul_finite_norm_lt_one_iff (v : V) (a : J) :
    ‖((πᵥ v * a : J) : A).2 v‖ < 1 ↔ ‖(a : A).2 v‖ ≤ 1 := by
  have hnorm : ‖((πᵥ v * a : J) : A).2 v‖ =
      (Rat.HeightOneSpectrum.primesEquiv v : ℝ)⁻¹ * ‖(a : A).2 v‖ := by
    change ‖RestrictedProduct.mulSingle (fun p : V ↦ p.adicCompletionIntegers ℚ) v
      (rationalLocalUniformizer v : v.adicCompletion ℚ) v * (a : A).2 v‖ = _
    rw [RestrictedProduct.mulSingle_eq_same, norm_mul, ← norm_idele_ofAdicCompletion v,
      ← ideleNorm_apply, ← rationalThetaRadialUniformizer, ideleNorm_rationalThetaRadialUniformizer]
  -- The local norm is an integral power of the inverse prime.
  let x := ideleFiniteCoordinate ℚ a v
  obtain ⟨k, hk⟩ := mem_iUnion.mp (show x ∈ ⋃ k : ℤ, rationalLocalNormShell v k by
    rw [RationalLocalNormShell.iUnion_eq_univ]; exact mem_univ _)
  change ‖(a : A).2 v‖ = _ at hk
  have h₀ := inv_pos.mpr (RationalLocalNormShell.prime_pos v)
  have h₁ := inv_lt_one_of_one_lt₀ (RationalLocalNormShell.one_lt_prime v)
  rw [hnorm, hk, mul_comm, ← zpow_add_one₀ h₀.ne',
    zpow_lt_one_iff_right_of_lt_one₀ h₀ h₁, zpow_le_one_iff_right_of_lt_one₀ h₀ h₁]
  omega

private theorem uniformizer_mul_mem_integral_nonunit_iff (p : Nat.Primes) (a : J) :
    (let x : A := ((πᵥ (vₚ p) * a : J) : A)
     x ∈ rationalIntegralAdeles ∧ x ∉ rationalAdelePrimeUnits p) ↔
    (a : A) ∈ rationalIntegralAdeles := by
  let v := vₚ p
  let x : A := ((πᵥ v * a : J) : A)
  have hi (y : A) : y ∈ rationalIntegralAdeles ↔ ∀ w : V, ‖y.2 w‖ ≤ 1 := by
    change (∀ w : V, y.2 w ∈ w.adicCompletionIntegers ℚ) ↔ _
    simp only [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]
  have hu : x ∈ rationalAdelePrimeUnits p ↔ ‖x.2 v‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.symm
  change (x ∈ rationalIntegralAdeles ∧ x ∉ rationalAdelePrimeUnits p) ↔ _
  rw [hi, hi, hu]
  have h := uniformizer_mul_finite_norm_lt_one_iff v a
  constructor
  · rintro ⟨hx, hxu⟩ w
    by_cases hw : w = v
    · subst w
      exact h.mp (lt_of_le_of_ne (hx v) hxu)
    · rw [← uniformizer_mul_finite_of_ne v w a hw]
      exact hx w
  · intro ha
    have hx := h.mpr (ha v)
    refine ⟨fun w ↦ ?_, hx.ne⟩
    by_cases hw : w = v
    · subst w
      exact hx.le
    · change ‖((πᵥ v * a : J) : A).2 w‖ ≤ 1
      rw [uniformizer_mul_finite_of_ne v w a hw]
      exact ha w

private theorem uniformizer_mul_norm_cpow (p : Nat.Primes) (a : J) (z : ℂ) :
    ((ideleNorm (πᵥ (vₚ p) * a) : ℝ) : ℂ) ^ z =
      ((p : ℝ) : ℂ) ^ (-z) * ((ideleNorm a : ℝ) : ℂ) ^ z := by
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have ha : 0 ≤ ideleNorm a := (ideleClassNorm_mk a ▸ ideleClassNorm_pos (QuotientGroup.mk a)).le
  have hu : ideleNorm (πᵥ (vₚ p)) = (p : ℝ)⁻¹ := by
    rw [ideleNorm_rationalThetaRadialUniformizer, Equiv.apply_symm_apply]
  rw [map_mul, hu, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hp) ha,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hp, Complex.cpow_neg]

local notation "W(" a "," z ")" => ((ideleNorm (a : J) : ℝ) : ℂ) ^ (z : ℂ)

-- An existing mask `U` may be kept through the cut if it is invariant under
-- this translation. We use this first with `univ`, and then with the other
-- prime's unit condition.
private theorem prime_cut_density (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) (z : ℂ) (U : Set A)
    (hU : ∀ x : J, ((πᵥ (vₚ p) * x : J) : A) ∈ U ↔ (x : A) ∈ U) (a : J) :
    let f (x : J) := U.indicator (rationalAdeleUnramified b) (x : A) * W(x, z)
    (rationalAdelePrimeUnits p ∩ U).indicator (rationalAdeleUnramified b) (a : A) * W(a, z) =
      f a - ((p : ℝ) : ℂ) ^ (-z) * f ((πᵥ (vₚ p))⁻¹ * a) := by
  let x := (πᵥ (vₚ p))⁻¹ * a
  have ha : πᵥ (vₚ p) * x = a := by simp [x]
  have hmem := uniformizer_mul_mem_integral_nonunit_iff p x
  have hreal := uniformizer_mul_real (vₚ p) x
  have hpow := uniformizer_mul_norm_cpow p x z
  have hkeep := hU x
  simp only [ha] at hmem hreal hpow hkeep
  dsimp only
  change _ = _ - _ * (U.indicator (rationalAdeleUnramified b) (x : A) * W(x, z))
  simp only [Set.indicator_apply, Set.mem_inter_iff, rationalAdeleUnramified, ← hreal, ← hkeep]
  by_cases hu : (a : A) ∈ U
  · by_cases hi : (a : A) ∈ rationalIntegralAdeles <;>
      by_cases hp : (a : A) ∈ rationalAdelePrimeUnits p <;>
      simp [hu, hi, hp, ← hmem, hpow, mul_left_comm]
  · simp [hu]

set_option linter.concreteInstances false

variable [MeasurableSpace J] [BorelSpace J]

private theorem prime_cut_integral (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) (z : ℂ) (U : Set A)
    (hU : ∀ x : J, ((πᵥ (vₚ p) * x : J) : A) ∈ U ↔ (x : A) ∈ U)
    (hf : Integrable (fun a : J ↦ U.indicator (rationalAdeleUnramified b) (a : A) * W(a, z))
      rationalIdeleHaar) :
    let g (a : J) := (rationalAdelePrimeUnits p ∩ U).indicator
      (rationalAdeleUnramified b) (a : A) * W(a, z)
    Integrable g rationalIdeleHaar ∧ (∫ a, g a ∂rationalIdeleHaar) =
      (1 - ((p : ℝ) : ℂ) ^ (-z)) *
        ∫ a : J, U.indicator (rationalAdeleUnramified b) (a : A) * W(a, z) ∂rationalIdeleHaar := by
  let f (a : J) := U.indicator (rationalAdeleUnramified b) (a : A) * W(a, z)
  let c := ((p : ℝ) : ℂ) ^ (-z)
  let u := (πᵥ (vₚ p))⁻¹
  have hi : Integrable (fun a ↦ c * f (u * a)) rationalIdeleHaar :=
    ((measurePreserving_mul_left rationalIdeleHaar u).integrable_comp_of_integrable hf).const_mul c
  simp only [prime_cut_density p b z U hU]
  exact ⟨hf.sub hi, by rw [integral_sub hf hi, integral_const_mul, integral_mul_left_eq_self,
    sub_mul, one_mul]⟩

/-- On the convergence half-plane the repaired joint unit cut is absolutely
integrable, and its raw idelic Mellin integral has the two reciprocal Euler
factors. There are no moment or LF-space hypotheses on the Schwartz tensor. -/
public theorem rationalTwoPrimeMaskedZetaIntegral (p q : Nat.Primes) (hpq : p ≠ q)
    (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 1 < z.re) :
    Integrable (fun a : J ↦ (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q).indicator
      (rationalAdeleUnramified b) (a : A) * W(a, z)) rationalIdeleHaar ∧
    (∫ a : J, (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q).indicator
      (rationalAdeleUnramified b) (a : A) * W(a, z) ∂rationalIdeleHaar) =
    (1 - ((p : ℝ) : ℂ) ^ (-z)) * (1 - ((q : ℝ) : ℂ) ^ (-z)) *
      ∫ a : J, rationalAdeleUnramified b (a : A) * W(a, z) ∂rationalIdeleHaar := by
  have hq := prime_cut_integral q b z univ (fun _ ↦ iff_of_true trivial trivial)
    (by simpa using integrable_rationalUnramifiedZetaIntegrand b hz)
  simp only [inter_univ, indicator_univ] at hq
  have hU (x : J) : ((πᵥ (vₚ p) * x : J) : A) ∈ rationalAdelePrimeUnits q ↔
      (x : A) ∈ rationalAdelePrimeUnits q := by
    have hne : vₚ q ≠ vₚ p := fun h ↦ hpq ((vₚ).injective h).symm
    unfold rationalAdelePrimeUnits
    simp only [Set.mem_ofPred_eq, uniformizer_mul_finite_of_ne _ _ _ hne]
  obtain ⟨hi, he⟩ := prime_cut_integral p b z (rationalAdelePrimeUnits q) hU hq.1
  exact ⟨hi, by rw [he, hq.2, mul_assoc]⟩

end Masullo
