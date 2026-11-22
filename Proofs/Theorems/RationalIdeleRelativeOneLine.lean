module

public import Theorems.RationalIdeleHaarComparison
public import Lemmas.RationalIntegralAdeles
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Lemmas.RationalLocalNormShell
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Failure of absolute convergence on the rational relative 1-line

For Masullo's Proposition 3.4.2.1, p. 145, the unramified Gaussian tensor
already has infinite absolute integral at `1 + 2 I`. Translate the unit-mass
positive real strip by a uniformizer at each prime. The resulting shells
are disjoint and the absolute integral on each is bounded below by a fixed
positive constant times the reciprocal of that prime.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Classical ENNReal Function

namespace Masullo

local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
local notation "P[" v "]" => (((pOf v : Nat.Primes) : ℕ) : ℝ)

/-- The real Gaussian times the integral-finite indicator, restricted to rational ideles. -/
@[expose] public noncomputable def rationalIdeleGaussian (a : J) : ℝ :=
  (rationalIntegralAdeles : Set A).indicator
    (fun b ↦ Real.exp (-Real.pi * rationalAdeleReal b ^ 2)) (a : A)

/-- The complex Gaussian zeta integrand on the full rational idele group. -/
@[expose] public noncomputable def rationalIdeleGaussianZetaIntegrand (s : ℂ) (a : J) : ℂ :=
  (rationalIdeleGaussian a : ℂ) * (ideleNorm a : ℂ) ^ s

private theorem gaussian_nonneg (a : J) : 0 ≤ rationalIdeleGaussian a :=
  indicator_nonneg (fun b _ ↦ (Real.exp_pos (-Real.pi * rationalAdeleReal b ^ 2)).le) _

private theorem idelicNorm_pos (a : J) : 0 < ideleNorm a := by
  rw [← ideleClassNorm_mk]
  exact ideleClassNorm_pos (QuotientGroup.mk a)

/-- At real exponent one the complex integrand has the indicated nonnegative real modulus. -/
public theorem norm_rationalIdeleGaussianZetaIntegrand_of_re_eq_one {s : ℂ} (hs : s.re = 1)
    (a : J) :
    ‖rationalIdeleGaussianZetaIntegrand s a‖ = rationalIdeleGaussian a * ideleNorm a := by
  rw [rationalIdeleGaussianZetaIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussian_nonneg a), Complex.norm_cpow_eq_rpow_re_of_pos (idelicNorm_pos a),
    hs, Real.rpow_one]

private noncomputable def primeMultiplier (v : V) : J :=
  IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (rationalLocalUniformizer v)

private theorem norm_uniformizer (v : V) :
    ‖(rationalLocalUniformizer v : v.adicCompletion ℚ)‖ = P[v]⁻¹ := by
  have h : rationalLocalUniformizer v ∈ rationalLocalNormShell v 1 := by
    rw [RationalLocalNormShell.eq_translate]
    exact ⟨1, ⟨1, map_one _⟩, by simp⟩
  change ‖(rationalLocalUniformizer v : v.adicCompletion ℚ)‖ = P[v]⁻¹ ^ (1 : ℤ) at h
  simpa only [zpow_one] using h

private theorem ideleNorm_primeMultiplier (v : V) : ideleNorm (primeMultiplier v) = P[v]⁻¹ := by
  rw [primeMultiplier, ideleNorm_apply, norm_idele_ofAdicCompletion, norm_uniformizer]

private theorem real_primeMultiplier_mul (v : V) (a : J) :
    rationalIdeleReal (primeMultiplier v * a) = rationalIdeleReal a := by
  unfold rationalIdeleReal
  rw [show ((primeMultiplier v * a : J) : A).1 Rat.infinitePlace =
    1 * (a : A).1 Rat.infinitePlace from rfl, one_mul]

private theorem finite_norm_primeMultiplier (v w : V) :
    ‖(primeMultiplier v : A).2 w‖ = if w = v then P[v]⁻¹ else 1 := by
  classical
  change ‖RestrictedProduct.mulSingle (fun u : V ↦ u.adicCompletionIntegers ℚ) v
    (rationalLocalUniformizer v : v.adicCompletion ℚ) w‖ = _
  split_ifs with hw
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, norm_uniformizer]
  · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, norm_one]

private noncomputable def unitStrip : Set J :=
  rationalIdeleUnitWindow ∩ {a | ideleNorm a ∈ Icc 1 (Real.exp 1)}

private theorem real_eq_norm_of_mem_unitStrip {a : J} (ha : a ∈ unitStrip) :
    rationalIdeleReal a = ideleNorm a := by
  rw [ideleNorm_eq_abs_rationalIdeleReal _ (finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow ha.1),
    abs_of_pos ha.1.1]

private noncomputable def primeShell (v : V) : Set J :=
  (fun a ↦ primeMultiplier v * a) '' unitStrip

private theorem finite_norm_of_mem_primeShell {v : V} {a : J} (ha : a ∈ primeShell v) (w : V) :
    ‖(a : A).2 w‖ = if w = v then P[v]⁻¹ else 1 := by
  classical
  rcases ha with ⟨b, hb, rfl⟩
  have hw : ‖(b : A).2 w‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hb.1 w)
  change ‖(primeMultiplier v : A).2 w * (b : A).2 w‖ = _
  rw [norm_mul, hw, mul_one, finite_norm_primeMultiplier]

private theorem primeShell_disjoint : Pairwise (Disjoint on primeShell) := by
  classical
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro a hav haw
  have h1 := finite_norm_of_mem_primeShell hav v
  have h2 := finite_norm_of_mem_primeShell haw v
  rw [ite_eq_left rfl] at h1
  rw [ite_eq_right hvw] at h2
  exact (inv_lt_one_of_one_lt₀ (RationalLocalNormShell.one_lt_prime v)).ne (h1.symm.trans h2)

private theorem primeShell_integralFinite {v : V} {a : J} (ha : a ∈ primeShell v) :
    (a : A) ∈ rationalIntegralAdeles := by
  classical
  intro w
  rw [mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff,
    finite_norm_of_mem_primeShell ha]
  split_ifs
  · exact (inv_lt_one_of_one_lt₀ (RationalLocalNormShell.one_lt_prime v)).le
  · exact le_rfl

private theorem primeShell_lower {v : V} {a : J} (ha : a ∈ primeShell v) :
    Real.exp (-Real.pi * (Real.exp 1) ^ 2) * P[v]⁻¹ ≤ rationalIdeleGaussian a * ideleNorm a := by
  have hint := primeShell_integralFinite ha
  rcases ha with ⟨b, hb, rfl⟩
  have hr : rationalIdeleReal b ∈ Icc 1 (Real.exp 1) :=
    (real_eq_norm_of_mem_unitStrip hb).symm ▸ hb.2
  have hg : Real.exp (-Real.pi * (Real.exp 1) ^ 2) ≤
      rationalIdeleGaussian (primeMultiplier v * b) := by
    rw [rationalIdeleGaussian, indicator_of_mem hint, rationalAdeleReal_apply]
    change _ ≤ Real.exp (-Real.pi * rationalIdeleReal (primeMultiplier v * b) ^ 2)
    rw [real_primeMultiplier_mul, Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (zero_le_one.trans hr.1) hr.2 2)
      (neg_nonpos.mpr Real.pi_pos.le)
  have hn : P[v]⁻¹ ≤ ideleNorm (primeMultiplier v * b) := by
    rw [map_mul, ideleNorm_primeMultiplier]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hb.2.1 (inv_nonneg.mpr (RationalLocalNormShell.prime_pos v).le)
  exact mul_le_mul hg hn (by positivity) (gaussian_nonneg _)

set_option linter.concreteInstances false

variable [MeasurableSpace J] [BorelSpace J]

private theorem measurableSet_primeShell (v : V) : MeasurableSet (primeShell v) := by
  have hb : MeasurableSet unitStrip := isOpen_rationalIdeleUnitWindow.measurableSet.inter
    (continuous_ideleNorm.measurable measurableSet_Icc)
  exact (MeasurableEquiv.mulLeft (primeMultiplier v)).measurableSet_image.mpr hb

private theorem measure_primeShell (v : V) : rationalIdeleHaar (primeShell v) = 1 := by
  rw [← measure_preimage_mul rationalIdeleHaar (primeMultiplier v) (primeShell v), primeShell,
    Set.preimage_image_eq _ (mul_right_injective _)]
  exact rationalIdeleHaar_unitStrip

private theorem primeShell_lintegral_lower (v : V) :
    ENNReal.ofReal (Real.exp (-Real.pi * (Real.exp 1) ^ 2) * P[v]⁻¹) ≤
      ∫⁻ a in primeShell v, ENNReal.ofReal (rationalIdeleGaussian a * ideleNorm a) ∂rationalIdeleHaar := by
  rw [← mul_one (ENNReal.ofReal _), ← measure_primeShell v, ← setLIntegral_const]
  exact setLIntegral_mono' (measurableSet_primeShell v) fun _ ha ↦
    ENNReal.ofReal_le_ofReal (primeShell_lower ha)

/-- The nonnegative Gaussian times the finite indicator times the idelic norm has infinite
integral on the full rational idele group for its calibrated Haar measure. -/
public theorem lintegral_rationalIdeleGaussian_mul_ideleNorm_eq_top :
    (∫⁻ a, ENNReal.ofReal (rationalIdeleGaussian a * ideleNorm a) ∂rationalIdeleHaar) = ∞ := by
  let C : ℝ := Real.exp (-Real.pi * (Real.exp 1) ^ 2)
  let e : V ≃ Nat.Primes := pOf
  let s := fun p : Nat.Primes ↦ primeShell (e.symm p)
  let f := fun a : J ↦ ENNReal.ofReal (rationalIdeleGaussian a * ideleNorm a)
  have hC : 0 < C := Real.exp_pos _
  have hsum : (∑' p : Nat.Primes, ENNReal.ofReal (1 / (p : ℝ))) = ∞ := by
    by_contra h
    apply Nat.Primes.not_summable_one_div
    have hpos (p : Nat.Primes) : 0 ≤ (1 / (p : ℝ)) := by positivity
    simpa only [ENNReal.toReal_ofReal (hpos _)] using ENNReal.summable_toReal h
  have hs : Pairwise (Disjoint on s) := fun _ _ hp ↦ primeShell_disjoint (e.symm.injective.ne hp)
  apply top_unique
  calc
    ∞ = ∑' p : Nat.Primes, ENNReal.ofReal C * ENNReal.ofReal (1 / (p : ℝ)) := by
      rw [ENNReal.tsum_mul_left, hsum, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    _ ≤ ∑' p : Nat.Primes, ∫⁻ a in s p, f a ∂rationalIdeleHaar := by
      apply tsum_le_tsum
      intro p
      change ENNReal.ofReal C * ENNReal.ofReal (1 / (p : ℝ)) ≤
        ∫⁻ a in s p, f a ∂rationalIdeleHaar
      rw [← ENNReal.ofReal_mul hC.le]
      have hep : pOf (e.symm p) = p := e.apply_symm_apply p
      simpa only [s, f, C, one_div, hep] using primeShell_lintegral_lower (e.symm p)
    _ = ∫⁻ a in ⋃ p, s p, f a ∂rationalIdeleHaar :=
      (lintegral_iUnion (fun p ↦ measurableSet_primeShell (e.symm p)) hs f).symm
    _ ≤ ∫⁻ a, f a ∂rationalIdeleHaar := setLIntegral_le_lintegral _ _

/-- The Gaussian times the finite indicator times the norm is not Haar integrable. -/
public theorem not_integrable_rationalIdeleGaussian_mul_ideleNorm :
    ¬ Integrable (fun a ↦ rationalIdeleGaussian a * ideleNorm a) rationalIdeleHaar := by
  intro h
  have hf := (hasFiniteIntegral_iff_ofReal (ae_of_all rationalIdeleHaar fun a ↦
    mul_nonneg (gaussian_nonneg a) (idelicNorm_pos a).le)).mp h.hasFiniteIntegral
  rw [lintegral_rationalIdeleGaussian_mul_ideleNorm_eq_top] at hf
  exact (lt_irrefl _) hf

/-- In the Gaussian example no twist with real exponent one is Lebesgue integrable. -/
public theorem not_integrable_rationalIdeleGaussianZetaIntegrand_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    ¬ Integrable (rationalIdeleGaussianZetaIntegrand s) rationalIdeleHaar := by
  intro h
  apply not_integrable_rationalIdeleGaussian_mul_ideleNorm
  simpa only [norm_rationalIdeleGaussianZetaIntegrand_of_re_eq_one hs] using h.norm

/-- The norm twist `1 + 2 I` is an explicit counterexample to the claimed finiteness. -/
public theorem not_integrable_rationalIdeleGaussianZetaIntegrand_one_add_two_I :
    ¬ Integrable (rationalIdeleGaussianZetaIntegrand (1 + 2 * Complex.I)) rationalIdeleHaar :=
  not_integrable_rationalIdeleGaussianZetaIntegrand_of_re_eq_one (by norm_num [Complex.mul_re])

end Masullo
