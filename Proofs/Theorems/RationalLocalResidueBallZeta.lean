module

public import Theorems.RationalLocalHaarDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Lemmas.PadicAddHaar
import Lemmas.RationalLocalAdditiveModulus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp

/-!
# A translated-ball witness for the finite local zeta residue

The indicator of `1 + p ℤ_[p]` has constant raw zeta integral in
(3.3.1.7), PDF p. 130, under the rational Haar normalization (A.3.2.2–3),
p. 560. At `p = 3` its nonzero Fourier zero mode contrasts with the
absence of a pole in (3.3.2.23), p. 141.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Padic ENNReal

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "G[" v "]" => (K[v])ˣ
local notation "p[" v "]" => ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)
local notation "e[" v "]" => Rat.HeightOneSpectrum.adicCompletion.padicEquiv v

local instance (v : V) : Fact (p[v]).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

/-- The pullback of `1 + p ℤ_[p]` to the rational completion at `v`. -/
@[expose]
public noncomputable def rationalLocalOneResidueBall (v : V) : Set K[v] :=
  letI : Fact (p[v]).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  {x | ‖(p[v] : ℚ_[p[v]])⁻¹ * (e[v] x - 1)‖ ≤ 1}

local notation "S[" v "]" => rationalLocalOneResidueBall v
local notation "f[" v "]" => Set.indicator (S[v]) (fun _ ↦ (1 : ℂ))
local notation "F[" v "," s "]" =>
  (fun x : G[v] ↦ f[v] (x : K[v]) * (‖(x : K[v])‖ : ℂ) ^ s)

private theorem prime_gt_one (v : V) : 1 < (p[v] : ℝ) := by
  exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt

private theorem measurableSet_oneResidueBall (v : V) : MeasurableSet S[v] := by
  have he : Continuous (e[v]) := (e[v]).continuous
  exact (isClosed_le ((continuous_const.mul (he.sub continuous_const)).norm)
    continuous_const).measurableSet

private theorem norm_eq_one_of_mem_oneResidueBall (v : V) {x : K[v]} (hx : x ∈ S[v]) :
    ‖x‖ = 1 := by
  change ‖(p[v] : ℚ_[p[v]])⁻¹ * (e[v] x - 1)‖ ≤ 1 at hx
  rw [norm_mul, norm_inv, Padic.norm_p, inv_inv] at hx
  have hp := zero_lt_one.trans (prime_gt_one v)
  have hle : ‖e[v] x - 1‖ ≤ 1 / (p[v] : ℝ) :=
    (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hx)
  have hlt : ‖e[v] x - 1‖ < ‖(1 : ℚ_[p[v]])‖ := by
    rw [norm_one]
    exact (by simpa only [one_div] using hle : ‖e[v] x - 1‖ ≤ (p[v] : ℝ)⁻¹).trans_lt
      (inv_lt_one_of_one_lt₀ (prime_gt_one v))
  rw [← norm_rationalLocal_padicEquiv v, Padic.norm_eq_of_norm_sub_lt_right hlt, norm_one]

private theorem oneResidueBall_addMass (v : V) :
    rationalLocalFieldAddHaar v S[v] = (p[v] : ℝ≥0∞)⁻¹ := by
  let E := (e[v]).toHomeomorph.toMeasurableEquiv
  let B : Set ℚ_[p[v]] := {x | ‖x‖ ≤ 1}
  let d : ℚ_[p[v]] → ℚ_[p[v]] := fun x ↦ (p[v] : ℚ_[p[v]])⁻¹ * x
  let t := MeasurableEquiv.subRight (1 : ℚ_[p[v]])
  have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
  have hd : Measurable d := by fun_prop
  change (padicAddHaar p[v]).comap E (E ⁻¹' (t ⁻¹' (d ⁻¹' B))) = _
  rw [E.measurableEmbedding.comap_apply, E.image_preimage, ← t.map_apply,
    show Measure.map t (padicAddHaar p[v]) = _ from map_sub_right_eq_self _ _,
    ← Measure.map_apply hd hB,
    show Measure.map d (padicAddHaar p[v]) = (p[v] : ℝ≥0∞)⁻¹ • padicAddHaar p[v] by
      simpa only [pow_one] using padicAddHaar_map_inv_pow p[v] 1,
    smul_apply, smul_eq_mul, padicAddHaar_integralBall, mul_one]

variable (v : V) [MeasurableSpace G[v]] [BorelSpace G[v]]

local notation "U[" v "]" => (Units.val : G[v] → K[v]) ⁻¹' S[v]
local notation "μ[" v "]" => rationalLocalMultiplicativeHaar v

private theorem oneResidueBall_mulMass :
    μ[v] U[v] = (ENNReal.ofReal (1 - (p[v] : ℝ)⁻¹))⁻¹ * (p[v] : ℝ≥0∞)⁻¹ := by
  let ν := rationalLocalFieldAddHaar v
  have hS := measurableSet_oneResidueBall v
  have hsub : S[v] ⊆ ({0}ᶜ : Set K[v]) := by
    intro x hx
    change x ≠ 0
    rintro rfl
    simpa using norm_eq_one_of_mem_oneResidueBall v hx
  rw [← Measure.map_apply Units.continuous_val.measurable hS,
    map_rationalLocalMultiplicativeHaar_val, smul_apply, smul_eq_mul,
    withDensity_apply _ hS, Measure.restrict_restrict_of_subset hsub, ← oneResidueBall_addMass v]
  congr 1
  calc
    _ = ∫⁻ _ in S[v], (1 : ℝ≥0∞) ∂ν := setLIntegral_congr_fun hS (by
      intro x hx
      simp [norm_eq_one_of_mem_oneResidueBall v hx])
    _ = ν S[v] := by simp

/-- At any rational finite place, the raw zeta integral of the translated
residue-ball indicator is absolutely convergent and independent of `s`. -/
public theorem rationalLocalOneResidueBall_zeta (s : ℂ) :
    Integrable F[v,s] μ[v] ∧ (∫ x, F[v,s] x ∂μ[v]) = ((p[v] : ℂ) - 1)⁻¹ := by
  have hU : MeasurableSet U[v] := (measurableSet_oneResidueBall v).preimage
    Units.continuous_val.measurable
  have heq : F[v,s] = (U[v]).indicator (fun _ ↦ 1) := by
    funext x
    by_cases hx : (x : K[v]) ∈ S[v]
    · rw [indicator_of_mem hx, norm_eq_one_of_mem_oneResidueBall v hx,
        Complex.ofReal_one, Complex.one_cpow, mul_one, indicator_of_mem (s := U[v]) hx]
    · rw [indicator_of_notMem hx, zero_mul, indicator_of_notMem (s := U[v]) hx]
  have hc : 0 < 1 - (p[v] : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (prime_gt_one v))
  have hfinite : μ[v] U[v] ≠ ∞ := by
    rw [oneResidueBall_mulMass v]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero))
  rw [heq, integrable_indicator_iff hU, integral_indicator_const _ hU]
  refine ⟨integrableOn_const hfinite, ?_⟩
  rw [Complex.real_smul, mul_one, Measure.real, oneResidueBall_mulMass v,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_natCast]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_natCast]
  have hp₀ : (p[v] : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
  have hp₁ : (p[v] : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.ne_one)
  field_simp

/-- At the place over three, the raw integral is identically `1/2`, but
its test has additive integral `1/3`, the Fourier value at zero. -/
public theorem rationalLocalOneResidueBall_three (hp : p[v] = 3) (s : ℂ) :
    Integrable F[v,s] μ[v] ∧ (∫ x, F[v,s] x ∂μ[v]) = 1 / 2 ∧
      (∫ x, f[v] x ∂rationalLocalFieldAddHaar v) = 1 / 3 := by
  obtain ⟨hi, hz⟩ := rationalLocalOneResidueBall_zeta v s
  refine ⟨hi, hz.trans ?_, ?_⟩
  · rw [hp]
    norm_num
  · rw [integral_indicator_const _ (measurableSet_oneResidueBall v), Complex.real_smul,
      mul_one, Measure.real, oneResidueBall_addMass v, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_natCast, hp]
    norm_num

end Masullo
