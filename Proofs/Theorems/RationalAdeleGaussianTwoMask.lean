module

public import Props.RationalAdeleStageCoordinates
public import Lemmas.SchwartzGaussian
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # A mixed real–dyadic cutoff escapes every rational adelic Schwartz stage -/

open NumberField IsDedekindDomain
open scoped Classical SchwartzMap

namespace Masullo
set_option backward.isDefEq.respectTransparency false

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)
local notation "v₂" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) p₂
local notation "e₂" => Padic.adicCompletionEquiv (𝓞 ℚ) p₂
local notation "O" => (fun v : V ↦ HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "W" => rationalFiniteIntegralAdeles

/-- Read the dyadic coordinate in `ℚ₂`, with its normalized absolute value. -/
public noncomputable def rationalAdeleTwoAbs (x : A) : ℝ := ‖(e₂).symm (x.2 v₂)‖

private noncomputable def spike (a : ℚ_[2]) : F := RestrictedProduct.single O v₂ (e₂ a)

private theorem spike_integral {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) : spike a ∈ W := by
  intro v
  by_cases hv : v = v₂
  · subst v
    rw [spike, RestrictedProduct.single_eq_same O v₂ (e₂ a)]
    let z : ℤ_[2] := ⟨a, ha⟩
    exact PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) p₂ z ▸
      ((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p₂) z).property
  · rw [spike, RestrictedProduct.single_eq_of_ne O (e₂ a) hv]
    exact (O v).zero_mem

private theorem spike_cell {M k : ℕ} (hM : 0 < M) (hk : multiplicity 2 M ≤ k) (t : ℝ) :
    rationalAdeleAt t (spike (2 ^ k)) ∈ rationalAdeleStageCell M ⟨0, pow_pos hM _⟩ := by
  have hm : (M : ℚ_[2]) ≠ 0 := by exact_mod_cast hM.ne'
  let a : ℚ_[2] := 2 ^ k / M
  have ha : ‖a‖ ≤ 1 := by
    dsimp only [a]
    rw [norm_div, div_le_one (norm_pos_iff.mpr hm), norm_pow,
      show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p,
      Padic.norm_eq_zpow_neg_valuation hm, Padic.valuation_natCast, zpow_neg, zpow_natCast, inv_pow]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) hk
  refine (mem_rationalAdeleStageCell_iff hM _ _).mpr ⟨spike a, spike_integral ha, ?_⟩
  simp only [rationalAdeleAt_finite, rationalAdeleStageRepresentative, Nat.cast_zero, zero_div,
    map_zero, zero_add]
  unfold spike
  rw [← RestrictedProduct.mul_single O v₂ (e₂ a) (M : F)]
  congr 1
  let ev : F →+* (v₂).adicCompletion ℚ := RestrictedProduct.evalRingHom _ v₂
  change e₂ _ = ev (M : F) * e₂ a
  rw [map_natCast, ← map_natCast e₂, ← map_mul]
  exact congrArg (fun b : ℚ_[2] ↦ e₂ b) (mul_div_cancel₀ (2 ^ k) hm).symm

/-- The unmasked integral-finite Gaussian already lies at level one. -/
public theorem rationalAdeleUnramified_gaussian_mem_stage_one :
    rationalAdeleUnramified (schwartzGaussian ℝ) ∈ rationalAdeleSchwartzStage 1 := by
  let f := (rationalAdeleStageCoordinates (M := 1) (by decide)).symm (fun _ ↦ schwartzGaussian ℝ)
  suffices h : f.val = rationalAdeleUnramified (schwartzGaussian ℝ) by rw [← h]; exact f.property
  funext x
  rw [show f.val = _ from rationalAdeleStageCoordinates_symm_eq_boxSum (M := 1) (by decide) _]
  simp [rationalAdeleBoxSum, rationalAdeleBox_stageCell, rationalAdeleStageCell,
    rationalAdeleUnramified]

private theorem gaussian_spike (n : ℕ) (t : ℝ) :
    rationalAdeleUnramified (schwartzGaussian ℝ) (rationalAdeleAt t (spike (2 ^ n))) =
      (Real.exp (-t ^ 2) : ℂ) := by
  have h : rationalAdeleAt t (spike (2 ^ n)) ∈ rationalIntegralAdeles := by
    change (rationalAdeleAt _ _).2 ∈ W
    rw [rationalAdeleAt_finite]
    apply spike_integral
    rw [norm_pow, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [rationalAdeleUnramified, Set.indicator_of_mem h, rationalAdeleReal_at, schwartzGaussian_apply,
    Real.norm_eq_abs, sq_abs]

private theorem twoAbs_spike (n : ℕ) (t : ℝ) :
    rationalAdeleTwoAbs (rationalAdeleAt t (spike (2 ^ n))) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [rationalAdeleTwoAbs, rationalAdeleAt_finite, spike,
    RestrictedProduct.single_eq_same O v₂ (e₂ (2 ^ n)), ContinuousAlgEquiv.symm_apply_apply,
    norm_pow, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p, inv_pow]

/-- Without any regularity assumption on the cutoff, the mixed real–dyadic
mask destroys finite-stage membership of the integral-finite Gaussian. -/
public theorem rationalAdeleGaussian_twoMask_not_mem_stage (ρ : ℝ → ℝ)
    (h₁ : Set.EqOn ρ 1 (Set.Icc 0 (7 / 4))) (h₀ : Set.EqOn ρ 0 (Set.Ici 2))
    {M : ℕ} (hM : 0 < M) :
    (fun x : A ↦ rationalAdeleUnramified (schwartzGaussian ℝ) x *
      (ρ (|rationalAdeleReal x| * rationalAdeleTwoAbs x) : ℂ)) ∉ rationalAdeleSchwartzStage M := by
  intro hf
  let f : rationalAdeleSchwartzStage M := ⟨_, hf⟩
  let k := multiplicity 2 M
  let t := 3 * (2 : ℝ) ^ k
  have hv (n : ℕ) (hn : k ≤ n) := rationalAdeleStageCoordinates_eq_on_cell hM f (spike_cell hM hn t)
  have he := (hv k le_rfl).symm.trans (by simpa only [rationalAdeleReal_at] using hv (k + 2) (by omega))
  change _ * (_ : ℂ) = _ * (_ : ℂ) at he
  simp only [gaussian_spike, rationalAdeleReal_at, twoAbs_spike] at he
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have harg (d : ℕ) : t * ((2 : ℝ) ^ (k + d))⁻¹ = 3 / 2 ^ d := by
    dsimp only [t]; rw [pow_add]; field_simp
  have h3 : ρ 3 = 0 := h₀ (by norm_num : (3 : ℝ) ∈ Set.Ici 2)
  have hq : ρ (3 / 4) = 1 := h₁ (by norm_num : (3 / 4 : ℝ) ∈ Set.Icc 0 (7 / 4))
  rw [abs_of_nonneg ht, show t * ((2 : ℝ) ^ k)⁻¹ = 3 by simpa using harg 0,
    harg 2, show (3 / 2 ^ 2 : ℝ) = 3 / 4 by norm_num, h3, hq] at he
  exact Complex.exp_ne_zero (-(t : ℂ) ^ 2) (by simpa using he.symm)

end Masullo
