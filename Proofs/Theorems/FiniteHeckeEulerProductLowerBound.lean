module

public import Theorems.FiniteHeckeCharacterEulerProduct

/-! A uniform positive lower bound for the finite Hecke Euler product on `Re s = 2`. -/

open Filter IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

private theorem summable_finitePlaceExp :
    Summable (fun v : Places ↦ Real.exp (-2 * Real.log (finitePlaceNorm v))) := by
  have h := (summable_finitePlace_log_powers (K := K) (by norm_num : (1 : ℝ) < 2)).comp_injective
    (show Function.Injective (fun v : Places ↦ (v, (0 : ℕ))) from fun _ _ h ↦ congrArg Prod.fst h)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (h.mul_left (Real.log 2)⁻¹).of_nonneg_of_le (fun _ ↦ Real.exp_nonneg _) fun v ↦ ?_
  have hq := two_le_finitePlaceNorm v
  have hq0 : 0 < finitePlaceNorm v := (by norm_num : (0 : ℝ) < 2).trans_le hq
  change Real.exp (-2 * Real.log (finitePlaceNorm v)) ≤ (Real.log 2)⁻¹ *
    (Real.log (finitePlaceNorm v) / finitePlaceNorm v ^ (2 * ((0 : ℕ) + 1 : ℝ)))
  simp only [Nat.cast_zero, zero_add, mul_one]
  rw [Real.rpow_def_of_pos hq0, mul_comm (Real.log (finitePlaceNorm v)) 2,
    div_eq_mul_inv, ← Real.exp_neg, ← neg_mul, ← mul_assoc]
  exact le_mul_of_one_le_left (Real.exp_nonneg _) <|
    (one_le_inv_mul₀ hl).mpr (Real.log_le_log (by norm_num) hq)

/-- The sum of inverse squared ideal norms used for the center estimate. -/
@[expose] public noncomputable def finiteHeckeRightLineLoss (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 K), Real.exp (-2 * Real.log (finitePlaceNorm v))

/-- The finite Euler product of a unitary Hecke character is bounded away from zero
on `Re s = 2`. The bound furnished by the proof depends only on the number field. -/
public theorem exp_le_norm_finiteHeckeCharacterEulerProduct
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    {s : ℂ} (hs : s.re = 2) :
    Real.exp (-finiteHeckeRightLineLoss K) ≤ ‖finiteHeckeCharacterEulerProduct χ s‖ := by
  let a (v : Places) := Real.exp (-2 * Real.log (finitePlaceNorm v))
  have ha : Summable a := summable_finitePlaceExp
  have hs' : 1 < s.re := hs ▸ (by norm_num : (1 : ℝ) < 2)
  have hz := norm_finiteHeckeCoefficient_le_one χ hχ
  let F (v : Places) := finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s
  have hfactor (v : Places) : Real.exp (-a v) ≤ ‖F v‖ := by
    let w := finiteHeckeMonomial (finiteHeckeCoefficient χ) v s
    have hw : ‖w‖ ≤ a v := by
      simp only [w, a, finiteHeckeMonomial, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hs]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (hz v)
    have hden : ‖1 - w‖ ≤ Real.exp (a v) := calc
      ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa only [norm_one] using norm_sub_le (1 : ℂ) w
      _ ≤ 1 + a v := add_le_add_right hw 1
      _ ≤ Real.exp (a v) := by simpa only [add_comm] using Real.add_one_le_exp (a v)
    change Real.exp (-a v) ≤ ‖(1 - w)⁻¹‖
    rw [Real.exp_neg, norm_inv]
    exact inv_anti₀ (norm_pos_iff.mpr (finiteHecke_denom_ne_zero (hz v) (zero_lt_one.trans hs'))) hden
  -- Use convergence of the actual all-place Euler product to pass the finite bounds to the limit.
  have hp : HasProd F (finiteHeckeCharacterEulerProduct χ s) := by
    unfold finiteHeckeCharacterEulerProduct
    simp only [finiteHecke_localPolynomial_eval_inv]
    exact (finiteHeckeEulerFactor_hasProdLocallyUniformlyOn hz).hasProd hs'
  refine ge_of_tendsto' ((continuous_norm.tendsto _).comp hp) fun S ↦ ?_
  calc
    Real.exp (-(∑' v, a v)) ≤ Real.exp (∑ v ∈ S, -a v) := by
      rw [Finset.sum_neg_distrib, Real.exp_le_exp, neg_le_neg_iff]
      exact ha.sum_le_tsum S (fun v _ ↦ Real.exp_nonneg _)
    _ ≤ ‖∏ v ∈ S, F v‖ := by
      rw [Real.exp_sum, norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ Real.exp_nonneg _) (fun v _ ↦ hfactor v)

/-- In particular there is one positive bound for the entire right line. -/
public theorem finiteHeckeCharacterEulerProduct_lower_bound
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s.re = 2 → c ≤ ‖finiteHeckeCharacterEulerProduct χ s‖ :=
  ⟨_, Real.exp_pos _, fun _ hs ↦ exp_le_norm_finiteHeckeCharacterEulerProduct χ hχ hs⟩

end Masullo
