module

public import Lemmas.ScaledPoisson
import Mathlib.Analysis.Complex.Exponential

/-!
# Theta inversion and tail estimates on the rational unramified lattice

These are the lattice counterparts of (2.2.3.2) and Theorem 2.2.3.4,
pp. 82–85 of Masullo's pinned edition, for the rational unramified tensor
`b ⊗ ∏ₚ 𝟙_{ℤₚ}` on the positive real norm section. The finite factors
select the integers and are self-dual in the normalization of Examples
A.3.1.5–8, pp. 557–558. The formal statements and proofs are about the
real lattice, not the adelic reduction itself.
-/

open scoped FourierTransform SchwartzMap

namespace Masullo

/-- The theta sum of the scaled integer lattice with the zero index omitted. -/
@[expose] public noncomputable def rationalTheta (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ∑' n : {n : ℤ // n ≠ 0}, b (t * (n : ℤ))

private theorem lattice_sum_split_zero (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) :
    (∑' n : ℤ, b (t * n)) = b 0 + rationalTheta b t := by
  have hs := (summable_norm_schwartz_int_mul b ht).of_norm
  let S : Set ℤ := (↑({0} : Finset ℤ) : Set ℤ)ᶜ
  let e : (S : Type) ≃ {n : ℤ // n ≠ 0} :=
    Equiv.subtypeEquivRight (fun n ↦ by simp [S])
  calc
    (∑' n : ℤ, b (t * n)) = b 0 + ∑' n : S, b (t * n) := by
      simpa only [Finset.sum_singleton, Int.cast_zero, mul_zero] using
        (hs.sum_add_tsum_compl (s := ({0} : Finset ℤ))).symm
    _ = b 0 + rationalTheta b t := by
      rw [rationalTheta]
      congr 1
      exact e.tsum_eq (fun n ↦ b (t * (n : ℤ)))

/-- Poisson summation with the zero modes on both sides separated, in the
real Fourier normalization `exp(-2πixy)`. -/
public theorem rationalTheta_inversion (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    rationalTheta b t = t⁻¹ • rationalTheta (𝓕 b) t⁻¹ + t⁻¹ • (𝓕 b) 0 - b 0 := by
  have h := schwartz_scaled_poisson b ht
  rw [lattice_sum_split_zero b ht.ne', lattice_sum_split_zero (𝓕 b) (inv_ne_zero ht.ne'),
    smul_add] at h
  -- Move the original zero mode to the right, retaining the Fourier zero mode.
  rw [eq_sub_iff_add_eq, add_comm (rationalTheta b t)]
  exact h.trans (add_comm _ _)

/-- Uniform large- and small-scale estimates on a bounded family of real Schwartz
functions, in the rational lattice model of Masullo's Theorem 2.2.3.4 (pp. 82–85).
The small-scale estimate retains the two zero modes. -/
public theorem rationalTheta_uniform_tail_bounds {B : Set 𝓢(ℝ, ℂ)}
    (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ B,
      (∀ t : ℝ, 1 ≤ t → ‖rationalTheta b t‖ ≤ C / t ^ N) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 →
        ‖rationalTheta b t - t⁻¹ • (𝓕 b) 0 + b 0‖ ≤ C * t ^ N) := by
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_uniform_schwartz_lattice_bound hB N
  let F : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℂ _
  obtain ⟨C₂, _, hfourier⟩ := exists_uniform_schwartz_lattice_bound (hB.image F) (N + 1)
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left ..), fun b hb ↦ ⟨?_, ?_⟩⟩
  · intro t ht
    exact (hlarge b hb t ht).trans
      (div_le_div_of_nonneg_right (le_max_left ..) (by positivity))
  · intro t ht ht₁
    have hinv := (one_le_inv₀ ht).mpr ht₁
    have hbF : 𝓕 b ∈ F '' B := ⟨b, hb, rfl⟩
    have hrem : rationalTheta b t - t⁻¹ • (𝓕 b) 0 + b 0 =
        t⁻¹ • rationalTheta (𝓕 b) t⁻¹ := by
      rw [rationalTheta_inversion b ht]
      abel
    rw [hrem, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹)]
    calc
      _ ≤ t⁻¹ * (C₂ / (t⁻¹) ^ (N + 1)) := by
        exact mul_le_mul_of_nonneg_left (hfourier (𝓕 b) hbF t⁻¹ hinv) (by positivity)
      _ = C₂ * t ^ N := by
        rw [inv_pow, div_inv_eq_mul, pow_succ]
        field_simp
      _ ≤ max C₁ C₂ * t ^ N := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)

/-- When both zero modes vanish, the uncorrected theta function decays on both
sides of the log-norm line, uniformly on the specified bounded family. -/
public theorem rationalTheta_uniform_log_bound {B : Set 𝓢(ℝ, ℂ)}
    (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ B, b 0 = 0 → (𝓕 b) 0 = 0 → ∀ x : ℝ,
      ‖rationalTheta b (Real.exp x)‖ ≤ C * Real.exp (-(N : ℝ) * |x|) := by
  obtain ⟨C, hC, h⟩ := rationalTheta_uniform_tail_bounds hB N
  refine ⟨C, hC, fun b hb hzero hfzero x ↦ ?_⟩
  obtain ⟨hlarge, hsmall⟩ := h b hb
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, neg_mul, Real.exp_neg, Real.exp_nat_mul, ← div_eq_mul_inv]
    exact hlarge (Real.exp x) (Real.one_le_exp hx)
  · rw [abs_of_neg (lt_of_not_ge hx), neg_mul_neg, Real.exp_nat_mul]
    simpa [hzero, hfzero] using hsmall (Real.exp x) (Real.exp_pos x)
      (Real.exp_le_one_iff.mpr (le_of_not_ge hx))

end Masullo
