module

public import Theorems.RationalThetaInversion

/-!
# The lower norm edge of a rational theta band

On the rational unramified section, apply Masullo's (2.2.3.2), p. 82, to
an input with both zero modes zero and the band bound (7.3.2.14), p. 355,
for `S = {∞}`. Until the pair `±2` enters the band, only the dual samples
at `±1` can contribute. These are consequences for the global theta
image, not the local sum over the two real `S`-units.
-/

open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Below the entry of the second pair of dual lattice points, the first pair
accounts for the entire two-moment rational theta sum. -/
public theorem rationalTheta_eq_first_pair_of_band (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFb : (𝓕 b) 0 = 0) {B t : ℝ}
    (hband : ∀ ξ : ℝ, B < |ξ| → (𝓕 b) ξ = 0) (ht : 0 < t) (htB : B < 2 * t⁻¹) :
    rationalTheta b t = t⁻¹ • ((𝓕 b) t⁻¹ + (𝓕 b) (-t⁻¹)) := by
  rw [rationalTheta_inversion b ht, hb, hFb, smul_zero, add_zero, sub_zero]
  congr 1
  let p : {n : ℤ // n ≠ 0} := ⟨1, by decide⟩
  let m : {n : ℤ // n ≠ 0} := ⟨-1, by decide⟩
  have hpm : p ≠ m := by decide
  unfold rationalTheta
  rw [tsum_eq_sum (s := {p, m}) (fun n hn ↦ ?_), Finset.sum_pair hpm]
  · change (𝓕 b) (t⁻¹ * (↑(1 : ℤ) : ℝ)) + (𝓕 b) (t⁻¹ * (↑(-1 : ℤ) : ℝ)) = _
    simp
  · apply hband
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hn₁ : (n : ℤ) ≠ 1 := fun he ↦ hn.1 (Subtype.ext he)
    have hn₂ : (n : ℤ) ≠ -1 := fun he ↦ hn.2 (Subtype.ext he)
    have hn₀ := n.property
    have htwo : (2 : ℤ) ≤ |(n : ℤ)| := by
      by_cases h : 0 ≤ (n : ℤ)
      · rw [abs_of_nonneg h]
        omega
      · rw [abs_of_neg (lt_of_not_ge h)]
        omega
    have hcast : (2 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast htwo
    calc
      B < 2 * t⁻¹ := htB
      _ = t⁻¹ * 2 := mul_comm _ _
      _ ≤ t⁻¹ * |((n : ℤ) : ℝ)| := mul_le_mul_of_nonneg_left hcast (inv_nonneg.mpr ht.le)

/-- With both zero modes removed, a Fourier band of radius `B` forces the
unramified rational theta sum to vanish when the inverse norm exceeds `B`. -/
public theorem rationalTheta_eq_zero_of_inv_gt_band (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFb : (𝓕 b) 0 = 0) {B t : ℝ}
    (hband : ∀ ξ : ℝ, B < |ξ| → (𝓕 b) ξ = 0) (ht : 0 < t) (htB : B < t⁻¹) :
    rationalTheta b t = 0 := by
  have hi := inv_pos.mpr ht
  rw [rationalTheta_eq_first_pair_of_band b hb hFb hband ht (by linarith)]
  rw [hband _ (by simpa [abs_of_pos hi] using htB),
    hband _ (by simpa [abs_of_pos hi] using htB), add_zero, smul_zero]

end Masullo
