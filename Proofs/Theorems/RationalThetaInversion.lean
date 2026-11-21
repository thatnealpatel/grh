module

public import Lemmas.ScaledPoisson

/-!
# Theta inversion on the rational unramified lattice

This is the lattice identity corresponding to (2.2.3.2), p. 82 of
Masullo's pinned edition, for the rational unramified tensor
`b ⊗ ∏ₚ 𝟙_{ℤₚ}` on the positive real norm section. The finite factors
select the integers and are self-dual in the normalization of Examples
A.3.1.5–8, pp. 557–558. The formal statement and proof are about the
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

end Masullo
