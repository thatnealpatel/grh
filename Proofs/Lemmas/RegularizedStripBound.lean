module

public import Lemmas.SeparatedHeightStripBound

/-! Propagate rapid value bounds for a numerator through a regularization. Only the
boundary of each rectangle needs a quotient identity and a reciprocal estimate. -/

open Complex Set

namespace Masullo

/-- On an edge, one numerator seminorm absorbs both the regularizing `s` and the
polynomial loss of the inverse denominator. -/
private theorem weighted_edge_bound {s B Φ D : ℂ} {N k : ℕ} {C M : ℝ}
    (hB : B = s * Φ / D) (hC : 0 ≤ C)
    (hD : ‖D⁻¹‖ ≤ C * (1 + ‖s‖) ^ k)
    (hΦ : (1 + ‖s‖) ^ (N + 1 + k) * ‖Φ‖ ≤ M) : ‖s ^ N * B‖ ≤ C * M := by
  have hs : ‖s‖ ≤ 1 + ‖s‖ := by linarith
  rw [hB, div_eq_mul_inv, norm_mul, norm_pow, norm_mul, norm_mul]
  calc
    _ ≤ (1 + ‖s‖) ^ N * (((1 + ‖s‖) * ‖Φ‖) * (C * (1 + ‖s‖) ^ k)) := by gcongr
    _ = C * ((1 + ‖s‖) ^ (N + 1 + k) * ‖Φ‖) := by rw [pow_add, pow_succ]; ring
    _ ≤ C * M := mul_le_mul_of_nonneg_left hΦ hC

/-- Closed-strip estimate for an explicit holomorphic regularization `B`. No estimate on
`D⁻¹` is needed away from the selected edges. -/
public theorem rapid_regularization_on_strip {B Φ D : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hB : DiffContOnCl ℂ B (re ⁻¹' Ioo a b))
    (heq : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → D s ≠ 0 → B s = s * Φ s / D s)
    (hΦ : ∀ m : ℕ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      (1 + ‖s‖) ^ m * ‖Φ s‖ ≤ M)
    (hv : ∃ V : ℝ, 0 ≤ V ∧ ∀ w : ℂ, w.re = a ∨ w.re = b →
      D w ≠ 0 ∧ ‖(D w)⁻¹‖ ≤ V)
    (hh : ∃ H : ℝ, 0 ≤ H ∧ ∃ k : ℕ, ∀ R : ℝ, 0 < R → ∃ T : ℝ, R < T ∧
      ∀ w : ℂ, a ≤ w.re → w.re ≤ b → w.im = -T ∨ w.im = T →
        D w ≠ 0 ∧ ‖(D w)⁻¹‖ ≤ H * (1 + ‖w‖) ^ k) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖s ^ N * B s‖ ≤ C := by
  obtain ⟨V, hV, hv⟩ := hv
  obtain ⟨H, hH, k, hh⟩ := hh
  intro N
  obtain ⟨M, hM⟩ := hΦ (N + 1 + k)
  refine ⟨max (V * M) (H * M), norm_pow_mul_le_on_strip_of_separated_heights hab hB N ?_ ?_⟩
  · intro w hw
    obtain ⟨hn, hd⟩ := hv w hw
    have hw' : a ≤ w.re ∧ w.re ≤ b := by rcases hw with h | h <;> simp [h, hab.le]
    apply le_trans _ (le_max_left _ _)
    apply weighted_edge_bound (heq w hw'.1 hw'.2 hn) hV _ (hM w hw'.1 hw'.2)
    exact hd.trans (le_mul_of_one_le_right hV (one_le_pow₀ (by linarith [norm_nonneg w]) :
      1 ≤ (1 + ‖w‖) ^ k))
  · intro R hR
    obtain ⟨T, hT, h⟩ := hh R hR
    refine ⟨-T, T, neg_lt_neg hT, hT, ?_⟩
    intro w ha hb hi
    obtain ⟨hn, hd⟩ := h w ha hb hi
    exact (weighted_edge_bound (heq w ha hb hn) hH hd (hM w ha hb)).trans (le_max_right _ _)

end Masullo
