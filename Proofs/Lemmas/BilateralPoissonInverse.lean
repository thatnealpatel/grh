module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

/-!
# Bilateral Poisson moment inversion

Source: `75ca254:.godel/bob/full-lattice-deletion-33.md:9–19`.
Consumer: `6aa093a:.godel/bob/half-step-deletion-33.md`.
Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.

The normalized three-term stencil is summable on the integer lattice and is a
right inverse to convolution with `j ↦ r ^ j.natAbs` for `0 < r < 1`. This is
the bilateral sequence identity only, not its Fourier realization or the
certification of a particular deletion law.
-/

namespace Masullo.BilateralPoissonInverse

/-- The normalized inverse stencil for the bilateral Poisson moment kernel. -/
@[expose] public noncomputable def stencil (r : ℝ) (f : ℤ → ℝ) (k : ℤ) : ℝ :=
  ((1 + r ^ 2) * f k - r * (f (k - 1) + f (k + 1))) / (1 - r ^ 2)

/-- The stencil takes summable sequences to summable sequences. -/
public theorem summable_stencil (r : ℝ) {f : ℤ → ℝ} (hf : Summable f) :
    Summable (stencil r f) := by
  have hprev : Summable (fun j : ℤ => f (j - 1)) :=
    ((Equiv.subRight (1 : ℤ)).summable_iff).2 hf
  have hnext : Summable (fun j : ℤ => f (j + 1)) :=
    ((Equiv.addRight (1 : ℤ)).summable_iff).2 hf
  exact ((hf.mul_left (1 + r ^ 2)).sub ((hprev.add hnext).mul_left r)).div_const (1 - r ^ 2)

private theorem kernel_difference (r : ℝ) (n : ℤ) :
    (1 + r ^ 2) * r ^ n.natAbs - r * (r ^ (n - 1).natAbs + r ^ (n + 1).natAbs) =
      if n = 0 then 1 - r ^ 2 else 0 := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · have h₁ : (n - 1).natAbs = n.natAbs + 1 := by omega
    have h₂ : n.natAbs = (n + 1).natAbs + 1 := by omega
    simp only [ite_eq_right (ne_of_lt h), h₁, h₂, pow_succ]
    ring
  · norm_num
    ring
  · have h₁ : (n + 1).natAbs = n.natAbs + 1 := by omega
    have h₂ : n.natAbs = (n - 1).natAbs + 1 := by omega
    simp only [ite_eq_right (ne_of_gt h), h₁, h₂, pow_succ]
    ring

/-- Convolving the normalized stencil with the bilateral Poisson moment
kernel recovers `f` at every integer index. -/
public theorem hasSum_kernel_mul_stencil {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    {f : ℤ → ℝ} (hf : Summable f) (k : ℤ) :
    HasSum (fun j : ℤ => r ^ (k - j).natAbs * stencil r f j) (f k) := by
  let G (j : ℤ) : ℝ := r ^ (k - j).natAbs
  let W (m j : ℤ) : ℝ := G (j - m) * f j
  have hW (m : ℤ) : Summable (W m) := by
    refine hf.abs.of_norm_bounded fun j => ?_
    change |r ^ (k - (j - m)).natAbs * f j| ≤ |f j|
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr₀.le _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hr₀.le hr₁.le)
  -- Translate each series so that every term has the factor `f j`.
  have hshift (m : ℤ) :
      HasSum (fun j : ℤ => G j * f (j + m)) (∑' j, W m j) := by
    simpa only [Function.comp_def, Equiv.coe_addRight, W, add_sub_cancel_right] using
      ((Equiv.addRight m).hasSum_iff).2 (hW m).hasSum
  have horiginal := ((hshift 0).mul_left (1 + r ^ 2)).sub
    (((hshift (-1)).add (hshift 1)).mul_left r)
  have hreindexed := ((hW 0).hasSum.mul_left (1 + r ^ 2)).sub
    (((hW (-1)).hasSum.add (hW 1).hasSum).mul_left r)
  have hdelta (j : ℤ) : (1 + r ^ 2) * W 0 j - r * (W (-1) j + W 1 j) =
      if j = k then (1 - r ^ 2) * f k else 0 := by
    have h₁ : k - (j + 1) = k - j - 1 := by omega
    have h₂ : k - (j - 1) = k - j + 1 := by omega
    have hkernel : (1 + r ^ 2) * G j - r * (G (j + 1) + G (j - 1)) =
        if j = k then 1 - r ^ 2 else 0 := by
      simpa only [G, h₁, h₂, sub_eq_zero, eq_comm] using kernel_difference r (k - j)
    calc
      _ = ((1 + r ^ 2) * G j - r * (G (j + 1) + G (j - 1))) * f j := by
        simp only [W, sub_zero, sub_neg_eq_add]
        ring
      _ = _ := by rw [hkernel]; split <;> simp_all
  have hsum := (hreindexed.congr_fun fun j => (hdelta j).symm).unique
    (hasSum_ite_eq k ((1 - r ^ 2) * f k))
  rw [hsum] at horiginal
  have hden : 1 - r ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ hr₀.le hr₁ (by decide : (2 : ℕ) ≠ 0))).ne'
  have hnormalized := horiginal.div_const (1 - r ^ 2)
  rw [mul_div_cancel_left₀ (f k) hden] at hnormalized
  refine hnormalized.congr_fun fun j => ?_
  simp only [G, stencil, add_zero, sub_eq_add_neg, ← mul_div_assoc]
  ring

end Masullo.BilateralPoissonInverse
