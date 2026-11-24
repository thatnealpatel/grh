module

public import Lemmas.ZeroPrefixCosine
import all Lemmas.ConsecutiveHarmonicGrid -- unfold the node angle for distinctness
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Basic.Complex.BigOperators

/-!
# Pointwise complex moments of the rotated tilted grid

Source: `059232cff7d3894d8545eb11ffccf9cd2fec1646:.godel/bob/translated-step-11-1.md:31–41`,
“Match the prime answers with shallow conditional laws,” at height `t`. The same
construction is used in `.godel/bob/two-height-translated-radial.md:25` at both
heights and in `.godel/bob/translated-step-witness.md:37` at one height, at the
same revision.

This supplies the finite conditional law at a fixed frequency: its first
complex moment matches the prescribed answer and orders `2, …, n` vanish
before pairing with any translated multiplier. No measurable kernel or
complete translated-cutoff witness is asserted.

Owning check session: `01a20c71-faab-7613-8747-63acf6b0d98e`.
-/

open scoped BigOperators

namespace Masullo.RotatedTiltedGrid

open ConsecutiveHarmonicGrid (node average_cos_sin_eq_zero)
open ZeroPrefixCosine (threshold tiltedWeight tiltedGrid_spec)

/-- The `l`-th unit node on the odd-angle grid of size `n + 2`. -/
@[expose] public noncomputable def oddNode (n l : ℕ) : ℂ :=
  Complex.exp ((node (n + 2) l : ℂ) * Complex.I)

/-- The unit rotation that sends `-‖m‖` to `m`, chosen as the identity at zero. -/
@[expose] public noncomputable def rotation (m : ℂ) : ℂ :=
  if m = 0 then 1 else -m / (‖m‖ : ℂ)

/-- Rotate the nodes, leaving their weights indexed by the original grid. -/
@[expose] public noncomputable def rotatedNode (n : ℕ) (m : ℂ) (l : ℕ) : ℂ :=
  rotation m * oddNode n l

private theorem rotation_spec (m : ℂ) :
    ‖rotation m‖ = 1 ∧ rotation m * -(‖m‖ : ℂ) = m := by
  by_cases hm : m = 0
  · subst m
    simp [rotation]
  have hnorm : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  have hc : (‖m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  simp only [rotation, ite_eq_right hm]
  constructor
  · rw [norm_div, norm_neg, Complex.norm_of_nonneg (norm_nonneg _), div_self hnorm]
  · rw [mul_neg, div_mul_cancel₀ _ hc, neg_neg]

private theorem rotatedNode_injOn {n : ℕ} {m : ℂ} (hu : ‖rotation m‖ = 1) :
    Set.InjOn (rotatedNode n m) ↑(Finset.range (n + 2)) := by
  have hr : rotation m ≠ 0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have hN : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hangle (l : ℕ) (hl : l ∈ Finset.range (n + 2)) :
      node (n + 2) l ∈ Set.Ico 0 (2 * Real.pi) := by
    unfold node
    refine ⟨div_nonneg (by positivity) hN.le, (div_lt_iff₀ hN).mpr ?_⟩
    have hl' : (l : ℝ) + 1 ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Finset.mem_range.mp hl
    calc
      _ < (2 * ((n + 2 : ℕ) : ℝ)) * Real.pi :=
        mul_lt_mul_of_pos_right (by linarith only [hl']) Real.pi_pos
      _ = _ := by ring
  intro l hl j hj heq
  have hexp : Circle.exp (node (n + 2) l) = Circle.exp (node (n + 2) j) := by
    apply Subtype.ext
    simpa only [Circle.coe_exp, oddNode] using
      (mul_right_injective₀ hr heq : oddNode n l = oddNode n j)
  have he := Circle.exp_injOn_Ico (by rw [sub_zero] : 2 * Real.pi - 0 ≤ 2 * Real.pi)
    (hangle l hl) (hangle j hj) hexp
  unfold node at he
  have h := (mul_left_inj' Real.pi_pos.ne').mp ((div_left_inj₀ hN.ne').mp he)
  exact_mod_cast (show (l : ℝ) = (j : ℝ) by linarith only [h])

private theorem oddNode_pow (n k l : ℕ) :
    oddNode n l ^ k = Complex.exp (↑((k : ℝ) * node (n + 2) l) * Complex.I) := by
  rw [oddNode, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul]

private theorem sum_oddNode_pow_eq_zero {n k : ℕ} (hk : 0 < k) (hkn : k < n + 2) :
    (∑ l ∈ Finset.range (n + 2), oddNode n l ^ k) = 0 := by
  -- The landed cosine and sine identities are the two coordinates of the
  -- same geometric sum; both are needed for complex cancellation.
  obtain ⟨hc, hs⟩ := average_cos_sin_eq_zero (by omega) hk hkn
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have cancel (s : ℝ) (h : s / ((n + 2 : ℕ) : ℝ) = 0) : s = 0 := by
    simpa only [zero_mul] using (div_eq_iff hN).mp h
  apply Complex.ext
  · simpa only [Complex.re_sum, oddNode_pow, Complex.exp_ofReal_mul_I_re, Complex.zero_re]
      using cancel _ hc
  · simpa only [Complex.im_sum, oddNode_pow, Complex.exp_ofReal_mul_I_im, Complex.zero_im]
      using cancel _ hs

private theorem tilted_term (n l : ℕ) (r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (tiltedWeight n r l : ℂ) * oddNode n l ^ k =
      (oddNode n l ^ k - (r : ℂ) * (oddNode n l ^ (k + 1) + oddNode n l ^ (k - 1))) /
        ((n + 2 : ℕ) : ℂ) := by
  let θ := node (n + 2) l
  let z := oddNode n l
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hcos : 2 * (Real.cos θ : ℂ) = z + z⁻¹ := by
    rw [Complex.ofReal_cos, Complex.cos, neg_mul, Complex.exp_neg]
    change 2 * ((z + z⁻¹) / 2) = _
    ring
  have hdown : z⁻¹ * z ^ k = z ^ (k - 1) := calc
    _ = z⁻¹ * (z * z ^ (k - 1)) := by rw [← pow_succ', Nat.sub_add_cancel hk]
    _ = _ := inv_mul_cancel_left₀ hz _
  have hw : (tiltedWeight n r l : ℂ) =
      (1 - (r : ℂ) * (z + z⁻¹)) / ((n + 2 : ℕ) : ℂ) := by
    simp only [tiltedWeight, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    change (1 - 2 * (r : ℂ) * (Real.cos θ : ℂ)) / ((n + 2 : ℕ) : ℂ) = _
    rw [mul_comm (2 : ℂ) (r : ℂ), mul_assoc, hcos]
  change (tiltedWeight n r l : ℂ) * z ^ k = _
  rw [hw, div_mul_eq_mul_div, sub_mul, one_mul, mul_assoc, add_mul, hdown, ← pow_succ']

private theorem unrotated_moment {n k : ℕ} (r : ℝ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∑ l ∈ Finset.range (n + 2), (tiltedWeight n r l : ℂ) * oddNode n l ^ k) =
      if k = 1 then -(r : ℂ) else 0 := by
  have hN : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Finset.sum_congr rfl (fun l _ ↦ tilted_term n l r hk), ← Finset.sum_div,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_oddNode_pow_eq_zero (k := k) (by omega) (by omega),
    sum_oddNode_pow_eq_zero (k := k + 1) (by omega) (by omega)]
  -- The mode k-1 is constant exactly at k=1, where its sum cancels the
  -- denominator n+2. All three frequencies are otherwise in [1, n+1].
  by_cases h : k = 1
  · subst k
    simp only [Nat.sub_self, pow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, zero_add, zero_sub, neg_div, mul_div_cancel_right₀ _ hN, ite_true]
  · rw [sum_oddNode_pow_eq_zero (k := k - 1) (by omega) (by omega)]
    simp [h]

/-- The prescribed `n+2` distinct rotated nodes and tilted weights form a circle
probability law, with complex first moment `m` and all moments `2, …, n` zero. -/
public theorem rotatedTiltedGrid_spec {n : ℕ} (hn : 1 ≤ n) {m : ℂ}
    (hm : ‖m‖ ≤ threshold n) :
    (∀ l ∈ Finset.range (n + 2), 0 ≤ tiltedWeight n ‖m‖ l) ∧
    (∑ l ∈ Finset.range (n + 2), tiltedWeight n ‖m‖ l) = 1 ∧
    (∀ l ∈ Finset.range (n + 2), ‖rotatedNode n m l‖ = 1) ∧
    Set.InjOn (rotatedNode n m) ↑(Finset.range (n + 2)) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∑ l ∈ Finset.range (n + 2), (tiltedWeight n ‖m‖ l : ℂ) * rotatedNode n m l ^ k) =
        if k = 1 then m else 0 := by
  obtain ⟨hw, hmass, _⟩ := tiltedGrid_spec hn (norm_nonneg m) hm
  obtain ⟨hu, hfirst⟩ := rotation_spec m
  refine ⟨hw, hmass, fun l _ ↦ ?_, rotatedNode_injOn hu, ?_⟩
  · rw [rotatedNode, norm_mul, hu, one_mul, oddNode, Complex.norm_exp_ofReal_mul_I]
  · intro k hk hkn
    have hrotate (l : ℕ) :
        (tiltedWeight n ‖m‖ l : ℂ) * rotatedNode n m l ^ k =
          rotation m ^ k * ((tiltedWeight n ‖m‖ l : ℂ) * oddNode n l ^ k) := by
      rw [rotatedNode, mul_pow, mul_left_comm]
    rw [Finset.sum_congr rfl (fun l _ ↦ hrotate l), ← Finset.mul_sum,
      unrotated_moment _ hk hkn]
    by_cases h : k = 1
    · subst k
      simpa only [ite_true, pow_one] using hfirst
    · simp [h]

end Masullo.RotatedTiltedGrid
