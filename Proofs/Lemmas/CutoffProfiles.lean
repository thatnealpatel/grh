module

public import Lemmas.CutoffMajorant
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth tests for the divisor cutoff argument

This project construction supplies positive-log, compactly supported tests for
approximating an exponential difference. The weighted second derivative has
bounded integral even as the lower cutoff approaches zero. The tests here do
not yet have zero mass: The application at Masullo's (13.3.1.2), p. 522 of the
pinned edition, needs a separate mass correction and a distribution identity.
-/

open Function MeasureTheory Set
open scoped ContDiff

namespace Masullo

noncomputable section

private def cutoffChi (x : ℝ) : ℝ := Real.smoothTransition (x - 1)

private def cutoffLower (N x : ℝ) : ℝ := cutoffChi (N * x)

private def cutoffUpper (N x : ℝ) : ℝ := 1 - cutoffChi (N⁻¹ * x)

private def cutoffExp (c : ℂ) (x : ℝ) : ℂ := Complex.exp (-c * (x : ℂ))

private def cutoffDiff (z q : ℂ) (x : ℝ) : ℂ := cutoffExp z x - cutoffExp q x

/-- The positive-log test before subtracting the fixed mass-one bump. -/
@[expose] public def cutoffTest (z : ℂ) (z₀ : ℝ) (N x : ℝ) : ℂ :=
  (Real.smoothTransition (N * x - 1) * (1 - Real.smoothTransition (N⁻¹ * x - 1))) •
    (Complex.exp (-z * (x : ℂ)) - Complex.exp (-(z₀ : ℂ) * (x : ℂ)))

private theorem cutoffChi_smooth : ContDiff ℝ ∞ cutoffChi :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem cutoffChi_range (x : ℝ) : cutoffChi x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem cutoffChi_zero {x : ℝ} (hx : x ≤ 1) : cutoffChi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)

private theorem cutoffChi_one {x : ℝ} (hx : 2 ≤ x) : cutoffChi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutoffChi_deriv_off {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) :
    deriv cutoffChi x = 0 ∧ deriv (deriv cutoffChi) x = 0 := by
  by_cases hl : x < 1
  · have h : EqOn cutoffChi (fun _ ↦ (0 : ℝ)) (Iio 1) := fun _ hy ↦ cutoffChi_zero hy.le
    exact ⟨by simpa using h.deriv isOpen_Iio hl,
      by simpa using (h.deriv isOpen_Iio).deriv isOpen_Iio hl⟩
  · have hr : 2 < x := lt_of_not_ge fun hu ↦ hx ⟨le_of_not_gt hl, hu⟩
    have h : EqOn cutoffChi (fun _ ↦ (1 : ℝ)) (Ioi 2) := fun _ hy ↦ cutoffChi_one hy.le
    exact ⟨by simpa using h.deriv isOpen_Ioi hr,
      by simpa using (h.deriv isOpen_Ioi).deriv isOpen_Ioi hr⟩

private theorem cutoffChi_bounds : ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
    ∀ x, ‖deriv cutoffChi x‖ ≤ M₁ ∧ ‖deriv (deriv cutoffChi) x‖ ≤ M₂ := by
  have h₁ := (contDiff_infty_iff_deriv.mp cutoffChi_smooth).2
  have h₂ := (contDiff_infty_iff_deriv.mp h₁).2
  obtain ⟨M₁, hb₁⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    h₁.continuous.continuousOn
  obtain ⟨M₂, hb₂⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    h₂.continuous.continuousOn
  have hmem : (1 : ℝ) ∈ Icc 1 2 := by norm_num [mem_Icc]
  have hm₁ := (norm_nonneg _).trans (hb₁ 1 hmem)
  have hm₂ := (norm_nonneg _).trans (hb₂ 1 hmem)
  refine ⟨M₁, M₂, hm₁, hm₂, fun x ↦ ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · exact ⟨hb₁ x hx, hb₂ x hx⟩
  · obtain ⟨hx₁, hx₂⟩ := cutoffChi_deriv_off hx
    simpa only [hx₁, hx₂, norm_zero] using And.intro hm₁ hm₂

/-- A single differentiation calculation for the lower and upper affine profiles. -/
private theorem cutoff_affine_derivs (s k b : ℝ) :
    let g := fun x : ℝ ↦ b + s * cutoffChi (k * x)
    deriv g = (fun x ↦ s * (deriv cutoffChi (k * x) * k)) ∧
      deriv (deriv g) = (fun x ↦ s * (deriv (deriv cutoffChi) (k * x) * k ^ 2)) := by
  intro g
  have hχ := cutoffChi_smooth.differentiable (by simp)
  have hχ' := ((contDiff_infty_iff_deriv.mp cutoffChi_smooth).2).differentiable (by simp)
  have h₁ : deriv g = (fun x ↦ s * (deriv cutoffChi (k * x) * k)) := by
    funext x
    exact ((((hχ (k * x)).hasDerivAt.comp x (hasDerivAt_const_mul k)).const_mul s).const_add b).deriv
  refine ⟨h₁, ?_⟩
  rw [h₁]
  funext x
  calc
    _ = s * ((deriv (deriv cutoffChi) (k * x) * k) * k) :=
      ((((hχ' (k * x)).hasDerivAt.comp x (hasDerivAt_const_mul k)).mul_const k).const_mul s).deriv
    _ = _ := by ring

private theorem cutoffExp_smooth (c : ℂ) : ContDiff ℝ ∞ (cutoffExp c) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul h).cexp

private theorem hasDerivAt_cutoffExp (c : ℂ) (x : ℝ) :
    HasDerivAt (cutoffExp c) (cutoffExp c x * -c) x := by
  have h : HasDerivAt (fun y : ℂ ↦ Complex.exp (-c * y)) (cutoffExp c x * -c) (x : ℂ) :=
    (hasDerivAt_const_mul (-c)).cexp
  exact h.comp_ofReal

private theorem cutoffDiff_derivs (z q : ℂ) :
    deriv (cutoffDiff z q) = (fun x ↦ cutoffExp z x * -z - cutoffExp q x * -q) ∧
    deriv (deriv (cutoffDiff z q)) =
      (fun x ↦ cutoffExp z x * (-z) ^ 2 - cutoffExp q x * (-q) ^ 2) := by
  have h₁ : deriv (cutoffDiff z q) = _ :=
    funext fun x ↦ ((hasDerivAt_cutoffExp z x).sub (hasDerivAt_cutoffExp q x)).deriv
  refine ⟨h₁, ?_⟩
  rw [h₁]
  funext x
  simpa only [Pi.sub_def, pow_two, mul_assoc] using
    (((hasDerivAt_cutoffExp z x).mul_const (-z)).sub
      ((hasDerivAt_cutoffExp q x).mul_const (-q))).deriv

private theorem weighted_cutoffExp_le {a δ x : ℝ} {c : ℂ} (b : ℂ)
    (hx : 0 ≤ x) (hc : a + δ ≤ c.re) :
    Real.exp (a * x) * ‖cutoffExp c x * b‖ ≤ ‖b‖ * Real.exp (-δ * x) := by
  have hre : (-c * (x : ℂ)).re = -c.re * x := by
    simp [Complex.mul_re]
  rw [norm_mul, cutoffExp, Complex.norm_exp, hre]
  calc
    _ = ‖b‖ * Real.exp ((a - c.re) * x) := by
      rw [sub_mul, sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx)) (norm_nonneg b)

private theorem weighted_cutoffDiff_linear {a x : ℝ} {z q : ℂ}
    (hx : 0 ≤ x) (hz : a ≤ z.re) (hq : a ≤ q.re) :
    Real.exp (a * x) * ‖cutoffDiff z q x‖ ≤ (‖z - (a : ℂ)‖ + ‖q - (a : ℂ)‖) * x := by
  let c := z - (a : ℂ)
  let d := q - (a : ℂ)
  have hshift (u : ℂ) : (Real.exp (a * x) : ℂ) * cutoffExp u x = cutoffExp (u - (a : ℂ)) x := by
    simp only [cutoffExp, Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul]
    congr 1
    ring
  have hweight : Real.exp (a * x) • cutoffDiff z q x = cutoffDiff c d x := by
    simp only [cutoffDiff, Complex.real_smul, mul_sub, hshift, c, d]
  have hc : 0 + (0 : ℝ) ≤ c.re := by simpa [c, Complex.sub_re] using sub_nonneg.mpr hz
  have hd : 0 + (0 : ℝ) ≤ d.re := by simpa [d, Complex.sub_re] using sub_nonneg.mpr hq
  have hrate (y : ℝ) (hy : y ∈ Ico (0 : ℝ) x) :
      ‖cutoffExp c y * -c - cutoffExp d y * -d‖ ≤ ‖c‖ + ‖d‖ := by
    apply (norm_sub_le _ _).trans
    exact add_le_add
      (by simpa using weighted_cutoffExp_le (a := 0) (δ := 0) (-c) hy.1 hc)
      (by simpa using weighted_cutoffExp_le (a := 0) (δ := 0) (-d) hy.1 hd)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := cutoffDiff c d) (fun y _ ↦ ((hasDerivAt_cutoffExp c y).sub
      (hasDerivAt_cutoffExp d y)).hasDerivWithinAt) hrate x ⟨hx, le_rfl⟩
  have hzero : cutoffDiff c d 0 = 0 := by simp [cutoffDiff, cutoffExp]
  simp only [hzero, sub_zero] at hmv
  rw [← hweight, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at hmv
  exact hmv

/-- Smooth tests supported away from zero, with one weighted integral bound for all scales. -/
public theorem cutoffTest_uniform {a z₀ : ℝ} {z : ℂ} (hz : a < z.re) (hz₀ : a < z₀) :
    ∃ C : ℝ, ∀ N : ℝ, 2 ≤ N →
      let f := cutoffTest z z₀ N
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi (0 : ℝ) ∧
        (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
          (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) ≤ C := by
  obtain ⟨M₁, M₂, hm₁, hm₂, hb⟩ := cutoffChi_bounds
  let q : ℂ := z₀
  let δ := min z.re z₀ - a
  let A₁ := ‖z‖ + ‖q‖
  let A₂ := ‖z‖ ^ 2 + ‖q‖ ^ 2
  let B := ‖z - (a : ℂ)‖ + ‖q - (a : ℂ)‖
  have hδ : 0 < δ := sub_pos.mpr (lt_min hz hz₀)
  have hzδ : a + δ ≤ z.re := by dsimp only [δ]; linarith [min_le_left z.re z₀]
  have hqδ : a + δ ≤ q.re := by
    change a + δ ≤ z₀
    dsimp only [δ]
    linarith [min_le_right z.re z₀]
  refine ⟨(2 + A₂ + 2 * M₁ * A₁ + M₂ * 2) / δ + (2 * M₁ * A₁ + 2 * M₂ * B), ?_⟩
  intro N hN f
  have hNp : 0 < N := by linarith
  have hL : ContDiff ℝ ∞ (cutoffLower N) := cutoffChi_smooth.comp (contDiff_const.mul contDiff_id)
  have hU : ContDiff ℝ ∞ (cutoffUpper N) :=
    contDiff_const.sub (cutoffChi_smooth.comp (contDiff_const.mul contDiff_id))
  have hΔ : ContDiff ℝ ∞ (cutoffDiff z q) := (cutoffExp_smooth z).sub (cutoffExp_smooth q)
  have hf : ContDiff ℝ ∞ f := (hL.mul hU).smul hΔ
  have hsup : support f ⊆ Icc (1 / N) (2 * N) := by
    intro x hx
    by_contra hxI
    apply hx
    change (cutoffLower N x * cutoffUpper N x : ℝ) • cutoffDiff z q x = 0
    by_cases hl : x < 1 / N
    · have h0 : cutoffLower N x = 0 := cutoffChi_zero (by
        rw [mul_comm N x]; exact ((lt_div_iff₀ hNp).mp hl).le)
      simp [h0]
    · have hu : 2 * N < x := lt_of_not_ge fun hh ↦ hxI ⟨le_of_not_gt hl, hh⟩
      have h1 : cutoffChi (N⁻¹ * x) = 1 := cutoffChi_one (by
        rw [mul_comm N⁻¹ x, ← div_eq_mul_inv]; exact (le_div_iff₀ hNp).mpr hu.le)
      simp [cutoffUpper, h1]
  have hts : tsupport f ⊆ Icc (1 / N) (2 * N) := closure_minimal hsup isClosed_Icc
  have hs : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsup
  refine ⟨hf, hs, fun x hx ↦ (one_div_pos.mpr hNp).trans_le (hts hx).1, ?_⟩
  have hLr (x : ℝ) : cutoffLower N x ∈ Icc (0 : ℝ) 1 := cutoffChi_range _
  have hUr (x : ℝ) : cutoffUpper N x ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (cutoffChi_range _).2, sub_le_self _ (cutoffChi_range _).1⟩
  obtain ⟨hL₁, hL₂⟩ := cutoff_affine_derivs 1 N 0
  obtain ⟨hU₁, hU₂⟩ := cutoff_affine_derivs (-1) N⁻¹ 1
  simp only [one_mul, zero_add] at hL₁ hL₂
  simp only [neg_one_mul, ← sub_eq_add_neg] at hU₁ hU₂
  change deriv (cutoffLower N) = _ at hL₁
  change deriv (deriv (cutoffLower N)) = _ at hL₂
  change deriv (cutoffUpper N) = _ at hU₁
  change deriv (deriv (cutoffUpper N)) = _ at hU₂
  have hLb (x : ℝ) : ‖deriv (cutoffLower N) x‖ ≤ N * M₁ ∧
      ‖deriv (deriv (cutoffLower N)) x‖ ≤ N ^ 2 * M₂ := by
    rw [hL₂, hL₁]
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg hNp.le]
    exact ⟨by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hb _).1 hNp.le,
      by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hb _).2 (sq_nonneg N)⟩
  have hLo (x : ℝ) (hx : x ∉ Icc (1 / N) (2 / N)) :
      deriv (cutoffLower N) x = 0 ∧ deriv (deriv (cutoffLower N)) x = 0 := by
    have ho : N * x ∉ Icc (1 : ℝ) 2 := fun hm ↦ hx
      ⟨(div_le_iff₀ hNp).mpr (by simpa only [mul_comm] using hm.1),
       (le_div_iff₀ hNp).mpr (by simpa only [mul_comm] using hm.2)⟩
    obtain ⟨ho₁, ho₂⟩ := cutoffChi_deriv_off ho
    rw [hL₂, hL₁]
    simp [ho₁, ho₂]
  have hUb (x : ℝ) : ‖deriv (cutoffUpper N) x‖ ≤ M₁ / N ∧
      ‖deriv (deriv (cutoffUpper N)) x‖ ≤ M₂ / N ^ 2 := by
    rw [hU₂, hU₁]
    simp only [norm_neg, norm_mul, norm_pow, norm_inv, Real.norm_of_nonneg hNp.le,
      inv_pow, div_eq_mul_inv]
    exact ⟨mul_le_mul_of_nonneg_right (hb _).1 (inv_nonneg.mpr hNp.le),
      mul_le_mul_of_nonneg_right (hb _).2 (inv_nonneg.mpr (sq_nonneg N))⟩
  have hUo (x : ℝ) (hx : x ∉ Icc N (2 * N)) : deriv (cutoffUpper N) x = 0 := by
    have ho : N⁻¹ * x ∉ Icc (1 : ℝ) 2 := by
      rw [mul_comm N⁻¹ x, ← div_eq_mul_inv]
      intro hm
      exact hx ⟨by simpa only [one_mul] using (le_div_iff₀ hNp).mp hm.1,
        (div_le_iff₀ hNp).mp hm.2⟩
    simp only [hU₁, (cutoffChi_deriv_off ho).1, zero_mul, neg_zero]
  have hΔb (x : ℝ) (hx : 0 < x) :
      Real.exp (a * x) * ‖cutoffDiff z q x‖ ≤ 2 * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv (cutoffDiff z q) x‖ ≤ A₁ * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv (deriv (cutoffDiff z q)) x‖ ≤ A₂ * Real.exp (-δ * x) := by
    obtain ⟨hd₁, hd₂⟩ := cutoffDiff_derivs z q
    have hadd (b e : ℂ) :
        Real.exp (a * x) * ‖cutoffExp z x * b - cutoffExp q x * e‖ ≤
          (‖b‖ + ‖e‖) * Real.exp (-δ * x) := by
      refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le).trans ?_
      rw [mul_add, add_mul]
      exact add_le_add (weighted_cutoffExp_le b hx.le hzδ) (weighted_cutoffExp_le e hx.le hqδ)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [cutoffDiff, mul_one, norm_one, one_add_one_eq_two] using hadd 1 1
    · rw [hd₁]; simpa only [A₁, norm_neg] using hadd (-z) (-q)
    · rw [hd₂]; simpa only [A₂, pow_two, norm_mul, norm_neg] using hadd (-z * -z) (-q * -q)
  have h₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2.continuous
  apply weightedCutoffIntegrals_le hδ hNp hf.continuous hs h₂ hs.deriv.deriv
  have htwo : (2 : ℕ∞ω) ≤ ∞ := by simp
  exact cutoff_pointwise_majorant (A₀ := 2) (A₁ := A₁) (A₂ := A₂) (B := B)
    hN hδ hm₁ hm₂ (by dsimp [A₁]; positivity)
    (by dsimp [B]; positivity) (hL.of_le htwo) (hU.of_le htwo) (hΔ.of_le htwo)
    hLr hUr (fun x _ ↦ hLb x) hLo hUb hUo hΔb
    (fun x hx ↦ weighted_cutoffDiff_linear hx.le hz.le hz₀.le)

/-- Both cutoffs are one at a positive point once the real scale is large enough. -/
public theorem cutoffTest_eq_at_large_scale {z : ℂ} {z₀ N x : ℝ}
    (hN : 0 < N) (hx : 0 < x) (hl : 2 / x ≤ N) (hu : x ≤ N) :
    cutoffTest z z₀ N x = Complex.exp (-z * (x : ℂ)) - Complex.exp (-(z₀ : ℂ) * (x : ℂ)) := by
  have h₁ : cutoffLower N x = 1 := cutoffChi_one ((div_le_iff₀ hx).mp hl)
  have h₂ : cutoffChi (N⁻¹ * x) = 0 := cutoffChi_zero (by
    rw [mul_comm N⁻¹ x, ← div_eq_mul_inv]
    exact (div_le_one hN).2 hu)
  change (cutoffLower N x * cutoffUpper N x : ℝ) • cutoffDiff z (z₀ : ℂ) x = _
  simp only [h₁, cutoffUpper, h₂, sub_zero, mul_one, one_smul, cutoffDiff, cutoffExp]

end

end Masullo
