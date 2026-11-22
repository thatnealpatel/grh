module

public import Lemmas.CompactLogMellin
public import Theorems.MonogenicPeriodizationSection
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Tactic.FieldSimp

/-! # Fourier coefficients, uniqueness, and a difference primitive for compact log profiles

These give the log-coordinate steps in the compact-away repair of Masullo's
Lemma 5.3.4.2(2), p. 260, at period `log 3`. They do not assert pole
removal or identify an adelic lift.
-/

open ContinuousMap Function MeasureTheory Set TopologicalSpace
open scoped ContDiff FourierTransform

namespace Masullo

-- On each compact, only finitely many integer translates can meet the support.
private theorem finite_int_translates_on {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    (hc : HasCompactSupport g) {K : Set ℝ} (hK : IsCompact K) :
    {k : ℤ | ∃ x ∈ K, g (x + (k : ℝ) * L) ≠ 0}.Finite := by
  obtain ⟨A, hA⟩ := hc.bddAbove_image continuous_abs.continuousOn
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_abs.continuousOn
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : ℤ) ((A + B) / L))).subset ?_
  rintro k ⟨x, hxK, hx⟩
  have h1 := hA (mem_image_of_mem _ (subset_tsupport _ hx))
  have h2 := hB (mem_image_of_mem _ hxK)
  rw [Metric.mem_closedBall, Int.dist_eq, Int.cast_zero, sub_zero, le_div_iff₀ hL]
  have h := abs_sub_le (x + (k : ℝ) * L) 0 x
  rw [sub_zero, add_sub_cancel_left, zero_sub, abs_neg, abs_mul, abs_of_pos hL] at h
  linarith

private theorem summable_norm_restrict_int_translate {f : C(ℝ, ℂ)}
    (hf : HasCompactSupport (f : ℝ → ℂ)) (K : Compacts ℝ) :
    Summable fun k : ℤ ↦ ‖(f.comp (ContinuousMap.addRight k)).restrict K‖ := by
  apply summable_of_hasFiniteSupport
  refine (finite_int_translates_on zero_lt_one hf K.isCompact).subset ?_
  intro k hk
  by_contra h
  apply hk
  simp only [norm_eq_zero]
  ext x
  change f ((x : ℝ) + (k : ℝ)) = 0
  by_contra hx
  exact h ⟨x, x.property, by simpa only [mul_one] using hx⟩

private theorem fourier_rescale_neg {L : ℝ} (hL : 0 < L) (g : ℝ → ℂ) (n : ℤ) :
    𝓕 (fun u : ℝ ↦ g (L * u)) (((-n : ℤ) : ℝ)) =
      compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) / (L : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let F (x : ℝ) := g x * Complex.exp ((2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) * x)
  have h (u : ℝ) : Complex.exp ((↑(-2 * Real.pi * u * ((-n : ℤ) : ℝ)) : ℂ) * Complex.I) •
      g (L * u) = F (L * u) := by
    simp only [smul_eq_mul, F, mul_comm (Complex.exp _) (g _)]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  simp_rw [h]
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hL), Complex.real_smul,
    Complex.ofReal_inv, div_eq_inv_mul]
  rfl

/-- The normalized Fourier coefficient at `-n` of the `L`-periodization of a
continuous compact log profile is its positive imaginary Mellin sample divided by `L`. -/
public theorem fourierCoeffOn_logPeriodization_neg {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    (hg : Continuous g) (hc : HasCompactSupport g) (n : ℤ) :
    fourierCoeffOn (a := 0) hL (logPeriodization L g) (-n) =
      compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) / (L : ℂ) := by
  let f : C(ℝ, ℂ) := ⟨fun u ↦ g (L * u), hg.comp (continuous_const.mul continuous_id)⟩
  have hf : HasCompactSupport (f : ℝ → ℂ) :=
    hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne')
  have hs := summable_norm_restrict_int_translate hf
  have hs' : Summable fun k : ℤ ↦ f.comp (ContinuousMap.addRight (k : ℝ)) :=
    summable_of_locally_summable_norm hs
  let P₁ := (f.periodic_tsum_comp_add_zsmul 1).lift
  have hP (u : ℝ) : P₁ (u : UnitAddCircle) = logPeriodization L g (L * u) := by
    simp only [P₁, Periodic.lift_coe, zsmul_one, logPeriodization]
    rw [← ContinuousMap.tsum_apply hs']
    congr 1
    funext k
    change g (L * (u + k)) = g (L * u + (k : ℝ) * L)
    congr 1
    ring
  have hchar (u : ℝ) : fourier n (u : UnitAddCircle) =
      fourier n ((L * u : ℝ) : AddCircle L) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_mul]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  have hcoeff : fourierCoeff P₁ (-n) =
      fourierCoeffOn (a := 0) hL (logPeriodization L g) (-n) := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
    simp only [neg_neg, zero_add, div_one, one_smul, sub_zero, one_div]
    simp_rw [hP, hchar]
    let F (x : ℝ) := fourier n (x : AddCircle L) • logPeriodization L g x
    simpa only [F, mul_zero, mul_one, fourier_coe_apply, sub_zero] using
      (intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) F hL.ne')
  rw [← hcoeff]
  exact (Real.fourierCoeff_tsum_comp_add hs (-n)).trans (fourier_rescale_neg hL g n)

/-- A continuous compact log profile with zero Mellin samples on the imaginary
lattice of period `L` has identically zero `L`-periodization. -/
public theorem logPeriodization_eq_zero_of_compactLogMellin_samples_eq_zero {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hM : ∀ n : ℤ, compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) = 0)
    (x : ℝ) : logPeriodization L g x = 0 := by
  let f : C(ℝ, ℂ) := ⟨fun u ↦ g (L * u), hg.comp (continuous_const.mul continuous_id)⟩
  have hf : HasCompactSupport (f : ℝ → ℂ) :=
    hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne')
  have hF (n : ℤ) : 𝓕 (f : ℝ → ℂ) (n : ℝ) = 0 := by
    simpa only [f, ContinuousMap.coe_mk, neg_neg, hM, zero_div] using fourier_rescale_neg hL g (-n)
  have hsum : Summable fun n : ℤ ↦ 𝓕 (f : ℝ → ℂ) (n : ℝ) := by
    simp only [hF, summable_zero]
  have hP := Real.tsum_eq_tsum_fourier (summable_norm_restrict_int_translate hf) hsum (x / L)
  simp only [hF, zero_mul, tsum_zero] at hP
  have harg (k : ℤ) : L * (x / L + k) = x + (k : ℝ) * L := by
    rw [mul_add, mul_comm L (x / L), div_mul_cancel₀ _ hL.ne', mul_comm L (k : ℝ)]
  simpa only [f, ContinuousMap.coe_mk, harg, logPeriodization] using hP

/-- The forward one-sided translate sum in the real log coordinate. -/
@[expose] public noncomputable def logDifferencePrimitive (L : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℕ, g (x + (k : ℝ) * L)

private theorem logDifferencePrimitive_eqOn_finset {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    (hc : HasCompactSupport g) {K : Set ℝ} (hK : IsCompact K) :
    ∃ s : Finset ℕ, EqOn (logDifferencePrimitive L g)
      (fun x ↦ ∑ k ∈ s, g (x + (k : ℝ) * L)) K := by
  classical
  have hf := (finite_int_translates_on hL hc hK).preimage
    (Nat.cast_injective (R := ℤ)).injOn
  refine ⟨hf.toFinset, fun x hx ↦ tsum_eq_sum (fun k hk ↦ ?_)⟩
  by_contra h
  exact hk (hf.mem_toFinset.mpr ⟨x, hx, by simpa only [Int.cast_natCast] using h⟩)

/-- For a compactly supported profile, the forward translate sum preserves
`C^n` regularity, independently of whether the periodization vanishes. -/
public theorem contDiff_logDifferencePrimitive {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    {n : ℕ∞ω} (hg : ContDiff ℝ n g) (hc : HasCompactSupport g) :
    ContDiff ℝ n (logDifferencePrimitive L g) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  obtain ⟨s, heq⟩ := logDifferencePrimitive_eqOn_finset hL hc
    (isCompact_Icc (α := ℝ) (a := x - 1) (b := x + 1))
  have hsum : ContDiff ℝ n (fun y : ℝ ↦ ∑ k ∈ s, g (y + (k : ℝ) * L)) :=
    ContDiff.sum fun k _ ↦ hg.comp (contDiff_id.add contDiff_const)
  apply hsum.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show x - 1 < x by linarith) (show x < x + 1 by linarith)]
    with y hy using heq hy

/-- Zero periodization makes the forward translate sum a continuous, compactly
supported primitive for the difference with its translate by `L`. -/
public theorem logDifferencePrimitive_spec {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hP : ∀ x : ℝ, logPeriodization L g x = 0) :
    Continuous (logDifferencePrimitive L g) ∧ HasCompactSupport (logDifferencePrimitive L g) ∧
      ∀ x : ℝ, g x = logDifferencePrimitive L g x - logDifferencePrimitive L g (x + L) := by
  have hs (x : ℝ) : Summable (fun k : ℤ ↦ g (x + (k : ℝ) * L)) := by
    refine summable_of_hasFiniteSupport ((finite_int_translates_on hL hc
      (isCompact_singleton (x := x))).subset ?_)
    exact fun k hk ↦ ⟨x, mem_singleton x, hk⟩
  have hnat (x : ℝ) : Summable (fun k : ℕ ↦ g (x + (k : ℝ) * L)) := by
    simpa only [Function.comp_def, Int.cast_natCast] using
      (hs x).comp_injective (Nat.cast_injective (R := ℤ))
  refine ⟨continuous_iff_continuousAt.mpr (fun x ↦ ?_), ?_, fun x ↦ ?_⟩
  · obtain ⟨s, heq⟩ := logDifferencePrimitive_eqOn_finset hL hc
      (isCompact_Icc (α := ℝ) (a := x - 1) (b := x + 1))
    have hcont : Continuous (fun y : ℝ ↦ ∑ k ∈ s, g (y + (k : ℝ) * L)) :=
      continuous_finsetSum _ fun k _ ↦ hg.comp (continuous_id.add continuous_const)
    apply hcont.continuousAt.congr
    filter_upwards [Icc_mem_nhds (show x - 1 < x by linarith) (show x < x + 1 by linarith)]
      with y hy using (heq hy).symm
  · obtain ⟨a, ha⟩ := hc.bddBelow
    obtain ⟨b, hb⟩ := hc.bddAbove
    have hz {y : ℝ} (hy : y < a ∨ b < y) : g y = 0 := by
      by_contra h
      have ht := subset_tsupport g h
      exact hy.elim (fun hya ↦ (not_lt_of_ge (ha ht)) hya)
        (fun hby ↦ (not_lt_of_ge (hb ht)) hby)
    apply HasCompactSupport.intro (K := Icc a b) isCompact_Icc
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hxa | hbx
    · let f (k : ℤ) := g (x + (k : ℝ) * L)
      have hneg : Summable (fun k : ℕ ↦ f (-(k + 1))) :=
        (hs x).comp_injective (show Injective Int.negSucc from @Int.negSucc.inj)
      have hsplit : logPeriodization L g x = logDifferencePrimitive L g x +
          ∑' k : ℕ, f (-(k + 1)) := by
        exact tsum_of_nat_of_neg_add_one (f := f) (by simpa only [f, Int.cast_natCast] using hnat x)
          hneg
      have ht : ∀ k : ℕ, f (-(k + 1)) = 0 := by
        intro k
        apply hz (Or.inl (lt_of_le_of_lt ?_ hxa))
        push_cast
        have hm := mul_nonpos_of_nonpos_of_nonneg (a := -((k : ℝ) + 1))
          (neg_nonpos.mpr (by positivity)) hL.le
        linarith
      rw [tsum_congr ht, tsum_zero, add_zero, hP] at hsplit
      exact hsplit.symm
    · unfold logDifferencePrimitive
      rw [tsum_congr (fun k ↦ hz (Or.inr (lt_of_lt_of_le hbx
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hL.le))))), tsum_zero]
  · have hshift (k : ℕ) : x + ((k + 1 : ℕ) : ℝ) * L = x + L + (k : ℝ) * L := by
      push_cast
      ring
    exact eq_sub_of_add_eq (by simpa only [logDifferencePrimitive, Nat.cast_zero, zero_mul,
      add_zero, hshift] using (hnat x).tsum_eq_zero_add.symm)

end Masullo
