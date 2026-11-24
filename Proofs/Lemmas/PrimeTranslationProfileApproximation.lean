module

public import Lemmas.PrimeTranslationEndpointSchur

import all Lemmas.PrimeTranslationEndpointAsymptotic -- reciprocal sum and affine error bounds
import Mathlib.NumberTheory.LSeries.WeakPNT

/-! # Approximation on the prime-translation endpoint profiles

Source: `bdd74f2:.godel/adhoc/prime-translation-norm.md`, §2 (pointwise
endpoint estimate) and §3 (its use on the endpoint span).
Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.

Scope: the untwisted translation sum on the zero-extended left profile,
approximated by the reflected profile times `exp (D / 2)`. This supplies
analytic input for the pole-cancellation argument, not the pole operator or
its cancellation theorem.
-/

open Filter MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt Topology

namespace Masullo

/-- The left endpoint profile, zero outside `[0,D]`. -/
@[expose] public noncomputable def primeTranslationProfile (D : ℝ) : ℝ → ℝ :=
  (Set.Icc 0 D).indicator (fun x ↦ exp (-x / 2))

/-- The right endpoint profile, obtained by reflecting the left one at `D / 2`. -/
@[expose] public noncomputable def primeTranslationReflectedProfile (D x : ℝ) : ℝ :=
  primeTranslationProfile D (D - x)

/-- The untwisted two-sided translation sum with the strict cutoff `1 ≤ n < exp D`.
For the window operator this sum is evaluated on `[0,D]` with zero-extended input. -/
@[expose] public noncomputable def primeTranslationApply (D : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n * (u (x + log n) + u (x - log n))

private theorem profile_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    primeTranslationProfile D x = exp (-x / 2) :=
  Set.indicator_of_mem hx _

private theorem profile_off {D x : ℝ} (hx : x ∉ Set.Icc 0 D) :
    primeTranslationProfile D x = 0 :=
  Set.indicator_of_notMem hx _

-- An equality at the translated support boundary still lies inside the outer cutoff.
private theorem log_filter_cutoff {D s : ℝ} (hs : s < D) :
    (Finset.Ico 1 ⌈exp D⌉₊).filter (fun n : ℕ ↦ log n ≤ s) =
      Finset.Icc 1 ⌊exp s⌋₊ := by
  ext n
  by_cases hn : 1 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, hn, true_and, Nat.lt_ceil,
      Nat.le_floor_iff (Real.exp_pos s).le, Real.log_le_iff_le_exp hn']
    exact ⟨And.right, fun h ↦ ⟨h.trans_lt (Real.exp_lt_exp.mpr hs), h⟩⟩
  · simp [hn]

private theorem profile_translation_row {D x : ℝ} (hx : x ∈ Set.Ioo 0 D) :
    primeTranslationApply D (primeTranslationProfile D) x = primeTranslationProfile D x *
      ((∑ n ∈ Finset.Icc 1 ⌊exp (D - x)⌋₊, Λ n / (n : ℝ)) + Chebyshev.psi (exp x)) := by
  have hterm (n : ℕ) (hn : 1 ≤ n) :
      Λ n / sqrt n *
          (primeTranslationProfile D (x + log n) + primeTranslationProfile D (x - log n)) =
        (if log n ≤ D - x then exp (-x / 2) * (Λ n / (n : ℝ)) else 0) +
        (if log n ≤ x then exp (-x / 2) * Λ n else 0) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn' : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
    have hlog := Real.log_nonneg hn1
    have hsqrt := Real.sqrt_pos.mpr hn'
    have hexp : exp (log n / 2) = sqrt n := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn']
      congr 1
      ring
    rw [mul_add]
    congr 1
    · by_cases h : log n ≤ D - x
      · rw [ite_eq_left h, profile_on ⟨by linarith [hx.1], by linarith⟩,
          show -(x + log n) / 2 = -x / 2 - log n / 2 by ring, Real.exp_sub, hexp]
        calc
          _ = exp (-x / 2) * (Λ n / (sqrt n) ^ 2) := by field_simp
          _ = _ := by rw [Real.sq_sqrt hn'.le]
      · rw [ite_eq_right h, profile_off (fun hz ↦ h (by linarith [hz.2])), mul_zero]
    · by_cases h : log n ≤ x
      · rw [ite_eq_left h, profile_on ⟨by linarith, by linarith [hx.2]⟩,
          show -(x - log n) / 2 = -x / 2 + log n / 2 by ring, Real.exp_add, hexp]
        field_simp
      · rw [ite_eq_right h, profile_off (fun hz ↦ h (by linarith [hz.1])), mul_zero]
  rw [primeTranslationApply, profile_on ⟨hx.1.le, hx.2.le⟩, psi_eq_sum_Icc_one]
  rw [mul_add (exp (-x / 2)), Finset.mul_sum, Finset.mul_sum,
    ← log_filter_cutoff (sub_lt_self D hx.1), ← log_filter_cutoff hx.2,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n hn ↦ hterm n (Finset.mem_Ico.mp hn).1

private theorem exists_psi_abs_error {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |Chebyshev.psi y - y| ≤ δ * y + C := by
  have hnear : ∀ᶠ y in atTop, |Chebyshev.psi y / y - 1| < δ := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp Chebyshev.tendsto_psi_div_atTop δ hδ)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hnear
  have hC : 0 ≤ Chebyshev.psi Y + |Y| := add_nonneg (Chebyshev.psi_nonneg Y) (abs_nonneg Y)
  refine ⟨Chebyshev.psi Y + |Y|, hC, fun y hy ↦ ?_⟩
  by_cases h : Y ≤ y
  · have hy' := zero_lt_one.trans_le hy
    have herr : |(Chebyshev.psi y - y) / y| < δ := by
      rw [sub_div, div_self hy'.ne']
      exact hY y h
    rw [abs_div, abs_of_pos hy'] at herr
    exact ((div_lt_iff₀ hy').mp herr).le.trans (le_add_of_nonneg_right hC)
  · have hsmall : |Chebyshev.psi y - y| ≤ Chebyshev.psi Y + |Y| := by
      calc
        |Chebyshev.psi y - y| ≤ |Chebyshev.psi y| + |y| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_of_nonneg (Chebyshev.psi_nonneg y), abs_of_nonneg (zero_le_one.trans hy)]
          exact add_le_add (Chebyshev.psi_mono (le_of_not_ge h))
            ((le_of_not_ge h).trans (le_abs_self Y))
    exact hsmall.trans (le_add_of_nonneg_left (mul_nonneg hδ.le (zero_le_one.trans hy)))

/-- The two pieces of the profile error: the relative prime number theorem
error follows the reflected profile, and the affine error follows the left one. -/
public theorem primeTranslationProfileTwoPiece {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D x : ℝ}, x ∈ Set.Ioo 0 D →
      |primeTranslationApply D (primeTranslationProfile D) x -
        exp (D / 2) * primeTranslationReflectedProfile D x| ≤
        δ * exp (D / 2) * primeTranslationReflectedProfile D x +
          (C + (log 4 + 4) * (1 + D)) * primeTranslationProfile D x := by
  obtain ⟨C, hC, hψ⟩ := exists_psi_abs_error hδ
  refine ⟨C, hC, fun {D x} hx ↦ ?_⟩
  let U : ℝ := ∑ n ∈ Finset.Icc 1 ⌊exp (D - x)⌋₊, Λ n / (n : ℝ)
  let f := primeTranslationProfile D x
  let g := primeTranslationReflectedProfile D x
  change |primeTranslationApply D (primeTranslationProfile D) x - exp (D / 2) * g| ≤
    δ * exp (D / 2) * g + (C + (log 4 + 4) * (1 + D)) * f
  have hf : f = exp (-x / 2) := profile_on ⟨hx.1.le, hx.2.le⟩
  have hf₀ : 0 ≤ f := by rw [hf]; positivity
  have hg : g = exp (-(D - x) / 2) :=
    profile_on ⟨sub_nonneg.mpr hx.2.le, sub_le_self D hx.1.le⟩
  have hcross : exp (D / 2) * g = f * exp x := by
    rw [hg, hf, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hrow : primeTranslationApply D (primeTranslationProfile D) x =
      f * (U + Chebyshev.psi (exp x)) := profile_translation_row hx
  have hU₀ : 0 ≤ U := Finset.sum_nonneg fun n _ ↦
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hU : U ≤ (log 4 + 4) * (1 + D) := by
    have hrec := reciprocal_vonMangoldt_le (Real.one_le_exp (sub_nonneg.mpr hx.2.le))
    rw [Real.log_exp] at hrec
    exact hrec.trans (mul_le_mul_of_nonneg_left (by linarith [hx.1])
      (add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)))
  calc
    _ = f * |U + (Chebyshev.psi (exp x) - exp x)| := by
      rw [hrow, hcross, ← mul_sub, add_sub_assoc, abs_mul, abs_of_nonneg hf₀]
    _ ≤ f * (U + |Chebyshev.psi (exp x) - exp x|) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans_eq (by rw [abs_of_nonneg hU₀])) hf₀
    _ ≤ f * ((log 4 + 4) * (1 + D) + (δ * exp x + C)) :=
      mul_le_mul_of_nonneg_left (add_le_add hU (hψ _ (Real.one_le_exp hx.1.le))) hf₀
    _ = δ * (f * exp x) + (C + (log 4 + 4) * (1 + D)) * f := by ring
    _ = _ := by rw [← hcross]; ring

/-- On the entire open window, the two-sided translation sum on `f_D` is
uniformly approximated by `exp (D / 2) * g_D` with relative error measured
against `exp (D / 2) * (f_D + g_D)`. -/
public theorem primeTranslationProfileApproximationOn {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ x ∈ Set.Ioo 0 D,
      |primeTranslationApply D (primeTranslationProfile D) x -
        exp (D / 2) * primeTranslationReflectedProfile D x| ≤
        η * exp (D / 2) * (primeTranslationProfile D x + primeTranslationReflectedProfile D x) := by
  obtain ⟨C, _, hC⟩ := primeTranslationProfileTwoPiece hη
  filter_upwards [eventually_affine_lt_exp C (log 4 + 4) hη] with D hD
  intro x hx
  have hf : 0 ≤ primeTranslationProfile D x := by
    rw [profile_on ⟨hx.1.le, hx.2.le⟩]
    positivity
  calc
    _ ≤ _ := hC hx
    _ ≤ η * exp (D / 2) * primeTranslationReflectedProfile D x +
          η * exp (D / 2) * primeTranslationProfile D x :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hD.le hf)
    _ = _ := by ring

/-- The endpoint profile approximation almost everywhere on the closed window.
The endpoints are excluded in the exact row calculation because the outer
cutoff is strict even when `exp D` is an integer. -/
public theorem primeTranslationProfileApproximation {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ᵐ x ∂volume.restrict (Set.Icc 0 D),
      |primeTranslationApply D (primeTranslationProfile D) x -
        exp (D / 2) * primeTranslationReflectedProfile D x| ≤
        η * exp (D / 2) * (primeTranslationProfile D x + primeTranslationReflectedProfile D x) := by
  filter_upwards [primeTranslationProfileApproximationOn hη] with D hD
  have hIoo : Set.Ioo 0 D =ᵐ[(volume : Measure ℝ)] Set.Icc 0 D := Ioo_ae_eq_Icc
  rw [← Measure.restrict_congr_set hIoo]
  exact (ae_restrict_mem measurableSet_Ioo).mono hD

end Masullo
