module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # One-shell sampling for a prime translation

Source: `309f4808a753:.godel/conjectures/closed/unsigned-edge-rh-row-bound.md`,
lines 63–83 (scan pin `df36e0b4e122`). Owning check session:
`01a21064-e15a-7bed-9349-0a50688b4367`.

Scope: one clipped dyadic shell and one of the two translation signs. The
consumer is the four-type dyadic assembly in source lines 78–83. The short-interval
von Mangoldt estimate is an input here. In Lean the assembled estimate would feed
`hrrow` in `Lemmas.PrimeTranslationCorrectedSchur`; this is not that full row.
-/

open MeasureTheory Set
open Real (log sqrt)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

/-- At a given integration point, the visible samples fit in a single half-open
interval of length `8 * K * τ`. The unit of padding also covers a lone sample. -/
private theorem shellWeightedOverlap {K τ a ε M : ℝ} {S : Finset ℕ}
    (hK : 0 < K) (hτ : 0 < τ) (hpad : 1 ≤ 4 * K * τ)
    (hε : ε = 1 ∨ ε = -1) (hM : 0 ≤ M)
    (hS : ∀ n ∈ S, 2 ≤ n ∧ K ≤ (n : ℝ) ∧ (n : ℝ) < 2 * K)
    (hmass : ∀ t : ℝ,
      (∑ n ∈ (Finset.Ico ⌈K⌉₊ ⌈2 * K⌉₊).filter
        (fun n : ℕ ↦ t < (n : ℝ) ∧ (n : ℝ) ≤ t + 8 * K * τ), Λ n) ≤ M * (8 * K * τ))
    (s : ℝ) :
    (∑ n ∈ S.filter (fun n : ℕ ↦ s ∈ Icc (a + ε * log (n : ℝ) - τ)
      (a + ε * log (n : ℝ) + τ)), Λ n / sqrt (n : ℝ)) ≤ M * (8 * K * τ) / sqrt K := by
  let T := S.filter (fun n : ℕ ↦
    s ∈ Icc (a + ε * log (n : ℝ) - τ) (a + ε * log (n : ℝ) + τ))
  change (∑ n ∈ T, Λ n / sqrt (n : ℝ)) ≤ _
  have hsqrtK : 0 < sqrt K := Real.sqrt_pos.2 hK
  by_cases hT : T.Nonempty
  · let m := T.min' hT
    have hm := Finset.mem_filter.mp (T.min'_mem hT)
    have hmpos : 0 < (m : ℝ) := hK.trans_le (hS m hm.1).2.1
    let t : ℝ := (m : ℝ) - 1
    have hsub : T ⊆ (Finset.Ico ⌈K⌉₊ ⌈2 * K⌉₊).filter
        (fun n : ℕ ↦ t < (n : ℝ) ∧ (n : ℝ) ≤ t + 8 * K * τ) := by
      intro n hn
      have hnT := Finset.mem_filter.mp hn
      have hnShell := (hS n hnT.1).2
      have hnpos : 0 < (n : ℝ) := hK.trans_le hnShell.1
      have hmn : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (T.min'_le n hn)
      have hs_m := hm.2
      have hs_n := hnT.2
      have hlogdiam : log (n : ℝ) - log (m : ℝ) ≤ 2 * τ := by
        rcases hε with rfl | rfl
        · simp only [one_mul] at hs_m hs_n
          linarith only [hs_n.1, hs_m.2]
        · simp only [neg_mul, one_mul] at hs_m hs_n
          linarith only [hs_m.1, hs_n.2]
      have hlog : 1 - (m : ℝ) / n ≤ log (n : ℝ) - log (m : ℝ) := by
        rw [← Real.log_div hnpos.ne' hmpos.ne', ← inv_div (n : ℝ) m]
        exact Real.one_sub_inv_le_log_of_pos (div_pos hnpos hmpos)
      have hdiam : (n : ℝ) - m ≤ 4 * K * τ := by
        calc
          (n : ℝ) - m = (1 - (m : ℝ) / n) * n := by
            rw [sub_mul, one_mul, div_mul_cancel₀ _ hnpos.ne']
          _ ≤ (log (n : ℝ) - log (m : ℝ)) * n := mul_le_mul_of_nonneg_right hlog hnpos.le
          _ ≤ (2 * τ) * n := mul_le_mul_of_nonneg_right hlogdiam hnpos.le
          _ ≤ (2 * τ) * (2 * K) := mul_le_mul_of_nonneg_left hnShell.2.le (by positivity)
          _ = 4 * K * τ := by ring
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hnShell.1, Nat.lt_ceil.mpr hnShell.2⟩,
          by dsimp [t]; linarith only [hmn], by dsimp [t]; linarith only [hpad, hdiam]⟩
    calc
      (∑ n ∈ T, Λ n / sqrt (n : ℝ)) ≤ ∑ n ∈ T, Λ n / sqrt K := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hsqrtK
          (Real.sqrt_le_sqrt (hS n (Finset.mem_filter.mp hn).1).2.1)
      _ = (∑ n ∈ T, Λ n) / sqrt K := (Finset.sum_div _ _ _).symm
      _ ≤ M * (8 * K * τ) / sqrt K := (div_le_div_iff_of_pos_right hsqrtK).mpr
        ((Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)).trans (hmass t))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty]
    positivity

/-- Local pointwise averaging on an arbitrary clipped shell costs the exact
unprofiled mass in the constant term and `8 * B * M * sqrt K` times the integral
on the padded logarithmic window. The mass premise is for the whole shell
intersected with each ordinary interval `(t, t + 8 * K * τ]`, not for the clip. -/
public theorem primeTranslationShellSampling {K τ a ε A B M : ℝ} {S : Finset ℕ}
    {F : ℝ → ℝ} (hK : 1 ≤ K) (hτ : 0 < τ) (_hτ₁ : τ ≤ 1) (hpad : 1 ≤ 4 * K * τ)
    (hε : ε = 1 ∨ ε = -1) (hS : ∀ n ∈ S, 2 ≤ n ∧ K ≤ (n : ℝ) ∧ (n : ℝ) < 2 * K)
    (hF_nonneg : ∀ x, 0 ≤ F x) (hF : LocallyIntegrable F volume)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (haverage : ∀ n ∈ S, F (a + ε * log (n : ℝ)) ≤ A + (B / τ) *
      ∫ s in Icc (a + ε * log (n : ℝ) - τ) (a + ε * log (n : ℝ) + τ), F s)
    (hmass : ∀ t : ℝ,
      (∑ n ∈ (Finset.Ico ⌈K⌉₊ ⌈2 * K⌉₊).filter
        (fun n : ℕ ↦ t < (n : ℝ) ∧ (n : ℝ) ≤ t + 8 * K * τ), Λ n) ≤ M * (8 * K * τ)) :
    (∑ n ∈ S, (Λ n / sqrt (n : ℝ)) * F (a + ε * log (n : ℝ))) ≤
      A * (∑ n ∈ S, Λ n / sqrt (n : ℝ)) + 8 * B * M * sqrt K *
        ∫ s in (if ε = 1 then Icc (a + log K - τ) (a + log (2 * K) + τ)
          else Icc (a - log (2 * K) - τ) (a - log K + τ)), F s := by
  let z (n : ℕ) := a + ε * log (n : ℝ)
  let I (n : ℕ) := Icc (z n - τ) (z n + τ)
  let J := if ε = 1 then Icc (a + log K - τ) (a + log (2 * K) + τ)
    else Icc (a - log (2 * K) - τ) (a - log K + τ)
  let w (n : ℕ) := Λ n / sqrt (n : ℝ)
  let C := M * (8 * K * τ) / sqrt K
  let g (n : ℕ) (s : ℝ) := w n * (I n).indicator F s
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hsqrtK : 0 < sqrt K := Real.sqrt_pos.2 hKpos
  have hw (n : ℕ) : 0 ≤ w n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hsub (n : ℕ) (hn : n ∈ S) : I n ⊆ J := by
    have hnShell := (hS n hn).2
    have hlo := Real.log_le_log hKpos hnShell.1
    have hhi := Real.log_le_log (hKpos.trans_le hnShell.1) hnShell.2.le
    intro s hs
    dsimp [I, z] at hs
    dsimp [J]
    rcases hε with rfl | rfl
    · simp only [one_mul] at hs
      rw [ite_eq_left (rfl : (1 : ℝ) = 1)]
      exact ⟨by linarith only [hs.1, hlo], by linarith only [hs.2, hhi]⟩
    · rw [ite_eq_right (by norm_num : (-1 : ℝ) ≠ 1)]
      simp only [neg_mul, one_mul] at hs
      exact ⟨by linarith only [hs.1, hhi], by linarith only [hs.2, hlo]⟩
  have hJcompact : IsCompact J := by
    dsimp [J]
    split <;> exact isCompact_Icc
  have hJmeas : MeasurableSet J := hJcompact.isClosed.measurableSet
  have hJint : Integrable (J.indicator F) volume :=
    (hF.integrableOn_isCompact hJcompact).integrable_indicator hJmeas
  have hg (n : ℕ) (_ : n ∈ S) : Integrable (g n) volume :=
    ((hF.integrableOn_isCompact (isCompact_Icc : IsCompact (I n))).integrable_indicator
      measurableSet_Icc).const_mul (w n)
  have hterms (n : ℕ) : (∫ s, g n s) = w n * ∫ s in I n, F s := by
    dsimp only [g]
    rw [integral_const_mul, integral_indicator measurableSet_Icc]
  have hsum (s : ℝ) : (∑ n ∈ S, g n s) = (∑ n ∈ S.filter (fun n ↦ s ∈ I n), w n) * F s := by
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hs : s ∈ I n
    · simp only [g, Set.indicator_of_mem hs, ite_eq_left hs]
    · simp only [g, Set.indicator_of_notMem hs, mul_zero, ite_eq_right hs]
  have hpoint : (fun s ↦ ∑ n ∈ S, g n s) ≤ fun s ↦ C * J.indicator F s := by
    intro s
    change (∑ n ∈ S, g n s) ≤ C * J.indicator F s
    by_cases hs : s ∈ J
    · rw [hsum, Set.indicator_of_mem hs]
      exact mul_le_mul_of_nonneg_right (shellWeightedOverlap hKpos hτ hpad hε hM hS hmass s)
        (hF_nonneg s)
    · rw [Set.indicator_of_notMem hs, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun n hn ↦ ?_)
      have hns : s ∉ I n := fun h ↦ hs (hsub n hn h)
      simp only [g, Set.indicator_of_notMem hns, mul_zero]
  have havg : (∑ n ∈ S, w n * ∫ s in I n, F s) ≤ C * ∫ s in J, F s := by
    calc
      _ = ∑ n ∈ S, ∫ s, g n s := Finset.sum_congr rfl fun n _ ↦ (hterms n).symm
      _ = ∫ s, ∑ n ∈ S, g n s := (integral_finsetSum S hg).symm
      _ ≤ ∫ s, C * J.indicator F s :=
        integral_mono (integrable_finsetSum S hg) (hJint.const_mul C) hpoint
      _ = _ := by rw [integral_const_mul, integral_indicator hJmeas]
  have hscale : B / τ * C = 8 * B * M * sqrt K := by
    have hratio : K / sqrt K = sqrt K :=
      (div_eq_iff hsqrtK.ne').2 (Real.mul_self_sqrt hKpos.le).symm
    calc
      B / τ * C = 8 * B * M * (K / sqrt K) := by
        dsimp [C]
        field_simp [hτ.ne', hsqrtK.ne']
      _ = _ := by rw [hratio]
  change (∑ n ∈ S, w n * F (z n)) ≤
    A * (∑ n ∈ S, w n) + 8 * B * M * sqrt K * ∫ s in J, F s
  calc
    _ ≤ ∑ n ∈ S, w n * (A + B / τ * ∫ s in I n, F s) :=
      Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (haverage n hn) (hw n)
    _ = A * (∑ n ∈ S, w n) + B / τ * (∑ n ∈ S, w n * ∫ s in I n, F s) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ ↦ by ring
    _ ≤ A * (∑ n ∈ S, w n) + B / τ * (C * ∫ s in J, F s) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left havg (div_nonneg hB hτ.le))
    _ = _ := by rw [← mul_assoc, hscale]

end Masullo
