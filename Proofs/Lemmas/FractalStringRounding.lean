module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Rounding the fractal-string counting tail

For `t > T`, the reciprocal-length counting kernel `⌊x / t⌋₊` is a finite sum of
interval indicators, one per positive integer threshold. The lower cutoff `T` is
excluded, but an atom at an upper endpoint `x / n` must be counted. For the two
positive Stieltjes measures with cumulatives `G` and `F`, the difference of the
rounded tails is thus a sum of increments of `G - F`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace FractalStringRounding

/-- `k + 1` is the positive threshold index. The non-strict inequality at `x / (k + 1)` includes
exact integer coincidences. -/
public theorem floor_div_eq_sum_indicator {T x t : ℝ} (hT : 0 < T) (hx : 0 ≤ x)
    (ht : T < t) :
    ⌊x / t⌋₊ = ∑ k ∈ Finset.range ⌊x / T⌋₊,
      (Ioc T (x / ((k + 1 : ℕ) : ℝ))).indicator (fun _ ↦ (1 : ℕ)) t := by
  classical
  have hmem (k : ℕ) : t ∈ Ioc T (x / ((k + 1 : ℕ) : ℝ)) ↔ k < ⌊x / t⌋₊ := by
    have hk : 0 < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
    rw [mem_Ioc, and_iff_right ht, le_div_iff₀ hk, mul_comm t, ← le_div_iff₀ (hT.trans ht),
      ← Nat.le_floor_iff' (Nat.succ_ne_zero k), Nat.succ_le_iff]
  have hle : ⌊x / t⌋₊ ≤ ⌊x / T⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_left hx hT ht.le)
  have hfilter : (Finset.range ⌊x / T⌋₊).filter (fun k ↦
      t ∈ Ioc T (x / ((k + 1 : ℕ) : ℝ))) = Finset.range ⌊x / t⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, hmem]
    exact ⟨And.right, fun hk ↦ ⟨hk.trans_le hle, hk⟩⟩
  symm
  calc
    _ = ∑ _k ∈ (Finset.range ⌊x / T⌋₊).filter (fun k ↦
        t ∈ Ioc T (x / ((k + 1 : ℕ) : ℝ))), (1 : ℕ) := by
      rw [Finset.sum_filter]
      simp only [indicator_apply]
    _ = ⌊x / t⌋₊ := by
      rw [hfilter]
      simp

private theorem indicator_floor_tail_eq_sum {T x : ℝ} (hT : 0 < T) (hx : 0 ≤ x) :
    (Ioi T).indicator (fun t ↦ (⌊x / t⌋₊ : ℝ)) = fun t ↦
      ∑ k ∈ Finset.range ⌊x / T⌋₊,
        (Ioc T (x / ((k + 1 : ℕ) : ℝ))).indicator (fun _ ↦ (1 : ℝ)) t := by
  classical
  funext t
  by_cases ht : T < t
  · rw [indicator_of_mem ht, floor_div_eq_sum_indicator hT hx ht, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [indicator_apply]
    split_ifs <;> simp
  · simp [ht]

/-- The rounded tail is integrable for any locally finite positive measure. Each interval
in the sum has finite mass, even if the entire tail has infinite mass. -/
public theorem floor_tail_integrable_and_eq_sum (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    {T x : ℝ} (hT : 0 < T) (hx : 0 ≤ x) :
    IntegrableOn (fun t ↦ (⌊x / t⌋₊ : ℝ)) (Ioi T) μ ∧
      (∫ t in Ioi T, (⌊x / t⌋₊ : ℝ) ∂μ) =
        ∑ k ∈ Finset.range ⌊x / T⌋₊, μ.real (Ioc T (x / ((k + 1 : ℕ) : ℝ))) := by
  have hi (k : ℕ) : Integrable
      ((Ioc T (x / ((k + 1 : ℕ) : ℝ))).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  constructor
  · rw [← integrable_indicator_iff measurableSet_Ioi, indicator_floor_tail_eq_sum hT hx]
    exact integrable_finsetSum _ fun k _ ↦ hi k
  · rw [← integral_indicator measurableSet_Ioi, indicator_floor_tail_eq_sum hT hx,
      integral_finsetSum _ (fun k _ ↦ hi k)]
    simp only [integral_indicator_const (1 : ℝ) measurableSet_Ioc, smul_eq_mul, mul_one]

private theorem cutoff_le_threshold {T x : ℝ} (hT : 0 < T) {k : ℕ}
    (hk : k ∈ Finset.range ⌊x / T⌋₊) : T ≤ x / ((k + 1 : ℕ) : ℝ) := by
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ x / T :=
    (Nat.le_floor_iff' (Nat.succ_ne_zero k)).1 (Nat.succ_le_of_lt (Finset.mem_range.1 hk))
  exact (le_div_iff₀ hkpos).2 (by simpa only [mul_comm T] using (le_div_iff₀ hT).1 hcast)

/-- The finite discrepancy bound for the harmonic thresholds. If a threshold is exactly `T`,
its increment is zero and it need not be removed from the sum. -/
public theorem abs_threshold_discrepancy_le {T x : ℝ} (hT : 0 < T) (E : ℝ → ℝ)
    (hE : ∀ u, T ≤ u → |E u| ≤ 1) :
    |∑ k ∈ Finset.range ⌊x / T⌋₊, (E (x / ((k + 1 : ℕ) : ℝ)) - E T)| ≤
      2 * (⌊x / T⌋₊ : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.range ⌊x / T⌋₊, |E (x / ((k + 1 : ℕ) : ℝ)) - E T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range ⌊x / T⌋₊, (2 : ℝ) := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      let u := x / ((k + 1 : ℕ) : ℝ)
      have htri : |E u - E T| ≤ |E u| + |E T| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (E u) 0 (E T)
      exact htri.trans ((add_le_add (hE u (cutoff_le_threshold hT hk)) (hE T le_rfl)).trans
        (by norm_num))
    _ = 2 * (⌊x / T⌋₊ : ℝ) := by simp [nsmul_eq_mul, mul_comm]

/-- The exact difference of the two positive Stieltjes tail integrals. This uses the
`Ioc` mass formula, including when the interval is empty because `x / (k + 1) = T`. -/
public theorem stieltjes_tail_sub_eq_sum {T x : ℝ} (hT : 0 < T) (hx : 0 ≤ x)
    (G F : StieltjesFunction ℝ) :
    (∫ t in Ioi T, (⌊x / t⌋₊ : ℝ) ∂G.measure) -
        (∫ t in Ioi T, (⌊x / t⌋₊ : ℝ) ∂F.measure) =
      ∑ k ∈ Finset.range ⌊x / T⌋₊,
        ((G (x / ((k + 1 : ℕ) : ℝ)) - F (x / ((k + 1 : ℕ) : ℝ))) - (G T - F T)) := by
  rw [(floor_tail_integrable_and_eq_sum G.measure hT hx).2,
    (floor_tail_integrable_and_eq_sum F.measure hT hx).2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hnext := cutoff_le_threshold hT hk
  simp only [Measure.real, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (G.mono hnext)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hnext))]
  abel

/-- A cumulative discrepancy of at most one bounds the difference of the rounded
Stieltjes tails by twice the number of thresholds. -/
public theorem abs_stieltjes_tail_sub_le {T x : ℝ} (hT : 0 < T) (hx : 0 ≤ x)
    (G F : StieltjesFunction ℝ) (hE : ∀ u, T ≤ u → |G u - F u| ≤ 1) :
    |(∫ t in Ioi T, (⌊x / t⌋₊ : ℝ) ∂G.measure) -
        (∫ t in Ioi T, (⌊x / t⌋₊ : ℝ) ∂F.measure)| ≤ 2 * (⌊x / T⌋₊ : ℝ) := by
  rw [stieltjes_tail_sub_eq_sum hT hx G F]
  exact abs_threshold_discrepancy_le hT (fun u ↦ G u - F u) hE

end FractalStringRounding
