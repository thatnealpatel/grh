module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Polynomial tail of a boundary Mellin jet -/

open MeasureTheory Set

namespace Masullo

/-- Squared divided jet with the exponential factor removed. -/
@[expose] public noncomputable def sobolevJetPolynomial (s : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  |x| ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)

@[simp] public theorem sobolevJetPolynomial_neg (s : ℝ) (m : ℕ) (x : ℝ) :
    sobolevJetPolynomial s m (-x) = sobolevJetPolynomial s m x := by
  simp only [sobolevJetPolynomial, abs_neg, neg_sq]

private theorem continuous_sobolevJetPolynomial (s : ℝ) (m : ℕ) :
    Continuous (sobolevJetPolynomial s m) := by
  unfold sobolevJetPolynomial
  exact (continuous_abs.pow _).div
    ((show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
      (fun x ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))))
    (fun x ↦ ne_of_gt (by positivity))

private theorem sobolevJetPolynomial_compare {s x : ℝ} (hs : 0 ≤ s) (hx : 1 < x) (m : ℕ) :
    sobolevJetPolynomial s m x ≤ x ^ (2 * (m : ℝ) - s) ∧
    x ^ (2 * (m : ℝ) - s) ≤ (2 : ℝ) ^ (s / 2) * sobolevJetPolynomial s m x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hbase : (x ^ 2 : ℝ) ^ (s / 2) = x ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hlower : x ^ s ≤ (1 + x ^ 2) ^ (s / 2) := by
    rw [← hbase]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hupper : (1 + x ^ 2) ^ (s / 2) ≤ (2 : ℝ) ^ (s / 2) * x ^ s := by
    rw [← hbase, ← Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg x)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg (x - 1)]) (by positivity)
  rw [sobolevJetPolynomial, abs_of_pos hx0, Real.rpow_sub hx0,
    show 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
  refine ⟨div_le_div_of_nonneg_left (by positivity) (by positivity) hlower, ?_⟩
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ x ^ (2 * m) * ((2 : ℝ) ^ (s / 2) * x ^ s) := by gcongr
    _ = _ := by ring

/-- On the positive tail the reciprocal Sobolev weight gives the ordinary
power test with exponent `2m - s`, including divergence at exponent `-1`. -/
public theorem integrableOn_sobolevJetPolynomial_Ioi_iff {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    IntegrableOn (sobolevJetPolynomial s m) (Ioi 1) ↔ 2 * (m : ℝ) + 1 < s := by
  constructor
  · intro htail
    have hpower : IntegrableOn (fun x : ℝ ↦ x ^ (2 * (m : ℝ) - s)) (Ioi 1) := by
      apply (htail.const_mul ((2 : ℝ) ^ (s / 2))).mono' (measurable_id.pow_const _).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      change ‖x ^ (2 * (m : ℝ) - s)‖ ≤ _
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact (sobolevJetPolynomial_compare hs hx m).2
    have := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hpower
    linarith
  · intro hm
    have hpower := (integrableOn_Ioi_rpow_iff (s := 2 * (m : ℝ) - s) zero_lt_one).2 (by linarith)
    apply hpower.mono' (continuous_sobolevJetPolynomial s m).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (by unfold sobolevJetPolynomial; positivity)]
    exact (sobolevJetPolynomial_compare hs hx m).1

public theorem integrable_sobolevJetPolynomial {s : ℝ} (hs : 0 ≤ s) {m : ℕ}
    (hm : 2 * (m : ℝ) + 1 < s) : Integrable (sobolevJetPolynomial s m) := by
  have hpos := (integrableOn_sobolevJetPolynomial_Ioi_iff hs m).2 hm
  have hneg : IntegrableOn (sobolevJetPolynomial s m) (Iio (-1)) := by
    have hp : IntegrableOn (sobolevJetPolynomial s m) (Ioi (-(-1 : ℝ))) := by simpa using hpos
    simpa only [sobolevJetPolynomial_neg] using hp.comp_neg_Iio
  have hcompact : IntegrableOn (sobolevJetPolynomial s m) (Icc (-1) 1) :=
    (continuous_sobolevJetPolynomial s m).continuousOn.integrableOn_compact isCompact_Icc
  have h := hneg.union (hcompact.union hpos)
  rwa [Icc_union_Ioi_eq_Ici (by norm_num), Iio_union_Ici, integrableOn_univ] at h

end Masullo
