module

public import Lemmas.CompactKernelPairing
public import Lemmas.InteriorLogJet
import Lemmas.SobolevJetTail
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # The exact boundary threshold for weighted Mellin jets

This is a project criterion for the log-Lebesgue model of (9.2.2.4) and
(10.2.2.4)–(10.2.2.5). At the strip boundary at least one tail has no
exponential decay, and equality in the polynomial threshold is excluded.
-/

open MeasureTheory Set

namespace Masullo

private theorem norm_dividedJet_sq (α s : ℝ) (z : ℂ) (m : ℕ) (x : ℝ) :
    ‖(x : ℂ) ^ m * Complex.exp (z * x) / (symmetricStripWeightRoot α s x : ℂ)‖ ^ 2 =
      Real.exp (2 * (z.re * x - α * |x|)) * sobolevJetPolynomial s m x := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_of_nonneg (symmetricStripWeightRoot_pos α s x).le,
    div_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul, symmetricStripWeightRoot_sq,
    sobolevJetPolynomial, mul_sub, Real.exp_sub, div_eq_mul_inv, mul_inv_rev]
  push_cast
  rw [Nat.mul_comm m 2]
  ring

private theorem continuous_dividedLogJetKernel (α s : ℝ) (z : ℂ) (m : ℕ) :
    Continuous (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)) :=
  (by fun_prop : Continuous (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x))).div
    (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s))
    (fun x ↦ by exact_mod_cast (symmetricStripWeightRoot_pos α s x).ne')

/-- At `|Re z| = α`, the kernel divided by the square root of the strip
weight is in `L²(dx)` exactly for `2m + 1 < s`. This includes the width-zero
case. The statement concerns only the log-line model, not adelic completion. -/
public theorem memLp_boundaryLogJet_iff {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| = α) (m : ℕ) :
    MemLp (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)) 2 volume ↔ 2 * (m : ℝ) + 1 < s := by
  let k := fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
    (symmetricStripWeightRoot α s x : ℂ)
  have hcont : Continuous k := continuous_dividedLogJetKernel α s z m
  change MemLp k 2 volume ↔ _
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  constructor
  · intro hk
    -- Select the nondecaying tail, reflecting it onto `(1, ∞)` if necessary.
    have htail : IntegrableOn (sobolevJetPolynomial s m) (Ioi 1) := by
      rcases le_total 0 z.re with h | h
      · refine hk.integrableOn.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
        have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
        change ‖k x‖ ^ 2 = _
        rw [show ‖k x‖ ^ 2 = _ from norm_dividedJet_sq α s z m x,
          abs_of_nonneg hx0, ← hz, abs_of_nonneg h, sub_self, mul_zero, Real.exp_zero, one_mul]
      · have hneg : IntegrableOn (fun x ↦ ‖k x‖ ^ 2) (Iio (-1 : ℝ)) := hk.integrableOn
        refine (hneg.comp_neg_Ioi (c := (1 : ℝ))).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
        have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
        change ‖k (-x)‖ ^ 2 = _
        rw [show ‖k (-x)‖ ^ 2 = _ from norm_dividedJet_sq α s z m (-x),
          abs_neg, abs_of_nonneg hx0, ← hz, abs_of_nonpos h, mul_neg, neg_mul, sub_self,
          mul_zero, Real.exp_zero, one_mul, sobolevJetPolynomial_neg]
    exact (integrableOn_sobolevJetPolynomial_Ioi_iff hs m).1 htail
  · intro hm
    refine (integrable_sobolevJetPolynomial hs hm).mono' (hcont.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    have hRe : z.re * x ≤ α * |x| := by rw [← hz, ← abs_mul]; exact le_abs_self _
    rw [Real.norm_of_nonneg (sq_nonneg _), show ‖k x‖ ^ 2 = _ from norm_dividedJet_sq α s z m x]
    exact mul_le_of_le_one_left (by unfold sobolevJetPolynomial; positivity)
      (Real.exp_le_one_iff.mpr (by linarith))

/-- An allowed boundary jet as a continuous complex-linear functional in
weighted `L²(dx)` coordinates. -/
public noncomputable def boundaryLogJet {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| = α) {m : ℕ} (hm : 2 * (m : ℝ) + 1 < s) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  weightedLogJet ((memLp_boundaryLogJet_iff hs hz m).2 hm)

/-- If `W*u` represents the profile `u` in weighted coordinates, the boundary
functional is the absolutely convergent bilinear integral against `x^m exp(zx)`. -/
public theorem boundaryLogJet_toLp {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| = α) {m : ℕ} (hm : 2 * (m : ℝ) + 1 < s) (u : ℝ → ℂ)
    (hu : MemLp (fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * u x) 2 volume) :
    Integrable (fun x ↦ u x * ((x : ℂ) ^ m * Complex.exp (z * x))) ∧
    boundaryLogJet hs hz hm (hu.toLp _) =
      ∫ x : ℝ, u x * ((x : ℂ) ^ m * Complex.exp (z * x)) :=
  weightedLogJet_toLp ((memLp_boundaryLogJet_iff hs hz m).2 hm) u hu

/-- The weighted `L²(dx)` test for a log-line jet: The conjugate of the
kernel divided by the weight root, cut off on `[-n,n]`. -/
public noncomputable def boundaryLogJetTest (α s : ℝ) (z : ℂ) (m n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  compactConjKernel (continuous_dividedLogJetKernel α s z m) n

/-- In weighted coordinates, the chosen test is the truncated conjugate
divided kernel, almost everywhere. -/
public theorem boundaryLogJetTest_ae_eq (α s : ℝ) (z : ℂ) (m n : ℕ) :
    (boundaryLogJetTest α s z m n : ℝ → ℂ) =ᵐ[volume]
      (Icc (-(n : ℝ)) n).indicator (fun x : ℝ ↦ star ((x : ℂ) ^ m * Complex.exp (z * x) /
        (symmetricStripWeightRoot α s x : ℂ))) :=
  compactConjKernel_ae_eq (continuous_dividedLogJetKernel α s z m) n

/-- A boundary jet has a bounded extension agreeing with its bilinear Mellin
pairing on the compact conjugate-kernel tests exactly for `2m + 1 < s`.
Here `k = x^m exp(zx)/W` and the test stands for the reweighted profile
`W*u = 1_{[-n,n]} conj(k)`. The right-hand integral is `∫ u(x) x^m exp(zx) dx`.
This concerns the ambient rational log line, not just the theta inputs. -/
public theorem boundaryLogJet_exists_extension_iff {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| = α) (m : ℕ) :
    let k := fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)
    (∃ F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ, ∀ n : ℕ,
      F (boundaryLogJetTest α s z m n) = ∫ x in Icc (-(n : ℝ)) n, star (k x) * k x) ↔
      2 * (m : ℝ) + 1 < s := by
  exact (exists_compactKernelPairing_iff (continuous_dividedLogJetKernel α s z m)).trans
    (memLp_boundaryLogJet_iff hs hz m)

end Masullo
