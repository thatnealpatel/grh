module

public import Lemmas.SignedPoissonDefect
public import Lemmas.ZetaZeroOrders
import Lemmas.ZetaZeroSummability
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Signed Poisson defect for the full zeta divisor

Source: `d675c849:.godel/bob/deep-retained-excess.md:31–38`, equation (3).
Downstream use: `b4a66edd:.godel/bob/interior-trace-depth-transfer.md:18`.

Scope: both traces use every distinct open critical-strip zero of zeta, weighted by
its analytic order. The convolution is on the whole real line at every height,
and the defect sum is restricted to zeros strictly right of the interior line.
No uniform horizontal separation or logarithmic-derivative identification is needed.
The off-support identity and bounds were accepted at `49385594` (original
Lean baseline `20ac2a9d`, unchanged relevant sources at `4c47eae3`; original
owning check session `01a20c03-fe6f-73b3-a1bb-bf0df5b6ef1a`).

Right-limit sources: `fb2dc2ff:.godel/bob/uncut-defect-price.md:3–7` and
`892abdb1:.godel/bob/uncut-depth-discount.md:7–11,19–23`.
The endpoint takes the right limit of the actual smoothed full trace, including
lines through divisor points, and excludes the supporting depth from the limit
sum. No arithmetic identification or discount estimate is asserted.

Lean baseline for the right limit: `3d2886df` (same proofs at `1de21475`).
Owning check session for the right limit: `01a20c3b-0de7-75d0-b4f0-194be0854305`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace SignedPoissonDefect

open Masullo

private theorem poisson_nonneg {h : ℝ} (hh : 0 ≤ h) (y : ℝ) : 0 ≤ poisson h y :=
  div_nonneg (div_nonneg hh (by positivity)) Real.pi_pos.le

private theorem norm_kernel (d x : ℝ) : ‖kernel d x‖ = kernel |d| x := by
  rw [kernel, kernel, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (show 0 ≤ d ^ 2 + x ^ 2 by positivity), sq_abs]

private theorem abs_sub_re_le (s : ℝ) (ρ : criticalStripZetaZeros) :
    |s - (ρ : ℂ).re| ≤ |s| + 1 := by
  obtain ⟨_, hlo, hhi⟩ := mem_criticalStripZetaZeros.mp ρ.property
  exact (abs_sub _ _).trans (by rw [abs_of_pos hlo]; gcongr)

/-- The centered quadratic majorant, with constants depending only on a width cap
and a lower bound on the translated denominator. -/
private theorem norm_weighted_kernel_le (v : ℝ) (ρ : criticalStripZetaZeros) (d : ℝ)
    {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (hd : |d| ≤ M)
    (hdenom : a ≤ d ^ 2 + (v - (ρ : ℂ).im) ^ 2) :
    ‖(zetaZeroOrder ρ : ℝ) * kernel d (v - (ρ : ℂ).im)‖ ≤
      (M * (2 + (2 + 2 * v ^ 2) / a)) *
        ((zetaZeroOrder ρ : ℝ) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) := by
  let C := (2 + 2 * v ^ 2) / a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let u := v - (ρ : ℂ).im
  let D := d ^ 2 + u ^ 2
  let Z := 1 + ‖shiftedZetaZero ρ‖ ^ 2
  have hD : 0 < D := ha.trans_le hdenom
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hsize : Z ≤ 2 + 2 * v ^ 2 + 2 * u ^ 2 := by
    have hre := pow_le_pow_left₀ (abs_nonneg _) (abs_re_shiftedZetaZero_lt ρ).le 2
    rw [sq_abs] at hre
    have him : (shiftedZetaZero ρ).im = v - u := by simp [shiftedZetaZero, u]
    dsimp only [Z]
    rw [Complex.sq_norm, Complex.normSq_apply, him]
    nlinarith only [hre, sq_nonneg (v + u)]
  have hbase : 2 + 2 * v ^ 2 ≤ C * D := by
    calc
      _ = C * a := (div_mul_cancel₀ _ ha.ne').symm
      _ ≤ C * D := mul_le_mul_of_nonneg_left hdenom hC
  have hbound : Z ≤ (2 + C) * D := by
    have huD : u ^ 2 ≤ D := le_add_of_nonneg_left (sq_nonneg _)
    linarith only [hsize, hbase, huD, add_mul 2 C D]
  have hk : kernel |d| u ≤ M * (2 + C) / Z := by
    rw [kernel, sq_abs]
    calc
      _ ≤ M / D := div_le_div_of_nonneg_right hd hD.le
      _ ≤ _ := by
        apply (div_le_div_iff₀ hD hZ).2
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hbound hM
  rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), norm_kernel]
  calc
    _ ≤ (zetaZeroOrder ρ : ℝ) * (M * (2 + C) / Z) :=
      mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
    _ = _ := by change _ = M * (2 + C) * ((zetaZeroOrder ρ : ℝ) / Z); ring

/-- Only a cofinite denominator bound is needed for pointwise summability. -/
private theorem summable_norm_weighted_kernel (v : ℝ) (d : criticalStripZetaZeros → ℝ)
    {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (hd : ∀ ρ, |d ρ| ≤ M)
    (hdenom : ∀ᶠ ρ in cofinite, a ≤ d ρ ^ 2 + (v - (ρ : ℂ).im) ^ 2) :
    Summable (fun ρ ↦ ‖(zetaZeroOrder ρ : ℝ) * kernel (d ρ) (v - (ρ : ℂ).im)‖) := by
  refine Summable.of_norm_bounded_eventually
    (summable_zetaZeroOrder_div_one_add_norm_sq.mul_left (M * (2 + (2 + 2 * v ^ 2) / a))) ?_
  filter_upwards [hdenom] with ρ hρ
  rw [norm_norm]
  exact norm_weighted_kernel_le v ρ (d ρ) hM ha (hd ρ) hρ

private theorem eventually_one_le_ordinate_sq (v : ℝ) :
    ∀ᶠ ρ : criticalStripZetaZeros in cofinite, 1 ≤ (v - (ρ : ℂ).im) ^ 2 := by
  have hfin := shiftedZetaZero_preimage_finite (isCompact_closedBall (0 : ℂ) (|v| + 2))
  filter_upwards [hfin.eventually_cofinite_notMem] with ρ hρ
  have hu : 1 ≤ |v - (ρ : ℂ).im| := by
    by_contra! hnear
    apply hρ
    change shiftedZetaZero ρ ∈ Metric.closedBall (0 : ℂ) (|v| + 2)
    rw [mem_closedBall_zero_iff]
    calc
      _ ≤ |(shiftedZetaZero ρ).re| + |(shiftedZetaZero ρ).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        have him : (shiftedZetaZero ρ).im = (ρ : ℂ).im := by simp [shiftedZetaZero]
        have htri := abs_sub_abs_le_abs_sub (ρ : ℂ).im v
        rw [abs_sub_comm (ρ : ℂ).im v] at htri
        rw [him]
        linarith [abs_re_shiftedZetaZero_lt ρ]
  simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hu 2

/-- The multiplicity-weighted signed trace over the full open-strip zeta divisor. -/
@[expose] public noncomputable def zetaSignedTrace (s v : ℝ) : ℝ :=
  ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℝ) *
    kernel (s - (ρ : ℂ).re) (v - (ρ : ℂ).im)

/-- Absolute pointwise convergence of the signed trace. The tail estimate uses
large ordinate difference, not separation of zero real parts from the line. -/
public theorem summable_norm_zetaSignedTrace (s v : ℝ) :
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℝ) *
      kernel (s - (ρ : ℂ).re) (v - (ρ : ℂ).im)‖) := by
  refine summable_norm_weighted_kernel v (fun ρ ↦ s - (ρ : ℂ).re)
    (by positivity) zero_lt_one (abs_sub_re_le s) ?_
  exact (eventually_one_le_ordinate_sq v).mono fun ρ hρ ↦
    hρ.trans (le_add_of_nonneg_left (sq_nonneg _))

private theorem kernel_zero_width (x : ℝ) : kernel 0 x = 0 := by
  simp [kernel]

private theorem integrable_weighted_atom {h d : ℝ} (hh : 0 < h) (m x : ℝ) :
    Integrable (fun y : ℝ ↦ m * (poisson h y * kernel d (x - y))) := by
  by_cases hd : d = 0
  · simp [hd, kernel_zero_width]
  apply Integrable.const_mul _ m
  -- The convolution is nonzero; a nonintegrable Bochner integrand would give zero.
  apply Integrable.of_integral_ne_zero
  rw [poisson_convolution_kernel hh hd]
  exact mul_ne_zero (mt Real.sign_eq_zero_iff.mp hd) (by unfold kernel; positivity)

private theorem integral_norm_weighted_atom {h d m : ℝ} (hh : 0 < h) (hd : d ≠ 0)
    (hm : 0 ≤ m) (x : ℝ) :
    (∫ y : ℝ, ‖m * (poisson h y * kernel d (x - y))‖) = m * kernel (h + |d|) x := by
  simp_rw [norm_mul, Real.norm_of_nonneg hm,
    Real.norm_of_nonneg (poisson_nonneg hh.le _), norm_kernel]
  rw [integral_const_mul, poisson_convolution_kernel hh (abs_pos.mpr hd).ne',
    Real.sign_of_pos (abs_pos.mpr hd), abs_abs, one_mul]

private theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℝ} (hF : ∀ i, Integrable (F i))
    (hS : Summable fun i ↦ ∫ y, ‖F i y‖) : Integrable (fun y ↦ ∑' i, F i y) := by
  have hmeas (i : ι) := (hF i).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have heq (i : ι) : (∫⁻ y, ‖F i y‖ₑ) = ENNReal.ofReal (∫ y, ‖F i y‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm (ae_of_all _ fun _ ↦ norm_nonneg _)]
    simp only [ofReal_norm]
  calc
    _ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ := lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm
    _ = ∑' i, ∫⁻ y, ‖F i y‖ₑ := lintegral_tsum fun i ↦ (hmeas i).aemeasurable.eNorm
    _ = ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖) := by
      simp_rw [heq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hS).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

private theorem poisson_mul_zetaSignedTrace_hasSum {h s : ℝ} (hh : 0 < h) (v : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * zetaSignedTrace s (v - y)) ∧
    HasSum (fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℝ) *
      (Real.sign (s - (ρ : ℂ).re) * kernel (h + |s - (ρ : ℂ).re|) (v - (ρ : ℂ).im)))
      (∫ y : ℝ, poisson h y * zetaSignedTrace s (v - y)) := by
  let d := fun ρ : criticalStripZetaZeros ↦ s - (ρ : ℂ).re
  let x := fun ρ : criticalStripZetaZeros ↦ v - (ρ : ℂ).im
  let F := fun (ρ : criticalStripZetaZeros) (y : ℝ) ↦
    (zetaZeroOrder ρ : ℝ) * (poisson h y * kernel (d ρ) (x ρ - y))
  have hF (ρ : criticalStripZetaZeros) : Integrable (F ρ) :=
    integrable_weighted_atom hh _ _
  have hnorm (ρ : criticalStripZetaZeros) :
      (∫ y, ‖F ρ y‖) ≤ ‖(zetaZeroOrder ρ : ℝ) * kernel (h + |d ρ|) (x ρ)‖ := by
    by_cases hd : d ρ = 0
    · simp only [F, hd, kernel_zero_width, mul_zero, norm_zero, integral_zero]
      exact norm_nonneg _
    · change (∫ y, ‖(zetaZeroOrder ρ : ℝ) * (poisson h y * kernel (d ρ) (x ρ - y))‖) ≤ _
      rw [integral_norm_weighted_atom hh hd (Nat.cast_nonneg _) _]
      exact Real.le_norm_self _
  -- Unlike the unsmoothed widths, all widths in this majorant are at least h.
  have hS : Summable (fun ρ ↦ ∫ y, ‖F ρ y‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hnorm
    refine summable_norm_weighted_kernel v (fun ρ ↦ h + |d ρ|)
      (M := h + (|s| + 1)) (a := h ^ 2) (by positivity) (by positivity) (fun ρ ↦ ?_) ?_
    · rw [abs_of_nonneg (by positivity)]
      exact add_le_add_right (abs_sub_re_le s ρ) h
    · exact Eventually.of_forall fun ρ ↦
        (pow_le_pow_left₀ hh.le (le_add_of_nonneg_right (abs_nonneg (d ρ))) 2).trans
          (le_add_of_nonneg_right (sq_nonneg _))
  have hpoint (y : ℝ) : (∑' ρ, F ρ y) = poisson h y * zetaSignedTrace s (v - y) := by
    rw [zetaSignedTrace, ← tsum_mul_left]
    apply tsum_congr
    intro ρ
    simp only [F, x, d, sub_right_comm v (ρ : ℂ).im y]
    ac_rfl
  have hterm (ρ : criticalStripZetaZeros) : (∫ y, F ρ y) =
      (zetaZeroOrder ρ : ℝ) * (Real.sign (d ρ) * kernel (h + |d ρ|) (x ρ)) := by
    -- At a supporting line the kernel is identically zero, even at x = y.
    by_cases hd : d ρ = 0
    · simp [F, hd, kernel_zero_width]
    · dsimp only [F]
      rw [integral_const_mul, poisson_convolution_kernel hh hd]
  exact ⟨by simpa only [hpoint] using integrable_tsum_of_summable_integral_norm hF hS,
    by simpa only [hterm, hpoint] using hasSum_integral_of_summable_integral_norm hF hS⟩

/-- The whole-line convolution integrand is Bochner integrable without a
uniform gap between the interior line and the real parts of the zeros. -/
public theorem integrable_poisson_mul_zetaSignedTrace {h s : ℝ} (hh : 0 < h)
    (_hβ : ∀ ρ : criticalStripZetaZeros, (ρ : ℂ).re ≠ s) (v : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * zetaSignedTrace s (v - y)) :=
  (poisson_mul_zetaSignedTrace_hasSum (s := s) hh v).1

/-- Convergence of the actual right-hand series of the signed Poisson defect,
with its sum identified before passing to `tsum`. -/
public theorem zeta_signed_poisson_defect_hasSum {s₀ s₁ : ℝ} (_hs₀ : 1 / 2 < s₀)
    (hs : s₀ < s₁) (_hs₁ : 1 < s₁)
    (hβ : ∀ ρ : criticalStripZetaZeros, (ρ : ℂ).re ≠ s₀) (v : ℝ) :
    HasSum (fun ρ : {ρ : criticalStripZetaZeros // s₀ < (ρ : ℂ).re} ↦
      (zetaZeroOrder ρ.1 : ℝ) * (kernel (s₁ - (ρ.1 : ℂ).re) (v - (ρ.1 : ℂ).im) +
        kernel (s₁ + (ρ.1 : ℂ).re - 2 * s₀) (v - (ρ.1 : ℂ).im)))
      (zetaSignedTrace s₁ v - ∫ y : ℝ, poisson (s₁ - s₀) y * zetaSignedTrace s₀ (v - y)) := by
  classical
  have hout := (summable_norm_zetaSignedTrace s₁ v).of_norm.hasSum
  have hconv := (poisson_mul_zetaSignedTrace_hasSum (s := s₀) (sub_pos.mpr hs) v).2
  let G (ρ : criticalStripZetaZeros) := (zetaZeroOrder ρ : ℝ) *
    (kernel (s₁ - (ρ : ℂ).re) (v - (ρ : ℂ).im) +
      kernel (s₁ + (ρ : ℂ).re - 2 * s₀) (v - (ρ : ℂ).im))
  let R : Set criticalStripZetaZeros := {ρ | s₀ < (ρ : ℂ).re}
  change HasSum (G ∘ Subtype.val (p := (· ∈ R))) _
  apply hasSum_subtype_iff_indicator.mpr
  apply (hout.sub hconv).congr_fun
  intro ρ
  rcases lt_or_gt_of_ne (hβ ρ) with hleft | hright
  · have hn : ρ ∉ R := not_lt_of_ge hleft.le
    have hw : 0 < s₀ - (ρ : ℂ).re := sub_pos.mpr hleft
    have hadd : s₁ - s₀ + (s₀ - (ρ : ℂ).re) = s₁ - (ρ : ℂ).re := by ring
    simp only [indicator_of_notMem hn, Real.sign_of_pos hw, abs_of_pos hw, hadd, one_mul,
      sub_self]
  · have hr : ρ ∈ R := hright
    have hw : s₀ - (ρ : ℂ).re < 0 := sub_neg.mpr hright
    have hadd : s₁ - s₀ + -(s₀ - (ρ : ℂ).re) = s₁ + (ρ : ℂ).re - 2 * s₀ := by ring
    simp only [indicator_of_mem hr, G, Real.sign_of_neg hw, abs_of_neg hw, hadd, neg_mul,
      one_mul, mul_neg, sub_neg_eq_add, mul_add]

/-- Equation (3): exterior trace minus Poisson-smoothed interior trace is the
multiplicity-weighted sum of two kernels per zero strictly right of `s₀`. -/
public theorem zeta_signed_poisson_defect {s₀ s₁ : ℝ} (hs₀ : 1 / 2 < s₀)
    (hs : s₀ < s₁) (hs₁ : 1 < s₁)
    (hβ : ∀ ρ : criticalStripZetaZeros, (ρ : ℂ).re ≠ s₀) (v : ℝ) :
    zetaSignedTrace s₁ v - (∫ y : ℝ, poisson (s₁ - s₀) y * zetaSignedTrace s₀ (v - y)) =
      ∑' ρ : {ρ : criticalStripZetaZeros // s₀ < (ρ : ℂ).re},
        (zetaZeroOrder ρ.1 : ℝ) * (kernel (s₁ - (ρ.1 : ℂ).re) (v - (ρ.1 : ℂ).im) +
          kernel (s₁ + (ρ.1 : ℂ).re - 2 * s₀) (v - (ρ.1 : ℂ).im)) :=
  (zeta_signed_poisson_defect_hasSum hs₀ hs hs₁ hβ v).tsum_eq.symm

private theorem norm_sign_le_one (d : ℝ) : ‖Real.sign d‖ ≤ 1 := by
  unfold Real.sign
  split <;> [simp; split <;> simp]

/-- The right limit of the actual full-divisor defect is the multiplicity-weighted
strict tail. The approaching line may pass through zeros, where the
width-zero kernel contributes nothing to the convolution. -/
public theorem tendsto_zeta_signed_poisson_defect_right {s s₁ : ℝ} (hs : 1 / 2 < s)
    (hss₁ : s < s₁) (hs₁ : 1 < s₁) (v : ℝ) :
    Tendsto (fun u ↦ zetaSignedTrace s₁ v -
      ∫ y : ℝ, poisson (s₁ - u) y * zetaSignedTrace u (v - y))
      (𝓝[>] s) (𝓝 (∑' ρ : {ρ : criticalStripZetaZeros // s < (ρ : ℂ).re},
        (zetaZeroOrder ρ.1 : ℝ) * (kernel (s₁ - (ρ.1 : ℂ).re) (v - (ρ.1 : ℂ).im) +
          kernel (s₁ + (ρ.1 : ℂ).re - 2 * s) (v - (ρ.1 : ℂ).im)))) := by
  classical
  let β (ρ : criticalStripZetaZeros) := (ρ : ℂ).re
  let x (ρ : criticalStripZetaZeros) := v - (ρ : ℂ).im
  let m (ρ : criticalStripZetaZeros) := (zetaZeroOrder ρ : ℝ)
  let outer (ρ : criticalStripZetaZeros) := m ρ * kernel (s₁ - β ρ) (x ρ)
  let smoothed (u : ℝ) (ρ : criticalStripZetaZeros) :=
    m ρ * (Real.sign (u - β ρ) * kernel (s₁ - u + |u - β ρ|) (x ρ))
  let F (u : ℝ) (ρ : criticalStripZetaZeros) := outer ρ - smoothed u ρ
  let R : Set criticalStripZetaZeros := {ρ | s < β ρ}
  let G (ρ : criticalStripZetaZeros) :=
    m ρ * (kernel (s₁ - β ρ) (x ρ) + kernel (s₁ + β ρ - 2 * s) (x ρ))
  -- The interior sign stabilizes separately for each fixed zero.
  have hterm (ρ : criticalStripZetaZeros) :
      Tendsto (fun u ↦ F u ρ) (𝓝[>] s) (𝓝 (R.indicator G ρ)) := by
    by_cases hβ : s < β ρ
    · have hmem : ρ ∈ R := hβ
      rw [indicator_of_mem hmem]
      have hp : 0 < s₁ + β ρ - 2 * s := by linarith only [hss₁, hβ]
      have hk : ContinuousAt (fun u ↦ kernel (s₁ + β ρ - 2 * u) (x ρ)) s := by
        unfold kernel
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
      refine Tendsto.congr' ?_ (((continuousAt_const.add hk).const_mul (m ρ)).tendsto.mono_left
        nhdsWithin_le_nhds)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hβ)] with u hu
      have hw : u - β ρ < 0 := sub_neg.mpr hu.out
      have hadd : s₁ - u + -(u - β ρ) = s₁ + β ρ - 2 * u := by ring
      simp only [F, outer, smoothed, Real.sign_of_neg hw, abs_of_neg hw, hadd, neg_one_mul,
        mul_neg, sub_neg_eq_add, Pi.add_apply, mul_add]
    · have hn : ρ ∉ R := hβ
      rw [indicator_of_notMem hn]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin (a := s) (s := Ioi s)] with u hu
      have hw : 0 < u - β ρ := sub_pos.mpr ((le_of_not_gt hβ).trans_lt hu.out)
      have hadd : s₁ - u + (u - β ρ) = s₁ - β ρ := by ring
      simp only [F, outer, smoothed, Real.sign_of_pos hw, abs_of_pos hw, hadd, one_mul,
        sub_self]
  -- Localize before using a common denominator bound for all smoothed widths.
  let r := (s + s₁) / 2
  let δ := s₁ - r
  have hsr : s < r := by dsimp [r]; linarith only [hss₁]
  have hδ : 0 < δ := by dsimp [δ, r]; linarith only [hss₁]
  have hnear : ∀ᶠ u in 𝓝[>] s, u < r := nhdsWithin_le_nhds (Iio_mem_nhds hsr)
  let C := (s₁ + 1) * (2 + (2 + 2 * v ^ 2) / δ ^ 2)
  let bound (ρ : criticalStripZetaZeros) :=
    ‖outer ρ‖ + C * (m ρ / (1 + ‖shiftedZetaZero ρ‖ ^ 2))
  have hsum : Summable bound := (summable_norm_zetaSignedTrace s₁ v).add
    (summable_zetaZeroOrder_div_one_add_norm_sq.mul_left C)
  have hbound : ∀ᶠ u in 𝓝[>] s, ∀ ρ, ‖F u ρ‖ ≤ bound ρ := by
    filter_upwards [self_mem_nhdsWithin (a := s) (s := Ioi s), hnear] with u hsu hur
    intro ρ
    let w := s₁ - u + |u - β ρ|
    have hδw : δ ≤ w := by dsimp [δ, w]; linarith only [hur, abs_nonneg (u - β ρ)]
    have hwM : |w| ≤ s₁ + 1 := by
      have hu : 0 < u := by linarith only [hs, hsu.out]
      have h := abs_sub_re_le u ρ
      rw [abs_of_pos hu] at h
      rw [abs_of_pos (hδ.trans_le hδw)]
      dsimp [w, β]
      linarith only [h]
    calc
      ‖F u ρ‖ ≤ ‖outer ρ‖ + ‖smoothed u ρ‖ := norm_sub_le _ _
      _ ≤ bound ρ := by
        refine add_le_add le_rfl ?_
        change ‖m ρ * (Real.sign (u - β ρ) * kernel w (x ρ))‖ ≤ C * _
        calc
          _ = ‖Real.sign (u - β ρ)‖ * ‖m ρ * kernel w (x ρ)‖ := by
            rw [mul_left_comm, norm_mul]
          _ ≤ ‖m ρ * kernel w (x ρ)‖ :=
            mul_le_of_le_one_left (norm_nonneg _) (norm_sign_le_one _)
          _ ≤ _ := norm_weighted_kernel_le v ρ w (by linarith only [hs₁]) (by positivity) hwM
            ((pow_le_pow_left₀ hδ.le hδw 2).trans (le_add_of_nonneg_right (sq_nonneg _)))
  have hlim := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  have heq : (fun u ↦ ∑' ρ, F u ρ) =ᶠ[𝓝[>] s]
      (fun u ↦ zetaSignedTrace s₁ v -
        ∫ y : ℝ, poisson (s₁ - u) y * zetaSignedTrace u (v - y)) := by
    filter_upwards [hnear] with u hur
    have hh : 0 < s₁ - u := by dsimp [δ] at hδ; linarith only [hur, hδ]
    exact ((summable_norm_zetaSignedTrace s₁ v).of_norm.hasSum.sub
      (poisson_mul_zetaSignedTrace_hasSum (s := u) hh v).2).tsum_eq
  rw [← tsum_subtype R G] at hlim
  exact hlim.congr' heq

end SignedPoissonDefect
