module

public import Lemmas.PoissonDivisorCarriers
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exterior-trace budget for the Poisson-smoothed error envelope

Source: `4c47eae3387e:.godel/bob/uncut-poisson-transfer.md:9–15` for the
smoothed budget. At that revision, `uncut-census-window.md:5,37` gives the
kernel convention and pointwise majorant; line 49 points to the transfer.

Scope: the summed inverse-square error budget at the frozen center, with
positive Poisson width and fixed normalization `R`. The trace is the actual
paired open-strip zeta divisor sum: full analytic order on the right, half
analytic order on the line, and no factor of `π` in the trace kernels. This
makes no logarithmic-derivative identification or gamma/pole estimate and
does not transfer the full screen.

Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.
-/

open MeasureTheory

namespace PoissonExteriorEnvelope

open SignedPoissonDefect (kernel poisson poisson_convolution_kernel)
open PoissonDivisorCarriers (RightZetaZero zetaDepth zetaOrdinate pairWeight envelope
  zetaLocalEnvelope localEnvelope summable_zeta_envelope)
open Masullo (zetaZeroOrder mem_criticalStripZetaZeros)

/-- The unnormalized pair `p_b^a`: two Cauchy kernels, not their average. -/
@[expose] public noncomputable def pairedKernel (a b x : ℝ) : ℝ :=
  kernel (a - b) x + kernel (a + b) x

private theorem envelope_nonneg (x : ℝ) : 0 ≤ envelope x := by
  unfold envelope
  positivity

private theorem kernel_pos {d : ℝ} (hd : 0 < d) (x : ℝ) : 0 < kernel d x := by
  unfold kernel
  positivity

private theorem pairedKernel_nonneg {a b : ℝ} (ha : 1 / 2 < a) (hb₀ : 0 ≤ b)
    (hb₁ : b ≤ 1 / 2) (x : ℝ) : 0 ≤ pairedKernel a b x :=
  add_nonneg (kernel_pos (by linarith : 0 < a - b) x).le
    (kernel_pos (by linarith : 0 < a + b) x).le

private theorem tangent_le_kernel {d : ℝ} (hd : 1 / 2 ≤ d) (x : ℝ) :
    (2 - d) * envelope x ≤ 4 * kernel d x := by
  have hd₀ : 0 < d := by linarith
  have hd₂ : 1 ≤ 4 * d ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd) (show 0 ≤ d + 1 / 2 by positivity)]
  calc
    _ ≤ (1 / d) * envelope x :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hd₀).2 (by nlinarith [sq_nonneg (d - 1)]))
        (envelope_nonneg x)
    _ ≤ _ := by
      rw [envelope, kernel, ← div_eq_mul_inv, div_div, ← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr hd₂) (sq_nonneg x)]

/-- The universal comparison with the actual width-one pair, including at
critical-line depth `b = 0`. -/
public theorem envelope_le_two_pairedKernel {b : ℝ} (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1 / 2)
    (x : ℝ) : envelope x ≤ 2 * pairedKernel 1 b x := by
  have h := add_le_add (tangent_le_kernel (d := 1 - b) (by linarith) x)
    (tangent_le_kernel (d := 1 + b) (by linarith) x)
  calc
    envelope x = ((2 - (1 - b)) * envelope x + (2 - (1 + b)) * envelope x) / 2 := by ring
    _ ≤ (4 * kernel (1 - b) x + 4 * kernel (1 + b) x) / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = 2 * pairedKernel 1 b x := by unfold pairedKernel; ring

private theorem integral_poisson_kernel_add {h d : ℝ} (hh : 0 < h) (hd : 0 < d) (x : ℝ) :
    (∫ y : ℝ, poisson h y * kernel d (x + y)) = kernel (h + d) x := by
  rw [← integral_neg_eq_self (f := fun y : ℝ ↦ poisson h y * kernel d (x + y))]
  have he (y : ℝ) : poisson h (-y) = poisson h y := by simp [poisson, kernel]
  simpa only [he, ← sub_eq_add_neg, Real.sign_of_pos hd, abs_of_pos hd, one_mul] using
    poisson_convolution_kernel hh hd.ne' x

/-- Paired semigroup at the frozen ordinate difference `x = γ - t`:
translating the observation height to `t - y` changes `x` to `x + y`. -/
public theorem poisson_pairedKernel {a b h : ℝ} (ha : 1 / 2 < a) (hb₀ : 0 ≤ b)
    (hb₁ : b ≤ 1 / 2) (hh : 0 < h) (x : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * pairedKernel a b (x + y)) ∧
      (∫ y : ℝ, poisson h y * pairedKernel a b (x + y)) = pairedKernel (a + h) b x := by
  have hm : 0 < a - b := by linarith
  have hp : 0 < a + b := by linarith
  have hi {d : ℝ} (hd : 0 < d) : Integrable (fun y ↦ poisson h y * kernel d (x + y)) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_poisson_kernel_add hh hd]
    exact (kernel_pos (add_pos hh hd) x).ne'
  simp only [pairedKernel, mul_add]
  refine ⟨(hi hm).add (hi hp), ?_⟩
  rw [integral_add (hi hm) (hi hp), integral_poisson_kernel_add hh hm,
    integral_poisson_kernel_add hh hp,
    show h + (a - b) = a + h - b by ring, show h + (a + b) = a + h + b by ring]

local notation "ν" =>
  (fun ρ : RightZetaZero ↦ pairWeight (zetaDepth ρ) (zetaZeroOrder (Subtype.val ρ)))

/-- The source's `W_a` at height `t`, as the paired divisor series for the
exterior line `Re s = 1/2 + a`. -/
@[expose] public noncomputable def zetaExteriorTrace (a t : ℝ) : ℝ :=
  ∑' ρ : RightZetaZero, ν ρ * pairedKernel a (zetaDepth ρ) (zetaOrdinate ρ - t)

private theorem weight_nonneg (ρ : RightZetaZero) : 0 ≤ ν ρ := by
  simp only [pairWeight]
  split <;> positivity

private theorem depth_bounds (ρ : RightZetaZero) : 0 ≤ zetaDepth ρ ∧ zetaDepth ρ < 1 / 2 := by
  have hre := (mem_criticalStripZetaZeros.mp ρ.1.property).2.2
  exact ⟨sub_nonneg.mpr ρ.property, by unfold zetaDepth; linarith⟩

private theorem kernel_le_envelope {d : ℝ} (hd : 0 < d) (x : ℝ) :
    kernel d x ≤ (d + d⁻¹) * envelope x := by
  have h₀ : d ≤ (d + d⁻¹) * d ^ 2 := by
    rw [add_mul, show d⁻¹ * d ^ 2 = d by field_simp]
    exact le_add_of_nonneg_left (by positivity)
  have h₁ : d * x ^ 2 ≤ (d + d⁻¹) * x ^ 2 :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg x)
  rw [kernel, envelope, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [mul_add (d + d⁻¹)]
  linarith only [h₀, h₁, hd]

/-- The actual right/line exterior series converges at every exterior width
and height, with no counting or convergence hypothesis. -/
public theorem summable_zetaExteriorTrace {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    Summable (fun ρ : RightZetaZero ↦ ν ρ *
      pairedKernel a (zetaDepth ρ) (zetaOrdinate ρ - t)) := by
  let K := a + 1 / 2 + (a - 1 / 2)⁻¹
  have hk {d : ℝ} (hlo : a - 1 / 2 ≤ d) (hhi : d ≤ a + 1 / 2) (x : ℝ) :
      kernel d x ≤ K * envelope x :=
    (kernel_le_envelope ((sub_pos.mpr ha).trans_le hlo) x).trans <|
      mul_le_mul_of_nonneg_right (add_le_add hhi (inv_anti₀ (sub_pos.mpr ha) hlo))
        (envelope_nonneg x)
  apply ((summable_zeta_envelope t).mul_left (2 * K)).of_nonneg_of_le
  · intro ρ
    obtain ⟨hb₀, hb₁⟩ := depth_bounds ρ
    exact mul_nonneg (weight_nonneg ρ) (pairedKernel_nonneg ha hb₀ hb₁.le _)
  · intro ρ
    obtain ⟨hb₀, hb₁⟩ := depth_bounds ρ
    let b := zetaDepth ρ
    let x := zetaOrdinate ρ - t
    have h := add_le_add (hk (d := a - b) (by dsimp [b]; linarith) (by dsimp [b]; linarith) x)
      (hk (d := a + b) (by dsimp [b]; linarith) (by dsimp [b]; linarith) x)
    calc
      _ ≤ ν ρ * (K * envelope x + K * envelope x) :=
        mul_le_mul_of_nonneg_left h (weight_nonneg ρ)
      _ = _ := by dsimp only [x]; ring

private theorem poisson_nonneg {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ poisson h y := by
  unfold poisson kernel
  positivity

private theorem integrable_tsum_of_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℝ}
    (hF : ∀ i, Integrable (F i)) (hS : Summable fun i ↦ ∫ y, ‖F i y‖) :
    Integrable (fun y ↦ ∑' i, F i y) := by
  have hm (i : ι) := (hF i).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hm, hasFiniteIntegral_iff_eNorm.2 ?_⟩
  have he (i : ι) : (∫⁻ y, ‖F i y‖ₑ) = ENNReal.ofReal (∫ y, ‖F i y‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm (ae_of_all _ fun _ ↦ norm_nonneg _)]
    simp only [ofReal_norm]
  calc
    _ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ := lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm
    _ = ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖) := by
      rw [lintegral_tsum fun i ↦ (hm i).aemeasurable.eNorm]
      simp_rw [he]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hS).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The real Poisson integral of `W_a` is `W_(a+h)` at the same center. The
weighted pair integrals are absolutely summable, justifying the exchange. -/
public theorem poisson_zetaExteriorTrace {a h : ℝ} (ha : 1 / 2 < a) (hh : 0 < h) (t : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * zetaExteriorTrace a (t - y)) ∧
      (∫ y : ℝ, poisson h y * zetaExteriorTrace a (t - y)) = zetaExteriorTrace (a + h) t := by
  let F (ρ : RightZetaZero) (y : ℝ) := ν ρ *
    (poisson h y * pairedKernel a (zetaDepth ρ) (zetaOrdinate ρ - t + y))
  have hpair (ρ : RightZetaZero) :=
    poisson_pairedKernel ha (depth_bounds ρ).1 (depth_bounds ρ).2.le hh (zetaOrdinate ρ - t)
  have hF (ρ : RightZetaZero) : Integrable (F ρ) := (hpair ρ).1.const_mul _
  have hnonneg (ρ : RightZetaZero) (y : ℝ) : 0 ≤ F ρ y :=
    mul_nonneg (weight_nonneg ρ) (mul_nonneg (poisson_nonneg hh y)
      (pairedKernel_nonneg ha (depth_bounds ρ).1 (depth_bounds ρ).2.le _))
  have hterm (ρ : RightZetaZero) : (∫ y, F ρ y) =
      ν ρ * pairedKernel (a + h) (zetaDepth ρ) (zetaOrdinate ρ - t) := by
    dsimp only [F]
    rw [integral_const_mul, (hpair ρ).2]
  have hL1 : Summable (fun ρ ↦ ∫ y, ‖F ρ y‖) := by
    simp_rw [Real.norm_of_nonneg (hnonneg _ _), hterm]
    exact summable_zetaExteriorTrace (by linarith : 1 / 2 < a + h) t
  have hpoint (y : ℝ) : (∑' ρ, F ρ y) = poisson h y * zetaExteriorTrace a (t - y) := by
    rw [zetaExteriorTrace, ← tsum_mul_left]
    refine tsum_congr fun ρ ↦ ?_
    dsimp only [F]
    rw [show zetaOrdinate ρ - (t - y) = zetaOrdinate ρ - t + y by ring]
    ring
  refine ⟨by simpa only [hpoint] using integrable_tsum_of_integral_norm hF hL1, ?_⟩
  simpa only [hpoint, hterm, zetaExteriorTrace] using
    (integral_tsum_of_summable_integral_norm hF hL1).symm

private theorem zetaLocalEnvelope_le {R : ℝ} (hR : 0 < R) (u : ℝ) :
    zetaLocalEnvelope R u ≤ 2 * (zetaExteriorTrace 1 u / R) := by
  rw [zetaLocalEnvelope, localEnvelope, zetaExteriorTrace, ← mul_div_assoc, ← tsum_mul_left]
  apply div_le_div_of_nonneg_right _ hR.le
  apply (summable_zeta_envelope u).tsum_le_tsum _
    ((summable_zetaExteriorTrace (by norm_num : (1 / 2 : ℝ) < 1) u).mul_left 2)
  intro ρ
  rw [mul_left_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left
    (envelope_le_two_pairedKernel (depth_bounds ρ).1 (depth_bounds ρ).2.le _) (weight_nonneg ρ)

/-- The Poisson-smoothed normalized envelope is integrable and is bounded by
`2 W_(1+h)(t) / R`. Only the height is translated in the integral. -/
public theorem poisson_zetaLocalEnvelope_le {h R : ℝ} (hh : 0 < h) (hR : 0 < R) (t : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * zetaLocalEnvelope R (t - y)) ∧
      (∫ y : ℝ, poisson h y * zetaLocalEnvelope R (t - y)) ≤
        2 * (zetaExteriorTrace (1 + h) t / R) := by
  let f (y : ℝ) := poisson h y * zetaLocalEnvelope R (t - y)
  let g (y : ℝ) := 2 * (poisson h y * zetaExteriorTrace 1 (t - y)) / R
  have hw := poisson_zetaExteriorTrace (by norm_num : (1 / 2 : ℝ) < 1) hh t
  have hg : Integrable g := (hw.1.const_mul 2).div_const R
  have hfg (y : ℝ) : f y ≤ g y := by
    calc
      _ ≤ poisson h y * (2 * (zetaExteriorTrace 1 (t - y) / R)) :=
        mul_le_mul_of_nonneg_left (zetaLocalEnvelope_le hR _) (poisson_nonneg hh y)
      _ = _ := by dsimp only [g]; ring
  have hnonneg (y : ℝ) : 0 ≤ f y :=
    mul_nonneg (poisson_nonneg hh y) <| div_nonneg
      (tsum_nonneg fun ρ ↦ mul_nonneg (weight_nonneg ρ) (envelope_nonneg _)) hR.le
  have hp : Continuous (poisson h) := by
    unfold poisson kernel
    exact (continuous_const.div (by fun_prop) (fun y ↦
      (show 0 < h ^ 2 + y ^ 2 by positivity).ne')).div_const _
  have he : Continuous envelope := by
    unfold envelope
    exact Continuous.inv₀ (by fun_prop) (fun _ ↦ by positivity)
  have hm : AEStronglyMeasurable f volume := by
    have hs : AEStronglyMeasurable
        (fun y : ℝ ↦ ∑' ρ : RightZetaZero, ν ρ * envelope (zetaOrdinate ρ - (t - y))) volume := by
      apply AEStronglyMeasurable.tsum
      intro ρ
      exact (show Continuous (fun y : ℝ ↦ ν ρ * envelope (zetaOrdinate ρ - (t - y))) by
        fun_prop).aestronglyMeasurable
    rw [show f = poisson h *
        ((fun y ↦ ∑' ρ : RightZetaZero, ν ρ * envelope (zetaOrdinate ρ - (t - y))) *
          fun _ ↦ R⁻¹) by
      funext y
      simp only [f, zetaLocalEnvelope, localEnvelope, div_eq_mul_inv, Pi.mul_apply]]
    exact hp.aestronglyMeasurable.mul (hs.mul aestronglyMeasurable_const)
  have hf : Integrable f := hg.mono' hm (ae_of_all _ fun y ↦ by
    rw [Real.norm_of_nonneg (hnonneg y)]
    exact hfg y)
  refine ⟨hf, (integral_mono hf hg hfg).trans_eq ?_⟩
  dsimp only [g]
  rw [integral_div, integral_const_mul, hw.2, mul_div_assoc]

end PoissonExteriorEnvelope
