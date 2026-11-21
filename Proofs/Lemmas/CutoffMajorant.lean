module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted majorants for two-scale cutoff tests

A project estimate for the cutoff argument at the interface of Masullo's
(13.3.1.2)–(13.3.1.3), p. 522 of the pinned edition. The cutoffs have
disjoint transition layers. The exponential difference vanishes linearly
near zero, which bounds the weighted second derivative by an exponential
background plus a thin layer. This does not establish equality of the
full and capped distributions. Integrating the majorant gives a bound
uniform in the cutoff scale, as needed for the compact-test Laplace estimate.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

private theorem cutoff_deriv_deriv_mul {L U : ℝ → ℝ}
    (hL : ContDiff ℝ 2 L) (hU : ContDiff ℝ 2 U) (x : ℝ) :
    deriv (deriv (fun y ↦ L y * U y)) x =
      deriv (deriv L) x * U x + 2 * (deriv L x * deriv U x) +
        L x * deriv (deriv U) x := by
  have hL₁ (y : ℝ) : HasDerivAt L (deriv L y) y :=
    (hL.differentiable two_ne_zero y).hasDerivAt
  have hU₁ (y : ℝ) : HasDerivAt U (deriv U y) y :=
    (hU.differentiable two_ne_zero y).hasDerivAt
  have hL₂ := (hL.differentiable_deriv_two x).hasDerivAt
  have hU₂ := (hU.differentiable_deriv_two x).hasDerivAt
  have hfirst : deriv (fun y ↦ L y * U y) =
      (fun y ↦ deriv L y * U y + L y * deriv U y) :=
    funext fun y ↦ ((hL₁ y).mul (hU₁ y)).deriv
  rw [hfirst]
  calc
    _ = (deriv (deriv L) x * U x + deriv L x * deriv U x) +
        (deriv L x * deriv U x + L x * deriv (deriv U) x) :=
      ((hL₂.mul (hU₁ x)).add ((hL₁ x).mul hU₂)).deriv
    _ = _ := by ring

private theorem cutoff_deriv_deriv_smul {p : ℝ → ℝ} {Δ : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p) (hΔ : ContDiff ℝ 2 Δ) (x : ℝ) :
    deriv (deriv (fun y ↦ p y • Δ y)) x =
      p x • deriv (deriv Δ) x + (2 * deriv p x) • deriv Δ x + deriv (deriv p) x • Δ x := by
  have hp₁ (y : ℝ) : HasDerivAt p (deriv p y) y :=
    (hp.differentiable two_ne_zero y).hasDerivAt
  have hΔ₁ (y : ℝ) : HasDerivAt Δ (deriv Δ y) y :=
    (hΔ.differentiable two_ne_zero y).hasDerivAt
  have hp₂ := (hp.differentiable_deriv_two x).hasDerivAt
  have hΔ₂ := (hΔ.differentiable_deriv_two x).hasDerivAt
  have hfirst : deriv (fun y ↦ p y • Δ y) =
      (fun y ↦ p y • deriv Δ y + deriv p y • Δ y) :=
    funext fun y ↦ ((hp₁ y).smul (hΔ₁ y)).deriv
  rw [hfirst]
  calc
    _ = (p x • deriv (deriv Δ) x + deriv p x • deriv Δ x) +
        (deriv p x • deriv Δ x + deriv (deriv p) x • Δ x) :=
      (((hp₁ x).smul hΔ₂).add (hp₂.smul (hΔ₁ x))).deriv
    _ = _ := by
      rw [mul_smul, two_smul ℝ]
      abel

/-- Weighted pointwise estimate with an exponential background and one thin layer. -/
public theorem cutoff_pointwise_majorant {L U : ℝ → ℝ} {Δ : ℝ → ℂ}
    {N a δ M₁ M₂ A₀ A₁ A₂ B : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B)
    (hL : ContDiff ℝ 2 L) (hU : ContDiff ℝ 2 U) (hΔ : ContDiff ℝ 2 Δ)
    (hL_range : ∀ x, L x ∈ Set.Icc (0 : ℝ) 1)
    (hU_range : ∀ x, U x ∈ Set.Icc (0 : ℝ) 1)
    (hL_layer : ∀ x ∈ Set.Icc (1 / N) (2 / N),
      ‖deriv L x‖ ≤ N * M₁ ∧ ‖deriv (deriv L) x‖ ≤ N ^ 2 * M₂)
    (hL_off : ∀ x ∉ Set.Icc (1 / N) (2 / N),
      deriv L x = 0 ∧ deriv (deriv L) x = 0)
    (hU_bounds : ∀ x, ‖deriv U x‖ ≤ M₁ / N ∧ ‖deriv (deriv U) x‖ ≤ M₂ / N ^ 2)
    (hU_off : ∀ x ∉ Set.Icc N (2 * N), deriv U x = 0)
    (hΔ_exp : ∀ x > 0,
      Real.exp (a * x) * ‖Δ x‖ ≤ A₀ * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv Δ x‖ ≤ A₁ * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv (deriv Δ) x‖ ≤ A₂ * Real.exp (-δ * x))
    (hΔ_linear : ∀ x > 0, Real.exp (a * x) * ‖Δ x‖ ≤ B * x) :
    let f : ℝ → ℂ := fun y ↦ (L y * U y : ℝ) • Δ y
    let C₀ : ℝ := A₀ + A₂ + 2 * M₁ * A₁ + M₂ * A₀
    let C₁ : ℝ := 2 * M₁ * A₁ + 2 * M₂ * B
    ∀ x > 0, Real.exp (a * x) * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
      C₀ * Real.exp (-δ * x) + (Set.Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x := by
  classical
  intro f C₀ C₁ x hx
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hN₁ : 1 ≤ N := le_trans (by norm_num) hN
  have hN₂ : 1 ≤ N ^ 2 := one_le_pow₀ hN₁
  have h2N : 2 / N ≤ 1 := (div_le_iff₀ hNpos).2 (by simpa only [one_mul] using hN)
  -- The two first derivatives cannot be nonzero at the same point.
  have hcross : deriv L x * deriv U x = 0 := by
    by_cases hI : x ∈ Set.Icc (1 / N) (2 / N)
    · have hxN : x < N := lt_of_le_of_lt (hI.2.trans h2N) (lt_of_lt_of_le (by norm_num) hN)
      have hJ : x ∉ Set.Icc N (2 * N) := fun hj ↦ (not_le_of_gt hxN) hj.1
      rw [hU_off x hJ, mul_zero]
    · rw [(hL_off x hI).1, zero_mul]

  let p : ℝ → ℝ := fun y ↦ L y * U y
  have hp : ContDiff ℝ 2 p := hL.mul hU
  have hL₀ : ‖L x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hL_range x).1]
    exact (hL_range x).2
  have hU₀ : ‖U x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hU_range x).1]
    exact (hU_range x).2
  have hU₁ : ‖deriv U x‖ ≤ M₁ := (hU_bounds x).1.trans (div_le_self hM₁ hN₁)
  have hU₂ : ‖deriv (deriv U) x‖ ≤ M₂ := (hU_bounds x).2.trans (div_le_self hM₂ hN₂)
  have hp₀ : ‖p x‖ ≤ 1 := by
    change ‖L x * U x‖ ≤ 1
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul hL₀ hU₀ (norm_nonneg (U x)) (zero_le_one' ℝ)
  have hnorm_prod (l u : ℝ) : ‖l * U x + L x * u‖ ≤ ‖l‖ + ‖u‖ := by
    calc
      _ ≤ ‖l * U x‖ + ‖L x * u‖ := norm_add_le _ _
      _ = ‖l‖ * ‖U x‖ + ‖L x‖ * ‖u‖ := by simp only [norm_mul]
      _ ≤ ‖l‖ * 1 + 1 * ‖u‖ := add_le_add
        (mul_le_mul_of_nonneg_left hU₀ (norm_nonneg l))
        (mul_le_mul_of_nonneg_right hL₀ (norm_nonneg u))
      _ = _ := by simp only [mul_one, one_mul]
  have hp₁_eq : deriv p x = deriv L x * U x + L x * deriv U x :=
    (((hL.differentiable two_ne_zero x).hasDerivAt).mul
      ((hU.differentiable two_ne_zero x).hasDerivAt)).deriv
  have hp₂_eq : deriv (deriv p) x = deriv (deriv L) x * U x + L x * deriv (deriv U) x := by
    simpa only [p, hcross, mul_zero, add_zero] using cutoff_deriv_deriv_mul hL hU x
  have hp₁ : ‖deriv p x‖ ≤ ‖deriv L x‖ + M₁ := by
    rw [hp₁_eq]
    exact (hnorm_prod _ _).trans (add_le_add le_rfl hU₁)
  have hp₂ : ‖deriv (deriv p) x‖ ≤ ‖deriv (deriv L) x‖ + M₂ := by
    rw [hp₂_eq]
    exact (hnorm_prod _ _).trans (add_le_add le_rfl hU₂)

  have hf₀ : ‖f x‖ = ‖p x‖ * ‖Δ x‖ := norm_smul (p x) (Δ x)
  have hf₂ : ‖deriv (deriv f) x‖ ≤
      ‖p x‖ * ‖deriv (deriv Δ) x‖ + (2 * ‖deriv p x‖) * ‖deriv Δ x‖ +
        ‖deriv (deriv p) x‖ * ‖Δ x‖ := by
    change ‖deriv (deriv (fun y ↦ p y • Δ y)) x‖ ≤ _
    rw [cutoff_deriv_deriv_smul hp hΔ x]
    calc
      _ ≤ (‖p x • deriv (deriv Δ) x‖ + ‖(2 * deriv p x) • deriv Δ x‖) +
          ‖deriv (deriv p) x • Δ x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul, norm_mul, Real.norm_ofNat]

  let w := Real.exp (a * x)
  let E := Real.exp (-δ * x)
  let W₀ := w * ‖Δ x‖
  let W₁ := w * ‖deriv Δ x‖
  let W₂ := w * ‖deriv (deriv Δ) x‖
  let layer := 2 * ‖deriv L x‖ * W₁ + ‖deriv (deriv L) x‖ * W₀
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hW₀ : 0 ≤ W₀ := mul_nonneg hw (norm_nonneg _)
  have hW₁ : 0 ≤ W₁ := mul_nonneg hw (norm_nonneg _)
  have hW₂ : 0 ≤ W₂ := mul_nonneg hw (norm_nonneg _)
  have hWexp : W₀ ≤ A₀ * E ∧ W₁ ≤ A₁ * E ∧ W₂ ≤ A₂ * E := hΔ_exp x hx
  have hWlin : W₀ ≤ B * x := hΔ_linear x hx
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  have hbase : W₀ + W₂ + (2 * M₁) * W₁ + M₂ * W₀ ≤ C₀ * E := by
    calc
      _ ≤ A₀ * E + A₂ * E + (2 * M₁) * (A₁ * E) + M₂ * (A₀ * E) :=
        add_le_add (add_le_add (add_le_add hWexp.1 hWexp.2.2)
          (mul_le_mul_of_nonneg_left hWexp.2.1 (mul_nonneg hTwo hM₁)))
          (mul_le_mul_of_nonneg_left hWexp.1 hM₂)
      _ = _ := by dsimp only [C₀]; ring
  have hmain : w * (‖f x‖ + ‖deriv (deriv f) x‖) ≤ C₀ * E + layer := by
    calc
      _ ≤ w * (‖p x‖ * ‖Δ x‖ + (‖p x‖ * ‖deriv (deriv Δ) x‖ +
          (2 * ‖deriv p x‖) * ‖deriv Δ x‖ + ‖deriv (deriv p) x‖ * ‖Δ x‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hf₀.le hf₂) hw
      _ = ‖p x‖ * W₀ + ‖p x‖ * W₂ + (2 * ‖deriv p x‖) * W₁ + ‖deriv (deriv p) x‖ * W₀ := by
        dsimp only [W₀, W₁, W₂]
        ring
      _ ≤ 1 * W₀ + 1 * W₂ + (2 * (‖deriv L x‖ + M₁)) * W₁ +
          (‖deriv (deriv L) x‖ + M₂) * W₀ :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hp₀ hW₀)
          (mul_le_mul_of_nonneg_right hp₀ hW₂))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp₁ hTwo) hW₁))
          (mul_le_mul_of_nonneg_right hp₂ hW₀)
      _ = (W₀ + W₂ + (2 * M₁) * W₁ + M₂ * W₀) + layer := by
        dsimp only [layer]
        ring
      _ ≤ _ := add_le_add hbase le_rfl

  change w * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
    C₀ * E + (Set.Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x
  refine hmain.trans (add_le_add le_rfl ?_)
  by_cases hI : x ∈ Set.Icc (1 / N) (2 / N)
  · rw [Set.indicator_of_mem hI (fun _ ↦ C₁ * N)]
    obtain ⟨hL₁, hL₂⟩ := hL_layer x hI
    have hE : E ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hδ.le) hx.le)
    have hW₁A : W₁ ≤ A₁ := hWexp.2.1.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hA₁)
    have hthin₁ : 2 * ‖deriv L x‖ * W₁ ≤ 2 * (N * M₁) * A₁ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL₁ hTwo) hW₁A hW₁
        (mul_nonneg hTwo (mul_nonneg hNpos.le hM₁))
    have hthin₂ : ‖deriv (deriv L) x‖ * W₀ ≤ (2 * M₂ * B) * N := by
      have hcoef : 0 ≤ N ^ 2 * M₂ := mul_nonneg (sq_nonneg N) hM₂
      calc
        _ ≤ (N ^ 2 * M₂) * (B * x) := mul_le_mul hL₂ hWlin hW₀ hcoef
        _ ≤ (N ^ 2 * M₂) * (B * (2 / N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI.2 hB) hcoef
        _ = _ := by field_simp [ne_of_gt hNpos]
    calc
      layer ≤ 2 * (N * M₁) * A₁ + (2 * M₂ * B) * N := add_le_add hthin₁ hthin₂
      _ = C₁ * N := by dsimp only [C₁]; ring
  · rw [Set.indicator_of_notMem hI (fun _ ↦ C₁ * N)]
    obtain ⟨hL₁, hL₂⟩ := hL_off x hI
    simp only [layer, hL₁, hL₂, norm_zero, mul_zero, zero_mul, add_zero, le_refl]

/-- Integrating a moving layer of width `1 / N` and height `C₁ * N`
costs `C₁`, uniformly in the scale `N`. -/
public theorem weightedCutoffIntegrals_le {f : ℝ → ℂ} {a δ C₀ C₁ N : ℝ}
    (hδ : 0 < δ) (hN : 0 < N)
    (hf : Continuous f) (hs : HasCompactSupport f)
    (hf₂ : Continuous (deriv (deriv f)))
    (hs₂ : HasCompactSupport (deriv (deriv f)))
    (hmajor : ∀ x > 0,
      Real.exp (a * x) * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
        C₀ * Real.exp (-δ * x) + (Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
        (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) ≤
      C₀ / δ + C₁ := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let I := Icc (1 / N) (2 / N)
  let p : ℝ → ℝ := fun x ↦ Real.exp (a * x) * ‖f x‖
  let q : ℝ → ℝ := fun x ↦ Real.exp (a * x) * ‖deriv (deriv f) x‖
  let g : ℝ → ℝ := fun x ↦ C₀ * Real.exp (-δ * x)
  let b : ℝ → ℝ := I.indicator (fun _ ↦ C₁ * N)
  have hI : MeasurableSet I := measurableSet_Icc
  have hsub : I ⊆ Ioi (0 : ℝ) := fun _ hx ↦ (one_div_pos.mpr hN).trans_le hx.1
  have hlen : 2 / N - 1 / N = 1 / N := by simp only [div_eq_mul_inv]; ring
  have hμI : μ I = ENNReal.ofReal (1 / N) := by
    change volume.restrict (Ioi (0 : ℝ)) I = _
    rw [Measure.restrict_apply hI, inter_eq_left.mpr hsub]
    change volume (Icc (1 / N) (2 / N)) = _
    rw [Real.volume_Icc, hlen]
  have hw : Continuous (fun x : ℝ ↦ Real.exp (a * x)) := by fun_prop
  have hp : Integrable p μ :=
    (hw.mul hf.norm).integrable_of_hasCompactSupport
      (hs.comp_left (g := fun z : ℂ ↦ ‖z‖) norm_zero).mul_left |>.integrableOn
  have hq : Integrable q μ :=
    (hw.mul hf₂.norm).integrable_of_hasCompactSupport
      (hs₂.comp_left (g := fun z : ℂ ↦ ‖z‖) norm_zero).mul_left |>.integrableOn
  have hexp : Integrable (fun x : ℝ ↦ Real.exp (-δ * x)) μ :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hδ) 0
  have hg : Integrable g μ := hexp.const_mul C₀
  have hb : Integrable b μ := by
    apply (integrable_indicator_iff hI).mpr
    exact integrableOn_const (by rw [hμI]; exact ENNReal.ofReal_ne_top)
  have hgint : (∫ x, g x ∂μ) = C₀ / δ := by
    change (∫ x : ℝ in Ioi (0 : ℝ), C₀ * Real.exp (-δ * x)) = _
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hδ)]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]
  -- The layer width cancels its height's factor of `N`.
  have hbint : (∫ x, b x ∂μ) = C₁ := by
    dsimp only [b]
    rw [integral_indicator_const _ hI, measureReal_def, hμI,
      ENNReal.toReal_ofReal (one_div_nonneg.mpr hN.le), smul_eq_mul]
    field_simp [hN.ne']
  have hle : (fun x ↦ p x + q x) ≤ᵐ[μ] (fun x ↦ g x + b x) := by
    have hpos : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem (μ := volume) hpos] with x hx
    simpa only [p, q, g, b, I, mul_add] using hmajor x (mem_Ioi.mp hx)
  change (∫ x, p x ∂μ) + (∫ x, q x ∂μ) ≤ _
  calc
    _ = ∫ x, (p x + q x) ∂μ := (integral_add hp hq).symm
    _ ≤ ∫ x, (g x + b x) ∂μ := integral_mono_ae (hp.add hq) (hg.add hb) hle
    _ = C₀ / δ + C₁ := by rw [integral_add hg hb, hgint, hbint]

end Masullo
