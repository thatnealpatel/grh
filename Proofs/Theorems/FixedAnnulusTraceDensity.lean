module

public import Lemmas.FixedAnnulusFourier
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # The diagonal trace density of a Fourier window kernel

The diagonal is formed from the rank-one series in `L¹` for the same measure as the
underlying `L²` space. It is not the restriction of a product-measure a.e. kernel identity.
-/

open MeasureTheory InnerProductSpace
open scoped ENNReal InnerProductSpace

namespace Masullo.OperatorTrace
noncomputable section

variable {L : ℝ} [Fact (0 < L)] {μ : Measure ℝ}
local notation "H" => Lp ℂ 2 μ

/-- The pointwise sum of conjugate Riesz input times output for the rank-one presentation
of `windowKernel p q f` composed on the right with `Q`. -/
@[expose] public def windowKernelTraceDensity (p q : H) (f : C(AddCircle L, ℂ))
    (Q : H →L[ℂ] H) (x : ℝ) : ℂ :=
  ∑' k : ℤ, star (Q.adjoint (W q (fourier (T := L) k)) x) * outputMode p f k x

private theorem windowKernelTraceDensity_spec (p q : H) (f : C(AddCircle L, ℂ))
    (hf : Summable (fourierCoeff f)) (Q : H →L[ℂ] H) :
    Integrable (windowKernelTraceDensity p q f Q) μ ∧
    (∀ᵐ x ∂μ, Summable fun k : ℤ =>
      ‖star (Q.adjoint (W q (fourier (T := L) k)) x) * outputMode p f k x‖) ∧
    (∫ x, windowKernelTraceDensity p q f Q x ∂μ) =
      ∑' k : ℤ, ⟪W q (fourier (T := L) k), Q (outputMode p f k)⟫_ℂ := by
  let u := outputMode p f
  let v (k : ℤ) := Q.adjoint (W q (fourier (T := L) k))
  let D (k : ℤ) := (ContinuousLinearMap.mul ℂ ℂ).holder 1 (star (v k)) (u k)
  have hD (k : ℤ) : (D k : ℝ → ℂ) =ᵐ[μ] fun x => star (v k x) * u k x := by
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1) (star (v k)) (u k),
      Lp.coeFn_star (v k)] with x hx hs
    simp only [D, hx, hs, ContinuousLinearMap.mul_apply', Pi.star_apply]
  have hnorm (z : H) : ‖star z‖ = ‖z‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star z), eLpNorm_star]
  have hsD : Summable (fun k => ‖D k‖) := by
    apply (windowKernel_rankOne (p := p) (q := q) hf Q).1.of_nonneg_of_le
      (fun k => norm_nonneg (D k))
    intro k
    rw [norm_rankOne, mul_comm]
    calc
      ‖D k‖ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖star (v k)‖ * ‖u k‖ :=
        (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le (r := 1) _ _
      _ ≤ ‖v k‖ * ‖u k‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_mul_le ℂ ℂ))
          (norm_nonneg _)
  have htop : (∑' k, ‖D k‖ₑ) ≠ ∞ := tsum_eNorm_ne_top_iff_summable_norm.2 hsD
  have hDall := ae_all_iff.2 hD
  have hsum : ((∑' k, D k) : Lp ℂ 1 μ) =ᵐ[μ] windowKernelTraceDensity p q f Q := by
    filter_upwards [Lp.coeFn_tsum htop, hDall] with x hx hDx
    simpa only [windowKernelTraceDensity, hDx, u, v] using hx
  refine ⟨(memLp_one_iff_integrable.1 (Lp.memLp _)).congr hsum, ?_, ?_⟩
  · have h : ∀ᵐ x ∂μ, Summable fun k => ‖D k x‖ := by
      apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
      simpa only [← Lp.eNorm_def] using htop
    filter_upwards [h, hDall] with x hx hDx
    simpa only [hDx, u, v] using hx
  · have hI (k : ℤ) : L1.integralCLM' ℂ (D k) =
        ⟪W q (fourier (T := L) k), Q (u k)⟫_ℂ := by
      rw [← L1.integral_eq', L1.integral_eq_integral, ← Q.adjoint_inner_left, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hD k] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
      rfl
    rw [← integral_congr_ae hsum, ← L1.integral_eq_integral, L1.integral_eq' ℂ]
    simpa only [ContinuousLinearMap.coe_coe, hI, u] using
      (hsD.of_norm.hasSum.mapL (L1.integralCLM' ℂ)).tsum_eq.symm

/-- The diagonal series is absolutely convergent almost everywhere and sums to an
integrable density for the underlying `L²` measure. -/
public theorem windowKernel_traceDensity_integrable (p q : H) (f : C(AddCircle L, ℂ))
    (hf : Summable (fourierCoeff f)) (Q : H →L[ℂ] H) :
    Integrable (windowKernelTraceDensity p q f Q) μ ∧
    ∀ᵐ x ∂μ, Summable fun k : ℤ =>
      ‖star (Q.adjoint (W q (fourier (T := L) k)) x) * outputMode p f k x‖ := by
  obtain ⟨hi, ha, _⟩ := windowKernelTraceDensity_spec p q f hf Q
  exact ⟨hi, ha⟩

/-- In any Hilbert basis, the trace is the integral of the rank-one diagonal density. -/
public theorem windowKernel_traceDensity {ι : Type*} (b : HilbertBasis ι ℂ H) (p q : H)
    (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f)) (Q : H →L[ℂ] H) :
    HasSum (fun i => ⟪b i, windowKernel p q f (Q (b i))⟫_ℂ)
      (∫ x, windowKernelTraceDensity p q f Q x ∂μ) := by
  rw [(windowKernelTraceDensity_spec p q f hf Q).2.2]
  exact (windowKernel_trace b p q f hf Q).2

/-- Multiplication on the underlying `L²` by an essentially bounded complex function. -/
public def logMultiplier {m : ℝ → ℂ} (hm : MemLp m ∞ μ) : H →L[ℂ] H :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 (hm.toLp m)

/-- The bounded multiplier acts by pointwise multiplication almost everywhere. -/
public theorem logMultiplier_apply_ae {m : ℝ → ℂ} (hm : MemLp m ∞ μ) (z : H) :
    (logMultiplier hm z : ℝ → ℂ) =ᵐ[μ] fun x => m x * z x := by
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2 (hm.toLp m) z =ᵐ[μ] _
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hm.toLp m) z,
    hm.coeFn_toLp] with x hx hm'
  simpa only [ContinuousLinearMap.mul_apply', hm'] using hx

private theorem logMultiplier_adjoint_apply_ae {m : ℝ → ℂ} (hm : MemLp m ∞ μ) (z : H) :
    ((logMultiplier hm).adjoint z : ℝ → ℂ) =ᵐ[μ] fun x => star (m x) * z x := by
  have he : (logMultiplier hm).adjoint z = logMultiplier hm.star z := by
    apply ext_inner_right ℂ
    intro u
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [logMultiplier_apply_ae hm u, logMultiplier_apply_ae hm.star z] with x hu hz
    simp only [RCLike.inner_apply, hu, hz, Pi.star_apply, map_mul, starRingEnd_apply,
      star_star]
    ring
  rw [he]
  exact logMultiplier_apply_ae hm.star z

/-- After a right multiplication, the new rank-one diagonal is the old density times the
multiplier, not its conjugate: the Riesz input vector sees the adjoint multiplier. -/
public theorem windowKernelTraceDensity_comp_logMultiplier (p q : H) (f : C(AddCircle L, ℂ))
    (Q : H →L[ℂ] H) {m : ℝ → ℂ} (hm : MemLp m ∞ μ) :
    windowKernelTraceDensity p q f (Q.comp (logMultiplier hm)) =ᵐ[μ]
      fun x => m x * windowKernelTraceDensity p q f Q x := by
  have h (k : ℤ) := logMultiplier_adjoint_apply_ae hm (Q.adjoint (W q (fourier (T := L) k)))
  filter_upwards [ae_all_iff.2 h] with x hx
  simp only [windowKernelTraceDensity]
  rw [← tsum_mul_left]
  congr 1
  funext k
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, hx k,
    star_mul, star_star, mul_assoc, mul_left_comm]

/-- One density represents all right-localized basis traces. In particular this applies to
any bounded measurable multiplier, or to an indicator of a measurable set. -/
public theorem windowKernel_localized_traceDensity {ι : Type*} (b : HilbertBasis ι ℂ H)
    (p q : H) (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f)) (Q : H →L[ℂ] H)
    {m : ℝ → ℂ} (hm : MemLp m ∞ μ) :
    Integrable (fun x => m x * windowKernelTraceDensity p q f Q x) μ ∧
    HasSum (fun i => ⟪b i, windowKernel p q f (Q (logMultiplier hm (b i)))⟫_ℂ)
      (∫ x, m x * windowKernelTraceDensity p q f Q x ∂μ) := by
  have he := windowKernelTraceDensity_comp_logMultiplier p q f Q hm
  have hi := (windowKernel_traceDensity_integrable p q f hf (Q.comp (logMultiplier hm))).1
  refine ⟨hi.congr he, ?_⟩
  rw [← integral_congr_ae he]
  exact windowKernel_traceDensity b p q f hf (Q.comp (logMultiplier hm))

end

namespace RealLogLevel

/-- The projected fixed-annulus convolution on weighted log `L²` has one integrable
Fourier diagonal density for both its unlocalized trace and all right-localized traces. -/
public theorem fixedAnnulus_traceDensity (α : ℝ) (r : ℕ) (Y : ℝ) {p φ : ℝ → ℂ}
    (hp : Continuous p) (hpK : HasCompactSupport p)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    ∃ (R : ℝ) (hR : 0 < R),
      let : Fact (0 < 8 * R) := ⟨by positivity⟩
      ∃ f : C(AddCircle (8 * R), ℂ),
        Summable (fourierCoeff f) ∧
        let P : H α r := (hp.memLp_of_hasCompactSupport (μ := μ α r) hpK).toLp p
        let qD := q α r (-(2 * R)) (2 * R)
        let QY := Q α r Y
        let d := windowKernelTraceDensity P qD f QY
        let B := (windowKernel P qD f).comp QY
        (∀ z : H α r, (B z : ℝ → ℂ) =ᵐ[μ α r]
          fun x => p x * ∫ y, φ (x - y) * (QY z) y) ∧
        Integrable d (μ α r) ∧
        (∀ {ι : Type*} (b : HilbertBasis ι ℂ (H α r)),
          HasSum (fun i => ⟪b i, B (b i)⟫_ℂ) (∫ x, d x ∂μ α r)) ∧
        ∀ {m : ℝ → ℂ} (hm : MemLp m ∞ (μ α r)),
          Integrable (fun x => m x * d x) (μ α r) ∧
          ∀ {ι : Type*} (b : HilbertBasis ι ℂ (H α r)),
            HasSum (fun i => ⟪b i, B (logMultiplier hm (b i))⟫_ℂ) (∫ x, m x * d x ∂μ α r) := by
  obtain ⟨R, hR, f, _, _, _, hf, B, hB, _, hsum, _⟩ :=
    fixedAnnulus_fourier_presentation.{0} α r Y hp hpK hφ hφK
  let : Fact (0 < 8 * R) := ⟨by positivity⟩
  let P : H α r := (hp.memLp_of_hasCompactSupport (μ := μ α r) hpK).toLp p
  let qD := q α r (-(2 * R)) (2 * R)
  let QY := Q α r Y
  have hBeq : B = (windowKernel P qD f).comp QY :=
    hsum.unique (windowKernel_rankOne (p := P) (q := qD) hf QY).2
  have hi := (windowKernel_traceDensity_integrable P qD f hf QY).1
  refine ⟨R, hR, f, hf, hBeq ▸ hB, hi, ?_, ?_⟩
  · intro ι b
    exact windowKernel_traceDensity b P qD f hf QY
  · intro m hm
    refine ⟨hm.integrable_mul (memLp_one_iff_integrable.2 hi), ?_⟩
    intro ι b
    exact (windowKernel_localized_traceDensity b P qD f hf QY hm).2

end RealLogLevel
end Masullo.OperatorTrace
