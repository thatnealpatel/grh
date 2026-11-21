module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Recovering square integrability on a tail by smooth kernel tests -/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- A continuous compactly supported profile gives an `L²` class after
multiplication by any continuous weight. -/
public theorem weightedCompact_memLp {w u : ℝ → ℂ} (hw : Continuous w)
    (hu : Continuous u) (hc : HasCompactSupport u) :
    MemLp (fun x ↦ w x * u x) 2 volume :=
  (hw.mul hu).memLp_of_hasCompactSupport hc.mul_left

private theorem norm_toLp_sq {a : ℝ → ℂ} (ha : MemLp a 2 volume) :
    ‖ha.toLp a‖ ^ 2 = ∫ x, ‖a x‖ ^ 2 := by
  let A := ha.toLp a
  calc
    _ = (inner ℂ A A).re := (inner_self_eq_norm_sq (𝕜 := ℂ) A).symm
    _ = ∫ x, (inner ℂ (A x) (A x)).re := by
      rw [L2.inner_def]
      exact (integral_re (L2.integrable_inner (𝕜 := ℂ) A A)).symm
    _ = _ := integral_congr_ae (ha.coeFn_toLp.mono fun x hx ↦ by
      change A x = a x at hx
      change (inner ℂ (A x) (A x)).re = _
      rw [hx]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-- If a bounded functional represents the smooth compact-profile pairing,
the divided kernel `k` is square integrable on the indicated tail whenever
its conjugate there is the weighting of a smooth profile `u₀`.
The coordinate `e` allows either orientation of the real line. -/
public theorem integrableOn_sq_norm_of_smoothKernelPairing
    {w g k u₀ : ℝ → ℂ} (hw : Continuous w) (hg : Continuous g) (hk : Continuous k)
    (hu₀ : ContDiff ℝ ∞ u₀) (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ (e : ℝ → ℝ))
    (hdiv : ∀ x, g x = w x * k x) (hconj : ∀ x, 0 < e x → w x * u₀ x = star (k x))
    (F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ)
    (hF : ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u),
      F ((weightedCompact_memLp hw hu.continuous hc).toLp _) = ∫ x, u x * g x) :
    IntegrableOn (fun x ↦ ‖k x‖ ^ 2) (e ⁻¹' Ici 1) := by
  let q := fun x ↦ ‖k x‖ ^ 2
  let S := fun n : ℕ ↦ e ⁻¹' Icc 1 ((n : ℝ) + 2)
  have hS (n : ℕ) : MeasurableSet (S n) := e.continuous.measurable measurableSet_Icc
  have hmass (n : ℕ) : (∫⁻ x in S n, ENNReal.ofReal (q x)) ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
    let b : ContDiffBump ((n : ℝ) / 2 + 3 / 2) :=
      { rIn := (n : ℝ) / 2 + 1 / 2
        rOut := (n : ℝ) / 2 + 1
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    let χ : ℝ → ℝ := b ∘ e
    have hχ : ContDiff ℝ ∞ χ := b.contDiff.comp he
    have hcχ : HasCompactSupport χ := b.hasCompactSupport.comp_homeomorph e
    have hzero (x : ℝ) (hx : e x ≤ 0) : χ x = 0 := by
      have h : e x ∉ Function.support b := by
        rw [b.support_eq, Metric.mem_ball, Real.dist_eq, not_lt]
        dsimp [b]
        exact le_trans (by linarith) (neg_le_abs _)
      change b (e x) = 0
      simpa only [Function.mem_support, not_ne_iff] using h
    have hone (x : ℝ) (hx : x ∈ S n) : χ x = 1 := by
      apply b.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change 1 ≤ e x ∧ e x ≤ (n : ℝ) + 2 at hx
      dsimp [b]
      constructor <;> linarith [hx.1, hx.2]
    let c : ℝ → ℂ := fun x ↦ (χ x : ℂ)
    have hc : HasCompactSupport c := hcχ.comp_left (g := Complex.ofReal) (by simp)
    let u := c * u₀
    have hu : ContDiff ℝ ∞ u := (Complex.ofRealCLM.contDiff.comp hχ).mul hu₀
    have hcu : HasCompactSupport u := hc.mul_right
    let ha := weightedCompact_memLp hw hu.continuous hcu
    let A := ha.toLp _
    have hcut (x : ℝ) : w x * u x = c x * star (k x) := by
      change w x * (c x * u₀ x) = _
      rw [mul_left_comm]
      by_cases hx : 0 < e x
      · rw [hconj x hx]
      · have hc0 : c x = 0 := by simp [c, hzero x (le_of_not_gt hx)]
        simp [hc0]
    have hpair (x : ℝ) : (u x * g x).re = χ x * q x := by
      rw [hdiv x, ← mul_assoc, mul_comm (u x) (w x), hcut, mul_assoc]
      change (c x * ((starRingEnd ℂ) (k x) * k x)).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnorm (x : ℝ) : ‖w x * u x‖ ^ 2 = χ x ^ 2 * q x := by
      rw [hcut, norm_mul, mul_pow, norm_star]
      dsimp only [c, q]
      have h0 : 0 ≤ χ x := b.nonneg
      rw [Complex.norm_real, Real.norm_of_nonneg h0]
    have hi : Integrable (fun x ↦ χ x * q x) :=
      (hχ.continuous.mul (hk.norm.pow 2)).integrable_of_hasCompactSupport hcχ.mul_right
    have hnorm_int : Integrable (fun x ↦ ‖w x * u x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (hw.mul hu.continuous).aestronglyMeasurable).1 ha
    have hval : (F A).re = ∫ x, χ x * q x := by
      have hi' : Integrable (fun x ↦ u x * g x) :=
        (hu.continuous.mul hg).integrable_of_hasCompactSupport hcu.mul_right
      rw [hF u hu hcu]
      exact (integral_re hi').symm.trans (integral_congr_ae (ae_of_all _ hpair))
    have hA : ‖A‖ ≤ ‖F‖ := by
      have h : ‖A‖ ^ 2 ≤ ‖F‖ * ‖A‖ := calc
        _ = ∫ x, ‖w x * u x‖ ^ 2 := norm_toLp_sq ha
        _ ≤ ∫ x, χ x * q x := by
          refine integral_mono hnorm_int hi fun x ↦ ?_
          rw [hnorm]
          exact mul_le_mul_of_nonneg_right
            (calc
              χ x ^ 2 = χ x * χ x := sq _
              _ ≤ χ x * 1 := mul_le_mul_of_nonneg_left b.le_one b.nonneg
              _ = χ x := mul_one _)
            (sq_nonneg _)
        _ = (F A).re := hval.symm
        _ ≤ ‖F A‖ := Complex.re_le_norm _
        _ ≤ _ := F.le_opNorm A
      by_contra! hlt
      nlinarith [mul_pos (sub_pos.mpr hlt) ((norm_nonneg F).trans_lt hlt)]
    rw [← lintegral_indicator (hS n)]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (‖w x * u x‖ ^ 2) := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : x ∈ S n
        · rw [indicator_of_mem hx, hnorm, hone x hx, one_pow, one_mul]
        · rw [indicator_of_notMem hx]; exact bot_le
      _ = ENNReal.ofReal (‖A‖ ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hnorm_int (ae_of_all _ fun _ ↦ sq_nonneg _),
          ← norm_toLp_sq ha]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr)
  have hmono : Monotone S := by
    intro i j hij
    exact preimage_mono (Icc_subset_Icc le_rfl (by exact_mod_cast Nat.add_le_add_right hij 2))
  have hcover : ⋃ n, S n = e ⁻¹' Ici 1 := by
    ext x
    rw [mem_iUnion]
    change (∃ n : ℕ, 1 ≤ e x ∧ e x ≤ (n : ℝ) + 2) ↔ 1 ≤ e x
    constructor
    · rintro ⟨_, hx, _⟩; exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (e x)
      exact ⟨n, hx, by linarith⟩
  apply (lintegral_ofReal_ne_top_iff_integrable (hk.norm.pow 2).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ sq_nonneg _)).1
  change (∫⁻ x in e ⁻¹' Ici 1, ENNReal.ofReal (q x)) ≠ ⊤
  rw [← hcover, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hmass)

end Masullo
