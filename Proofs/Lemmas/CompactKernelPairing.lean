module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Testing a locally square-integrable kernel on its own truncations -/

open MeasureTheory Set

namespace Masullo

private theorem memLp_compactConjKernel {k : ℝ → ℂ} (hk : Continuous k) (n : ℕ) :
    MemLp ((Icc (-(n : ℝ)) n).indicator (fun x ↦ star (k x))) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  apply (memLp_two_iff_integrable_sq_norm hk.star.aestronglyMeasurable).2
  exact (hk.star.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc

/-- The `L²(dx)` class of the conjugate kernel restricted to `[-n,n]` and
extended by zero. Continuity of the kernel suffices for local square integrability. -/
public noncomputable def compactConjKernel {k : ℝ → ℂ} (hk : Continuous k) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_compactConjKernel hk n).toLp _

/-- The representative of the compact test is the indicator cut of the conjugate kernel. -/
public theorem compactConjKernel_ae_eq {k : ℝ → ℂ} (hk : Continuous k) (n : ℕ) :
    (compactConjKernel hk n : ℝ → ℂ) =ᵐ[volume]
      (Icc (-(n : ℝ)) n).indicator (fun x ↦ star (k x)) :=
  (memLp_compactConjKernel hk n).coeFn_toLp

private theorem inner_compactConjKernel {k : ℝ → ℂ} (hk : Continuous k) (n : ℕ)
    (v : Lp ℂ 2 (volume : Measure ℝ))
    (hv : ∀ᵐ x ∂volume, x ∈ Icc (-(n : ℝ)) n → v x = star (k x)) :
    inner ℂ v (compactConjKernel hk n) = ∫ x in Icc (-(n : ℝ)) n, star (k x) * k x := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards [compactConjKernel_ae_eq hk n, hv] with x hx hvx
  rw [RCLike.inner_apply, hx]
  by_cases h : x ∈ Icc (-(n : ℝ)) n
  · rw [indicator_of_mem h, indicator_of_mem h, hvx h]
    change _ * star (star _) = _
    rw [star_star]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

private theorem compactConjKernel_self {k : ℝ → ℂ} (hk : Continuous k) (n : ℕ) :
    inner ℂ (compactConjKernel hk n) (compactConjKernel hk n) =
      ∫ x in Icc (-(n : ℝ)) n, star (k x) * k x := by
  apply inner_compactConjKernel
  filter_upwards [compactConjKernel_ae_eq hk n] with x hx hxIcc
  rw [hx, indicator_of_mem hxIcc]

/-- A continuous functional can agree with the bilinear pairing against a
continuous kernel on its conjugate truncations exactly when the kernel is square integrable. -/
public theorem exists_compactKernelPairing_iff {k : ℝ → ℂ} (hk : Continuous k) :
    (∃ F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ, ∀ n : ℕ,
      F (compactConjKernel hk n) = ∫ x in Icc (-(n : ℝ)) n, star (k x) * k x) ↔
      MemLp k 2 volume := by
  constructor
  · rintro ⟨F, hF⟩
    let S := fun n : ℕ ↦ Icc (-(n : ℝ)) n
    have hnorm (n : ℕ) : ‖compactConjKernel hk n‖ ≤ ‖F‖ := by
      have h : ‖compactConjKernel hk n‖ ^ 2 ≤ ‖F‖ * ‖compactConjKernel hk n‖ := by
        calc
          _ = (F (compactConjKernel hk n)).re := by
            rw [hF n, ← compactConjKernel_self]
            exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
          _ ≤ ‖F (compactConjKernel hk n)‖ := Complex.re_le_norm _
          _ ≤ _ := F.le_opNorm _
      by_cases hzero : ‖compactConjKernel hk n‖ = 0
      · rw [hzero]; exact norm_nonneg _
      · exact le_of_mul_le_mul_right (by simpa only [pow_two] using h)
          (lt_of_le_of_ne (norm_nonneg _) (fun h ↦ hzero h.symm))
    have hmass (n : ℕ) : (∫ x in S n, ‖k x‖ ^ 2) = ‖compactConjKernel hk n‖ ^ 2 := by
      have hi : IntegrableOn (fun x ↦ star (k x) * k x) (S n) :=
        (hk.star.mul hk).continuousOn.integrableOn_compact isCompact_Icc
      calc
        _ = ∫ x in S n, (star (k x) * k x).re := by
          refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
          change ‖k x‖ ^ 2 = ((starRingEnd ℂ) (k x) * k x).re
          rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        _ = (∫ x in S n, star (k x) * k x).re := integral_re hi
        _ = _ := by
          rw [← compactConjKernel_self hk n]
          exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hmono : Monotone S := by
      intro i j hij
      have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      exact Icc_subset_Icc (neg_le_neg h) h
    have hcover : ⋃ n, S n = univ := by
      refine eq_univ_of_forall fun x ↦ ?_
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact mem_iUnion.mpr ⟨n, abs_le.mp hn⟩
    apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
    apply (lintegral_ofReal_ne_top_iff_integrable (hk.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x ↦ sq_nonneg ‖k x‖)).1
    suffices (∫⁻ x, ENNReal.ofReal (‖k x‖ ^ 2)) ≤ ENNReal.ofReal (‖F‖ ^ 2) from
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
    have hexhaust : (∫⁻ x, ENNReal.ofReal (‖k x‖ ^ 2)) =
        ⨆ n, ∫⁻ x in S n, ENNReal.ofReal (‖k x‖ ^ 2) := by
      simpa only [hcover, Measure.restrict_univ] using
        setLIntegral_iUnion_of_directed (μ := volume) (fun x ↦ ENNReal.ofReal (‖k x‖ ^ 2))
          hmono.directed_le
    rw [hexhaust]
    refine iSup_le fun n ↦ ?_
    have hi : IntegrableOn (fun x ↦ ‖k x‖ ^ 2) (S n) :=
      (hk.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x ↦ sq_nonneg ‖k x‖),
      hmass n]
    exact ENNReal.ofReal_le_ofReal (by gcongr; exact hnorm n)
  · intro h
    let hc := Complex.isometry_conj.lipschitzWith.comp_memLp (by simp) h
    refine ⟨innerSL ℂ (hc.toLp _), fun n ↦ ?_⟩
    rw [innerSL_apply_apply]
    apply inner_compactConjKernel
    exact hc.coeFn_toLp.mono fun _ hx _ ↦ hx

end Masullo
