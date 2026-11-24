module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Localization of the window kernel

Source: `.godel/alice/prime-conductor-window.md:52–62` at `85842a8fbdcc`, reused in
`.godel/alice/dyadic-conductor-window.md:54–56` at `f92105371112`.
Scope: spatial `L²` leakage of the filtered high piece; no prime or Gamma estimate.
Owner session: `01a20dea-9bff-7af6-950c-47bd0e521e1e`.
-/

open Filter MeasureTheory Set
open scoped Convolution ENNReal

namespace Masullo

local notation "mulℂ" => ContinuousLinearMap.mul ℂ ℂ

private theorem sq_lintegral_mul_le (a b : ℝ → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ y, a y * b y) ^ (2 : ℕ) ≤ (∫⁻ y, a y) * ∫⁻ y, a y * b y ^ (2 : ℕ) := by
  have hsqrt (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = z := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hsquare (z : ℝ≥0∞) : (z ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = z := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hproduct (z w : ℝ≥0∞) : z ^ (1 / 2 : ℝ) * (z * w ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = z * w := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc, ← pow_two, hsqrt, hsquare]
  have hab : Measurable (fun y ↦ a y * b y ^ (2 : ℕ)) := ha.mul (hb.pow_const 2)
  have hCS := ENNReal.lintegral_mul_norm_pow_le (μ := volume) ha.aemeasurable
    hab.aemeasurable (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [hproduct] at hCS
  simpa only [mul_pow, hsqrt] using pow_le_pow_left' hCS 2

private theorem eLpNorm_two_eq {u : ℝ → ℂ} (hu : AEStronglyMeasurable u volume) :
    eLpNorm u 2 volume = (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- The `L¹ × L²` bound, from weighted Cauchy–Schwarz and translation invariance in Tonelli's
formula. Start with measurable representatives so the nonnegative majorant is jointly measurable. -/
private theorem eLpNorm_mulConvolution_le_of_measurable {k h : ℝ → ℂ}
    (hk : Measurable k) (hh : Measurable h) :
    eLpNorm (k ⋆[mulℂ] h) 2 volume ≤ eLpNorm k 1 volume * eLpNorm h 2 volume := by
  let a : ℝ → ℝ≥0∞ := fun y ↦ ‖k y‖ₑ
  let b : ℝ → ℝ≥0∞ := fun x ↦ ‖h x‖ₑ
  have ha : Measurable a := hk.eNorm
  have hb : Measurable b := hh.eNorm
  have hsection (x : ℝ) : ‖(k ⋆[mulℂ] h) x‖ₑ ≤ ∫⁻ y, a y * b (x - y) := by
    rw [convolution_def]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun y ↦ ?_)
    simp only [a, b, ContinuousLinearMap.mul_apply', ← ofReal_norm, norm_mul,
      ENNReal.ofReal_mul (norm_nonneg _), le_rfl]
  have hprod : Measurable (fun p : ℝ × ℝ ↦ a p.2 * b (p.1 - p.2) ^ (2 : ℕ)) :=
    (ha.comp measurable_snd).mul ((hb.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  have hswap : (∫⁻ x : ℝ, ∫⁻ y : ℝ, a y * b (x - y) ^ (2 : ℕ)) =
      (∫⁻ y, a y) * ∫⁻ x, b x ^ (2 : ℕ) := by
    rw [lintegral_lintegral_swap (f := fun x y ↦ a y * b (x - y) ^ (2 : ℕ)) hprod.aemeasurable]
    calc
      _ = ∫⁻ y, a y * ∫⁻ x, b x ^ (2 : ℕ) := by
        refine lintegral_congr fun y ↦ ?_
        have hy : Measurable (fun x : ℝ ↦ b (x - y) ^ (2 : ℕ)) :=
          (hb.comp (measurable_id.sub measurable_const)).pow_const 2
        rw [lintegral_const_mul _ hy]
        congr 1
        exact (measurePreserving_sub_right volume y).lintegral_comp (hb.pow_const 2)
      _ = _ := lintegral_mul_const _ ha
  have hsq : (∫⁻ x, ‖(k ⋆[mulℂ] h) x‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ y, a y) ^ (2 : ℕ) * ∫⁻ x, b x ^ (2 : ℕ) := calc
    _ ≤ ∫⁻ x : ℝ, (∫⁻ y, a y) * ∫⁻ y, a y * b (x - y) ^ (2 : ℕ) := by
      refine lintegral_mono fun x ↦ (pow_le_pow_left' (hsection x) 2).trans ?_
      exact sq_lintegral_mul_le a (fun y ↦ b (x - y)) ha
        (hb.comp (measurable_const.sub measurable_id))
    _ = _ := by
      rw [lintegral_const_mul _ hprod.lintegral_prod_right', hswap, pow_two, mul_assoc]
  have hk' := hk.aestronglyMeasurable (μ := volume)
  have hh' := hh.aestronglyMeasurable (μ := volume)
  rw [eLpNorm_two_eq (hk'.convolution mulℂ hh'), eLpNorm_two_eq hh',
    eLpNorm_one_eq_lintegral_eNorm hk']
  refine (ENNReal.rpow_le_rpow hsq (by norm_num : 0 ≤ (1 / 2 : ℝ))).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num [a, b]

private theorem memLp_mulConvolution_bound {k h : ℝ → ℂ} (hk : Integrable k)
    (hh : MemLp h 2 volume) :
    MemLp (k ⋆[mulℂ] h) 2 volume ∧
      eLpNorm (k ⋆[mulℂ] h) 2 volume ≤ eLpNorm k 1 volume * eLpNorm h 2 volume := by
  have hmk := hk.aestronglyMeasurable
  have hmh := hh.aestronglyMeasurable
  have hbound := eLpNorm_mulConvolution_le_of_measurable
    hmk.stronglyMeasurable_mk.measurable hmh.stronglyMeasurable_mk.measurable
  rw [← convolution_congr mulℂ hmk.ae_eq_mk hmh.ae_eq_mk,
    ← eLpNorm_congr_ae hmk.ae_eq_mk, ← eLpNorm_congr_ae hmh.ae_eq_mk] at hbound
  refine ⟨?_, hbound⟩
  exact hbound.trans_lt
    (ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hk).eLpNorm_lt_top hh.eLpNorm_lt_top)

private theorem integrable_of_window_support {h : ℝ → ℂ} {L : ℝ} (hh : MemLp h 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → h x = 0) : Integrable h := by
  let : IsFiniteMeasure (volume.restrict (Icc 0 L)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have h₁ : MemLp h 1 (volume.restrict (Icc 0 L)) :=
    (hh.mono_measure Measure.restrict_le_self).mono_exponent (by norm_num)
  have hI : IntegrableOn h (Icc 0 L) := memLp_one_iff_integrable.mp h₁
  apply (hI.integrable_indicator measurableSet_Icc).congr
  filter_upwards [hs] with x hx
  by_cases hx' : x ∈ Icc 0 L
  · exact indicator_of_mem hx' h
  · rw [indicator_of_notMem hx' h, hx hx']

private theorem tail_measurableSet (d : ℝ) : MeasurableSet {s : ℝ | d ≤ |s|} :=
  measurableSet_le measurable_const continuous_abs.measurable

private theorem scaled_tail_mass (K : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (d : ℝ) :
    (∫ s : ℝ, ‖{s : ℝ | d ≤ |s|}.indicator (fun t ↦ (Y : ℂ) * K (Y * t)) s‖) =
      ∫ s in {s : ℝ | Y * d ≤ |s|}, ‖K s‖ := by
  let F := {s : ℝ | Y * d ≤ |s|}.indicator (fun t ↦ ‖K t‖)
  have hmem (s : ℝ) : d ≤ |s| ↔ Y * d ≤ |Y * s| := by
    rw [abs_mul, abs_of_pos hY, mul_le_mul_iff_right₀ hY]
  calc
    _ = ∫ s : ℝ, Y * F (Y * s) := by
      apply integral_congr_ae
      refine ae_of_all _ fun s ↦ ?_
      change ‖{t : ℝ | d ≤ |t|}.indicator (fun t ↦ (Y : ℂ) * K (Y * t)) s‖ = Y * F (Y * s)
      dsimp only [F]
      by_cases hs : d ≤ |s|
      · rw [indicator_of_mem (show s ∈ {t : ℝ | d ≤ |t|} from hs),
          indicator_of_mem (show Y * s ∈ {t : ℝ | Y * d ≤ |t|} from (hmem s).mp hs),
          norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
      · rw [indicator_of_notMem (show s ∉ {t : ℝ | d ≤ |t|} from hs),
          indicator_of_notMem (show Y * s ∉ {t : ℝ | Y * d ≤ |t|} from mt (hmem s).mpr hs),
          norm_zero, mul_zero]
    _ = ∫ s : ℝ, F s := by
      rw [integral_const_mul, Measure.integral_comp_mul_left F Y, abs_of_pos (inv_pos.mpr hY),
        smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hY.ne', one_mul]
    _ = _ := integral_indicator (tail_measurableSet _)

private theorem mulConvolution_eq_tail_off_window {k h : ℝ → ℂ} {L d x : ℝ}
    (hs : ∀ᵐ u ∂volume, u ∉ Icc 0 L → h u = 0) (hx : x ∉ Icc (-d) (L + d)) :
    (k ⋆[mulℂ] h) x = ({y : ℝ | d ≤ |y|}.indicator k ⋆[mulℂ] h) x := by
  rw [convolution_def, convolution_def]
  apply integral_congr_ae
  have hshift := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℝ) x
  have hlocal : ∀ᵐ y ∂volume, x - y ∉ Icc 0 L → h (x - y) = 0 :=
    hshift.tendsto_ae.eventually hs
  filter_upwards [hlocal] with y hy
  by_cases hy' : y ∈ {y : ℝ | d ≤ |y|}
  · rw [indicator_of_mem hy']
  · have habs : |y| < d := lt_of_not_ge hy'
    have hxy : x - y ∉ Icc 0 L := by
      intro hxy
      obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
      exact hx ⟨by linarith [hxy.1], by linarith [hxy.2]⟩
    rw [hy hxy, (mulℂ _).map_zero, (mulℂ _).map_zero]

/-- Outside the enlarged window, the filtered high piece `h + K_Y * h` has `L²` norm
at most the input `L²` norm times the original kernel's `L¹` tail beyond `Y*d`.
The convolution is the Lebesgue integral of `K_Y(y) * h(x - y)`, absolutely convergent
for almost every `x`. Both `toReal` norms are finite by the `MemLp` conclusions and hypothesis. -/
public theorem windowKernelLocalization {L Y d : ℝ} (_hL : 0 ≤ L) (hY : 0 < Y) (hd : 0 < d)
    {h K : ℝ → ℂ} (hh : MemLp h 2 volume) (hK : Integrable K)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → h x = 0) :
    let kY : ℝ → ℂ := fun y ↦ (Y : ℂ) * K (Y * y)
    let r : ℝ → ℂ := h + (kY ⋆[mulℂ] h)
    let E := (Icc (-d) (L + d))ᶜ
    (∀ᵐ x ∂volume, ConvolutionExistsAt kY h x mulℂ volume) ∧
      MemLp r 2 volume ∧ MemLp (E.indicator r) 2 volume ∧
      (eLpNorm (E.indicator r) 2 volume).toReal ≤
        (eLpNorm h 2 volume).toReal * ∫ s in {s : ℝ | Y * d ≤ |s|}, ‖K s‖ := by
  dsimp only
  let kY : ℝ → ℂ := fun y ↦ (Y : ℂ) * K (Y * y)
  let kT := {y : ℝ | d ≤ |y|}.indicator kY
  let r := h + (kY ⋆[mulℂ] h)
  let E := (Icc (-d) (L + d))ᶜ
  change (∀ᵐ x ∂volume, ConvolutionExistsAt kY h x mulℂ volume) ∧
    MemLp r 2 volume ∧ MemLp (E.indicator r) 2 volume ∧ _
  have hkY : Integrable kY := (hK.comp_mul_left' hY.ne').const_mul (Y : ℂ)
  have hkT : Integrable kT := hkY.indicator (tail_measurableSet d)
  have hE : MeasurableSet E := measurableSet_Icc.compl
  have hr : MemLp r 2 volume := hh.add (memLp_mulConvolution_bound hkY hh).1
  refine ⟨hkY.ae_convolution_exists mulℂ (integrable_of_window_support hh hs),
    hr, hr.indicator hE.nullMeasurableSet, ?_⟩
  have hsub : Icc 0 L ⊆ Icc (-d) (L + d) := Icc_subset_Icc (by linarith) (by linarith)
  have heq : r =ᵐ[volume.restrict E] (kT ⋆[mulℂ] h) := by
    filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae hs] with x hx hzero
    simp only [r, Pi.add_apply, hzero (fun hin ↦ hx (hsub hin)), zero_add]
    exact mulConvolution_eq_tail_off_window hs hx
  have hnorm : eLpNorm (E.indicator r) 2 volume ≤
      eLpNorm kT 1 volume * eLpNorm h 2 volume := calc
    _ = eLpNorm r 2 (volume.restrict E) :=
      eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet
    _ = eLpNorm (kT ⋆[mulℂ] h) 2 (volume.restrict E) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm (kT ⋆[mulℂ] h) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ _ := (memLp_mulConvolution_bound hkT hh).2
  have hmass : (eLpNorm kT 1 volume).toReal = ∫ s in {s : ℝ | Y * d ≤ |s|}, ‖K s‖ := by
    have hnonneg : 0 ≤ ∫ s, ‖kT s‖ := integral_nonneg (fun s ↦ norm_nonneg (kT s))
    rw [eLpNorm_one_eq_lintegral_eNorm hkT.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm hkT, ENNReal.toReal_ofReal hnonneg]
    exact scaled_tail_mass K hY d
  have hnorm' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hkT).eLpNorm_ne_top hh.eLpNorm_ne_top) hnorm
  simpa only [ENNReal.toReal_mul, hmass, mul_comm] using hnorm'

end Masullo
