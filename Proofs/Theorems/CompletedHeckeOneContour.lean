module

public import Theorems.CompletedHeckeOneExhaustion
import Lemmas.AnalyticSlabSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The completed trivial Hecke contour identity

In §B.4.2.1, p. 614, Masullo applies the good-rectangle limit of
(B.3.2.1)–(2), p. 606, to (B.4.2.1). The zero sum in (B.4.2.2) is
understood there as a height cutoff. We repair the passage to the
unrestricted sum: keep the disk count of the same numerator used to
choose the rectangles, prove absolute summability, and identify the
cofinal rectangle limit with the sum over the whole zero divisor.
The same-continuation conductor reflection underlying (B.4.2.3) is used
here only for zero exclusion on the open left half-plane. The theorem is
not a local-factor evaluation or a trace comparison.
Source reading provisional (pinned Markdown and numbered PDF layout).
-/

open Complex Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- At `a = 2`, (B.4.2.2) for the completed trivial Euler product and every
smooth compact log profile. The sum counts full orders of the ordinary
zeros of the very same continuation and is absolutely convergent. -/
public theorem exists_completedHecke_one_contour_identity
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ,
      Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s) ∧
      Differentiable ℂ H ∧
      (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      (∀ z, H z = 0 → z ≠ 0 ∧ z ≠ 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ L z = 0 ∧
        analyticOrderNatAt H z = analyticOrderNatAt L z) ∧
      (∀ z, z ≠ 0 → z ≠ 1 → L z = 0 → H z = 0) ∧
      (∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        let Φ := compactLogMellin g
        let V := fun (σ t : ℝ) ↦ Φ ((σ : ℂ) + (t : ℂ) * I) *
          logDeriv L ((σ : ℂ) + (t : ℂ) * I)
        let W := fun (z : {z : ℂ // H z = 0}) ↦ (analyticOrderNatAt H z.val : ℂ) * Φ z.val
        Integrable (V 2) ∧ Integrable (V (-1)) ∧ Summable (fun z ↦ ‖W z‖) ∧
          ((∫ t, V 2 t) - (∫ t, V (-1) t)) / (2 * (Real.pi : ℂ)) =
            (∑' z, W z) - Φ 0 - Φ 1) := by
  classical
  obtain ⟨L, H, hL, hdiffL, hEuler, hH, hclear, ⟨C, _, hcount⟩, _, _, hgood⟩ :=
    exists_completedHeckeEulerProduct_one_gaussianContinuation_horizontal_count v r hr
  obtain ⟨hpos, hzero⟩ := completedHecke_one_poleCleared_values v r hr hEuler hH hclear
  have h₁ : H 1 ≠ 0 := by
    intro h
    simp [h] at hpos
  have h₀ : H 0 ≠ 0 := hzero ▸ mul_ne_zero (exp_ne_zero _) h₁
  -- The Euler half-plane and the checked reflection exclude only the exterior.
  have hright (s : ℂ) (hs : 1 < s.re) : L s ≠ 0 := by
    rw [hEuler s hs]
    exact (completedHeckeEulerProduct_logDeriv χ₀ (fun _ ↦ norm_one) hs).1
  have hzeros (z : ℂ) (hz : H z = 0) :
      z ≠ 0 ∧ z ≠ 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ L z = 0 ∧
        analyticOrderNatAt H z = analyticOrderNatAt L z := by
    have hz₀ : z ≠ 0 := fun h ↦ h₀ (h ▸ hz)
    have hz₁ : z ≠ 1 := fun h ↦ h₁ (h ▸ hz)
    let q : ℂ → ℂ := fun s ↦ (s - 1) * s
    have hqz : q z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz₁) hz₀
    have hLz : L z = 0 := (mul_eq_zero.mp ((hclear z hz₀ hz₁).symm.trans hz)).resolve_left hqz
    have hl : 0 ≤ z.re := le_of_not_gt fun h ↦ by
      have hw : 1 < (1 - z).re := by simp only [sub_re, one_re]; linarith
      apply hright (1 - z) hw
      have href := completedHecke_one_reflection v r hr hEuler hH hclear z hz₀ hz₁
      simpa only [hLz, mul_zero] using href.eq_of_nhds
    refine ⟨hz₀, hz₁, hl, le_of_not_gt (fun h ↦ hright z h hLz), hLz, ?_⟩
    -- Pole clearing multiplies the ordinary germ by a nonvanishing analytic factor.
    have hq : AnalyticAt ℂ q z := by dsimp [q]; fun_prop
    have hLa : AnalyticAt ℂ L z := Complex.analyticAt_iff_eventually_differentiableAt.mpr (by
      filter_upwards [eventually_ne_nhds hz₀, eventually_ne_nhds hz₁] with s hs₀ hs₁
      exact hdiffL s hs₀ hs₁)
    have heq : H =ᶠ[𝓝 z] fun s ↦ q s * L s := by
      filter_upwards [eventually_ne_nhds hz₀, eventually_ne_nhds hz₁] with s hs₀ hs₁
      exact hclear s hs₀ hs₁
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr heq, analyticOrderAt_fun_mul hq hLa,
      hq.analyticOrderAt_eq_zero.mpr hqz, zero_add]
  refine ⟨L, H, hL, hdiffL, hEuler, hH, hclear, hzeros,
    fun z hz₀ hz₁ hz ↦ by rw [hclear z hz₀ hz₁, hz, mul_zero], ?_⟩
  -- This is the manuscript's rectangle limit, with both pole terms retained.
  obtain ⟨T, Z, hrect, hlim⟩ :=
    completedHecke_one_tendsto_zeroSum_at_good_heights v r hr hL hdiffL hEuler hH hclear hgood
  have hstrip (z : ℂ) (hz : H z = 0) : -1 < z.re ∧ z.re < 2 :=
    let h := hzeros z hz
    ⟨by linarith [h.2.2.1], by linarith [h.2.2.2.1]⟩
  have hT : Tendsto T atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ))
      (fun n ↦ by linarith [(hrect n).1]) tendsto_natCast_atTop_atTop
  -- Each zero eventually lies in all these rectangles; monotonicity is not needed.
  have hcofinal : Tendsto (fun n ↦ (Z n).subtype (fun z ↦ H z = 0)) atTop
      (atTop : Filter (Finset {z : ℂ // H z = 0})) := by
    simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
    intro z
    filter_upwards [hT.eventually (eventually_gt_atTop |z.val.im|)] with n hn
    exact Finset.singleton_subset_iff.mpr <| Finset.mem_subtype.mpr <|
      ((hrect n).2.2 z).mpr
        ⟨mem_reProdIm.mpr ⟨hstrip z z.property, abs_lt.mp hn⟩, z.property⟩
  intro g hg hc
  obtain ⟨hR, hV, hcutoff⟩ := hlim g hg hc
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hc 2 3
  -- The linear disk count and cubic vertical decay give an absolute zero sum.
  have habs := summable_norm_analyticOrder_mul_of_disk_count hH h₁ hstrip hB.le hcount
    (Φ := compactLogMellin g) (by
      intro z hz₁ hz₂
      have htest := hdecay z.re z.im (abs_le.mpr ⟨by linarith, hz₂⟩)
      rwa [Complex.re_add_im] at htest)
  refine ⟨hR, hV, habs, ?_⟩
  let W (z : ℂ) := (analyticOrderNatAt H z : ℂ) * compactLogMellin g z
  have hsum : Summable (fun z : {z : ℂ // H z = 0} ↦ W z.val) :=
    habs.of_norm_bounded (fun _ ↦ le_rfl)
  have htotal : Tendsto (fun S : Finset {z : ℂ // H z = 0} ↦ ∑ z ∈ S, W z.val)
      atTop (𝓝 (∑' z : {z : ℂ // H z = 0}, W z.val)) := hsum.hasSum
  have hrectSum := (htotal.comp hcofinal).congr fun n ↦
    Finset.sum_subtype_of_mem W (fun z hz ↦ (((hrect n).2.2 z).mp hz).2)
  have heq := tendsto_nhds_unique hrectSum hcutoff
  dsimp only at heq ⊢
  change _ = (∑' z : {z : ℂ // H z = 0}, W z.val) - _ - _
  rw [heq]
  ring

end Masullo
