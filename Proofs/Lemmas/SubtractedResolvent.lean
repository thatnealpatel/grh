module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Detecting the noncentral weights of a subtracted resolvent

This is a project lemma for the uniqueness argument on the test class in
Masullo's (13.3.1.2), p. 522. It continues a local identity off the poles and
recovers a coefficient by a continuous punctured limit. It does not assert
agreement of the capped and full distributions.
-/

open Filter Set
open scoped Topology

namespace Masullo

/-- A resolvent term subtracted at the common anchor `z₀`. -/
@[expose] public noncomputable def subtractedResolventTerm {ι : Type*} (w d : ι → ℂ)
    (z₀ z : ℂ) (i : ι) : ℂ :=
  d i * (z₀ - z) / ((z - w i) * (z₀ - w i))

/-- Normal convergence and pointwise summability where the active poles have a gap. -/
private theorem analyticAt_subtractedResolvent {ι : Type*} {w d : ι → ℂ} {z₀ z : ℂ}
    (hs : Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖) ^ 2))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, d i ≠ 0 → δ ≤ ‖z - w i‖ ∧ δ ≤ ‖z₀ - w i‖) :
    AnalyticAt ℂ (fun x ↦ ∑' i, subtractedResolventTerm w d z₀ x i) z ∧
      Summable (subtractedResolventTerm w d z₀ z) := by
  let R : ℝ := ‖z‖ + ‖z₀‖ + δ + 1
  let K : ℝ := 1 + (1 + R) / (δ / 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hz₀ : ‖z₀‖ ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have grow (x v : ℂ) (hx : ‖x‖ ≤ R) (h : δ / 2 ≤ ‖x - v‖) :
      1 + ‖v‖ ≤ K * ‖x - v‖ := by
    have htri : ‖v‖ ≤ ‖x‖ + ‖x - v‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le x (x - v)
    have ha : 1 ≤ ‖x - v‖ / (δ / 2) :=
      (le_div_iff₀ (by positivity)).2 (by simpa using h)
    calc
      1 + ‖v‖ ≤ (1 + R) + ‖x - v‖ := by linarith
      _ ≤ (1 + R) * (‖x - v‖ / (δ / 2)) + ‖x - v‖ := by
        linarith [mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 1 + R)]
      _ = K * ‖x - v‖ := by dsimp [K]; ring
  have bounds {x : ℂ} (hx : x ∈ Metric.ball z (δ / 2)) :
      ‖x‖ ≤ R ∧ ∀ i, d i ≠ 0 → δ / 2 ≤ ‖x - w i‖ ∧ δ / 2 ≤ ‖z₀ - w i‖ := by
    have hx' : ‖x - z‖ < δ / 2 := (mem_ball_iff_norm.1 hx)
    refine ⟨?_, fun i hi ↦ ⟨?_, by linarith [(hgap i hi).2]⟩⟩
    · have ht := norm_add_le (x - z) z
      rw [sub_add_cancel] at ht
      dsimp [R]
      linarith [norm_nonneg z₀]
    · have ht := norm_sub_le (x - w i) (x - z)
      have he : (x - w i) - (x - z) = z - w i := by abel
      rw [he] at ht
      linarith [(hgap i hi).1]
  -- On this ball each active denominator grows at least linearly in the pole norm.
  let u : ι → ℝ := fun i ↦ (2 * R * K ^ 2) * (‖d i‖ / (1 + ‖w i‖) ^ 2)
  have hu : Summable u := hs.mul_left _
  have hle (i : ι) (x : ℂ) (hx : x ∈ Metric.ball z (δ / 2)) :
      ‖subtractedResolventTerm w d z₀ x i‖ ≤ u i := by
    by_cases hi : d i = 0
    · simp [subtractedResolventTerm, u, hi]
    obtain ⟨hxR, hg⟩ := bounds hx
    obtain ⟨h1, h2⟩ := hg i hi
    have hp₁ : 0 < ‖x - w i‖ := by linarith
    have hp₂ : 0 < ‖z₀ - w i‖ := by linarith
    have hnum : ‖z₀ - x‖ ≤ 2 * R := by linarith [norm_sub_le z₀ x]
    have hden : (1 + ‖w i‖) ^ 2 ≤ (K * ‖x - w i‖) * (K * ‖z₀ - w i‖) := by
      rw [pow_two]
      exact mul_le_mul (grow _ _ hxR h1) (grow _ _ hz₀ h2) (by positivity) (by positivity)
    calc
      ‖subtractedResolventTerm w d z₀ x i‖ =
          (‖d i‖ * ‖z₀ - x‖) / (‖x - w i‖ * ‖z₀ - w i‖) := by
        simp only [subtractedResolventTerm, norm_div, norm_mul]
      _ ≤ (‖d i‖ * (2 * R)) / (‖x - w i‖ * ‖z₀ - w i‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (norm_nonneg _))
          (by positivity)
      _ = (2 * R * K ^ 2) * (‖d i‖ / ((K * ‖x - w i‖) * (K * ‖z₀ - w i‖))) := by
        field_simp [hK.ne', hp₁.ne', hp₂.ne']
      _ ≤ u i := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden) (by positivity)
  have hd (i : ι) : DifferentiableOn ℂ (fun x ↦ subtractedResolventTerm w d z₀ x i)
      (Metric.ball z (δ / 2)) := by
    intro x hx
    by_cases hi : d i = 0
    · simpa only [subtractedResolventTerm, hi, zero_mul, zero_div] using
        (differentiableWithinAt_const (c := (0 : ℂ)))
    obtain ⟨h1, h2⟩ := (bounds hx).2 i hi
    have hn₁ : x - w i ≠ 0 := norm_pos_iff.mp (by linarith)
    have hn₂ : z₀ - w i ≠ 0 := norm_pos_iff.mp (by linarith)
    have hnum : DifferentiableAt ℂ (fun x ↦ d i * (z₀ - x)) x := by fun_prop
    have hden : DifferentiableAt ℂ (fun x ↦ (x - w i) * (z₀ - w i)) x := by fun_prop
    exact (hnum.fun_div hden (mul_ne_zero hn₁ hn₂)).differentiableWithinAt
  have hz : z ∈ Metric.ball z (δ / 2) := Metric.mem_ball_self (by positivity)
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hu hd Metric.isOpen_ball hle
  exact ⟨hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hz),
    hu.of_norm_bounded (fun i ↦ hle i z hz)⟩

/-- Agreement with a function analytic off zero forces every noncentral weight to vanish. -/
public theorem subtractedResolvent_weight_eq_zero {ι : Type*} [Countable ι]
    (w d : ι → ℂ) (hw : Function.Injective w) (z₀ : ℂ)
    (hsep : ∀ z : ℂ, ∃ δ : ℝ, 0 < δ ∧ ∀ i, w i ≠ z → δ ≤ ‖z - w i‖)
    (ha : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ‖z₀ - w i‖)
    (hs : Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖) ^ 2))
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G ({0} : Set ℂ)ᶜ)
    (hagree : ∃ z ∈ (range w ∪ {0})ᶜ,
      (fun x ↦ ∑' i, subtractedResolventTerm w d z₀ x i) =ᶠ[𝓝 z] G)
    (i : ι) (hi : w i ≠ 0) : d i = 0 := by
  classical
  let U : Set ℂ := (range w ∪ {0})ᶜ
  let F : ℂ → ℂ := fun x ↦ ∑' j, subtractedResolventTerm w d z₀ x j
  have hcount : (range w ∪ ({0} : Set ℂ)).Countable :=
    (countable_range w).union (countable_singleton 0)
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  obtain ⟨e, he, hanchor⟩ := ha
  have havoid {x : ℂ} (hx : x ∈ U) (j : ι) : w j ≠ x :=
    fun h ↦ hx (Or.inl ⟨j, h⟩)
  have hreg {x : ℂ} (hx : x ∈ U) : AnalyticAt ℂ F x ∧
      Summable (subtractedResolventTerm w d z₀ x) := by
    obtain ⟨δ, hδ, hgap⟩ := hsep x
    exact analyticAt_subtractedResolvent hs (lt_min hδ he)
      (fun j _ ↦ ⟨(min_le_left _ _).trans (hgap j (havoid hx j)),
        (min_le_right _ _).trans (hanchor j)⟩)
  -- Continue the identity on the connected complement of all the excluded points.
  obtain ⟨z, hz, heq⟩ := hagree
  have hall : EqOn F G U := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun _ hx ↦ (hreg hx).1) (fun x hx ↦ hG x (fun hx₀ ↦ hx (Or.inr hx₀)))
    (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected hz heq
  -- Drop the i-th summand to make the remainder analytic across its pole.
  let d' : ι → ℂ := fun j ↦ if j = i then 0 else d j
  let H : ℂ → ℂ := fun x ↦ ∑' j, subtractedResolventTerm w d' z₀ x j
  have hs' : Summable (fun j ↦ ‖d' j‖ / (1 + ‖w j‖) ^ 2) := by
    apply hs.of_nonneg_of_le (fun j ↦ by positivity)
    intro j
    by_cases hj : j = i
    · simp only [d', hj, ite_true, norm_zero, zero_div]; positivity
    · simp [d', hj]
  obtain ⟨δ, hδ, hgap⟩ := hsep (w i)
  have hH : AnalyticAt ℂ H (w i) := (analyticAt_subtractedResolvent hs' (lt_min hδ he)
    (fun j hj ↦ by
      have hji : j ≠ i := by intro h; simp [d', h] at hj
      exact ⟨(min_le_left _ _).trans (hgap j (hw.ne hji)),
        (min_le_right _ _).trans (hanchor j)⟩)).1
  have hsplit {x : ℂ} (hx : x ∈ U) : F x = subtractedResolventTerm w d z₀ x i + H x := by
    refine ((hreg hx).2.tsum_eq_add_tsum_ite i).trans ?_
    congr 1
    apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [d', h, subtractedResolventTerm]
  have hz₀i : z₀ - w i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le he (hanchor i))
  have hG' : ContinuousAt G (w i) := (hG _ (by simpa using hi)).continuousAt
  -- After multiplication by x - w i, both sides extend continuously to w i.
  let L : ℂ → ℂ := fun x ↦ (x - w i) * G x
  let M : ℂ → ℂ := fun x ↦ d i * (z₀ - x) / (z₀ - w i) + (x - w i) * H x
  have hL : ContinuousAt L (w i) := (continuousAt_id.sub continuousAt_const).mul hG'
  have hM : ContinuousAt M (w i) :=
    ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      continuousAt_const hz₀i).add ((continuousAt_id.sub continuousAt_const).mul hH.continuousAt)
  have : NeBot (𝓝[U] (w i)) := mem_closure_iff_nhdsWithin_neBot.mp
    ((hcount.dense_compl ℝ) (w i))
  have hLM : L =ᶠ[𝓝[U] (w i)] M := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxi : x - w i ≠ 0 := sub_ne_zero.mpr (havoid hx i).symm
    change (x - w i) * G x = _
    rw [← hall hx, hsplit hx]
    dsimp [M, subtractedResolventTerm]
    field_simp [hxi, hz₀i]
  have hlim : L (w i) = M (w i) := tendsto_nhds_unique_of_eventuallyEq
    hL.continuousWithinAt hM.continuousWithinAt hLM
  simpa [L, M, hz₀i, mul_div_cancel_right₀] using hlim.symm

end Masullo
