# Subtracted resolvents determine the noncentral weights

**Status: Lean draft, not elaborated.** This is the residue step of the [Chapter 13 uniqueness repair](trace-divisor-uniqueness.md#a-one-sided-moment-uniqueness-lemma), not an argument supplied in the manuscript. The provisional source interface is the zero-moment condition (13.3.1.2) and capped sum (13.3.1.3), p. 522 of the [pinned edition](../sources/masullo/README.md). The proposed lemma starts *after* the cutoff transform has supplied agreement on a neighborhood. It does not assume a capped trace, supply the cutoff transform, or assume the residue as a premise.

## Interface

Use an injective countable family $w_i$, with the separation property that at each $z$ some positive distance separates $z$ from all $w_i\ne z$. This packages the no-finite-accumulation hypothesis without choosing an enumeration or a distinguished center. The anchor $z_0$ must be uniformly separated from the family; in the application use $\Re z_0>a$ and the bound on the real parts. Summability with denominator $1+|w_i|^2$ implies the slightly weaker weight used below, since $1+t^2\le (1+t)^2$ for $t\ge0$.

The subtracted term uses the single fraction $d_i(z_0-z)/((z-w_i)(z_0-w_i))$. Rewrite the difference of reciprocals **term by term away from the poles** before applying the lemma. The two separate series of reciprocals need not converge. Take $G(z)=C(z^{-1}-z_0^{-1})$ for the rational zero-integral test class; any $G$ analytic off zero works here. The neighborhood agreement is supplied by an identity on $\Re z>a$ and does not need to be assumed outside that half-plane.

## Candidate

The local lemma also applies after setting a single coefficient to zero. This lets the proof work with the same index type throughout. At $w_i\ne0$ multiply the punctured identity by $z-w_i$ and extend continuously, avoiding a Laurent-series API and never evaluating the original identity at its pole.

```lean
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

open Filter Set
open scoped Topology

namespace Masullo

/-- A resolvent term subtracted at the common anchor `z₀`. -/
noncomputable def subtractedResolventTerm {ι : Type*} (w d : ι → ℂ)
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
        field_simp [hK.ne', hp₁.ne', hp₂.ne'] <;> ring
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
    exact (((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).div
      ((differentiableAt_id.sub (differentiableAt_const _)).mul (differentiableAt_const _))
      (mul_ne_zero hn₁ hn₂)).differentiableWithinAt
  have hz : z ∈ Metric.ball z (δ / 2) := Metric.mem_ball_self (by positivity)
  exact ⟨(Complex.differentiableOn_tsum_of_summable_norm hu hd Metric.isOpen_ball hle)
    .analyticAt (Metric.isOpen_ball.mem_nhds hz), hu.of_norm_bounded (fun i ↦ hle i z hz)⟩

/-- Agreement with a function analytic off zero forces every noncentral weight to vanish. -/
theorem subtractedResolvent_weight_eq_zero {ι : Type*} [Countable ι]
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
  obtain ⟨z, hz, heq⟩ := hagree
  have hall : EqOn F G U := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun _ hx ↦ (hreg hx).1) (fun x hx ↦ hG x (fun hx₀ ↦ hx (Or.inr hx₀)))
    (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected hz heq
  let d' : ι → ℂ := fun j ↦ if j = i then 0 else d j
  let H : ℂ → ℂ := fun x ↦ ∑' j, subtractedResolventTerm w d' z₀ x j
  have hs' : Summable (fun j ↦ ‖d' j‖ / (1 + ‖w j‖) ^ 2) := by
    apply hs.of_nonneg_of_le (fun j ↦ by positivity)
    intro j
    by_cases hj : j = i
    · simp only [d', hj, if_true, norm_zero, zero_div]; positivity
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
  let L : ℂ → ℂ := fun x ↦ (x - w i) * G x
  let M : ℂ → ℂ := fun x ↦ d i * (z₀ - x) / (z₀ - w i) + (x - w i) * H x
  have hL : ContinuousAt L (w i) := (continuousAt_id.sub continuousAt_const).mul hG'
  have hM : ContinuousAt M (w i) :=
    ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      continuousAt_const hz₀i).add ((continuousAt_id.sub continuousAt_const).mul hH.continuousAt)
  haveI : NeBot (𝓝[U] (w i)) := mem_closure_iff_nhdsWithin_neBot.mp
    ((hcount.dense_compl ℝ) (w i))
  have hLM : L =ᶠ[𝓝[U] (w i)] M := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxi : x - w i ≠ 0 := sub_ne_zero.mpr (havoid hx i).symm
    change (x - w i) * G x = _
    rw [← hall hx, hsplit hx]
    dsimp [M, subtractedResolventTerm]
    field_simp [hxi, hz₀i] <;> ring
  have hlim : L (w i) = M (w i) := tendsto_nhds_unique_of_eventuallyEq
    hL.continuousWithinAt hM.continuousWithinAt hLM
  simpa [L, M, hz₀i, mul_div_cancel_right₀] using hlim.symm

end Masullo
```

## Source-level check plan

At Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, normal convergence uses `Complex.differentiableOn_tsum_of_summable_norm` (`Analysis/Complex/LocallyUniformLimit.lean`) and `DifferentiableOn.analyticAt` (`Analysis/Complex/CauchyIntegral.lean`). Propagate the local equality with `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (`Analysis/Analytic/Uniqueness.lean`) on the complement of a countable set, connected by `Set.Countable.isConnected_compl_of_one_lt_rank` (`Analysis/Normed/Module/Connected.lean`). The local sum split is `Summable.tsum_eq_add_tsum_ite` (`Topology/Algebra/InfiniteSum/Group.lean`), not a rearrangement of conditionally convergent reciprocal sums. The final continuous limits are on the nontrivial filter $\mathcal N[U](w_i)$ (`mem_closure_iff_nhdsWithin_neBot`); equality on $U$ is not asserted to hold at $w_i$.

Elaborate `Masullo.subtractedResolvent_weight_eq_zero` locally using the [exact-revision check](../../cmd/godel/README.md#checking-a-proof-candidate). The [checked cutoff series endpoint](trace-divisor-cutoff.md#lean-endpoint-and-next-check) now supplies the half-plane input for a later assembly. The exact algebraic and continuity tactic steps in the candidate above remain untested by Lean.
