module

public import Props.SchwartzTwoMomentBand
public import Lemmas.RationalThetaWeightedLog
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-band exhaustion of the weighted rational theta generators

For the rational unramified even model of (7.3.2.14), p. 355, and
(11.2.1.7)–(11.2.1.8), pp. 488–489, the finite additive Fourier bands
have dense theta images in the once-twisted weighted theta closure.
This gives the density input for increasing closed levels, not a bound
on the joint position and frequency cutoff or a local-to-global trace identity.
-/

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace Masullo

/-- On the two-mode kernel, theta summation with one twist is continuous
from the Schwartz topology to the weighted log-line Hilbert norm. -/
public theorem continuous_rationalThetaWeightedLog (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) : Continuous (rationalThetaWeightedLog a hs hα) :=
  rationalThetaWeightedLog_continuous_of_tail_bounds a hs hα

/-- Requiring some finite additive Fourier band on each real generator
leaves the weighted closure of the even rational theta profiles unchanged. -/
public theorem rationalThetaWeightedLog_band_closure (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) :
    closure (rationalThetaWeightedLog a hs hα ''
      {b : RationalThetaInput | Function.Even (⇑b.val) ∧
        ∃ B : ℝ, 0 < B ∧ ∀ ξ : ℝ, B < |ξ| → (𝓕 b.val) ξ = 0}) =
    closure (rationalThetaWeightedLog a hs hα ''
      {b : RationalThetaInput | Function.Even (⇑b.val)}) := by
  apply Subset.antisymm
  · exact closure_mono (image_mono fun _ hb ↦ hb.1)
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨b, he, rfl⟩
    obtain ⟨u, hu, h⟩ := exists_tendsto_fourierBand_twoMoments b.val he b.property.1 b.property.2
    let v (n : ℕ) : RationalThetaInput := ⟨u n, (h n).2.1, (h n).2.2.1⟩
    have hv : Tendsto v atTop (𝓝 b) := tendsto_subtype_rng.mpr hu
    exact mem_closure_of_tendsto ((continuous_rationalThetaWeightedLog a hs hα).tendsto b |>.comp hv)
      (.of_forall fun n ↦ ⟨v n, ⟨(h n).1, (h n).2.2.2⟩, rfl⟩)

/-- Rational real-lattice analogue of the strong limit in Theorem 11.2.1.4(1),
also for the positive-width Hardy–Sobolev norm. The target is the projection
onto the full weighted even theta closure, not a claimed ambient identity. -/
public theorem tendsto_rationalThetaWeightedEvenBand_projection
    (a : ℝ) {α s : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    {B : ℕ → ℝ} (hB : Monotone B) (hcofinal : ∀ R : ℝ, ∃ n, R ≤ B n)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n ↦
      (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ B n}).toSubmodule.starProjection x)
      atTop (𝓝 ((rationalThetaWeightedEvenImage a hs hα univ).toSubmodule.starProjection x)) := by
  let V (n : ℕ) := rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ B n}
  let G := rationalThetaWeightedEvenImage a hs hα univ
  let U (n : ℕ) := (V n).toSubmodule
  have hU : Monotone U := by
    intro m n hmn
    change (V m : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆ (V n : Set _)
    dsimp only [V]
    simp only [coe_rationalThetaWeightedEvenImage]
    exact closure_mono (image_mono fun b hb ↦ ⟨hb.1, fun ξ hξ ↦
      hb.2 ξ (fun h ↦ hξ ((show |ξ| ≤ B m from h).trans (hB hmn)))⟩)
  have hV (n : ℕ) : U n ≤ G.toSubmodule := by
    change (V n : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆ (G : Set _)
    dsimp only [V, G]
    simp only [coe_rationalThetaWeightedEvenImage, mem_univ, not_true_eq_false,
      false_implies, implies_true, and_true]
    exact closure_mono (image_mono fun _ hb ↦ hb.1)
  have hG : (⨆ n, U n).topologicalClosure = G.toSubmodule := by
    apply le_antisymm
    · exact (⨆ n, U n).topologicalClosure_minimal (iSup_le hV) G.isClosed
    · change (G : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆
        closure ((⨆ n, U n : Submodule ℂ _) : Set (Lp ℂ 2 (volume : Measure ℝ)))
      dsimp only [G]
      simp only [coe_rationalThetaWeightedEvenImage, mem_univ, not_true_eq_false,
        false_implies, implies_true, and_true]
      rw [← rationalThetaWeightedLog_band_closure a hs hα]
      apply closure_mono
      rintro _ ⟨b, ⟨he, R, _, hR⟩, rfl⟩
      obtain ⟨n, hn⟩ := hcofinal R
      apply le_iSup U n
      change rationalThetaWeightedLog a hs hα b ∈ (V n : Set (Lp ℂ 2 (volume : Measure ℝ)))
      dsimp only [V]
      rw [coe_rationalThetaWeightedEvenImage]
      exact subset_closure ⟨b, ⟨he, fun ξ hξ ↦ hR ξ (hn.trans_lt (lt_of_not_ge hξ))⟩, rfl⟩
  let (n : ℕ) : (U n).HasOrthogonalProjection :=
    inferInstanceAs (V n).toSubmodule.HasOrthogonalProjection
  let : (⨆ n, U n).topologicalClosure.HasOrthogonalProjection := by
    rw [hG]
    infer_instance
  simpa only [hG, U, V, G] using Submodule.starProjection_tendsto_closure_iSup U hU x

end Masullo
