module

public import Props.SchwartzTwoMomentBand
public import Lemmas.RationalThetaWeightedLog

/-!
# Finite-band exhaustion of the weighted rational theta generators

For the rational unramified even model of (7.3.2.14), p. 355, and
(11.2.1.7)–(11.2.1.8), pp. 488–489, the finite additive Fourier bands
have dense theta images in the once-twisted weighted theta closure.
This gives the density input for increasing closed levels, not a bound
on the joint position and frequency cutoff or a local-to-global trace identity.
-/

open Filter Set
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

end Masullo
