module

public import Theorems.RationalThetaBandClosure
public import Lemmas.RationalThetaLogReflection

/-! # Reflection of the rational weighted theta space

The two zero modes in (2.2.3.2), p. 82, disappear on the theta source of
(11.2.1.7), pp. 488–489. At the half twist, inversion of the argument of
theta is therefore Fourier transformation of its source. The reflection
preserves the full symmetric-strip theta closure, but exchanges a
Fourier support constraint for a spatial one. This supplies an operator
symmetry *after* the position-fixed level limit of (11.2.1.9)–(10), not
a justification for applying the above-one orbital theorem (p. 495) to
below-one tests at the same finite Fourier level. Locators are from the
pinned text extraction.
-/

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace Masullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

private theorem schwartz_fourier_fourier_apply (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (𝓕 b)) x = b (-x) := by
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) ↦ f (-x))
    (FourierPair.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) b)
  change (𝓕⁻ (𝓕 b)) (-x) = b (-x) at h
  rwa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg,
    ← SchwartzMap.fourier_coe] at h

/-- On the two-mode input, Fourier transformation swaps the two zero modes. -/
public noncomputable def rationalThetaInputFourier (b : RationalThetaInput) : RationalThetaInput :=
  ⟨𝓕 b.val, b.property.2, by rw [schwartz_fourier_fourier_apply, neg_zero, b.property.1]⟩

/-- The half twist cancels the norm factor in the checked theta inversion.
Fourier transforms the source, and reflection transforms the log coordinate. -/
public theorem rationalThetaLogReflection_weightedLog {α s : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (b : RationalThetaInput) :
    rationalThetaLogReflection (rationalThetaWeightedLog (1 / 2) hs hα b) =
      rationalThetaWeightedLog (1 / 2) hs hα (rationalThetaInputFourier b) := by
  apply Lp.ext
  filter_upwards [rationalThetaLogReflection_ae (rationalThetaWeightedLog (1 / 2) hs hα b),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (memLp_rationalTheta_weighted b (1 / 2) α s hs hα).coeFn_toLp,
    (memLp_rationalTheta_weighted (rationalThetaInputFourier b) (1 / 2) α s hs hα).coeFn_toLp]
    with x hR hb hF
  rw [hR]
  unfold rationalThetaWeightedLog
  rw [hb, hF]
  -- Masullo’s inversion supplies both corrections, which vanish on this input.
  have hθ := rationalTheta_inversion b.val (Real.exp_pos (-x))
  rw [b.property.1, b.property.2, smul_zero, add_zero, sub_zero,
    Real.exp_neg, inv_inv, Complex.real_smul, ← Real.exp_neg] at hθ
  change _ * (_ * rationalTheta b.val (Real.exp (-x))) =
    _ * (_ * rationalTheta (𝓕 b.val) (Real.exp x))
  have hweight : symmetricStripWeightRoot α s (-x) = symmetricStripWeightRoot α s x := by
    simp only [symmetricStripWeightRoot_apply, abs_neg, neg_sq]
  have hexp : Complex.exp (↑(1 / 2 : ℝ) * ↑(-x)) * (Real.exp x : ℂ) =
      Complex.exp (↑(1 / 2 : ℝ) * ↑x) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hθ, hweight, ← mul_assoc (Complex.exp _), hexp]

/-- A Fourier support constraint reflects to a *spatial* support constraint on the
source; the same band projection does not enter this statement twice. -/
public theorem rationalThetaLogReflection_freq_image {α s : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (freq : Set ℝ) :
    rationalThetaLogReflection '' (rationalThetaWeightedEvenImage (1 / 2) hs hα freq : Set H) =
      closure (rationalThetaWeightedLog (1 / 2) hs hα ''
        {b : RationalThetaInput | Function.Even (⇑b.val) ∧ ∀ x ∉ freq, b.val x = 0}) := by
  rw [coe_rationalThetaWeightedEvenImage]
  change rationalThetaLogReflection.toHomeomorph '' closure _ = _
  rw [rationalThetaLogReflection.toHomeomorph.image_closure]
  congr 1
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨rationalThetaInputFourier b, ⟨fourier_preserves_realSchwartz_even hb.1, hb.2⟩,
      (rationalThetaLogReflection_weightedLog hs hα b).symm⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hFF : rationalThetaInputFourier (rationalThetaInputFourier b) = b := by
      apply Subtype.ext
      ext x
      exact (schwartz_fourier_fourier_apply b.val x).trans (hb.1 x)
    refine ⟨_, ⟨rationalThetaInputFourier b, ⟨fourier_preserves_realSchwartz_even hb.1, ?_⟩, rfl⟩, ?_⟩
    · intro x hx
      exact congrArg (fun c : RationalThetaInput ↦ c.val x) hFF |>.trans (hb.2 x hx)
    · exact (rationalThetaLogReflection_weightedLog hs hα _).trans
        (congrArg (rationalThetaWeightedLog (1 / 2) hs hα) hFF)

/-- The geometric orthogonal projection at the full rational even level
commutes with log reflection. -/
public theorem rationalThetaLogReflection_starProjection {α s : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (u : H) :
    let G := (rationalThetaWeightedEvenImage (1 / 2) hs hα univ).toSubmodule
    rationalThetaLogReflection (G.starProjection u) = G.starProjection (rationalThetaLogReflection u) := by
  dsimp only
  let G := (rationalThetaWeightedEvenImage (1 / 2) hs hα univ).toSubmodule
  let R := rationalThetaLogReflection
  have hmap : G.map R.toLinearEquiv.toLinearMap = G := by
    apply SetLike.coe_injective
    change R '' (rationalThetaWeightedEvenImage (1 / 2) hs hα univ : Set H) =
      (rationalThetaWeightedEvenImage (1 / 2) hs hα univ : Set H)
    rw [rationalThetaLogReflection_freq_image, coe_rationalThetaWeightedEvenImage]
    simp
  have h := R.toLinearIsometry.map_starProjection' G u
  change R (G.starProjection u) = (G.map R.toLinearEquiv.toLinearMap).starProjection (R u) at h
  simpa only [hmap] using h

end Masullo
