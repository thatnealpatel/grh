module

public import Theorems.AdeleAdditiveDilation
public import Theorems.AdeleBoxPoisson
public import Lemmas.AdeleBoxDilation

/-! # Pointwise adelic theta inversion on the box span

Masullo's Theorem 2.2.3.2 and (2.2.3.2)–(3), PDF p. 82, invoke
adelic Riemann–Roch, with the counting-covolume normalization in
Remark 2.2.3.3. Here shifted ideal lattice Poisson and the integral
Fourier assembly give the full diagonal identity at the identity
idele (`adeleBoxSpan_diagonal_poisson`). Pullback in the box span and
Fourier covariance extend it to every idele. Absolute convergence on
both sides allows us to remove the two zero terms separately.

The stage comaps fix the measure; no extra self-duality or covolume
premise is used. `adeleIntegralClassMeasure_haar_probability` checks
the counting normalization separately for this same measure. The
integral uses the conjugated global trace character, with corrected
finite signs as in `AdeleTraceCharacter`, and not the as-printed
product of positive phases in Examples A.3.1.5–9, PDF pp. 557–558.
This is pointwise inversion on the algebraic box span, not continuity
on idele classes or inversion on the full Schwartz–Bruhat space.
Source reading: Provisional pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical ComplexConjugate Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "A" => AdeleRing (𝓞 K) K
local notation "J" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "ι" => algebraMap K A

/-- The actual Fourier integral of the pullback by multiplication by an idele.
The pushforward from the image law (A.3.1.4), PDF p. 556, supplies the
inverse norm. The same substitution gives inverse dilation in the conjugated
kernel from (2.2.4.32), PDF p. 92. -/
public theorem adeleFourier_dilate (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (h : J) (z : A) :
    adeleFourier μ (fun w ↦ f ((h : A) * w)) z =
      (ideleNorm h)⁻¹ • adeleFourier μ f ((↑(h⁻¹) : A) * z) := by
  let d := (ContinuousAddEquiv.mulLeft h).toHomeomorph
  let F : A → ℂ := fun w ↦ f w * conj (numberFieldAdeleAddChar (w * ((↑(h⁻¹) : A) * z)))
  have hpair (w : A) : ((h : A) * w) * ((↑(h⁻¹) : A) * z) = w * z := by
    rw [mul_comm (h : A) w, mul_assoc, ← mul_assoc (h : A), Units.mul_inv, one_mul]
  have hnorm : 0 < ideleNorm h := ideleClassNorm_mk h ▸ ideleClassNorm_pos (QuotientGroup.mk h)
  calc
    _ = ∫ w, F (d w) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        change f ((h : A) * w) * conj (numberFieldAdeleAddChar (w * z)) =
          f ((h : A) * w) * conj (numberFieldAdeleAddChar (((h : A) * w) * ((↑(h⁻¹) : A) * z)))
        rw [hpair]
    _ = ∫ w, F w ∂μ.map d := (d.measurableEmbedding.integral_map F).symm
    _ = (ideleNorm h)⁻¹ • adeleFourier μ f ((↑(h⁻¹) : A) * z) := by
      change (∫ w, F w ∂(μ.map (fun w : A ↦ (h : A) * w))) = _
      rw [map_adeleAddHaar_dilate, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hnorm.le)]
      rfl

omit [NumberField K] in
private theorem tsum_eq_zero_add_units (p : K → ℂ) (hp : Summable p) :
    (∑' t, p t) = p 0 + ∑' t : Kˣ, p (t : K) := by
  let S : Set K := (↑({0} : Finset K) : Set K)ᶜ
  let e : Kˣ ≃ S := unitsEquivNeZero.trans (Equiv.subtypeEquivRight (fun t ↦ by simp [S]))
  calc
    (∑' t, p t) = p 0 + ∑' t : S, p t := by
      simpa only [Finset.sum_singleton] using (hp.sum_add_tsum_compl (s := ({0} : Finset K))).symm
    _ = _ := congrArg (p 0 + ·) (e.tsum_eq (fun t : S ↦ p t)).symm

/-- At every actual idele, both full diagonal series converge absolutely.
On the nonzero diagonal, Poisson summation gives (2.2.3.2) with the
scaled Fourier value at zero minus the original value at zero. -/
public theorem adeleBoxSpan_theta_inversion (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (h : J) :
    Summable (fun t : K ↦ ‖f ((h : A) * ι t)‖) ∧
      Summable (fun t : K ↦ ‖adeleFourier μ f ((↑(h⁻¹) : A) * ι t)‖) ∧
      (∑' t : Kˣ, f ((h : A) * ι (t : K))) =
        (ideleNorm h)⁻¹ • (∑' t : Kˣ, adeleFourier μ f ((↑(h⁻¹) : A) * ι (t : K))) +
        (ideleNorm h)⁻¹ • adeleFourier μ f 0 - f 0 := by
  let p : K → ℂ := fun t ↦ f ((h : A) * ι t)
  let q : K → ℂ := fun t ↦ adeleFourier μ f ((↑(h⁻¹) : A) * ι t)
  let c : ℝ := (ideleNorm h)⁻¹
  -- Use the full identity at the identity idele on the pullback of f.
  obtain ⟨hp, hq, hP⟩ := adeleBoxSpan_diagonal_poisson μ E hμ (adeleBoxSpan_dilate hf h)
  change Summable (fun t ↦ ‖p t‖) at hp
  -- Covariance converts the Fourier samples; the positive norm can be cancelled.
  have hq' : Summable (fun t ↦ ‖c‖ * ‖q t‖) := by
    simpa only [adeleFourier_dilate, norm_smul, q, c] using hq
  have hc : c ≠ 0 := inv_ne_zero
    (ideleClassNorm_mk h ▸ ideleClassNorm_pos (QuotientGroup.mk h)).ne'
  have hq₀ : Summable (fun t ↦ ‖q t‖) :=
    (summable_mul_left_iff (norm_ne_zero_iff.mpr hc)).mp hq'
  have hfull : (∑' t, p t) = c • (∑' t, q t) := by
    calc
      (∑' t, p t) = ∑' t, c • q t := by simpa only [adeleFourier_dilate, p, q, c] using hP
      _ = c • (∑' t, q t) := hq₀.of_norm.tsum_const_smul c
  refine ⟨hp, hq₀, ?_⟩
  -- Separate the actual zero term before indexing the remainder by Kˣ.
  rw [tsum_eq_zero_add_units p hp.of_norm, tsum_eq_zero_add_units q hq₀.of_norm, smul_add] at hfull
  have hp₀ : p 0 = f 0 := by simp only [p, map_zero, mul_zero]
  have hq₁ : q 0 = adeleFourier μ f 0 := by simp only [q, map_zero, mul_zero]
  change (∑' t : Kˣ, p (t : K)) = c • (∑' t : Kˣ, q (t : K)) + c • adeleFourier μ f 0 - f 0
  rw [eq_sub_iff_add_eq, add_comm _ (f 0)]
  simpa only [hp₀, hq₁, add_comm (c • adeleFourier μ f 0)] using hfull

end Masullo
