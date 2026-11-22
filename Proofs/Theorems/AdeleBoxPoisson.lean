module

public import Lemmas.AdeleBoxDilation
public import Lemmas.AdeleBoxPoisson

import Theorems.FiniteBoxPoisson

/-! # Diagonal Poisson summation on the adelic box span

At the identity idele, Masullo's Theorem 2.2.3.2 (PDF p. 82) is a full
counting-series identity after restoring both zero terms. Masullo invokes an
adelic theorem there. Here `finiteBox_diagonal_poisson` supplies the shifted
lattice identity for each generator, and `adeleBox_fourier_integral` supplies
the actual Fourier integral with the corrected finite phases and cofinal
stage normalization (compare (2.2.4.32), p. 92). We then extend by finite
linearity (compare the rational tensor description in Example 2.1.3.1,
pp. 67–68). This step is on the box span and at the identity idele, not a
continuity assertion on the idele classes or an identification of the full
Schwartz–Bruhat space. Source readings: provisional pinned Markdown and
numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical ComplexConjugate Masullo.AdeleStage SchwartzMap

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "ι" => algebraMap K A

/-- Both full diagonal series converge absolutely and are equal for every
finite complex linear combination of translated box tensors. -/
public theorem adeleBoxSpan_diagonal_poisson (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) :
    Summable (fun t : K ↦ ‖f (ι t)‖) ∧
      Summable (fun t : K ↦ ‖adeleFourier μ f (ι t)‖) ∧
      (∑' t : K, f (ι t)) = ∑' t : K, adeleFourier μ f (ι t) := by
  let kernel (b : A → ℂ) (y : K) (w : A) := b w * conj (numberFieldAdeleAddChar (w * ι y))
  -- Keep integrability in the induction so that Fourier addition uses an ordinary integral.
  let P (b : A → ℂ) := (∀ y, Integrable (kernel b y) μ) ∧
    Summable (fun t : K ↦ ‖b (ι t)‖) ∧
    Summable (fun t : K ↦ ‖adeleFourier μ b (ι t)‖) ∧
    (∑' t : K, b (ι t)) = ∑' t : K, adeleFourier μ b (ι t)
  suffices P f from this.2
  change f ∈ Submodule.span ℂ {b | ∃ (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ),
    adeleBoxTensor φ a g = b} at hf
  refine Submodule.span_induction (p := fun b _ ↦ P b) ?_ ?_ ?_ ?_ hf
  · intro b hb
    obtain ⟨φ, a, g, rfl⟩ := hb
    have hbox := adeleBox_fourier_integral μ E hμ φ a g
    have hFourier (y : K) : adeleFourier μ (adeleBoxTensor φ a g) (ι y) =
        archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y) *
          ∏ᶠ v, finiteBoxLocalFourier a g y v := (hbox y).2
    refine ⟨fun y ↦ (hbox y).1, ?_⟩
    -- The tensor samples and the actual global integral are the two series of the lattice proof.
    simp_rw [adeleBoxTensor_diagonal_eq_indicator, hFourier]
    exact finiteBox_diagonal_poisson a g φ
  · simp [P, kernel, adeleFourier]
  · intro b c hb hc ihb ihc
    obtain ⟨hbi, hbx, hby, hbp⟩ := ihb
    obtain ⟨hci, hcx, hcy, hcp⟩ := ihc
    have hFourier (y : K) : adeleFourier μ (b + c) (ι y) =
        adeleFourier μ b (ι y) + adeleFourier μ c (ι y) := by
      simp only [adeleFourier, Pi.add_apply, add_mul]
      exact integral_add (hbi y) (hci y)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      simpa only [kernel, Pi.add_apply, add_mul] using (hbi y).fun_add (hci y)
    · exact (hbx.add hcx).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_add_le _ _)
    · simp_rw [hFourier]
      exact (hby.add hcy).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_add_le _ _)
    · simp only [Pi.add_apply, hFourier]
      rw [hbx.of_norm.tsum_add hcx.of_norm, hby.of_norm.tsum_add hcy.of_norm, hbp, hcp]
  · intro d b hb ihb
    obtain ⟨hbi, hbx, hby, hbp⟩ := ihb
    have hFourier (y : K) : adeleFourier μ (d • b) (ι y) = d * adeleFourier μ b (ι y) := by
      simp only [adeleFourier, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      simpa only [kernel, Pi.smul_apply, smul_eq_mul, mul_assoc] using (hbi y).const_mul d
    · simpa only [Pi.smul_apply, smul_eq_mul, norm_mul] using hbx.mul_left ‖d‖
    · simpa only [hFourier, norm_mul] using hby.mul_left ‖d‖
    · simp only [Pi.smul_apply, smul_eq_mul, hFourier, tsum_mul_left, hbp]

end Masullo
