module

public import Lemmas.ArchimedeanCompletionHaar
public import Theorems.CompletedHeckeEulerProduct
public import Theorems.RealGaussianMellin
public import Theorems.ComplexGaussianMellin

/-! # Archimedean Gaussian zeta integrals on the completion units

Equation (3.3.1.7), p. 130, pairs the test bilinearly with the character
on `F_vˣ`, against the multiplicative Tamagawa measure. The real tests
are those of (3.4.3.3)–(4), p. 152, on both signs. The provisional
text-based reading of (3.4.3.5)–(6), p. 152, gives the complex test the
same angular weight as the character, which cancels the integral at
weight one. We use the opposite-weight test from `complexZetaGaussian`
in the character's own coordinate. `complexGaussianZetaDensity_integral`
then supplies the nonzero Gamma value required by (3.4.3.12)–(13), p. 153.
-/

open Complex MeasureTheory NumberField InfinitePlace.Completion
open scoped ENNReal

namespace Masullo

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ]
variable [NumberField K]
variable (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)

public theorem realCompletionGaussianPair (hv : v.IsReal) :
    ∃ b : ℕ, b ≤ 1 ∧ ∀ s : ℂ, 0 < s.re →
      let F := fun u : v.Completionˣ ↦
        realZetaGaussian b (extensionEmbeddingOfIsReal hv u.val) *
          χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) *
          (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s)
      Integrable F (realCompletionHaar hv) ∧
        (∫ u, F u ∂realCompletionHaar hv) = localHeckeGammaFactor χ hχ v s := by
  -- Identify the parity and radial frequency of the actual restriction.
  obtain ⟨b, τ, hb, hchar, hGamma⟩ := localHeckeGammaFactor_real χ hχ hv
  refine ⟨b, hb, fun s hs ↦ ?_⟩
  let f (y : ℝ) : ℂ := realZetaGaussian b y * (if 0 < y then (1 : ℂ) else -1) ^ b *
    ((|y| : ℝ) : ℂ) ^ (s + (τ : ℂ) * I)
  -- Use the scalar Gamma evaluation and then the pushforward of multiplicative Haar.
  obtain ⟨hi, heq⟩ := realGaussianZetaDensity_integral b (by omega) τ hs
  obtain ⟨hi', heq'⟩ := pullback_integral (realCompletionEmbedding hv)
    (d := fun y : ℝ ↦ |y|⁻¹) (f := f) (g := realGaussianZetaDensity b τ s)
    (by fun_prop) (fun y ↦ inv_nonneg.mpr (abs_nonneg y)) (realCompletionHaar_map hv) (fun _ ↦ rfl) hi
  -- The character’s radial exponent adds to the complex Mellin parameter.
  have h (u : v.Completionˣ) :
      realZetaGaussian b (extensionEmbeddingOfIsReal hv u.val) *
          χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) * (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s) =
        f (extensionEmbeddingOfIsReal hv u.val) := by
    let y := extensionEmbeddingOfIsReal hv u.val
    have hr : 0 < |y| := abs_pos.mpr ((map_ne_zero (extensionEmbeddingOfIsReal hv)).mpr u.ne_zero)
    have hn : |y| = ‖u.val‖ :=
      (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _
    rw [hv.mult_eq_one, pow_one, ← hn, hchar u]
    change _ * (_ * exp _) * _ = _
    rw [← mul_assoc, mul_assoc (_ * _), positive_cpow_add_radial hr]
  dsimp only
  simp_rw [h]
  exact ⟨hi', heq'.trans (heq.trans (congrFun hGamma s).symm)⟩

public theorem complexCompletionGaussianPair (hv : v.IsComplex) :
    ∃ n : ℤ, ∀ s : ℂ, 0 < s.re →
      let F := fun u : v.Completionˣ ↦
        complexZetaGaussian n (extensionEmbedding v u.val) *
          χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) *
          (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s)
      Integrable F (complexCompletionHaar hv) ∧
        (∫ u, F u ∂complexCompletionHaar hv) = localHeckeGammaFactor χ hχ v s := by
  -- Identify the weight and log-squared-norm frequency in the same coordinate as the test.
  obtain ⟨n, τ, hchar, hGamma⟩ := localHeckeGammaFactor_complex χ hχ hv
  refine ⟨n, fun s hs ↦ ?_⟩
  let f (z : ℂ) : ℂ := complexZetaGaussian n z * (z / (‖z‖ : ℂ)) ^ n *
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (s + (τ : ℂ) * I)
  -- Use the scalar Gamma evaluation and then the pushforward of multiplicative Haar.
  obtain ⟨hi, heq⟩ := complexGaussianZetaDensity_integral n τ hs
  obtain ⟨hi', heq'⟩ := pullback_integral (complexCompletionEmbedding hv)
    (d := fun z : ℂ ↦ 2 / ‖z‖ ^ 2) (f := f) (g := complexGaussianZetaDensity n τ s)
    (by fun_prop) (fun z ↦ div_nonneg (by norm_num) (sq_nonneg ‖z‖)) (complexCompletionHaar_map hv) (fun _ ↦ rfl) hi
  -- The character’s radial exponent adds to the complex Mellin parameter.
  have h (u : v.Completionˣ) :
      complexZetaGaussian n (extensionEmbedding v u.val) *
          χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) * (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s) =
        f (extensionEmbedding v u.val) := by
    let z := extensionEmbedding v u.val
    have hz : z ≠ 0 := (map_ne_zero (extensionEmbedding v)).mpr u.ne_zero
    have hr : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) _
    have hn : ‖z‖ = ‖u.val‖ := (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _
    rw [hv.mult_eq_two, ← hn, hchar u]
    change _ * (_ * exp _) * _ = _
    rw [← mul_assoc, mul_assoc (_ * _), positive_cpow_add_radial hr]
  dsimp only
  simp_rw [h]
  exact ⟨hi', heq'.trans (heq.trans (congrFun hGamma s).symm)⟩

end Masullo
