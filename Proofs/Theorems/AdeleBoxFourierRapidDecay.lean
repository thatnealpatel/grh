module

public import Theorems.IdeleClassRapidDecay
public import Lemmas.AdeleBoxDilation
import Lemmas.ArchimedeanTraceFourierDecay
import Lemmas.GaussianDifferentIdele
import Theorems.FiniteBoxTraceDual
import Theorems.FiniteBoxCenteredMass
import Mathlib.Algebra.FiniteSupport.Basic

/-! # Large-norm decay for the actual additive Fourier integral

The reflected expression (2.2.3.7), PDF p. 83, needs rapid decay of the
nonzero principal sum of the Fourier transform, not just of the original
test. For (2.2.3.4) and the lattice estimate (2.2.3.8)–(13), pp. 83–84,
we supply the two needed bounds directly on the same integral as in theta
inversion. The box factors at arbitrary frequencies give centered support
in the inverse different times the inverse box scale, as suggested by the
unit-box calculation (A.3.1.8), p. 558. There the finite phases have norm
one, leaving a fixed centered mass. The trace Fourier transform of the
Archimedean Schwartz factor supplies all coordinate weights. We then use
the uniform lattice estimate and finite linearity, with no pointwise
continuity, quotient averaging, or treatment of zero modes here.
Source reading: Provisional pinned Markdown and numbered PDF layout.
-/

open Function IsDedekindDomain MeasureTheory NumberField
open scoped Classical ComplexConjugate Masullo.AdeleStage nonZeroDivisors Pointwise SchwartzMap WithZero

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "w[" v "]" => (Valued.v : Valuation K[v] ℤᵐ⁰)
local notation "mass[" g "," v "]" => @Measure.real K[v] (borel K[v])
  (finiteCompletionNormalizedHaar v) (Units.val g v • (O[v] : Set K[v]))

private theorem adeleBox_fourier_support_and_decay (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) :
    ∃ c : I,
      (∀ b : I, adeleFourier μ (adeleBoxTensor φ a g) (b : A) ≠ 0 →
        ∀ v : V, ‖(c * b).val.2 v‖ ≤ 1) ∧
      ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (b : I) (v : InfinitePlace K),
        ‖adeleFourier μ (adeleBoxTensor φ a g) (b : A)‖ * ‖b.val.1 v‖ ^ p ≤ C := by
  let h := ideleFinitePart (gaussianDifferentIdele K)
  let c : I := MulEquiv.prodUnits.symm (1, h * g)
  let H (b : A) (v : V) := finiteBoxLocalFourierAt a g v (b.2 v)
  have hprod (b : A) : adeleFourier μ (adeleBoxTensor φ a g) b =
      archimedeanTraceFourier K φ ((archimedeanEuclideanToAdele K).symm b.1) * ∏ᶠ v, H b v :=
    (adeleBox_fourier_at μ E hμ φ a g b).2
  have hsupport (b : A) : (H b).HasFiniteMulSupport := finiteBoxLocalFourierAt_hasFiniteMulSupport a g b.2
  refine ⟨c, ?_, ?_⟩
  · intro b hb v
    have hn : H (b : A) v ≠ 0 := by
      intro hz
      exact hb (by rw [hprod, finprod_eq_zero _ v hz (hsupport _), mul_zero])
    have hann := (finiteBox_annihilates_iff g h (finiteIdeal_gaussianDifferentIdele K) v (b.val.2 v))
    have hv := hann.mp (by
      by_contra hh
      apply hn
      dsimp only [H]
      rw [finiteBoxLocalFourierAt_eq, ite_eq_right hh])
    apply Valued.toNormedField.norm_le_one_iff.mpr
    change Valued.v ((h.val v * g.val v) * b.val.2 v) ≤ 1
    have hcancel : (h * g).val v * ((h * g)⁻¹ : Fˣ).val v = 1 := by
      change ((h * g) * (h * g)⁻¹ : Fˣ).val v = 1
      rw [mul_inv_cancel]
      rfl
    change w[v] ((h * g).val v * b.val.2 v) ≤ 1
    rw [map_mul]
    calc
      _ ≤ w[v] ((h * g).val v) * w[v] (((h * g)⁻¹ : Fˣ).val v) :=
        mul_le_mul_of_nonneg_left hv zero_le
      _ = 1 := by rw [← map_mul, hcancel, map_one]
  · intro p
    obtain ⟨B, hB, hb⟩ := exists_archimedeanTraceFourier_norm_mul_pow_le φ p
    let M : ℝ := ∏ᶠ v : V, mass[g,v]
    have hM : 0 ≤ M := finprod_nonneg fun v ↦ measureReal_nonneg
    refine ⟨M * B + 1, by linarith [mul_nonneg hM hB.le], fun b v ↦ ?_⟩
    have hf : ‖∏ᶠ v, H (b : A) v‖ ≤ M := by
      change normHom (∏ᶠ v, H (b : A) v) ≤ M
      rw [map_finprod normHom (hsupport _)]
      apply finprod_le_finprod₀
      · exact HasFiniteMulSupport.fun_comp (hsupport (b : A)) normHom.map_one
      · exact fun v ↦ show 0 ≤ ‖H (b : A) v‖ from norm_nonneg _
      · exact (finiteBox_centeredMass_finprod g).1
      · intro w
        change ‖finiteBoxLocalFourierAt a g w (b.val.2 w)‖ ≤ mass[g,w]
        rw [finiteBoxLocalFourierAt_eq]
        split
        · simp [norm_padicStdAddChar, abs_of_nonneg measureReal_nonneg]
        · simpa only [norm_zero] using (measureReal_nonneg : 0 ≤ mass[g,w])
    rw [hprod, norm_mul, mul_comm _ ‖∏ᶠ v, H (b : A) v‖, mul_assoc]
    exact (mul_le_mul hf (hb b.val.1 v) (by positivity) hM).trans (le_add_of_nonneg_right zero_le_one)

private def HasFourierRapidDecay (μ : Measure A) (f : A → ℂ) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ b : I, 1 ≤ ideleNorm b →
    (Summable fun k : Kˣ ↦ ‖adeleFourier μ f ((d k * b : I) : A)‖) ∧
    (∑' k : Kˣ, ‖adeleFourier μ f ((d k * b : I) : A)‖) ≤ C * ideleNorm b ^ (-(N : ℤ))

/-- At every large-norm idele, the nonzero principal series of the actual
additive Fourier integral on the box span is absolutely summable, and its
absolute sum decays uniformly faster than any inverse power of the norm. -/
public theorem adeleBoxSpan_fourier_rapidDecay (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : I, 1 ≤ ideleNorm b →
      (Summable fun k : Kˣ ↦ ‖adeleFourier μ f ((d k * b : I) : A)‖) ∧
      (∑' k : Kˣ, ‖adeleFourier μ f ((d k * b : I) : A)‖) ≤ C * ideleNorm b ^ (-(N : ℤ)) := by
  let Q (f : A → ℂ) (y : A) (x : A) := f x * conj (numberFieldAdeleAddChar (x * y))
  let P (f : A → ℂ) := (∀ y, Integrable (Q f y) μ) ∧ HasFourierRapidDecay μ f N
  suffices P f from this.2
  change f ∈ Submodule.span ℂ {b | ∃ (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ),
    adeleBoxTensor φ a g = b} at hf
  refine Submodule.span_induction (p := fun b _ ↦ P b) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨φ, a, g, rfl⟩
    obtain ⟨c, hs, hw⟩ := adeleBox_fourier_support_and_decay μ E hμ φ a g
    exact ⟨fun y ↦ (adeleBox_fourier_at μ E hμ φ a g y).1,
      idele_periodization_rapidDecay_of_support _ c hs hw N⟩
  · refine ⟨by simp [Q], 1, zero_lt_one, fun b hb ↦ ?_⟩
    simpa [adeleFourier] using zpow_nonneg (zero_le_one.trans hb) (-(N : ℤ))
  · rintro u w _ _ ⟨hiu, Cu, hCu, hU⟩ ⟨hiw, Cw, hCw, hW⟩
    have ht (y : A) : adeleFourier μ (u + w) y = adeleFourier μ u y + adeleFourier μ w y := by
      simp only [adeleFourier, Pi.add_apply, add_mul]
      exact integral_add (hiu y) (hiw y)
    refine ⟨fun y ↦ by simpa only [Q, Pi.add_apply, add_mul] using (hiu y).fun_add (hiw y),
      Cu + Cw, add_pos hCu hCw, fun b hb ↦ ?_⟩
    simp only [ht]
    obtain ⟨hu, hdu⟩ := hU b hb
    obtain ⟨hw, hdw⟩ := hW b hb
    have hle (k : Kˣ) : ‖adeleFourier μ u ((d k * b : I) : A) +
        adeleFourier μ w ((d k * b : I) : A)‖ ≤
        ‖adeleFourier μ u ((d k * b : I) : A)‖ + ‖adeleFourier μ w ((d k * b : I) : A)‖ :=
      norm_add_le _ _
    have hsum := (hu.add hw).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
    refine ⟨hsum, (hsum.tsum_le_tsum hle (hu.add hw)).trans ?_⟩
    rw [hu.tsum_add hw, add_mul]
    exact add_le_add hdu hdw
  · rintro e u _ ⟨hiu, C, hC, hU⟩
    have ht (y : A) : adeleFourier μ (e • u) y = e * adeleFourier μ u y := by
      simp only [adeleFourier, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    refine ⟨fun y ↦ by simpa only [Q, Pi.smul_apply, smul_eq_mul, mul_assoc] using (hiu y).const_mul e,
      ‖e‖ * C + 1, by linarith [mul_nonneg (norm_nonneg e) hC.le], fun b hb ↦ ?_⟩
    obtain ⟨hu, hdu⟩ := hU b hb
    simp only [ht, norm_mul]
    refine ⟨hu.mul_left _, ?_⟩
    rw [tsum_mul_left, add_mul, mul_assoc ‖e‖ C]
    exact (mul_le_mul_of_nonneg_left hdu (norm_nonneg _)).trans
      (le_add_of_nonneg_right (mul_nonneg zero_le_one (zpow_nonneg (zero_le_one.trans hb) _)))

end

end Masullo
