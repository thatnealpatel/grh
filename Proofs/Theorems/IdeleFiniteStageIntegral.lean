module

public import Theorems.IdeleRestrictedProductHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Pure tensor integrals on finite idele stages

The proof of Theorem 3.3.1.1(1), p. 130, factors the finite `S`-local
pairing. For the upstairs pairing (3.2.2.1), p. 124, Masullo uses a global
absolute-value product (3.2.2.6), p. 126, and asserts the Euler product
(3.4.1.6) for `Re s > 1`, p. 144. We supply the finite-stage integration
step on the actual ideles using the exact restrictions from
(A.3.2.5), p. 560. The inactive unit probability contributes one; active
Haar measures are not rescaled. This step uses an explicit tensor identity
on the stage, not the printed independence from the choice of admissible set.
It does not assert convergence as the stage grows. Passage readings are
provisional (Markdown and PDF layout).
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Masullo

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [mf : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [mu : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [bf : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [bu : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  (μa : (v : InfinitePlace K) → Measure v.Completionˣ)
  (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)ˣ)
  [ha : ∀ v, (μa v).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]

/-- Local integrability gives integrability of a pure tensor on the actual
open stage. Both its integral and its absolute mass are products of the
full local values at infinity and at the active finite places. -/
public theorem ideleFiniteStage_integral (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1)
    (μ : Measure I) (hμ : μ.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S)
    (g : I → ℂ) (a : (v : InfinitePlace K) → v.Completionˣ → ℂ)
    (f : (v : {v // v ∈ S}) → (v.val.adicCompletion K)ˣ → ℂ)
    (hA : ∀ v, Integrable (a v) (μa v)) (hF : ∀ v, Integrable (f v) (μf v.val))
    (hg : ∀ x : IdeleFiniteStage K S,
      g (ideleFiniteStageEmbedding K S x) = (∏ v, a v (x.1 v)) * (∏ v, f v (x.2.1 v))) :
    IntegrableOn g (range (ideleFiniteStageEmbedding K S)) μ ∧
    (∫ x in range (ideleFiniteStageEmbedding K S), g x ∂μ) =
      (∏ v, ∫ x, a v x ∂μa v) * (∏ v, ∫ x, f v x ∂μf v.val) ∧
    (∫ x in range (ideleFiniteStageEmbedding K S), ‖g x‖ ∂μ) =
      (∏ v, ∫ x, ‖a v x‖ ∂μa v) * (∏ v, ∫ x, ‖f v x‖ ∂μf v.val) := by
  have hj := (isOpenEmbedding_ideleFiniteStageEmbedding K S).measurableEmbedding
  -- Work on exactly the open stage, not on the entire upstairs measure.
  have hm := (hj.map_comap μ).symm
  rw [hμ] at hm
  have hg' : g ∘ ideleFiniteStageEmbedding K S = fun x ↦
      (∏ v, a v (x.1 v)) * (∏ v, f v (x.2.1 v)) := funext hg
  simp only [IntegrableOn, hm, hj.integrable_map_iff, hj.integral_map, hg', hg, norm_mul, norm_prod]
  -- The same product calculation applies to the complex values and their norms.
  obtain ⟨hi, hval⟩ := ideleFiniteStageProduct_tensor K μa μf S hS a f hA hF
  obtain ⟨_, hnorm⟩ := ideleFiniteStageProduct_tensor K μa μf S hS
    (fun v x ↦ ‖a v x‖) (fun v x ↦ ‖f v x‖) (fun v ↦ (hA v).norm) (fun v ↦ (hF v).norm)
  exact ⟨hi, hval, hnorm⟩

end Masullo
