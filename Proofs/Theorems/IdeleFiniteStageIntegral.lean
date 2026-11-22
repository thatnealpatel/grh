module

public import Theorems.IdeleRestrictedProductHaar
public import Theorems.IdeleFiniteStageZetaDensity
import Mathlib.MeasureTheory.Integral.Pi

/-! # Pure tensor integrals on finite idele stages

The proof of Theorem 3.3.1.1(1), p. 130, factors the finite `S`-local
pairing. For the upstairs pairing (3.2.2.1), p. 124, Masullo uses a global
absolute-value product (3.2.2.6), p. 126, and asserts the Euler product
(3.4.1.6) for `Re s > 1`, p. 144. We supply the finite-stage integration
step on the actual ideles using the exact restrictions from
(A.3.2.5), p. 560. The inactive unit probability contributes one; active
Haar measures are not rescaled. The Archimedean factor remains grouped as
in (3.4.1.2), p. 143. This step uses an explicit tensor identity
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
local notation "F" v => HeightOneSpectrum.adicCompletion K v
set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace K) → v.Completionˣ)

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

/-- Integrate a grouped Archimedean factor and separate active finite factors
on the actual open stage, retaining the exact local Haar measures. -/
public theorem ideleFiniteStage_integral_grouped (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1)
    (μ : Measure I) (hμ : μ.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S)
    (g : I → ℂ) (a : A → ℂ)
    (f : (v : {v // v ∈ S}) → (v.val.adicCompletion K)ˣ → ℂ)
    (hA : Integrable a (Measure.pi μa)) (hF : ∀ v, Integrable (f v) (μf v.val))
    (hg : ∀ x : IdeleFiniteStage K S,
      g (ideleFiniteStageEmbedding K S x) = a x.1 * (∏ v, f v (x.2.1 v))) :
    IntegrableOn g (range (ideleFiniteStageEmbedding K S)) μ ∧
    (∫ x in range (ideleFiniteStageEmbedding K S), g x ∂μ) =
      (∫ x, a x ∂Measure.pi μa) * (∏ v, ∫ x, f v x ∂μf v.val) ∧
    (∫ x in range (ideleFiniteStageEmbedding K S), ‖g x‖ ∂μ) =
      (∫ x, ‖a x‖ ∂Measure.pi μa) * (∏ v, ∫ x, ‖f v x‖ ∂μf v.val) := by
  have hj := (isOpenEmbedding_ideleFiniteStageEmbedding K S).measurableEmbedding
  -- Work on exactly the open stage, not on the entire upstairs measure.
  have hm := (hj.map_comap μ).symm
  rw [hμ] at hm
  have hg' : g ∘ ideleFiniteStageEmbedding K S = fun x ↦
      a x.1 * (∏ v, f v (x.2.1 v)) := funext hg
  simp only [IntegrableOn, hm, hj.integrable_map_iff, hj.integral_map, hg', hg, norm_mul, norm_prod]
  -- The same product calculation applies to the complex values and their norms.
  obtain ⟨hi, hval⟩ := ideleFiniteStageProduct_groupedTensor K μa μf S hS a f hA hF
  obtain ⟨_, hnorm⟩ := ideleFiniteStageProduct_groupedTensor K μa μf S hS
    (fun x ↦ ‖a x‖) (fun v x ↦ ‖f v x‖) hA.norm (fun v ↦ (hF v).norm)
  exact ⟨hi, hval, hnorm⟩

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
  let (v : InfinitePlace K) := archimedeanHaar_sigmaFinite K μa v
  obtain ⟨hi, hval, hnorm⟩ :=
    ideleFiniteStage_integral_grouped K μa μf S hS μ hμ g (fun x ↦ ∏ v, a v (x v))
      f (Integrable.fintype_prod_dep hA) hF hg
  simp only [norm_prod] at hnorm
  rw [integral_fintype_prod_eq_prod (μ := μa) (fun v x ↦ ‖a v x‖)] at hnorm
  rw [integral_fintype_prod_eq_prod (μ := μa) a] at hval
  exact ⟨hi, hval, hnorm⟩

/-- The raw zeta density of (3.2.2.1) on a stage containing the test exceptions
and ramification. Local integrability suffices for both stage formulas.
No splitting of the Archimedean test or normalization at active places is required. -/
public theorem ideleFiniteStage_zetaIntegral (E S : Finset V) (hES : E ⊆ S)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1)
    (μ : Measure I) (hμ : μ.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S)
    (χ : HeckeCharacter (𝓞 K) K) (hu : ∀ v ∉ S, χ.IsUnramifiedAt v) (s : ℂ)
    (arch : A → ℂ) (f : (v : V) → (F v)ˣ → ℂ) :
    let g (a : I) := ideleZetaTest K E arch f a *
      χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) *
      (‖(a : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s
    let aInf (x : A) := arch x *
      (∏ v : InfinitePlace K, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x v))) *
      ((∏ v : InfinitePlace K, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s
    let aFin (v : {v // v ∈ S}) (x : (F v.val)ˣ) := ideleFiniteTest K E f v x *
      χ.restrict v (x : F v.val) * (‖(x : F v.val)‖ : ℂ) ^ s
    Integrable aInf (Measure.pi μa) → (∀ v, Integrable (aFin v) (μf v.val)) →
      IntegrableOn g (range (ideleFiniteStageEmbedding K S)) μ ∧
      (∫ x in range (ideleFiniteStageEmbedding K S), g x ∂μ) =
        (∫ x, aInf x ∂Measure.pi μa) * (∏ v, ∫ x, aFin v x ∂μf v.val) ∧
      (∫ x in range (ideleFiniteStageEmbedding K S), ‖g x‖ ∂μ) =
        (∫ x, ‖aInf x‖ ∂Measure.pi μa) * (∏ v, ∫ x, ‖aFin v x‖ ∂μf v.val) := by
  intro g aInf aFin hA hF
  -- The density theorem supplies the pointwise repair on the exact stage.
  exact ideleFiniteStage_integral_grouped K μa μf S hS μ hμ g aInf aFin hA hF
    (ideleFiniteStage_zetaDensity K E S hES χ hu s arch f)

end Masullo
