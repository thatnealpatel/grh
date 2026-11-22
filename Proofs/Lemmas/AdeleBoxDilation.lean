module

public import Theorems.AdeleBoxFourier

/-! # Idelic pullbacks of adelic box tensors

An idele dilates the real Schwartz factor by a real continuous linear equivalence.
At finite places its inverse transports both the centre and the scale of the box.
The pullback therefore preserves the complex span of the tensors.
-/

open IsDedekindDomain NumberField Set
open scoped Classical InnerProductSpace Pointwise SchwartzMap

namespace Masullo

noncomputable section

/-- The complex span of Schwartz factors tensored with translated finite-box indicators. -/
@[expose] public def adeleBoxSpan (K : Type*) [Field K] [NumberField K] :
    Submodule ℂ (AdeleRing (𝓞 K) K → ℂ) :=
  Submodule.span ℂ {f | ∃ (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
    (a : FiniteAdeleRing (𝓞 K) K) (g : (FiniteAdeleRing (𝓞 K) K)ˣ), adeleBoxTensor φ a g = f}

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "A∞" => InfiniteAdeleRing K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v

/-- Each box tensor belongs to the box span. -/
public theorem adeleBoxTensor_mem_adeleBoxSpan (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) :
    adeleBoxTensor φ a g ∈ adeleBoxSpan K :=
  Submodule.subset_span ⟨φ, a, g, rfl⟩

private def archimedeanMixedUnit (h : I) : (mixedEmbedding.mixedSpace K)ˣ :=
  Units.map ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toMonoidHom.comp
    (MonoidHom.fst A∞ F)) h

/-- Multiplication by the Archimedean component of the idele in Euclidean mixed coordinates. -/
public def adeleBoxArchDilation (h : I) : E∞ ≃L[ℝ] E∞ :=
  let c := mixedEmbedding.euclidean.toMixed K
  c.trans ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (archimedeanMixedUnit h)).trans c.symm)

/-- The Archimedean equivalence acts as multiplication on the first component of the adeles. -/
public theorem adeleBoxArchDilation_apply (h : I) (x : A) :
    adeleBoxArchDilation h ((archimedeanEuclideanToAdele K).symm x.1) =
      (archimedeanEuclideanToAdele K).symm (((h : A) * x).1) := by
  let c := mixedEmbedding.euclidean.toMixed K
  apply c.injective
  change c (c.symm (↑(archimedeanMixedUnit h) * c ((archimedeanEuclideanToAdele K).symm x.1))) =
    c ((archimedeanEuclideanToAdele K).symm ((h : A).1 * x.1))
  rw [c.apply_symm_apply, archimedeanEuclideanToAdele_symm_mixed,
    archimedeanEuclideanToAdele_symm_mixed, map_mul]
  rfl

private theorem mem_finiteAdeleBox_mul_iff (u : Fˣ) (a : F) (g : Fˣ) (z : F) :
    (u : F) * z ∈ finiteAdeleBox a g ↔
      z ∈ finiteAdeleBox ((↑u⁻¹ : F) * a) (u⁻¹ * g) := by
  simp only [finiteAdeleBox, mem_ofPred_eq]
  refine forall_congr' fun v ↦ ?_
  let uv : (L[v])ˣ := Units.map (RestrictedProduct.evalMonoidHom (fun w : V ↦ L[w]) v) u
  change (uv : L[v]) * z v ∈ (a v + ·) '' (g.val v • (O[v] : Set L[v])) ↔
    z v ∈ (((↑uv⁻¹ : L[v]) * a v + ·) '' (((↑uv⁻¹ : L[v]) * g.val v) • (O[v] : Set L[v])))
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, h⟩
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    change (↑uv⁻¹ : L[v]) * a v + ((↑uv⁻¹ : L[v]) * g.val v) * t = z v
    change a v + g.val v * t = (uv : L[v]) * z v at h
    rw [mul_assoc, ← mul_add, h, Units.inv_mul_cancel_left]
  · rintro ⟨_, ⟨t, ht, rfl⟩, h⟩
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    change a v + g.val v * t = (uv : L[v]) * z v
    change (↑uv⁻¹ : L[v]) * a v + ((↑uv⁻¹ : L[v]) * g.val v) * t = z v at h
    rw [mul_assoc, ← mul_add] at h
    rw [← h, Units.mul_inv_cancel_left]

/-- Pullback of a box tensor by an actual idele; the inverse finite unit acts on
both the centre and the scale, while the Schwartz factor composes with the forward dilation. -/
public theorem adeleBoxTensor_dilate (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (h : I) :
    (fun x ↦ adeleBoxTensor φ a g ((h : A) * x)) =
      adeleBoxTensor (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (adeleBoxArchDilation h) φ)
        ((↑(ideleFinitePart h)⁻¹ : F) * a) ((ideleFinitePart h)⁻¹ * g) := by
  funext x
  have hfin : ((h : A) * x).2 = (ideleFinitePart h : F) * x.2 := by
    ext v : 1
    change (h : A).2 v * x.2 v = (ideleFinitePart h : F) v * x.2 v
    rw [ideleFinitePart_apply]
  have hm := mem_finiteAdeleBox_mul_iff (ideleFinitePart h) a g x.2
  simp only [adeleBoxTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, adeleBoxArchDilation_apply, hfin]
  by_cases hx : (ideleFinitePart h : F) * x.2 ∈ finiteAdeleBox a g
  · rw [indicator_of_mem hx, indicator_of_mem (hm.mp hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (hx ∘ hm.mpr)]

/-- The complex box span is stable under pullback by multiplication by any idele. -/
public theorem adeleBoxSpan_dilate {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (h : I) :
    (fun x ↦ f ((h : A) * x)) ∈ adeleBoxSpan K := by
  let D := LinearMap.funLeft ℂ ℂ (fun x : A ↦ (h : A) * x)
  change D f ∈ adeleBoxSpan K
  have hD : adeleBoxSpan K ≤ (adeleBoxSpan K).comap D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, a, g, rfl⟩
    change (fun x ↦ adeleBoxTensor φ a g ((h : A) * x)) ∈ adeleBoxSpan K
    rw [adeleBoxTensor_dilate]
    exact adeleBoxTensor_mem_adeleBoxSpan _ _ _
  exact hD hf

end

end Masullo
