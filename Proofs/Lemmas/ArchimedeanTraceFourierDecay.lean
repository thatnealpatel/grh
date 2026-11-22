module

public import Lemmas.ArchimedeanAdeleTrace

/-! # Archimedean coordinate weights for the trace Fourier integral -/

open NumberField NumberField.InfinitePlace InfinitePlace.Completion
open scoped Classical FourierTransform SchwartzMap

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

private theorem norm_le_traceFrequency (x : InfiniteAdeleRing K) (v : InfinitePlace K) :
    ‖x v‖ ≤ ‖archimedeanTraceFrequency K ((archimedeanEuclideanToAdele K).symm x)‖ := by
  let Y := archimedeanTraceFrequency K ((archimedeanEuclideanToAdele K).symm x)
  have hm : mixedEmbedding.euclidean.toMixed K Y =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K x).1,
        fun w ↦ 2 * star ((InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 w)) := by
    dsimp only [Y]
    rw [archimedeanTraceFrequency, ContinuousLinearEquiv.apply_symm_apply,
      archimedeanEuclideanToAdele_symm_mixed]
  by_cases hv : v.IsReal
  · let w : {v : InfinitePlace K // v.IsReal} := ⟨v, hv⟩
    have hw : Y.fst w = extensionEmbeddingOfIsReal hv (x v) :=
      congrArg (fun y : mixedEmbedding.mixedSpace K ↦ y.1 w) hm
    rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v), ← hw]
    exact (PiLp.norm_apply_le Y.fst w).trans (WithLp.norm_fst_le _ Y)
  · let w : {v : InfinitePlace K // v.IsComplex} := ⟨v, not_isReal_iff_isComplex.mp hv⟩
    have hw : Y.snd w = 2 * star (extensionEmbedding v (x v)) :=
      congrArg (fun y : mixedEmbedding.mixedSpace K ↦ y.2 w) hm
    have hn : ‖Y.snd w‖ = 2 * ‖x v‖ := by
      rw [hw, norm_mul, norm_star,
        (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
      norm_num
    calc
      ‖x v‖ ≤ ‖Y.snd w‖ := by rw [hn]; linarith [norm_nonneg (x v)]
      _ ≤ ‖Y‖ := (PiLp.norm_apply_le Y.snd w).trans (WithLp.norm_snd_le _ Y)

/-- The trace Fourier integral is uniformly bounded after weighting by any
power of any infinite completion radius. The real and complex frequency
coordinates have scales one and two, respectively. -/
public theorem exists_archimedeanTraceFourier_norm_mul_pow_le
    (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : InfiniteAdeleRing K) (v : InfinitePlace K),
      ‖archimedeanTraceFourier K φ ((archimedeanEuclideanToAdele K).symm y)‖ * ‖y v‖ ^ p ≤ C := by
  obtain ⟨B, hB, hb⟩ := (𝓕 φ).decay p 0
  refine ⟨‖(2 : ℂ) ^ nrComplexPlaces K‖ * B, mul_pos (by simp) hB, fun y v ↦ ?_⟩
  let z := archimedeanTraceFrequency K ((archimedeanEuclideanToAdele K).symm y)
  rw [archimedeanTraceFourier_eq, ← SchwartzMap.fourier_coe, norm_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(𝓕 φ) z‖ * ‖y v‖ ^ p ≤ ‖(𝓕 φ) z‖ * ‖z‖ ^ p := by
      gcongr
      exact norm_le_traceFrequency y v
    _ ≤ B := by simpa [mul_comm] using hb z

end Masullo
