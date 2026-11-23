module

public import Lemmas.TrivialHeckeGammaFactor

open NumberField

namespace Masullo

/-- The trivial Hecke character contributes Deligne's real Gamma factor at every real place. -/
public theorem localHeckeGammaFactor_one_real_eq_Gammaℝ
    {K : Type*} [Field K] [NumberField K]
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖(1 : HeckeCharacter (𝓞 K) K) x‖ = 1)
    {v : InfinitePlace K} (hv : v.IsReal) (s : ℂ) :
    localHeckeGammaFactor (1 : HeckeCharacter (𝓞 K) K) hχ v s = Complex.Gammaℝ s := by
  have hfactor : localHeckeGammaFactor (1 : HeckeCharacter (𝓞 K) K) hχ v =
      archimedeanGammaFactor Real.pi 2 0 0 := localHeckeGammaFactor_one_real hv
  rw [hfactor, archimedeanGammaFactor_real]
  simp

end Masullo
