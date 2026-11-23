module

public import Theorems.CompletedHeckeEulerProduct
import Lemmas.GammaRightLineLowerBound

/-!
# Archimedean lower bounds for the completed Hecke product

On `Re s = 2` the arguments of the chosen Gamma factors have integer or
half-integer real parts. The local lower bound keeps the frequency shift and
normalizing power of `π` or `2π`. It is a contour prerequisite, not a statement
about the zeros of a continuation.
-/

open Complex NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- Each chosen local factor for a unitary Hecke character admits an exponential
lower bound on the whole right line. The rate is independent of the height. -/
public theorem exists_localHeckeGammaFactor_rightLine_lower_bound
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ c, ‖χ c‖ = 1) (v : InfinitePlace K) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤
      ‖localHeckeGammaFactor χ hχ v (2 + (t : ℂ) * Complex.I)‖ := by
  rcases v.isReal_or_isComplex with hr | hc
  · obtain ⟨b, τ, _, _, h⟩ := localHeckeGammaFactor_real χ hχ hr
    rw [h]
    -- This covers both choices `b = 0` and `b = 1`.
    exact exists_archimedeanGammaFactor_real_rightLine_lower_bound b τ
  · obtain ⟨n, τ, _, h⟩ := localHeckeGammaFactor_complex χ hχ hc
    rw [h]
    -- The Gamma argument is `2 + |n| / 2 + i(t + τ)` for every angular weight.
    exact exists_archimedeanGammaFactor_complex_rightLine_lower_bound n τ

end Masullo
