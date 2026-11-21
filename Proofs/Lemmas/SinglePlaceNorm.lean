module

public import Mathlib.NumberTheory.NumberField.AdeleRing

open NumberField IsDedekindDomain
open scoped BigOperators

namespace Masullo

/-- The adelic norm of a single-place idele is the norm of its local unit. -/
public theorem norm_idele_ofAdicCompletion {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ‖(IdeleGroup.ofAdicCompletion (𝓞 K) K v u : AdeleRing (𝓞 K) K)‖ =
      ‖(u : v.adicCompletion K)‖ := by
  let := Classical.decEq (HeightOneSpectrum (𝓞 K))
  let x := IdeleGroup.ofAdicCompletion (𝓞 K) K v u
  change ‖(x : AdeleRing (𝓞 K) K)‖ = _
  rw [AdeleRing.norm_apply_of_isUnit x.isUnit]
  let f : HeightOneSpectrum (𝓞 K) → ℝ := fun w ↦ ‖(x : AdeleRing (𝓞 K) K).2 w‖
  change (∏ w : InfinitePlace K, ‖(1 : w.Completion)‖ ^ w.mult) * (∏ᶠ w, f w) = _
  let A := fun p : HeightOneSpectrum (𝓞 K) ↦ p.adicCompletionIntegers K
  have hoff (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ v) : f w = 1 := by
    change ‖RestrictedProduct.mulSingle A v (u : v.adicCompletion K) w‖ = 1
    rw [RestrictedProduct.mulSingle_eq_of_ne A _ hw, norm_one]
  have hat : f v = ‖(u : v.adicCompletion K)‖ := by
    change ‖RestrictedProduct.mulSingle A v (u : v.adicCompletion K) v‖ = _
    rw [RestrictedProduct.mulSingle_eq_same]
  rw [finprod_eq_single f v hoff, hat]
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]

end Masullo
