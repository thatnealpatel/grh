module

public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Finite-unit representatives of rational idele classes

We prove the algebraic existence part of Masullo's (A.2.2.1)–(A.2.2.3),
p. 546: A principal rescaling makes every finite component a local integral
unit. This does not assert a topological splitting or choose the real sign.
-/

open NumberField IsDedekindDomain
open scoped BigOperators WithZero Classical

namespace Masullo

private theorem exists_rational_place_generator (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ q : ℚˣ, ∀ w : HeightOneSpectrum (𝓞 ℚ),
      w.valuation ℚ (q : ℚ) = if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  classical
  let : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal (S := v.asIdeal)
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hp)
  refine ⟨Units.mk0 (algebraMap (𝓞 ℚ) ℚ p) ((IsFractionRing.injective (𝓞 ℚ) ℚ).ne hp0), ?_⟩
  intro w
  change w.valuation ℚ (algebraMap (𝓞 ℚ) ℚ p) = _
  rw [w.valuation_of_algebraMap]
  split_ifs with h
  · subst w
    exact v.intValuation_singleton hp0 hp
  · apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro hmem
    have hle : v.asIdeal ≤ w.asIdeal := hp ▸ Ideal.span_le.mpr (by simpa using hmem)
    exact h (HeightOneSpectrum.asIdeal_injective (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

/-- Every rational idele has a principal rescaling whose finite coordinates
are integral units. The valuation-one criterion concerns the value of each
local valuation, not equality of the coordinate itself to one. -/
public theorem exists_rational_principal_mul_finite_valued_eq_one (a : IdeleGroup (𝓞 ℚ) ℚ) :
    ∃ r : ℚˣ, ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a : IdeleGroup (𝓞 ℚ) ℚ) :
        AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
  classical
  let d := fun v ↦ Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v)
  obtain ⟨_, hne, hcofinite⟩ := AdeleRing.isUnit_iff.mp a.isUnit
  have hfinite : (Function.mulSupport d).Finite := hcofinite
  let S := hfinite.toFinset
  choose p hp using exists_rational_place_generator
  let factors := fun w ↦ p w ^ WithZero.log (d w)
  -- Each factor cancels the valuation at its own place and has value one elsewhere.
  refine ⟨∏ w ∈ S, factors w, fun v ↦ ?_⟩
  have hd0 : d v ≠ 0 := (Valuation.ne_zero_iff _).mpr (hne v)
  have hv : v.valuation ℚ (((∏ w ∈ S, factors w) : ℚˣ) : ℚ) = (d v)⁻¹ := by
    change v.valuation ℚ (Units.coeHom ℚ (∏ w ∈ S, factors w)) = _
    rw [map_prod (Units.coeHom ℚ), map_prod (v.valuation ℚ)]
    simp only [Units.coeHom_apply, factors, Units.val_zpow_eq_zpow_val, map_zpow₀, hp]
    by_cases hmem : v ∈ S
    · rw [Finset.prod_eq_single_of_mem v hmem (fun w _ hw ↦ by simp [Ne.symm hw])]
      rw [ite_eq_left rfl, ← WithZero.exp_zsmul, Int.zsmul_eq_mul, mul_neg, mul_one,
        WithZero.exp_neg, WithZero.exp_log hd0]
    · have h1 : d v = 1 := by
        by_contra hne'
        exact hmem (hfinite.mem_toFinset.mpr hne')
      rw [Finset.prod_eq_one (fun w hw ↦ by
        have hne : v ≠ w := fun h ↦ hmem (h ▸ hw)
        simp [hne]), h1, inv_one]
  change Valued.v (((algebraMap ℚ (v.adicCompletion ℚ))
    (((∏ w ∈ S, factors w) : ℚˣ) : ℚ)) * (a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1
  rw [map_mul, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, HeightOneSpectrum.adicCompletion.valued_coe, hv]
  exact inv_mul_cancel₀ hd0

end Masullo
