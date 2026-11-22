module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Valuation and factorization interfaces for the finite-idele ideal map -/

open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped Classical nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K

/-- A nonzero fractional ideal with no negative prime exponents is integral. -/
public theorem le_one_of_count_nonneg {j : J} (hj : j ≠ 0)
    (h : ∀ v : V, 0 ≤ FractionalIdeal.count K v j) : j ≤ 1 := by
  classical
  have hs : Function.HasFiniteMulSupport (fun v : V ↦ (v.asIdeal : J) ^ FractionalIdeal.count K v j) := by
    change {v : V | ¬ (v.asIdeal : J) ^ FractionalIdeal.count K v j = 1}.Finite
    apply eventually_cofinite.mp
    filter_upwards [FractionalIdeal.finite_factors j] with v hv
    rw [hv, zpow_zero]
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hj, finprod_eq_prod _ hs]
  apply Finset.prod_le_one₀ (fun _ _ ↦ FractionalIdeal.zero_le _)
  intro v _
  rw [← Int.toNat_of_nonneg (h v), zpow_natCast]
  exact pow_le_one₀ (FractionalIdeal.zero_le _) FractionalIdeal.coeIdeal_le_one

public theorem fractionalIdeal_units_ext_count {I J' : Jˣ}
    (h : ∀ v : V, FractionalIdeal.count K v (I : J) = FractionalIdeal.count K v (J' : J)) :
    I = J' := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J'.ne_zero]
  exact finprod_congr fun v ↦ congrArg (fun n : ℤ ↦ (v.asIdeal : J) ^ n) (h v)

public theorem finiteIdele_valuation_ne_zero (g : Fˣ) (v : V) :
    Valued.v ((g : F) v) ≠ 0 := by
  have hg := (FiniteAdeleRing.isUnit_iff.mp g.isUnit).1 v
  exact (map_ne_zero (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).2 hg

public theorem count_spanSingleton_eq_neg_log_valuation (a : K) (ha : a ≠ 0) (v : V) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) =
      -WithZero.log (v.valuation K a) := by
  obtain ⟨r, d, rfl⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ a
  have hr : r ≠ 0 := by
    intro h
    subst r
    exact ha (by simp [IsFractionRing.mk'_eq_div])
  have hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K r d) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) d)⁻¹ *
        ((Ideal.span {r} : Ideal (𝓞 K)) : J) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, ← map_mul, IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hJ,
    v.valuation_of_mk', WithZero.log_div (v.intValuation_ne_zero r hr) (v.intValuation_ne_zero' d),
    v.intValuation_if_neg hr, v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d),
    WithZero.log_exp, WithZero.log_exp]
  omega

/-- Prescribe a finitely supported tuple of integer ideal exponents by choosing local elements
of the prescribed valuation. Their valuation is one off the support, so they form a finite idele. -/
public theorem exists_finiteIdele_with_exponents (e : V → ℤ)
    (he : ∀ᶠ v in cofinite, e v = 0) :
    ∃ g : Fˣ, ∀ v : V, Valued.v ((g : F) v) = WithZero.exp (-(e v)) := by
  choose x hx using fun v : V ↦ valuedAdicCompletion_surjective K v (WithZero.exp (-(e v)))
  have hval : ∀ᶠ v in cofinite, Valued.v (x v) = 1 := by
    filter_upwards [he] with v hv
    simp [hx v, hv]
  let a : F := ⟨x, by
    filter_upwards [hval] with v hv
    exact (mem_adicCompletionIntegers (𝓞 K) K v).2 hv.le⟩
  have hunit : IsUnit a := FiniteAdeleRing.isUnit_iff.mpr ⟨fun v h ↦ by
    change x v = 0 at h
    simpa [h] using (hx v).symm, hval⟩
  obtain ⟨g, hg⟩ := hunit
  exact ⟨g, fun v ↦ hg ▸ hx v⟩

end Masullo
