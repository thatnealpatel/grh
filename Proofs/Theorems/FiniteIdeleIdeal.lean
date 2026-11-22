module

public import Lemmas.FiniteIdeleIdealCoordinates

/-! # The fractional ideal of a finite idele

Masullo, Proposition A.2.3.9, (A.2.3.23), PDF p. 552, states the exact sequence
with the ideal class group, not the formula for its map. We construct its
algebraic lift before quotienting: Multiply the finite prime ideals with the
exponents of the local idele coordinates. The image of a diagonal is principal,
and the kernel before quotienting is the product of the local integral units.
This module does not yet assert the quotient or topological exactness.
-/

open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped Classical nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K

private noncomputable def exponent (g : Fˣ) (v : V) : ℤ :=
  -WithZero.log (Valued.v ((g : F) v))

private theorem exponent_eventually_zero (g : Fˣ) : ∀ᶠ v in cofinite, exponent g v = 0 := by
  have h : ∀ᶠ v : V in cofinite, Valued.v ((g : F) v) = 1 :=
    eventually_cofinite.mpr (FiniteAdeleRing.hasFiniteMulSupport_valued g)
  filter_upwards [h] with v hv
  simp [exponent, hv]

private noncomputable def idealOf (g : Fˣ) : Jˣ :=
  Units.mk0 (∏ᶠ v : V, (v.asIdeal : J) ^ exponent g v) <|
    finprod_ne_zero fun v ↦ zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

private theorem count_idealOf (g : Fˣ) (v : V) :
    FractionalIdeal.count K v (idealOf g : J) = exponent g v :=
  FractionalIdeal.count_finprod K v _ (exponent_eventually_zero g)

/-- Multiply the prime ideals with exponents given by the local discrete valuations
(negating Mathlib's multiplicative valuation logarithm). -/
public noncomputable def finiteIdeleIdeal (K : Type*) [Field K] [NumberField K] :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun := idealOf
  map_one' := by
    apply fractionalIdeal_units_ext_count
    intro v
    rw [count_idealOf, Units.val_one, FractionalIdeal.count_one]
    change -WithZero.log (Valued.v (1 : v.adicCompletion K)) = 0
    simp
  map_mul' g h := by
    apply fractionalIdeal_units_ext_count
    intro v
    rw [Units.val_mul, FractionalIdeal.count_mul _ _ (idealOf g).ne_zero (idealOf h).ne_zero]
    simp only [count_idealOf]
    change -WithZero.log (Valued.v (g.val v * h.val v)) = exponent g v + exponent h v
    rw [map_mul,
      WithZero.log_mul (finiteIdele_valuation_ne_zero g v) (finiteIdele_valuation_ne_zero h v)]
    simp [exponent, neg_add_rev, add_comm]

public theorem count_finiteIdeleIdeal (g : Fˣ) (v : V) :
    FractionalIdeal.count K v (finiteIdeleIdeal K g : J) =
      -WithZero.log (Valued.v ((g : F) v)) :=
  count_idealOf g v

/-- The fractional ideal of the diagonal finite idele is the principal ideal `(a)`. -/
public theorem finiteIdeleIdeal_unitEmbedding (a : Kˣ) :
    (finiteIdeleIdeal K (FiniteAdeleRing.unitEmbedding (𝓞 K) K a) : J) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
  let j : Jˣ := Units.mk0 _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
  change _ = (j : J)
  congr 1
  apply fractionalIdeal_units_ext_count
  intro v
  rw [count_finiteIdeleIdeal, FiniteAdeleRing.unitEmbedding_apply,
    FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']
  exact (count_spanSingleton_eq_neg_log_valuation (a : K) a.ne_zero v).symm

/-- The finite integral-unit condition, expressed by valuation one at every place. -/
public theorem finiteIdeleIdeal_eq_one_iff (g : Fˣ) :
    finiteIdeleIdeal K g = 1 ↔ ∀ v : V, Valued.v ((g : F) v) = 1 := by
  constructor
  · intro hg v
    have h := count_finiteIdeleIdeal g v
    rw [hg, Units.val_one, FractionalIdeal.count_one, eq_comm, neg_eq_zero] at h
    rw [← WithZero.exp_log (finiteIdele_valuation_ne_zero g v), h, WithZero.exp_zero]
  · intro hg
    apply fractionalIdeal_units_ext_count
    intro v
    simp [count_finiteIdeleIdeal, hg v, FractionalIdeal.count_one]

/-- Every nonzero fractional ideal has a finite-idele representative. -/
public theorem finiteIdeleIdeal_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (finiteIdeleIdeal K) := by
  intro j
  let e (v : HeightOneSpectrum (𝓞 K)) := FractionalIdeal.count K v (j.val)
  obtain ⟨g, hg⟩ := exists_finiteIdele_with_exponents e (FractionalIdeal.finite_factors j.val)
  refine ⟨g, fractionalIdeal_units_ext_count (fun v ↦ ?_)⟩
  rw [count_finiteIdeleIdeal, hg v, WithZero.log_exp, neg_neg]

end Masullo
