module

public import Theorems.FiniteCompletionDifferentScale
import Lemmas.FiniteCompletionCanonicalTraceDual
import Mathlib.RingTheory.FractionalIdeal.Extended

/-! # The global different in the actual finite completions

Definition A.3.1.2(3) and Lemma A.3.1.3, PDF p. 556, use the local
different norms and their global product. Definition A.3.2.2(2), PDF
p. 560, uses the square root of the local discriminant norm for the
multiplicative unit mass. The placewise comparison needed to link these
formulas is supplied here: Extend the global codifferent, identify the
result with the local trace dual, and invert. This identifies the
arithmetic scales, not the Haar measures. The source reading is
provisional (Markdown and numbered PDF text, not rendered pages).
-/

open IsDedekindDomain IsLocalRing NumberField Module
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "R" => ℤ_[p]
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "d" => differentIdeal R O
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "i" => algebraMap (𝓞 K) O

attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

-- The trace dual description identifies the extension of the inverse different.
private theorem extend_codifferent :
    FractionalIdeal.extendedHom F O ((D : FractionalIdeal (𝓞 K)⁰ K)⁻¹) =
      (d : FractionalIdeal O⁰ F)⁻¹ := by
  let h : (𝓞 K)⁰ ≤ Submonoid.comap i O⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have he : IsLocalization.map F i h = algebraMap K F := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K)
    intro a
    rw [IsLocalization.map_eq]
    exact HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (𝓞 K) K v a
  apply FractionalIdeal.coeToSubmodule_inj.mp
  change (((D : FractionalIdeal (𝓞 K)⁰ K)⁻¹).extended F h : Submodule O F) = _
  have hD := congrArg (fun S : Submodule (𝓞 K) K ↦ (S : Set K))
    (FractionalIdeal.coeToSubmodule_dual_one (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K))
  rw [FractionalIdeal.coeToSubmodule_extended_eq_span, he,
    coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  change Submodule.span O ((algebraMap K F) ''
    ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) : Set K)) = _
  rw [hD, ← finiteCompletion_traceDual_eq_inv_differentIdeal v]
  exact (finiteCompletion_traceDual_eq_span_globalCodifferent v).symm

/-- Extending the global different to the actual completion integers gives
exactly the different over the base `ℤ_[p]`. -/
public theorem map_globalDifferent_eq_finiteCompletionDifferent : Ideal.map i D = d := by
  apply FractionalIdeal.coeIdeal_injective (K := F)
  change ((Ideal.map i D : Ideal O) : FractionalIdeal O⁰ F) = (d : FractionalIdeal O⁰ F)
  rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := K) F O]
  -- Taking inverses turns the codifferent comparison into the different comparison.
  have h := congrArg Inv.inv (extend_codifferent v)
  rwa [← map_inv₀, inv_inv, inv_inv] at h

/-- The local different exponent is the multiplicity at `v` in the global different. -/
public theorem finiteCompletionDifferentExponent_eq_global_multiplicity :
    finiteCompletionDifferentExponent v = multiplicity v.asIdeal D := by
  symm
  apply (finiteCompletion_differentIdeal_eq_maximalIdeal_pow_iff v _).mp
  rw [← map_globalDifferent_eq_finiteCompletionDifferent v,
    map_finiteCompletion_ideal v D differentIdeal_ne_bot]

/-- The local discriminant norm, expressed using the global different. -/
public theorem finiteCompletion_norm_discr_eq_inv_globalDifferent_residueNorm_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R O) :
    ‖Algebra.discr R b‖ = ((v.asIdeal.absNorm ^ multiplicity v.asIdeal D : ℕ) : ℝ)⁻¹ := by
  rw [finiteCompletion_norm_discr_eq_inv_residueNorm_pow v b,
    finiteCompletionDifferentExponent_eq_global_multiplicity v]

end Masullo
