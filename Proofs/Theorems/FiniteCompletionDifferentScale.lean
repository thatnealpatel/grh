module

public import Lemmas.FiniteCompletionDifferentQuotient
public import Lemmas.FiniteCompletionPrimePow
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # The discriminant scale of a finite completion

Masullo's (A.3.1.2), PDF p. 556, specifies the additive mass in terms
of the local different and the local discriminant. His (A.3.2.2), p. 560,
uses the same discriminant scale for the multiplicative unit mass. We
prove the arithmetic comparison underlying these prescriptions, by
multiplying the trace dual by a generator of the local different and
counting the resulting prime-power quotient. This does not construct
Haar measures or identify the local different with the global one.
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
local notation "m" => maximalIdeal O
set_option quotPrecheck false in
local notation "D" => Submodule.traceDual R ℚ_[p] (1 : Submodule O F)
set_option quotPrecheck false in
local notation "D'" => (D).restrictScalars R

attribute [local instance] finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

/-- The exponent of the maximal ideal in the actual local different. -/
public noncomputable def finiteCompletionDifferentExponent : ℕ := (Order.coheight d).toNat

/-- The actual local different is the indicated power of the maximal ideal. -/
public theorem finiteCompletion_differentIdeal_eq_maximalIdeal_pow :
    d = m ^ finiteCompletionDifferentExponent v := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hd₀ : d ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hd₀ hπ
  have hd : d = m ^ n := by rw [hn, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [finiteCompletionDifferentExponent, hd, IsDiscreteValuationRing.coheight_pow_maximalIdeal]
  simp

/-- A power of the maximal ideal gives the different precisely at the local exponent. -/
public theorem finiteCompletion_differentIdeal_eq_maximalIdeal_pow_iff (n : ℕ) :
    d = m ^ n ↔ n = finiteCompletionDifferentExponent v := by
  constructor
  · intro h
    rw [finiteCompletionDifferentExponent, h, IsDiscreteValuationRing.coheight_pow_maximalIdeal]
    simp
  · rintro rfl
    exact finiteCompletion_differentIdeal_eq_maximalIdeal_pow v

/-- The integer quotient by the different has cardinality the residue-field
size to the local different exponent. -/
public theorem finiteCompletion_card_quotient_differentIdeal :
    Nat.card (O ⧸ d) = v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v := by
  let n := finiteCompletionDifferentExponent v
  rw [finiteCompletion_differentIdeal_eq_maximalIdeal_pow v,
    ← Nat.card_congr (finiteCompletionPrimePowQuotientEquiv v n).toEquiv,
    ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]

/-- The trace-dual index is the norm of the local different. -/
public theorem finiteCompletion_card_traceDual_quotient :
    Nat.card (D' ⧸ LinearMap.range (finiteCompletionIntegersToTraceDual v)) =
      v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v := by
  let a := Submodule.IsPrincipal.generator d
  rw [Nat.card_congr (finiteCompletionTraceDualQuotientEquiv v a
    (Ideal.span_singleton_generator d)).toEquiv, finiteCompletion_card_quotient_differentIdeal]

/-- The base p-adic discriminant norm is the reciprocal of the norm of the
local different, as used in the local normalization in (A.3.1.2). -/
public theorem finiteCompletion_norm_discr_eq_inv_residueNorm_pow {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R O) :
    ‖Algebra.discr R b‖ = ((v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) : ℝ)⁻¹ := by
  rw [finiteCompletion_norm_discr_eq_inv_card_traceDual_quotient v b,
    finiteCompletion_card_traceDual_quotient v]

end Masullo
