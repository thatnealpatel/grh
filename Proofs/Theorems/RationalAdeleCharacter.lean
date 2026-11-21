module

public import Lemmas.RationalAdeleFiniteCharacter

import Theorems.RationalDiagonalPhases

/-!
# The standard additive character on the rational adeles

The positive real character pairs with the conjugates of the positive finite
characters. This repairs the sign for the rational lattice pairing of Examples
A.3.1.8 and A.3.1.11, pp. 558–559.
-/

open NumberField IsDedekindDomain
open scoped BigOperators ComplexConjugate

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
local notation "realEquiv" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The real coordinate of a rational adele. -/
public noncomputable def rationalAdeleReal (a : A) : ℝ := realEquiv (a.1 Rat.infinitePlace)

private theorem continuous_rationalAdeleReal : Continuous rationalAdeleReal :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    ((continuous_apply Rat.infinitePlace).comp continuous_fst)

/-- The real exponential times the restricted product of the conjugated finite characters. -/
public noncomputable def rationalAdeleAddChar : AddChar A ℂ where
  toFun a := Complex.exp (2 * Real.pi * Complex.I * (rationalAdeleReal a : ℂ)) *
    rationalFiniteAdeleAddChar a.2
  map_zero_eq_one' := by
    have h : rationalAdeleReal (0 : A) = 0 := map_zero realEquiv
    simp [h]
  map_add_eq_mul' a b := by
    have hreal : rationalAdeleReal (a + b) = rationalAdeleReal a + rationalAdeleReal b :=
      map_add realEquiv _ _
    simp only [hreal, Complex.ofReal_add, mul_add, Complex.exp_add]
    change _ * rationalFiniteAdeleAddChar (a.2 + b.2) = _
    rw [AddChar.map_add_eq_mul]
    ac_rfl

/-- Any finite set containing the nonintegral coordinates gives the same character value. -/
public theorem rationalAdeleAddChar_eq_prod (a : A) (S : Finset V)
    (hS : ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers ℚ) :
    rationalAdeleAddChar a = Complex.exp (2 * Real.pi * Complex.I * (rationalAdeleReal a : ℂ)) *
      (∏ v ∈ S, rationalLocalFiniteAddChar v (a.2 v)) := by
  change _ * rationalFiniteAdeleAddChar a.2 = _
  rw [rationalFiniteAdeleAddChar_eq_prod a.2 S hS]

/-- Continuity for the restricted-product topology, not the subspace topology of
    the unrestricted product. -/
public theorem continuous_rationalAdeleAddChar : Continuous (rationalAdeleAddChar : A → ℂ) :=
  (Complex.continuous_exp.comp <| continuous_const.mul <|
      Complex.continuous_ofReal.comp continuous_rationalAdeleReal).mul
    (continuous_rationalFiniteAdeleAddChar.comp continuous_snd)

/-- The character takes values on the complex unit circle. -/
public theorem norm_rationalAdeleAddChar (a : A) : ‖rationalAdeleAddChar a‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (rationalAdeleReal a : ℂ)) *
    rationalFiniteAdeleAddChar a.2‖ = 1
  rw [norm_mul, norm_rationalFiniteAdeleAddChar, mul_one, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The adelic character is trivial on every diagonal rational number. -/
public theorem rationalAdeleAddChar_algebraMap (r : ℚ) :
    rationalAdeleAddChar (algebraMap ℚ A r) = 1 := by
  classical
  let T : Finset Nat.Primes := (Nat.divisors r.den).preimage Subtype.val Subtype.val_injective.injOn
  have hT (p : Nat.Primes) : (p : ℕ) ∣ r.den → p ∈ T := by
    intro hp
    exact Finset.mem_preimage.mpr (Nat.mem_divisors.mpr ⟨hp, r.den_ne_zero⟩)
  have hreal : rationalAdeleReal (algebraMap ℚ A r) = (r : ℝ) := by
    rw [rationalAdeleReal, AdeleRing.algebraMap_fst_apply,
      ← InfinitePlace.Completion.WithAbs.ratCast_equiv _ (WithAbs.toAbs _ r), map_ratCast]
    rfl
  have hphase (v : V) : rationalLocalFiniteAddChar v ((algebraMap ℚ A r).2 v) =
      conj (rationalPadicPhase (pOf v) r) := rationalLocalFiniteAddChar_rat v r
  rw [rationalAdeleAddChar_eq_prod _ (T.map (pOf).symm.toEmbedding), hreal]
  · push_cast
    simp only [Finset.prod_map, Equiv.coe_toEmbedding, hphase, Equiv.apply_symm_apply]
    exact rationalDiagonal_phase_eq_one r T hT
  · intro v hv
    rw [← rationalLocalFiniteAddChar_eq_one_iff, hphase,
      ← map_one (starRingEnd ℂ),
      (show Function.Injective (conj : ℂ → ℂ) from star_injective).eq_iff,
      rationalPadicPhase_eq_one_iff]
    intro hd
    exact hv (Finset.mem_map.mpr ⟨pOf v, hT _ hd, (pOf).symm_apply_apply v⟩)

end Masullo
