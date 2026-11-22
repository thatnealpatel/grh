module

public import Lemmas.FiniteCompletionDiagonalTrace
public import Lemmas.RationalPadicPhase
import Theorems.RationalDiagonalPhases

/-! # The diagonal phase for the corrected number-field pairing

Masullo specifies the trace pullback in (A.3.1.7), p. 558, and the local
trace character in Example A.3.1.10 there. Examples A.3.1.5–8, pp. 557–558,
use a positive real character and a positive finite character. For the
pairing needed in Theorem 2.2.3.2, p. 82, we retain the positive
Archimedean phase and conjugate the finite factors in the character.
The Fourier kernel conjugates the character, so its finite factors are
positive. See `.godel/obligations/finite-diagonal-phase.md` for the reading
status and the sign check. Only diagonal compatibility is proved here.
-/

open IsDedekindDomain NumberField
open scoped BigOperators ComplexConjugate

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The positive phases over `p` multiply to the positive rational
`p`-adic phase of `Tr_{K/ℚ}(x)`. -/
public theorem finiteCompletionDiagonalPhase_prod_overPrime (p : Nat.Primes) (x : K) :
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    letI := finiteCompletionOverPrimeFintype (K := K) (p : ℕ)
    (∏ v : {v : HeightOneSpectrum (𝓞 K) // v.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))},
      finiteCompletionDiagonalPhase v.1 x) = rationalPadicPhase p (Algebra.trace ℚ K x) := by
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  let V := {v : HeightOneSpectrum (𝓞 K) // v.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))}
  let : Fintype V := finiteCompletionOverPrimeFintype (K := K) (p : ℕ)
  simp_rw [finiteCompletionDiagonalPhase_eq_overPrime (p : ℕ)]
  -- Evaluate the character on the trace sum by its additive character law.
  change (∏ v : V, (padicStdAddChar (p : ℕ)).toMonoidHom (Multiplicative.ofAdd _)) = _
  rw [← map_prod, ← ofAdd_sum, AddChar.toMonoidHom_apply]
  change padicStdAddChar (p : ℕ) (∑ v : V,
    @Algebra.trace ℚ_[(p : ℕ)] (v.1.adicCompletion K) _ _
      (finiteCompletionOverPrimeFieldAlgebra (p : ℕ) v)
      (algebraMap K (v.1.adicCompletion K) x)) = _
  rw [finiteCompletion_sum_trace_overPrime (p : ℕ) x]
  exact (rationalPadicPhase_apply p _).symm

-- Include both the base primes of the nontrivial local factors and the
-- denominator primes of the global trace. No character identity is used
-- to infer finite support or to restrict the outer product.
private theorem exists_diagonalPhase_grouped (x : K) :
    ∃ T : Finset Nat.Primes,
      (∀ p : Nat.Primes, (p : ℕ) ∣ (Algebra.trace ℚ K x).den → p ∈ T) ∧
      (∏ᶠ v, finiteCompletionDiagonalPhase v x) =
        ∏ p ∈ T, rationalPadicPhase p (Algebra.trace ℚ K x) := by
  classical
  let r := Algebra.trace ℚ K x
  let hf := finiteCompletionDiagonalPhase_hasFiniteMulSupport x
  let D : Finset Nat.Primes := (Nat.divisors r.den).preimage Subtype.val Subtype.val_injective.injOn
  let T := hf.toFinset.image finiteCompletionBasePrime ∪ D
  refine ⟨T, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_union_right _ (Finset.mem_preimage.mpr (Nat.mem_divisors.mpr ⟨hp, r.den_ne_zero⟩))
  · rw [finprod_finiteCompletionDiagonalPhase_group x T]
    · exact Finset.prod_congr rfl fun p _ ↦ finiteCompletionDiagonalPhase_prod_overPrime p x
    · intro v hv
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hf.mem_toFinset.mpr hv, rfl⟩)

/-- The product of the positive finite trace characters on the diagonal
is the positive Archimedean phase of the rational trace. The product has
finite multiplicative support by `finiteCompletionDiagonalPhase_hasFiniteMulSupport`. -/
public theorem finiteCompletionDiagonalPhase_finprod (x : K) :
    (∏ᶠ v, finiteCompletionDiagonalPhase v x) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K x : ℂ)) := by
  obtain ⟨T, hT, hgroup⟩ := exists_diagonalPhase_grouped x
  rw [hgroup]
  exact prod_rationalPadicPhase (Algebra.trace ℚ K x) T hT

private theorem finprod_conj_diagonalPhase (x : K) :
    (∏ᶠ v, conj (finiteCompletionDiagonalPhase v x)) =
      conj (∏ᶠ v, finiteCompletionDiagonalPhase v x) :=
  (map_finprod (starRingEnd ℂ) (finiteCompletionDiagonalPhase_hasFiniteMulSupport x)).symm

/-- With the corrected finite character (the conjugates of the positive
finite trace phases), its product with the positive Archimedean phase
is one on every diagonal element. -/
public theorem numberFieldDiagonal_phase_eq_one (x : K) :
    Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K x : ℂ)) *
      (∏ᶠ v, conj (finiteCompletionDiagonalPhase v x)) = 1 := by
  obtain ⟨T, hT, hgroup⟩ := exists_diagonalPhase_grouped x
  rw [finprod_conj_diagonalPhase, hgroup, map_prod]
  exact rationalDiagonal_phase_eq_one (Algebra.trace ℚ K x) T hT

/-- Conjugating the corrected character for the Fourier kernel makes its
finite factor the positive trace phase product, not its conjugate. -/
public theorem numberFieldDiagonal_fourier_finite_phase (x : K) :
    conj (∏ᶠ v, conj (finiteCompletionDiagonalPhase v x)) =
      ∏ᶠ v, finiteCompletionDiagonalPhase v x := by
  rw [finprod_conj_diagonalPhase, Complex.conj_conj]

end Masullo
