module

public import Lemmas.FiniteCompletionConductorChar
public import Lemmas.FiniteCompletionPrimePow
public import Lemmas.FiniteRingGaussSum

/-! # The Gauss transform at a positive finite conductor

For a finite place with different exponent `d`, the positive trace phase at
frequency `π⁻⁽ᵈ⁺ⁿ⁾` and a unit character of exact conductor `n > 0` give a
Gauss transform on the quotient of completion integers by `πⁿ`. This is a
finite-sum statement, with no choice of Haar measure.
-/

open IsDedekindDomain IsLocalRing NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => v.adicCompletionIntegers K
local notation "Q" n:max => (O ⧸ maximalIdeal O ^ n)

/-- The inverse-character Gauss transform on the conductor quotient, shifted by a residue. -/
@[expose] public noncomputable def finiteCompletionConductorGaussSum
    (π : O) (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) (χ : Oˣ →* ℂˣ)
    (hχ : (finiteCompletionUnitReduction v n).ker ≤ χ.ker) (b : Q n) : ℂ :=
  letI := finite_finiteCompletionPrimePowQuotient v n
  letI := Fintype.ofFinite (Q n)
  gaussSum (finiteCompletionConductorMulChar v hn χ hχ)⁻¹
    ((finiteCompletionConductorAddChar v π hπ n).mulShift b)

/-- The finite Gauss transform of the inverse character has multiplicative
covariance, squared modulus `#(O/πⁿ)` at `1`, and support precisely the units.
Both character hypotheses of the general finite-ring lemma are discharged
by the different and the minimality of the conductor. -/
public theorem finiteCompletionConductorGaussSum_profile
    (π : O) (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) (χ : Oˣ →* ℂˣ)
    (hχ : IsFiniteCompletionConductor v χ n) :
    let G := finiteCompletionConductorGaussSum v π hπ hn χ hχ.1
    (∀ b : Q n, G b = finiteCompletionConductorMulChar v hn χ hχ.1 b * G 1) ∧
    ‖G 1‖ ^ 2 = (Nat.card (Q n) : ℝ) ∧
    (∀ b : Q n, G b ≠ 0 ↔ IsUnit b) := by
  let := finite_finiteCompletionPrimePowQuotient v n
  let := Fintype.ofFinite (Q n)
  have h := finiteRingGaussSum_profile (finiteCompletionConductorMulChar v hn χ hχ.1)
    (finiteCompletionConductorAddChar v π hπ n)
    (finiteCompletionConductorAddChar_isPrimitive v π hπ n)
    (finiteCompletionConductorMulChar_nonunit_stabilizer v hn χ hχ)
  unfold finiteCompletionConductorGaussSum
  simpa only [AddChar.mulShift_one, Nat.card_eq_fintype_card] using h

end Masullo
