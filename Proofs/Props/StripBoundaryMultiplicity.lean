module

public import Lemmas.IdeleClassStripDivisor
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Pointwise boundary multiplicity in the centered Hecke strip

In Masullo's *The Music of the Primes*, p. 472, (10.4.3.38) repeats the
boundary and interior rules of p. 446, (10.2.2.5)–(10.2.2.6). The bracket
in the repeated rule (10.3.2.4), p. 454, is explicitly the greatest
nonnegative integer not exceeding its argument. We compare that rule as
written, not a boundary Sobolev-jet admissibility criterion. The enumeration
`0 ≤ m ≤ N - 1` is an integer inequality and gives `N` terms, even for `N = 0`.

For the comparison to `OpenStripHeckeZero`, we use the manuscript's strip
center `a = 1/2` in the repository's norm-twist coordinates, so `b` is the
real part of the unshifted exponent minus `1/2`. Both rules are applied to
the same finite positive order, namely `ideleClassHeckeOrder` for the index
comparison. This tests the counting rule, not an identification of the
manuscript's analytic zero divisor with the completed Hecke divisor. It
asserts neither the existence of edge zeros nor a comparison of sums.
-/

open NumberField

namespace Masullo

/-- The boundary cap in (10.4.3.38), for the manuscript's `s > 1`. -/
public noncomputable def manuscriptStripBoundaryCap (s : ℝ) : ℕ :=
  ⌊(s - 1) / 2 + 1⌋₊

public theorem manuscriptStripBoundaryCap_pos {s : ℝ} (hs : 1 < s) :
    0 < manuscriptStripBoundaryCap s :=
  Nat.floor_pos.mpr (le_add_of_nonneg_left (div_nonneg (sub_nonneg.mpr hs.le) (by norm_num)))

/-- The pointwise rule of (10.4.3.38) with a natural-valued cap. Outside the
closed strip there is no term. When `α = 0` the two edges are one point. -/
public noncomputable def manuscriptStripMultiplicity (α b : ℝ) (n cap : ℕ) : ℕ :=
  if |b| = α then min n cap else if |b| < α then n else 0

/-- Away from the edges, both counting rules give the full order in the
interior and zero outside the strip. -/
public theorem manuscriptStripMultiplicity_eq_open_of_ne {α b : ℝ} (hb : |b| ≠ α)
    (n cap : ℕ) :
    manuscriptStripMultiplicity α b n cap = (if |b| < α then n else 0) := by
  simp [manuscriptStripMultiplicity, hb]

/-- The exact mismatch locus, including the zero-order and zero-cap cases.
For `0 ≤ α`, `abs_eq` identifies the edge condition with `b = α ∨ b = -α`. -/
public theorem manuscriptStripMultiplicity_ne_open_iff {α b : ℝ} {n cap : ℕ} :
    manuscriptStripMultiplicity α b n cap ≠ (if |b| < α then n else 0) ↔
      |b| = α ∧ 0 < n ∧ 0 < cap := by
  by_cases hb : |b| = α
  · simp only [manuscriptStripMultiplicity, hb, ite_true, lt_self_iff_false, ite_false, true_and]
    rw [← Nat.pos_iff_ne_zero, lt_min_iff]
  · simp [manuscriptStripMultiplicity_eq_open_of_ne hb, hb]

variable {K : Type*} [Field K] [NumberField K]

local notation "Ω" => HeckeCharacter (𝓞 K) K

/-- For a character of finite positive order, the actual index has an entry
exactly in the strict interior. The entry is unique by `character_injective`. -/
public theorem exists_openStripHeckeZero_iff {α : ℝ} {χ : Ω} {n : ℕ}
    (hn : 0 < n) (hord : ideleClassHeckeOrder χ = ((n : ℤ) : WithTop ℤ)) :
    (∃ ρ : OpenStripHeckeZero K α, ρ.character = χ) ↔
      |(ideleClassNormExponent χ).re - 1 / 2| < α := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ρ.re_mem_strip
  · intro hb
    exact ⟨⟨χ, hb, ⟨n, hn, hord⟩⟩, rfl⟩

/-- The pointwise multiplicity read from the actual open-strip index: the
order of its unique entry over `χ`, or zero when there is no entry. -/
public noncomputable def openStripHeckeMultiplicity (α : ℝ) (χ : Ω) : ℕ := by
  classical
  exact if h : ∃ ρ : OpenStripHeckeZero K α, ρ.character = χ then h.choose.order else 0

/-- The actual index counts the full order in the strict interior and no
terms elsewhere, including either edge. -/
public theorem openStripHeckeMultiplicity_eq {α : ℝ} {χ : Ω} {n : ℕ}
    (hn : 0 < n) (hord : ideleClassHeckeOrder χ = ((n : ℤ) : WithTop ℤ)) :
    openStripHeckeMultiplicity α χ =
      (if |(ideleClassNormExponent χ).re - 1 / 2| < α then n else 0) := by
  classical
  have hmem := exists_openStripHeckeZero_iff (α := α) hn hord
  unfold openStripHeckeMultiplicity
  by_cases h : ∃ ρ : OpenStripHeckeZero K α, ρ.character = χ
  · rw [dite_eq_left h, ite_eq_left (hmem.mp h)]
    have ho := h.choose.heckeOrder_eq
    rw [h.choose_spec, hord] at ho
    exact Int.ofNat_inj.mp (WithTop.coe_inj.mp ho.symm)
  · rw [dite_eq_right h, ite_eq_right (fun hb ↦ h (hmem.mpr hb))]

/-- At every finite positive-order Hecke character, the rule with a positive
cap differs from the actual open-strip count exactly on the boundary. There
it counts `min n cap` terms while the index has no entry. -/
public theorem manuscriptStripMultiplicity_ne_openStripHeckeMultiplicity_iff
    {α : ℝ} {χ : Ω} {n cap : ℕ} (hn : 0 < n) (hcap : 0 < cap)
    (hord : ideleClassHeckeOrder χ = ((n : ℤ) : WithTop ℤ)) :
    manuscriptStripMultiplicity α ((ideleClassNormExponent χ).re - 1 / 2) n cap ≠
      openStripHeckeMultiplicity α χ ↔ |(ideleClassNormExponent χ).re - 1 / 2| = α := by
  rw [openStripHeckeMultiplicity_eq hn hord, manuscriptStripMultiplicity_ne_open_iff]
  simp [hn, hcap]

/-- The pointwise mismatch for the literal floor cap in (10.4.3.38). -/
public theorem manuscriptStripMultiplicity_floor_ne_openStripHeckeMultiplicity_iff
    {α s : ℝ} {χ : Ω} {n : ℕ} (hα : 0 ≤ α) (hs : 1 < s) (hn : 0 < n)
    (hord : ideleClassHeckeOrder χ = ((n : ℤ) : WithTop ℤ)) :
    manuscriptStripMultiplicity α ((ideleClassNormExponent χ).re - 1 / 2) n
        (manuscriptStripBoundaryCap s) ≠ openStripHeckeMultiplicity α χ ↔
      (ideleClassNormExponent χ).re - 1 / 2 = α ∨
        (ideleClassNormExponent χ).re - 1 / 2 = -α :=
  (manuscriptStripMultiplicity_ne_openStripHeckeMultiplicity_iff hn
    (manuscriptStripBoundaryCap_pos hs) hord).trans (abs_eq hα)

end Masullo
