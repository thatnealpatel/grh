module

public import Lemmas.SignedRowRecovery
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Close ratios give a short cofactor witness

This is the finite witness construction in consequence 2 of
`1d3802f7:.godel/alice/two-cofactor-strips.md` (lines 35–39), for the slope
lattice in `472c8e5d:.godel/alice/adaptive-complement-interval.md` (lines 15–19,
44–46). Both columns use the same list and cofactor pair: their inputs are the
same `x₁ = F₁ * h₁` and `x₂ = F₂ * h₂`. The witness construction only needs the
common inputs themselves, not their factorizations. The zero-quotient exclusion
separately uses the second factorization and coprimality of `x₁` with `F₂`.
This does not formalize the lattice count or the asymptotic price.

Owning check session: `01a208fa-736c-75e9-a336-a5cd6d3b0490`.
-/

namespace CloseRatiosShortWitness

private theorem output_sub_ratio_abs_le {q x y c d : ℕ} {δ : ℤ} {H : ℝ}
    (hd : 0 < d) (hgap : (c : ℤ) * x - (d : ℤ) * y = (q : ℤ) * δ)
    (hδ : |(δ : ℝ)| ≤ H) :
    |(y : ℝ) - (c : ℝ) / d * x| ≤ (q : ℝ) * H / d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hgapR : (c : ℝ) * x - (d : ℝ) * y = (q : ℝ) * δ := by exact_mod_cast hgap
  have herr : (y : ℝ) - (c : ℝ) / d * x = -((q : ℝ) * δ) / d := by
    apply (eq_div_iff hdR.ne').mpr
    rw [sub_mul, mul_right_comm ((c : ℝ) / d) (x : ℝ) (d : ℝ), div_mul_cancel₀ _ hdR.ne']
    linear_combination -hgapR
  rw [herr, abs_div, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q),
    abs_of_pos hdR]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg q)) hdR.le

/-- Two distinct positive primitive columns with close ratios on the same inputs
produce a difference of their actual outputs in the slope lattice. The first
coordinate is nonzero by recovery on the first row alone. The second rows are also
assumed to be actual positive rows with bounded signed gaps; the quotient identities
supply all the second-row information needed in the proof. -/
public theorem short_witness_of_close_ratios
    {q x₁ x₂ c d c' d' y₁ y₂ y₁' y₂' : ℕ} {δ₁ δ₂ δ₁' δ₂' Ty Ty' : ℤ} {H Z W η : ℝ}
    (hq : q.Prime) (hqx₁ : ¬ q ∣ x₁) (hx₁ : 0 < x₁) (_hx₂ : 0 < x₂)
    (hy₁ : 0 < y₁) (_hy₂ : 0 < y₂) (_hy₁' : 0 < y₁') (_hy₂' : 0 < y₂')
    (hc : 0 < c) (hd : 0 < d) (hc' : 0 < c') (hd' : 0 < d')
    (hcd : c.Coprime d) (hcd' : c'.Coprime d') (hcols : (c, d) ≠ (c', d'))
    (hdZ : (d : ℝ) ≤ Z) (hd'Z : (d' : ℝ) ≤ Z) (hcutoff : 4 * H * Z ≤ (x₁ : ℝ))
    (hgap₁ : (c : ℤ) * x₁ - (d : ℤ) * y₁ = (q : ℤ) * δ₁)
    (_hgap₂ : (c : ℤ) * x₂ - (d : ℤ) * y₂ = (q : ℤ) * δ₂)
    (hgap₁' : (c' : ℤ) * x₁ - (d' : ℤ) * y₁' = (q : ℤ) * δ₁')
    (_hgap₂' : (c' : ℤ) * x₂ - (d' : ℤ) * y₂' = (q : ℤ) * δ₂')
    (hδ₁ : |(δ₁ : ℝ)| ≤ H) (_hδ₂ : |(δ₂ : ℝ)| ≤ H)
    (hδ₁' : |(δ₁' : ℝ)| ≤ H) (_hδ₂' : |(δ₂' : ℝ)| ≤ H)
    (hTy : (x₁ : ℤ) * y₂ - (x₂ : ℤ) * y₁ = (q : ℤ) * Ty)
    (hTy' : (x₁ : ℤ) * y₂' - (x₂ : ℤ) * y₁' = (q : ℤ) * Ty')
    (hWTy : |(Ty : ℝ)| ≤ W) (hWTy' : |(Ty' : ℝ)| ≤ W)
    (hratio : |(c : ℝ) / d - (c' : ℝ) / d'| ≤ η) :
    let v₁ : ℤ := (y₁ : ℤ) - (y₁' : ℤ)
    let v₂ : ℤ := (y₂ : ℤ) - (y₂' : ℤ)
    let T : ℤ := ((x₁ : ℤ) * v₂ - (x₂ : ℤ) * v₁) / (q : ℤ)
    v₁ ≠ 0 ∧ (x₁ : ℤ) * v₂ - (x₂ : ℤ) * v₁ = (q : ℤ) * T ∧
      |(T : ℝ)| ≤ 2 * W ∧ |(v₁ : ℝ)| ≤ (x₁ : ℝ) * η + (q : ℝ) * H / d + (q : ℝ) * H / d' := by
  intro v₁ v₂ T
  have hv₁ : v₁ ≠ 0 := by
    intro hv
    have heq : y₁ = y₁' := by exact_mod_cast (sub_eq_zero.mp hv)
    subst y₁'
    obtain ⟨rfl, rfl⟩ := SignedRowRecovery.primitiveColumn_eq_of_signed_gaps
      hq hqx₁ hx₁ hy₁ hc hd hc' hd' hcd hcd' hdZ hd'Z hgap₁ hgap₁' hδ₁ hδ₁' hcutoff
    exact hcols rfl
  have hdet : (x₁ : ℤ) * v₂ - (x₂ : ℤ) * v₁ = (q : ℤ) * (Ty - Ty') := by
    dsimp only [v₁, v₂]
    linear_combination hTy - hTy'
  have hT : T = Ty - Ty' := Int.ediv_eq_of_eq_mul_right (by exact_mod_cast hq.ne_zero) hdet
  refine ⟨hv₁, ?_, ?_, ?_⟩
  · rwa [hT]
  · rw [hT, Int.cast_sub, two_mul]
    exact (abs_sub _ _).trans (add_le_add hWTy hWTy')
  · let r : ℝ := (c : ℝ) / d
    let r' : ℝ := (c' : ℝ) / d'
    let e : ℝ := (y₁ : ℝ) - r * x₁
    let e' : ℝ := (y₁' : ℝ) - r' * x₁
    have he : |e| ≤ (q : ℝ) * H / d := output_sub_ratio_abs_le hd hgap₁ hδ₁
    have he' : |e'| ≤ (q : ℝ) * H / d' := output_sub_ratio_abs_le hd' hgap₁' hδ₁'
    have hx : (0 : ℝ) ≤ x₁ := Nat.cast_nonneg x₁
    have hvR : (v₁ : ℝ) = (x₁ : ℝ) * (r - r') + e - e' := by
      dsimp only [v₁, e, e']
      push_cast
      ring
    calc
      |(v₁ : ℝ)| = |(x₁ : ℝ) * (r - r') + e - e'| := by rw [hvR]
      _ ≤ |(x₁ : ℝ) * (r - r')| + |e| + |e'| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (x₁ : ℝ) * |r - r'| + |e| + |e'| := by rw [abs_mul, abs_of_nonneg hx]
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hratio hx) he) he'

/-- At zero quotient, cancelling the label `F₂` by coprimality forces `x₁` to
divide `h₂ * v₁.natAbs`. Thus a nonzero first coordinate of width strictly
below `x₁ / h₂` excludes zero quotient. The width is stated after multiplication
by the positive `h₂`. -/
public theorem quotient_ne_zero_of_short_width {q x₁ F₂ h₂ : ℕ} {v₁ v₂ T : ℤ}
    (hh₂ : 0 < h₂) (hxF : x₁.Coprime F₂) (hv₁ : v₁ ≠ 0)
    (hdet : (x₁ : ℤ) * v₂ - ((F₂ : ℤ) * h₂) * v₁ = (q : ℤ) * T)
    (hshort : (h₂ : ℝ) * |(v₁ : ℝ)| < (x₁ : ℝ)) : T ≠ 0 := by
  intro hT
  rw [hT, mul_zero] at hdet
  have hcross : x₁ * v₂.natAbs = F₂ * h₂ * v₁.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      congrArg Int.natAbs (sub_eq_zero.mp hdet)
  have hdvd : x₁ ∣ h₂ * v₁.natAbs := hxF.dvd_of_dvd_mul_left
    ⟨v₂.natAbs, by rw [← mul_assoc, ← hcross]⟩
  have hle := Nat.le_of_dvd (Nat.mul_pos hh₂ (Int.natAbs_pos.mpr hv₁)) hdvd
  have hleR : (x₁ : ℝ) ≤ (h₂ : ℝ) * (v₁.natAbs : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_natAbs, Int.cast_abs] at hleR
  exact (not_lt_of_ge hleR) hshort

end CloseRatiosShortWitness
