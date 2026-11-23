module

public import Lemmas.ShiftedZetaZeros
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Lemmas.ZetaZeroHeightBudget

/-! # The displacement budget for the omitted rational divisor

Masullo's Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4), selects the
interior of the strip. The full explicit formula, p. 614, (B.4.2.2),
does not make that selection. This original argument supplies the tail
budget for suppressing the omitted Mellin samples in a short rational
test, conditional on a right-hand zero-density bound. Neither passage
supplies that bound or the suppression argument.
-/

namespace Masullo

/-- Distinct zeros omitted from the open strip of half-width `α`, above the
absolute height cutoff `T`. Both strip edges belong to the omitted set. -/
public abbrev omittedZetaTail (α T : ℝ) :=
  {ρ : criticalStripZetaZeros // α ≤ |(shiftedZetaZero ρ).re| ∧ T < |(ρ : ℂ).im|}

/-- A dyadic count with rate `q < 2` on the right at positive heights
supplies arbitrarily small displacement budgets after a finite split. -/
public theorem exists_omittedZetaTail_reciprocal_budget {α C q : ℝ}
    (hq₀ : 0 ≤ q) (hq₂ : q < 2)
    (hcount : ∀ (j : ℕ) (A : Finset criticalStripZetaZeros),
      (∀ ρ ∈ A, 1 / 2 + α ≤ (ρ : ℂ).re ∧ 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im < (2 : ℝ) ^ (j + 1)) →
      (A.card : ℝ) ≤ C * q ^ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧
      Summable (fun ρ : omittedZetaTail α T ↦ Real.pi / |(ρ.val : ℂ).im|) ∧
      (∑' ρ : omittedZetaTail α T, Real.pi / |(ρ.val : ℂ).im|) < ε := by
  classical
  let H (ρ : omittedZetaTail α 1) := |(ρ.val : ℂ).im|
  let W (ρ : omittedZetaTail α 1) := Real.pi / H ρ
  have hH (ρ : omittedZetaTail α 1) : 1 < H ρ := ρ.property.2
  -- Reflect and conjugate into the counted quadrant, then sum the dyadic blocks.
  have hW : Summable W := by
    apply summable_pi_div_height_of_dyadic_count H (fun ρ ↦ (hH ρ).le) hq₀ hq₂ (C := 4 * C)
    intro j A hA
    let e : omittedZetaTail α 1 ↪ criticalStripZetaZeros := Function.Embedding.subtype _
    rw [← Finset.card_map e]
    have hbound := zetaZero_card_abs_le_four_mul (hcount j) (A.map e) (by
      intro σ hσ
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hσ
      exact ⟨ρ.property.1, zero_lt_one.trans (hH ρ), hA ρ hρ⟩)
    simpa only [mul_assoc] using hbound
  -- A finite set accounts for all but the requested budget; put the height cutoff above it.
  obtain ⟨T, hT, hS, hsmall⟩ :=
    exists_summable_small_above_height H W (fun ρ ↦ (zero_lt_one.trans (hH ρ)).le) hW hε
  let e : omittedZetaTail α T ≃ {ρ : omittedZetaTail α 1 // T < H ρ} :=
    { toFun := fun ρ ↦ ⟨⟨ρ.val, ρ.property.1, hT.trans_lt ρ.property.2⟩, ρ.property.2⟩
      invFun := fun ρ ↦ ⟨ρ.val.val, ρ.val.property.1, ρ.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : {ρ : omittedZetaTail α 1 // T < H ρ} → ℝ := fun ρ ↦ W ρ.val
  have hs : Summable (f ∘ e) := hS.comp_injective e.injective
  have ht : (∑' ρ, (f ∘ e) ρ) < ε := (e.tsum_eq f).trans_lt hsmall
  exact ⟨T, hT, hs, ht⟩

end Masullo
