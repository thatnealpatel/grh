module

public import Lemmas.BalancedDivisorMultiplicity
import Mathlib.Logic.Equiv.Option

/-! # Balanced orderings with a marked positive slot

Sources: `0e672a90:.godel/bob/separated-signed-tuples.md`, lines 41–69
(unmarked multiplicity and the omitted slot); `6fe747e1:.godel/bob/detection-radius.md`,
lines 5 and 33 (corrected separation radius and arithmetic handoff);
`d5aca03a:.godel/bob/rounded-slot-frequency-band.md`, lines 5–25 (fixed positive slot).
Owning check session: `01a20938-230d-71be-9082-772ff1e0dec6`.

For a fixed support `I` and plus set `B`, fixing the start in one positive slot
leaves all negative orders and only the orders of the remaining positive starts.
The score may depend on `I`, `B`, and the marked start, and need not agree across
marked starts. This is only the finite multiplicity identity. It does not establish
slot recovery, sign-swap invariance, or descent of an arbitrary tuple gate to the
marked start. In particular the small-window recovery used in
`e018142:.godel/bob/windowed-harmonic-witness.md`, lines 5–11, is separate.
-/

open scoped BigOperators

namespace Masullo.BalancedDivisorMultiplicity

/-- Identify the marked input with `none`, then restrict the bijection to its
unmarked inputs and outputs. The inverse reinserts the prescribed pair. -/
private def markedEquivCompl {α β : Type*} [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    {e : α ≃ β // e a = b} ≃ ({x : α // x ≠ a} ≃ {y : β // y ≠ b}) :=
  ((Equiv.equivCongr (Equiv.optionSubtypeNe a).symm (Equiv.refl β)).subtypeEquiv
    (q := fun e ↦ e none = b) fun e ↦ by
      change e a = b ↔ e (Equiv.optionSubtypeNe a none) = b
      rw [Equiv.optionSubtypeNe_none]).trans (Equiv.optionSubtype b)

private def markedOrderingEquiv {h : ℕ} {I B : Finset ℕ} (i : Fin h) (p : ↥B) :
    {o : Ordering h I B // o.1 i = p} ≃
      ({j : Fin h // j ≠ i} ≃ {q : ↥B // q ≠ p}) × (Fin h ≃ ↥(I \ B)) :=
  Equiv.prodSubtypeFstEquivSubtypeProd.trans
    (Equiv.prodCongr (markedEquivCompl i p) (Equiv.refl _))

private theorem card_compl_point {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl (· = a), Fintype.card_subtype_eq]

/-- Every positive start has exactly `(h - 1)! * h!` orderings assigning it to
slot `i`: the first factorial counts the remaining positive orders, and the
second counts the unrestricted negative orders. -/
public theorem card_ordering_marked_fiber {h : ℕ} {I B : Finset ℕ}
    (hBI : B ⊆ I) (hI : I.card = 2 * h) (hB : B.card = h) (i : Fin h) (p : ↥B) :
    Fintype.card {o : Ordering h I B // o.1 i = p} = (h - 1).factorial * h.factorial := by
  have hC : (I \ B).card = h := by
    rw [Finset.card_sdiff_of_subset hBI, hI, hB]
    omega
  let ePlus : {j : Fin h // j ≠ i} ≃ {q : ↥B // q ≠ p} := Fintype.equivOfCardEq (by
    rw [card_compl_point, card_compl_point, Fintype.card_fin, Fintype.card_coe, hB])
  let eMinus : Fin h ≃ ↥(I \ B) := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, hC])
  rw [Fintype.card_congr (markedOrderingEquiv (I := I) i p), Fintype.card_prod,
    Fintype.card_equiv ePlus, Fintype.card_equiv eMinus, card_compl_point, Fintype.card_fin]

/-- The ordered contribution with an arbitrary real score of the designated
positive start. The ordered weight is constant on all orderings; the score is
constant only within each evaluation fiber. -/
public theorem sum_orderedWeight_mul_markedScore {h : ℕ} {I B : Finset ℕ}
    (hBI : B ⊆ I) (hI : I.card = 2 * h) (hB : B.card = h) (i : Fin h) (w F : ℕ → ℝ) :
    (∑ o : Ordering h I B, orderedWeight w o * F (o.1 i : ℕ)) =
      ((h - 1).factorial : ℝ) * (h.factorial : ℝ) * (∏ p ∈ I, w p) * ∑ p ∈ B, F p := by
  let mark (o : Ordering h I B) : ↥B := o.1 i
  calc
    _ = ∑ p : ↥B, ∑ o : {o : Ordering h I B // mark o = p},
        orderedWeight w o.val * F (o.val.1 i : ℕ) :=
      (Fintype.sum_fiberwise mark (fun o ↦ orderedWeight w o * F (o.1 i : ℕ))).symm
    _ = ∑ p : ↥B, (((h - 1).factorial : ℝ) * (h.factorial : ℝ) * (∏ q ∈ I, w q)) * F p := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = ∑ _o : {o : Ordering h I B // o.1 i = p}, (∏ q ∈ I, w q) * F p := by
          apply Finset.sum_congr rfl
          intro o _
          have ho : o.val.1 i = p := o.property
          rw [orderedWeight_eq hBI, ho]
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, card_ordering_marked_fiber hBI hI hB i p,
            nsmul_eq_mul, Nat.cast_mul, mul_assoc]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.univ_eq_attach, Finset.sum_attach]

end Masullo.BalancedDivisorMultiplicity
