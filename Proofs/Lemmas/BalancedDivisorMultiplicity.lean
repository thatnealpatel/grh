module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring

/-! # The labeled fiber of a balanced endpoint selection

Source: `0e672a90:.godel/bob/separated-signed-tuples.md`, lines 41–45 and
59–65 (multiplicity and constrained divisor count). Use the corrected support
radius `r = (log X)^2` from `6fe747e1:.godel/bob/detection-radius.md`, lines
5 and 33. Owning check session: `01a208fa-736c-75e9-a336-a5cd6d3b0490`.

This is the finite step at one shift, on one support `I` of size `2h` and one
plus set `B ⊆ I` of size `h`. If `I` is separated at the corrected radius,
every tuple in the fiber is separated there: it uses each element of `I` exactly
once. The identity itself needs only distinct starts in the support and positivity
of the starts, not primality or an endpoint spacing bound. It proves neither
privacy at the old radius nor any analytic estimate.
-/

open scoped BigOperators

namespace Masullo.BalancedDivisorMultiplicity

/-- Bijections from the plus and minus slots onto their respective sets of starts. -/
public abbrev Ordering (h : ℕ) (I B : Finset ℕ) : Type :=
  (Fin h ≃ ↥B) × (Fin h ≃ ↥(I \ B))

/-- The unbundled labeled tuples with no repetitions within each sign and with the
specified sets of starts. When `B ⊆ I`, the ranges partition `I`, so there are
also no repetitions across signs. -/
public abbrev TupleFiber (h : ℕ) (I B : Finset ℕ) : Type :=
  {a : (Fin h → ℕ) × (Fin h → ℕ) //
    Function.Injective a.1 ∧ Set.range a.1 = (B : Set ℕ) ∧
    Function.Injective a.2 ∧ Set.range a.2 = ((I \ B : Finset ℕ) : Set ℕ)}

private theorem slot_range {h : ℕ} {S : Finset ℕ} (e : Fin h ≃ ↥S) :
    Set.range (fun i ↦ (e i : ℕ)) = (S : Set ℕ) := by
  ext p
  change (∃ i, (e i : ℕ) = p) ↔ p ∈ S
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hp
    exact ⟨e.symm ⟨p, hp⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)⟩

private noncomputable def slotEquiv {h : ℕ} {S : Finset ℕ} (a : Fin h → ℕ)
    (ha : Function.Injective a) (hS : Set.range a = (S : Set ℕ)) : Fin h ≃ ↥S :=
  Equiv.ofBijective (fun i ↦ ⟨a i, show a i ∈ (S : Set ℕ) from hS ▸ ⟨i, rfl⟩⟩)
    ⟨fun _ _ he ↦ ha (congrArg Subtype.val he), fun ⟨p, hp⟩ ↦ by
      have hp' : p ∈ Set.range a := hS.symm ▸ (show p ∈ (S : Set ℕ) from hp)
      obtain ⟨i, hi⟩ := hp'
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Forgetting the codomain subtypes gives precisely the labeled tuple fiber;
restricting the codomains recovers the two bijections without relabeling any slot. -/
public noncomputable def orderingEquivTuples (h : ℕ) (I B : Finset ℕ) :
    Ordering h I B ≃ TupleFiber h I B where
  toFun o := ⟨⟨fun i ↦ (o.1 i : ℕ), fun i ↦ (o.2 i : ℕ)⟩,
    fun _ _ he ↦ o.1.injective (Subtype.ext he), slot_range o.1,
    fun _ _ he ↦ o.2.injective (Subtype.ext he), slot_range o.2⟩
  invFun a := ⟨slotEquiv a.val.1 a.property.1 a.property.2.1,
    slotEquiv a.val.2 a.property.2.2.1 a.property.2.2.2⟩
  left_inv o := by
    apply Prod.ext
    · apply Equiv.ext
      intro i
      rfl
    · apply Equiv.ext
      intro i
      rfl
  right_inv _ := rfl

/-- Balance and support size give `h!` orders on each side, including `h = 0`. -/
public theorem card_ordering {h : ℕ} {I B : Finset ℕ}
    (hBI : B ⊆ I) (hI : I.card = 2 * h) (hB : B.card = h) :
    Fintype.card (Ordering h I B) = h.factorial ^ 2 := by
  have hC : (I \ B).card = h := by
    rw [Finset.card_sdiff_of_subset hBI, hI, hB]
    omega
  let eB : Fin h ≃ ↥B := (Fintype.equivFinOfCardEq ((Fintype.card_coe B).trans hB)).symm
  let eC : Fin h ≃ ↥(I \ B) :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe (I \ B)).trans hC)).symm
  change Fintype.card ((Fin h ≃ ↥B) × (Fin h ≃ ↥(I \ B))) = h.factorial ^ 2
  rw [Fintype.card_prod, Fintype.card_equiv eB, Fintype.card_equiv eC, Fintype.card_fin, pow_two]

/-- The product of both endpoints of every start, `P_I`. -/
@[expose] public noncomputable def pairProduct (d : ℕ) (I : Finset ℕ) : ℝ :=
  ∏ p ∈ I, (p : ℝ) * ((p + d : ℕ) : ℝ)

/-- The divisor `v_B`: use the shifted endpoint on `B` and the start on `I \ B`. -/
@[expose] public noncomputable def selectedProduct (d : ℕ) (I B : Finset ℕ) : ℝ :=
  (∏ p ∈ B, ((p + d : ℕ) : ℝ)) * (∏ p ∈ I \ B, (p : ℝ))

/-- The product of the endpoints not used in `v_B`. -/
@[expose] public noncomputable def unselectedProduct (d : ℕ) (I B : Finset ℕ) : ℝ :=
  (∏ p ∈ B, (p : ℝ)) * (∏ p ∈ I \ B, ((p + d : ℕ) : ℝ))

/-- Product of the original per-start weights in the labeled slots. -/
@[expose] public noncomputable def orderedWeight {h : ℕ} {I B : Finset ℕ}
    (w : ℕ → ℝ) (o : Ordering h I B) : ℝ :=
  (∏ i, w (o.1 i)) * (∏ i, w (o.2 i))

/-- The source label `λ_p = log(1 + d/p)`. -/
@[expose] public noncomputable def logLabel (d p : ℕ) : ℝ :=
  Real.log (1 + (d : ℝ) / (p : ℝ))

/-- Sum of the plus labels minus the sum of the minus labels, in slot order. -/
@[expose] public noncomputable def signedFrequency {h : ℕ} {I B : Finset ℕ}
    (d : ℕ) (o : Ordering h I B) : ℝ :=
  (∑ i, logLabel d (o.1 i)) - (∑ i, logLabel d (o.2 i))

private theorem prod_slots {h : ℕ} {S : Finset ℕ} (e : Fin h ≃ ↥S) (f : ℕ → ℝ) :
    (∏ i, f (e i)) = ∏ p ∈ S, f p :=
  (e.prod_comp fun p : ↥S ↦ f p).trans (Finset.prod_attach S f)

private theorem sum_slots {h : ℕ} {S : Finset ℕ} (e : Fin h ≃ ↥S) (f : ℕ → ℝ) :
    (∑ i, f (e i)) = ∑ p ∈ S, f p :=
  (e.sum_comp fun p : ↥S ↦ f p).trans (Finset.sum_attach S f)

/-- All labeled orders use exactly one weight at each start in `I`. -/
public theorem orderedWeight_eq {h : ℕ} {I B : Finset ℕ} (hBI : B ⊆ I)
    (w : ℕ → ℝ) (o : Ordering h I B) :
    orderedWeight w o = ∏ p ∈ I, w p := by
  rw [orderedWeight, prod_slots, prod_slots, mul_comm]
  exact Finset.prod_sdiff hBI

/-- The selected and unselected endpoint products partition the factors of `P_I`. -/
public theorem selected_mul_unselected {I B : Finset ℕ} (hBI : B ⊆ I) (d : ℕ) :
    selectedProduct d I B * unselectedProduct d I B = pairProduct d I := by
  rw [pairProduct, Finset.prod_mul_distrib,
    ← Finset.prod_sdiff (f := fun p : ℕ ↦ (p : ℝ)) hBI,
    ← Finset.prod_sdiff (f := fun p : ℕ ↦ ((p + d : ℕ) : ℝ)) hBI]
  unfold selectedProduct unselectedProduct
  ac_rfl

/-- The signed slot frequency is the log of the selected product over the other
product, equivalently `log(v_B²/P_I)`. Positivity is automatic for prime starts. -/
public theorem signedFrequency_eq {h d : ℕ} {I B : Finset ℕ}
    (hBI : B ⊆ I) (hpos : ∀ p ∈ I, 0 < p) (o : Ordering h I B) :
    signedFrequency d o = Real.log (selectedProduct d I B ^ 2 / pairProduct d I) := by
  let a (p : ℕ) : ℝ := p
  let b (p : ℕ) : ℝ := (p + d : ℕ)
  have ha (p : ℕ) (hp : p ∈ I) : 0 < a p := Nat.cast_pos.mpr (hpos p hp)
  have hb (p : ℕ) (hp : p ∈ I) : 0 < b p :=
    Nat.cast_pos.mpr ((hpos p hp).trans_le (Nat.le_add_right p d))
  have hlog (S : Finset ℕ) (hSI : S ⊆ I) : (∑ p ∈ S, logLabel d p) =
      Real.log (∏ p ∈ S, b p) - Real.log (∏ p ∈ S, a p) := by
    rw [Real.log_prod (fun p hp ↦ (hb p (hSI hp)).ne'),
      Real.log_prod (fun p hp ↦ (ha p (hSI hp)).ne'), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hap := (ha p (hSI hp)).ne'
    rw [← Real.log_div (hb p (hSI hp)).ne' hap]
    have hr : b p / a p = 1 + (d : ℝ) / (p : ℝ) := by
      dsimp only [a, b]
      rw [Nat.cast_add, add_div, div_self hap]
    rw [logLabel, hr]
  have hC (p : ℕ) (hp : p ∈ I \ B) : p ∈ I := (Finset.mem_sdiff.mp hp).1
  have haB : 0 < ∏ p ∈ B, a p := Finset.prod_pos fun p hp ↦ ha p (hBI hp)
  have hbB : 0 < ∏ p ∈ B, b p := Finset.prod_pos fun p hp ↦ hb p (hBI hp)
  have haC : 0 < ∏ p ∈ I \ B, a p := Finset.prod_pos fun p hp ↦ ha p (hC p hp)
  have hbC : 0 < ∏ p ∈ I \ B, b p := Finset.prod_pos fun p hp ↦ hb p (hC p hp)
  have hv : 0 < selectedProduct d I B := mul_pos hbB haC
  have hu : 0 < unselectedProduct d I B := mul_pos haB hbC
  have hP : 0 < pairProduct d I := selected_mul_unselected hBI d ▸ mul_pos hv hu
  have hquot : selectedProduct d I B / unselectedProduct d I B =
      selectedProduct d I B ^ 2 / pairProduct d I := by
    apply (div_eq_div_iff hu.ne' hP.ne').2
    rw [← selected_mul_unselected hBI d, pow_two, mul_assoc]
  calc
    signedFrequency d o = Real.log (selectedProduct d I B / unselectedProduct d I B) := by
      rw [signedFrequency, sum_slots, sum_slots, hlog B hBI, hlog (I \ B) hC,
        Real.log_div hv.ne' hu.ne']
      change _ = Real.log ((∏ p ∈ B, b p) * (∏ p ∈ I \ B, a p)) -
        Real.log ((∏ p ∈ B, a p) * (∏ p ∈ I \ B, b p))
      rw [Real.log_mul hbB.ne' haC.ne', Real.log_mul haB.ne' hbC.ne']
      ring
    _ = _ := congrArg Real.log hquot

/-- The fixed-`I,B` contribution to the ordered signed sum. The kernel can also
encode a gate on the signed frequency (for example on `|t * ν|`). No sign or
regularity condition is needed for the kernel or the weights. At `h = 0`, both
products of endpoints are `1`, and the single empty ordering contributes `K 0`. -/
public theorem sum_orderedWeight_mul_kernel {h d : ℕ} {I B : Finset ℕ}
    (hBI : B ⊆ I) (hI : I.card = 2 * h) (hB : B.card = h) (hpos : ∀ p ∈ I, 0 < p)
    (w : ℕ → ℝ) (K : ℝ → ℝ) :
    (∑ o : Ordering h I B, orderedWeight w o * K (signedFrequency d o)) =
      (h.factorial : ℝ) ^ 2 * (∏ p ∈ I, w p) *
        K (Real.log (selectedProduct d I B ^ 2 / pairProduct d I)) := by
  simp only [orderedWeight_eq hBI, signedFrequency_eq hBI hpos, Finset.sum_const,
    Finset.card_univ, card_ordering hBI hI hB, nsmul_eq_mul, Nat.cast_pow, mul_assoc]

end Masullo.BalancedDivisorMultiplicity
