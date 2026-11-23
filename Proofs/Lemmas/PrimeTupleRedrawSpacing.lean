module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith

/-!
# Spacing under a partial redraw of a signed tuple

This is the literal no-change obstruction in
`233d4a52:.godel/bob/tuple-window-review.md:9`, used in
`454c049f:.godel/bob/tuple-redraw-cost.md:7–19`. Here `X` bounds the endpoints
(`X + 4D` in the former note, `X` in the latter). The shift `d > 0` and the
sign at each ordered slot stay fixed. Unchanged slots cancel, and each changed
slot contributes two endpoint factors to each of the integer products.

This applies in particular to genuine prime tuples, without using primality.
Inside the surviving band, a redraw within the strict spacing budget cannot
change the frequency, hence cannot cross between opposite signs of a test
that depends only on frequency. The result does not require equal numbers of
the two signs, assert equality of the tuples, or rule out larger redraws. It
does not formalize the later probability estimate or the additional matching
of opposite signs among the newly drawn slots.

Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.
-/

open scoped BigOperators

namespace PrimeTupleRedrawSpacing

/-- The start is positive and the shifted endpoint is at most `X`. Since `d`
is natural, these conditions bound both endpoints in `(0, X]`. -/
public def BoundedStarts {n : ℕ} (X : ℝ) (d : ℕ) (p : Fin n → ℕ) : Prop :=
  ∀ i, 0 < p i ∧ (↑(p i + d) : ℝ) ≤ X

/-- The log-ratio at one slot, with `true` denoting a plus sign. -/
public noncomputable def signedLabel (d p : ℕ) (positive : Bool) : ℝ :=
  if positive then Real.log ((↑(p + d) : ℝ) / p) else -Real.log ((↑(p + d) : ℝ) / p)

/-- The frequency of a signed ordered tuple. -/
public noncomputable def frequency {n : ℕ} (d : ℕ) (positive : Fin n → Bool)
    (p : Fin n → ℕ) : ℝ :=
  ∑ i, signedLabel d (p i) (positive i)

/-- Ordered slots at which the two tuple starts differ. -/
public def changedSlots {n : ℕ} (p q : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ p i ≠ q i

private def slotNum (d p q : ℕ) (positive : Bool) : ℕ :=
  if positive then (q + d) * p else q * (p + d)

private theorem slotNum_pos {d p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s : Bool) :
    0 < slotNum d p q s := by
  have hpd := hp.trans_le (Nat.le_add_right p d)
  have hqd := hq.trans_le (Nat.le_add_right q d)
  cases s
  · exact Nat.mul_pos hq hpd
  · exact Nat.mul_pos hqd hp

private theorem slotNum_le {d p q : ℕ} {X : ℝ}
    (hp : (↑(p + d) : ℝ) ≤ X) (hq : (↑(q + d) : ℝ) ≤ X) (s : Bool) :
    (slotNum d p q s : ℝ) ≤ X ^ 2 := by
  have hp' : (p : ℝ) ≤ X := (Nat.cast_le.mpr (Nat.le_add_right p d)).trans hp
  have hq' : (q : ℝ) ≤ X := (Nat.cast_le.mpr (Nat.le_add_right q d)).trans hq
  have hX : 0 ≤ X := (Nat.cast_nonneg (p + d)).trans hp
  cases s
  · simpa [slotNum, Nat.cast_mul, pow_two] using
      mul_le_mul hq' hp (Nat.cast_nonneg (p + d)) hX
  · simpa [slotNum, Nat.cast_mul, pow_two] using
      mul_le_mul hq hp' (Nat.cast_nonneg p) hX

private theorem log_slotNum_div {d p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s : Bool) :
    Real.log ((slotNum d p q s : ℝ) / (slotNum d q p s : ℝ)) =
      signedLabel d q s - signedLabel d p s := by
  have hp' : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp).ne'
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have hpd : (↑(p + d) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hp.trans_le (Nat.le_add_right p d))).ne'
  have hqd : (↑(q + d) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hq.trans_le (Nat.le_add_right q d))).ne'
  rw [Real.log_div (Nat.cast_pos.mpr (slotNum_pos hp hq s)).ne'
    (Nat.cast_pos.mpr (slotNum_pos hq hp s)).ne']
  cases s <;>
    simp only [slotNum, signedLabel, Bool.false_eq_true, ↓reduceIte, Nat.cast_mul,
      Real.log_div hpd hp', Real.log_div hqd hq'] <;>
    rw [Real.log_mul (by assumption) (by assumption),
      Real.log_mul (by assumption) (by assumption)] <;>
    linarith

/-- The new frequency minus the old is the log of a quotient of positive
integer products. Both integer heights are bounded using only the slots that
actually changed. In the empty product case both heights are `1`. -/
public theorem frequency_sub_eq_log_div {n d : ℕ} {X : ℝ} (_hd : 0 < d)
    {p q : Fin n → ℕ} (positive : Fin n → Bool)
    (hp : BoundedStarts X d p) (hq : BoundedStarts X d q) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧
      (A : ℝ) ≤ X ^ (2 * (changedSlots p q).card) ∧
      (B : ℝ) ≤ X ^ (2 * (changedSlots p q).card) ∧
      frequency d positive q - frequency d positive p = Real.log ((A : ℝ) / (B : ℝ)) := by
  let S := changedSlots p q
  let U i := slotNum d (p i) (q i) (positive i)
  let V i := slotNum d (q i) (p i) (positive i)
  have hU i : 0 < U i := slotNum_pos (hp i).1 (hq i).1 _
  have hV i : 0 < V i := slotNum_pos (hq i).1 (hp i).1 _
  have hA : 0 < ∏ i ∈ S, U i := Finset.prod_pos fun i _ ↦ hU i
  have hB : 0 < ∏ i ∈ S, V i := Finset.prod_pos fun i _ ↦ hV i
  refine ⟨∏ i ∈ S, U i, ∏ i ∈ S, V i, hA, hB, ?_, ?_, ?_⟩
  · rw [Nat.cast_prod, pow_mul, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ ↦ Nat.cast_nonneg (U i))
      (fun i _ ↦ slotNum_le (hp i).2 (hq i).2 _)
  · rw [Nat.cast_prod, pow_mul, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ ↦ Nat.cast_nonneg (V i))
      (fun i _ ↦ slotNum_le (hq i).2 (hp i).2 _)
  have hu i : (U i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hU i)).ne'
  have hv i : (V i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hV i)).ne'
  calc
    _ = ∑ i ∈ S, (signedLabel d (q i) (positive i) - signedLabel d (p i) (positive i)) := by
      unfold frequency S changedSlots
      rw [← Finset.sum_sub_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : p i = q i <;> simp [hi]
    _ = ∑ i ∈ S, Real.log ((U i : ℝ) / (V i : ℝ)) :=
      Finset.sum_congr rfl fun i _ ↦ (log_slotNum_div (hp i).1 (hq i).1 _).symm
    _ = _ := by
      rw [Real.log_div (Nat.cast_pos.mpr hA).ne' (Nat.cast_pos.mpr hB).ne',
        Nat.cast_prod, Nat.cast_prod, Real.log_prod (fun i _ ↦ hu i),
        Real.log_prod (fun i _ ↦ hv i), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ Real.log_div (hu i) (hv i)

private theorem inv_le_log_div_of_lt {u v : ℕ} (hu : 0 < u) (huv : u < v) :
    (v : ℝ)⁻¹ ≤ Real.log ((v : ℝ) / (u : ℝ)) := by
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr (hu.trans huv)
  have hstep : (u : ℝ) + 1 ≤ v := by exact_mod_cast Nat.succ_le_of_lt huv
  calc
    (v : ℝ)⁻¹ = 1 / (v : ℝ) := (one_div _).symm
    _ ≤ ((v : ℝ) - (u : ℝ)) / (v : ℝ) :=
      div_le_div_of_nonneg_right (by linarith only [hstep]) hvR.le
    _ = 1 - (u : ℝ) / (v : ℝ) := by rw [sub_div, div_self hvR.ne']
    _ ≤ Real.log ((v : ℝ) / (u : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos (div_pos huR hvR)
      rw [Real.log_div huR.ne' hvR.ne'] at h
      rw [Real.log_div hvR.ne' huR.ne']
      linarith only [h]

private theorem neg_pow_eq_inv (X : ℝ) (k : ℕ) :
    X ^ (-(2 * (k : ℤ))) = (X ^ (2 * k))⁻¹ := by
  rw [zpow_neg]
  norm_cast

/-- Distinct frequencies of tuples differing in at most `k` slots are
separated by at least `X⁻²ᵏ`. The exponent on the left is an integer. -/
public theorem spacing_of_ne {n d k : ℕ} {X : ℝ} (hd : 0 < d)
    {p q : Fin n → ℕ} (positive : Fin n → Bool)
    (hp : BoundedStarts X d p) (hq : BoundedStarts X d q)
    (hk : (changedSlots p q).card ≤ k)
    (hne : frequency d positive q ≠ frequency d positive p) :
    X ^ (-(2 * (k : ℤ))) ≤ |frequency d positive q - frequency d positive p| := by
  obtain ⟨A, B, hA, hB, hAX, hBX, hlog⟩ := frequency_sub_eq_log_div hd positive hp hq
  have hAB : A ≠ B := by
    intro h
    apply hne
    apply sub_eq_zero.mp
    have hb : (B : ℝ) ≠ 0 := (Nat.cast_pos.mpr hB).ne'
    simpa [h, div_self hb] using hlog
  obtain ⟨i, _⟩ : ∃ i, p i ≠ q i := by
    by_contra! h
    exact hne (congrArg (frequency d positive) (funext h).symm)
  have hX : 1 ≤ X :=
    (Nat.one_le_cast.mpr (Nat.succ_le_of_lt (hp i).1)).trans
      ((Nat.cast_le.mpr (Nat.le_add_right (p i) d)).trans (hp i).2)
  have hpow : X ^ (2 * (changedSlots p q).card) ≤ X ^ (2 * k) :=
    pow_le_pow_right₀ hX (Nat.mul_le_mul_left 2 hk)
  rw [hlog, neg_pow_eq_inv]
  rcases lt_or_gt_of_ne hAB with h | h
  · have hAR : (A : ℝ) ≠ 0 := (Nat.cast_pos.mpr hA).ne'
    have hBR : (B : ℝ) ≠ 0 := (Nat.cast_pos.mpr hB).ne'
    calc
      _ ≤ (B : ℝ)⁻¹ := inv_anti₀ (Nat.cast_pos.mpr hB) (hBX.trans hpow)
      _ ≤ Real.log ((B : ℝ) / (A : ℝ)) := inv_le_log_div_of_lt hA h
      _ = -Real.log ((A : ℝ) / (B : ℝ)) := by
        rw [Real.log_div hBR hAR, Real.log_div hAR hBR, neg_sub]
      _ ≤ _ := neg_le_abs _
  · exact (inv_anti₀ (Nat.cast_pos.mpr hA) (hAX.trans hpow)).trans
      ((inv_le_log_div_of_lt hB h).trans (le_abs_self _))

/-- Two surviving frequencies are identical when their band's diameter is
strictly smaller than the minimum nonzero spacing. -/
public theorem eq_of_survivors {n d k : ℕ} {X t : ℝ} (hd : 0 < d) (ht : 0 < t)
    {p q : Fin n → ℕ} (positive : Fin n → Bool)
    (hp : BoundedStarts X d p) (hq : BoundedStarts X d q)
    (hk : (changedSlots p q).card ≤ k)
    (hpBand : |t * frequency d positive p| ≤ 2 * Real.pi)
    (hqBand : |t * frequency d positive q| ≤ 2 * Real.pi)
    (hbudget : 4 * Real.pi / t < X ^ (-(2 * (k : ℤ)))) :
    frequency d positive q = frequency d positive p := by
  by_contra hne
  have hband := abs_sub (t * frequency d positive q) (t * frequency d positive p)
  rw [← mul_sub, abs_mul, abs_of_pos ht] at hband
  have hdiam : |frequency d positive q - frequency d positive p| ≤ 4 * Real.pi / t := by
    apply (le_div_iff₀ ht).mpr
    linarith only [hband, hpBand, hqBand]
  exact (not_lt_of_ge ((spacing_of_ne hd positive hp hq hk hne).trans hdiam)) hbudget

/-- The strict finite spacing budget, with no rounding of `k`. -/
public theorem spacing_budget_iff {k : ℕ} {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    4 * Real.pi / t < X ^ (-(2 * (k : ℤ))) ↔ 4 * Real.pi * X ^ (2 * k) < t := by
  rw [neg_pow_eq_inv, ← one_div, lt_div_iff₀ (pow_pos hX _),
    div_mul_eq_mul_div, div_lt_iff₀ ht, one_mul]

/-- The equivalent logarithmic budget. For `X > 1`, this also reads
`k < log (t / (4π)) / (2 * log X)`. -/
public theorem spacing_budget_iff_log {k : ℕ} {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    4 * Real.pi / t < X ^ (-(2 * (k : ℤ))) ↔
      2 * (k : ℝ) * Real.log X < Real.log (t / (4 * Real.pi)) := by
  have hpi : 0 < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [spacing_budget_iff hX ht, mul_comm (4 * Real.pi), ← lt_div_iff₀ hpi,
    ← Real.log_lt_log_iff (pow_pos hX _) (div_pos ht hpi), Real.log_pow, Nat.cast_mul]
  rfl

end PrimeTupleRedrawSpacing
