module

public import Lemmas.PositiveTupleCore
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Lemmas.PrimeShiftProductInjective
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm

/-! # The exact diagonal of ordered prime tuples

Source: `db760d6f:.godel/bob/dyadic-prime-pair-moments.md`, line 9 ("Exact diagonal
at growing order") and line 29 (central-cell budget). The same diagonal estimate
is used at orders `h` and `h - 1` in
`0e672a90:.godel/bob/separated-signed-tuples.md`, lines 45 and 57.
Owning check session: `01a208fa-736c-75e9-a336-a5cd6d3b0490`.

For one fixed positive shift, the indices are all ordered tuples of starts in
`S`, including repeats. No separation between starts and shifted starts is
required. This gives the finite diagonal estimate and its central-slice budget
for a supplied cell cover, not an estimate for the full signed test.
-/

open scoped BigOperators

namespace Masullo.OrderedPrimeTupleDiagonal

private theorem exists_perm_of_multiset_eq {h : ℕ} {u v : Fin h → ℕ}
    (heq : (List.ofFn u : Multiset ℕ) = (List.ofFn v : Multiset ℕ)) :
    ∃ σ : Equiv.Perm (Fin h), v = u ∘ σ := by
  -- Match the positions of each start separately, preserving its multiplicity.
  let e (p : ℕ) : {i // v i = p} ≃ {i // u i = p} := by
    have hcount := congrArg (Multiset.count p) heq.symm
    simp only [Multiset.coe_count, List.count_ofFn] at hcount
    rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcount
    exact Fintype.equivOfCardEq hcount
  exact ⟨Equiv.ofFiberEquiv e, funext (fun i ↦ (Equiv.ofFiberEquiv_map e i).symm)⟩

private theorem exists_perm_of_frequency_eq {S : Finset ℕ} {d h : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) {u v : Fin h → ℕ}
    (hu : ∀ i, u i ∈ S) (hv : ∀ i, v i ∈ S)
    (heq : (∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ))) =
      ∑ i, Real.log (((v i + d : ℕ) : ℝ) / (v i : ℝ))) :
    ∃ σ : Equiv.Perm (Fin h), v = u ∘ σ := by
  let ratio (a : Fin h → ℕ) (i : Fin h) : ℝ := ((a i + d : ℕ) : ℝ) / (a i : ℝ)
  have hden (a : Fin h → ℕ) (ha : ∀ i, a i ∈ S) (i : Fin h) : 0 < (a i : ℝ) := by
    exact_mod_cast (hprime _ (ha i)).1.pos
  have hratio (a : Fin h → ℕ) (ha : ∀ i, a i ∈ S) (i : Fin h) : 0 < ratio a i := by
    refine div_pos ?_ (hden a ha i)
    exact_mod_cast (hprime _ (ha i)).2.pos
  change (∑ i, Real.log (ratio u i)) = (∑ i, Real.log (ratio v i)) at heq
  rw [← Real.log_prod (fun i _ ↦ (hratio u hu i).ne'),
      ← Real.log_prod (fun i _ ↦ (hratio v hv i).ne')] at heq
  have hprod : (∏ i, ratio u i) = ∏ i, ratio v i :=
    Real.log_injOn_pos (Finset.prod_pos (fun i _ ↦ hratio u hu i))
      (Finset.prod_pos (fun i _ ↦ hratio v hv i)) heq
  dsimp only [ratio] at hprod
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib] at hprod
  have hcross := (div_eq_div_iff
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hden u hu i).ne'))
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hden v hv i).ne'))).mp hprod
  have hcrossNat : (∏ i, (u i + d)) * (∏ i, v i) = (∏ i, (v i + d)) * (∏ i, u i) := by
    exact_mod_cast hcross
  have hall (a : Fin h → ℕ) (ha : ∀ i, a i ∈ S) (p : ℕ) (hp : p ∈ List.ofFn a) :
      p.Prime ∧ (p + d).Prime := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hprime _ (ha i)
  apply exists_perm_of_multiset_eq
  refine PrimeShiftProductInjective.eq_of_cross_mul_eq hd (hall u hu) (hall v hv) ?_
  simpa only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, Fin.prod_ofFn,
    Function.comp_apply] using hcrossNat

private theorem sum_prod_tuples (S : Finset ℕ) (h : ℕ) (w : ℕ → ℝ) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin h ↦ S), ∏ i, w (u i)) = (∑ p ∈ S, w p) ^ h := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_univ_sum (fun _ : Fin h ↦ S) (fun _ p ↦ w p)).symm

/-- The exact-zero mass over ordered pairs of ordered `h`-tuples is bounded by
`h!` times the `h`th power of the sum of squared start weights. Equal-frequency
tuples have equal product weights, so even signed real start weights are allowed. -/
public theorem zeroMass_le {S : Finset ℕ} {d : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) (h : ℕ) (w : ℕ → ℝ) :
    PositiveTupleCore.zeroMass (Fintype.piFinset (fun _ : Fin h ↦ S))
      (fun u ↦ ∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ)))
      (fun u ↦ ∏ i, w (u i)) ≤ (h.factorial : ℝ) * (∑ p ∈ S, w p ^ 2) ^ h := by
  classical
  let A := Fintype.piFinset (fun _ : Fin h ↦ S)
  let f (u : Fin h → ℕ) := ∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ))
  let W (u : Fin h → ℕ) := ∏ i, w (u i)
  let fiber (u : Fin h → ℕ) := A.filter (fun v ↦ f u = f v)
  have hperm (u : Fin h → ℕ) (hu : u ∈ A) (v : Fin h → ℕ) (hv : v ∈ fiber u) :
      ∃ σ : Equiv.Perm (Fin h), v = u ∘ σ := by
    obtain ⟨hv, heq⟩ := Finset.mem_filter.mp hv
    exact exists_perm_of_frequency_eq hd hprime (Fintype.mem_piFinset.mp hu)
      (Fintype.mem_piFinset.mp hv) heq
  -- The image need not have `h!` elements: repeat entries may give the same tuple.
  have hcard (u : Fin h → ℕ) (hu : u ∈ A) : (fiber u).card ≤ h.factorial := by
    let reindex (σ : Equiv.Perm (Fin h)) := u ∘ σ
    calc
      (fiber u).card ≤ (Finset.univ.image reindex).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨σ, rfl⟩ := hperm u hu v hv
        exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
      _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin h))).card := Finset.card_image_le
      _ = _ := by simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  change PositiveTupleCore.zeroMass A f W ≤ _
  calc
    _ = ∑ u ∈ A, ∑ v ∈ fiber u, W u * W v := by
      unfold PositiveTupleCore.zeroMass
      simp only [fiber, Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ u ∈ A, (h.factorial : ℝ) * W u ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      calc
        _ = ∑ _v ∈ fiber u, W u ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          obtain ⟨σ, rfl⟩ := hperm u hu v hv
          have hW : W (u ∘ σ) = W u := Equiv.prod_comp σ (fun i ↦ w (u i))
          rw [hW, pow_two]
        _ = ((fiber u).card : ℝ) * W u ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard u hu)) (sq_nonneg _)
    _ = _ := by
      dsimp only [W]
      rw [← Finset.mul_sum]
      simp_rw [← Finset.prod_pow]
      exact congrArg ((h.factorial : ℝ) * ·) (sum_prod_tuples S h (fun p ↦ w p ^ 2))

/-- The positive central slice contains at least half the same-cell budget minus
half the permutation diagonal bound. In particular the central mass is strictly
positive whenever the displayed mass budget is positive. -/
public theorem centralMass_lower_bound {S : Finset ℕ} {d : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) (h : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p) {t : ℝ} (ht : 0 < t) {κ : Type*}
    (C : Finset κ) (hC : C.Nonempty) (cell : κ → Set ℝ)
    (hcover : ∀ u : Fin h → ℕ, (∀ i, u i ∈ S) →
      ∃ c ∈ C, (∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ))) ∈ cell c)
    (hdiam : ∀ c ∈ C, ∀ x ∈ cell c, ∀ y ∈ cell c, |x - y| ≤ 1 / (2 * t)) :
    ((∑ p ∈ S, w p) ^ (2 * h) / (C.card : ℝ) -
      (h.factorial : ℝ) * (∑ p ∈ S, w p ^ 2) ^ h) / 2 ≤
      PositiveTupleCore.centralMass (Fintype.piFinset (fun _ : Fin h ↦ S))
        (fun u ↦ ∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ)))
        (fun u ↦ ∏ i, w (u i)) t := by
  have hc := PositiveTupleCore.centralMass_lower_bound
    (Fintype.piFinset (fun _ : Fin h ↦ S))
    (fun u ↦ ∑ i, Real.log (((u i + d : ℕ) : ℝ) / (u i : ℝ)))
    (fun u ↦ ∏ i, w (u i))
    (fun u hu ↦ Finset.prod_nonneg (fun i _ ↦ hw _ (Fintype.mem_piFinset.mp hu i)))
    ht C hC cell (fun u hu ↦ hcover u (Fintype.mem_piFinset.mp hu)) hdiam
  rw [sum_prod_tuples] at hc
  rw [mul_comm 2 h, pow_mul]
  exact (div_le_div_of_nonneg_right (sub_le_sub_left (zeroMass_le hd hprime h w) _) (by norm_num))
    |>.trans hc

end Masullo.OrderedPrimeTupleDiagonal
