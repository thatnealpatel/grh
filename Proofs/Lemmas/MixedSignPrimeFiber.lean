module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Lemmas.PrimeShiftProductInjective
import all Lemmas.PrimeTupleRedrawSpacing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith

/-!
# Short-interval fibers of mixed-sign prime-pair assignments

Source: `454c049f:.godel/bob/tuple-redraw-cost.md:15–23` (the hidden-slot bound
at line 21), `d5aca03a:.godel/bob/distant-frequency-differences.md:25–27`, and
`d5aca03a:.godel/bob/endpoint-modulus-catalogues.md:9`. The short-interval step
applies to the two windows in `e018142:.godel/bob/windowed-harmonic-witness.md:48`.
Owning check session: `01a20938-230d-71be-9082-772ff1e0dec6`.

Only the undisclosed slots of a fixed mask are counted, in their given orders
within each sign. There is no sum over masks. The fiber excludes opposite-sign
coincidences, but retains all repetitions within a sign. The product mass is
unconditional: the interval and no-coincidence conditions only filter the sum.
This does not estimate the cost of choosing or revealing slots or establish the
surrounding redraw, distant-pair, or catalogue estimates.
-/

open scoped BigOperators

namespace Masullo.MixedSignPrimeFiber

open PrimeTupleRedrawSpacing

/-- Ordered starts on the plus and minus slots of a fixed mask. -/
public abbrev Assignment (rPlus rMinus : ℕ) := (Fin rPlus → ℕ) × (Fin rMinus → ℕ)

/-- The hidden signed log sum, using the same prime-pair label on both sides. -/
@[expose] public noncomputable def signedFrequency {rPlus rMinus : ℕ} (d : ℕ)
    (a : Assignment rPlus rMinus) : ℝ :=
  (∑ i, Real.log ((↑(a.1 i + d) : ℝ) / a.1 i)) -
    ∑ j, Real.log ((↑(a.2 j + d) : ℝ) / a.2 j)

/-- Assignments in the interval with no start shared by the two signs. -/
public noncomputable def intervalFiber (S : Finset ℕ) (d rPlus rMinus : ℕ) (lo hi : ℝ) :
    Finset (Assignment rPlus rMinus) := by
  classical
  exact ((Fintype.piFinset fun _ : Fin rPlus ↦ S) ×ˢ
    (Fintype.piFinset fun _ : Fin rMinus ↦ S)).filter fun a ↦
      signedFrequency d a ∈ Set.Icc lo hi ∧ ∀ i j, a.1 i ≠ a.2 j

/-- The original product weight of an assignment, without normalization. -/
@[expose] public def productWeight {rPlus rMinus : ℕ} (w : ℕ → ℝ)
    (a : Assignment rPlus rMinus) : ℝ :=
  (∏ i, w (a.1 i)) * ∏ j, w (a.2 j)

/-- Membership imposes the pool, the interval, and disjointness across signs. -/
public theorem mem_intervalFiber {S : Finset ℕ} {d rPlus rMinus : ℕ} {lo hi : ℝ}
    {a : Assignment rPlus rMinus} : a ∈ intervalFiber S d rPlus rMinus lo hi ↔
      ((∀ i, a.1 i ∈ S) ∧ (∀ j, a.2 j ∈ S)) ∧
        signedFrequency d a ∈ Set.Icc lo hi ∧ ∀ i j, a.1 i ≠ a.2 j := by
  simp only [intervalFiber, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]

private def starts {n : ℕ} (a : Fin n → ℕ) : Multiset ℕ := List.ofFn a

private theorem starts_append {m n : ℕ} (u : Fin m → ℕ) (v : Fin n → ℕ) :
    starts (Fin.append u v) = starts u + starts v := by
  rw [starts, starts, starts, List.ofFn_fin_append, Multiset.coe_add]

private theorem frequency_append {m n d : ℕ} (u : Fin m → ℕ) (v : Fin n → ℕ) :
    frequency d (fun _ ↦ true) (Fin.append u v) =
      (∑ i, Real.log ((↑(u i + d) : ℝ) / u i)) + ∑ j, Real.log ((↑(v j + d) : ℝ) / v j) := by
  rw [frequency, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, signedLabel, ite_true]

private theorem append_mem {S : Finset ℕ} {m n : ℕ} {u : Fin m → ℕ} {v : Fin n → ℕ}
    (hu : ∀ i, u i ∈ S) (hv : ∀ j, v j ∈ S) (i : Fin (m + n)) : Fin.append u v i ∈ S := by
  refine Fin.addCases ?_ ?_ i
  · simpa only [Fin.append_left] using hu
  · simpa only [Fin.append_right] using hv

private theorem starts_eq_of_frequency_eq {S : Finset ℕ} {n d : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) {u v : Fin n → ℕ}
    (hu : ∀ i, u i ∈ S) (hv : ∀ i, v i ∈ S)
    (heq : frequency d (fun _ ↦ true) u = frequency d (fun _ ↦ true) v) : starts u = starts v := by
  let ratio (a : Fin n → ℕ) (i : Fin n) : ℝ := ((a i + d : ℕ) : ℝ) / (a i : ℝ)
  have hden (a : Fin n → ℕ) (ha : ∀ i, a i ∈ S) (i : Fin n) : 0 < (a i : ℝ) :=
    Nat.cast_pos.mpr (hprime _ (ha i)).1.pos
  have hratio (a : Fin n → ℕ) (ha : ∀ i, a i ∈ S) (i : Fin n) : 0 < ratio a i :=
    div_pos (Nat.cast_pos.mpr (hprime _ (ha i)).2.pos) (hden a ha i)
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
  have hall (a : Fin n → ℕ) (ha : ∀ i, a i ∈ S) (p : ℕ) (hp : p ∈ starts a) :
      p.Prime ∧ (p + d).Prime := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hprime _ (ha i)
  refine PrimeShiftProductInjective.eq_of_cross_mul_eq hd (hall u hu) (hall v hv) ?_
  simpa only [starts, Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, Fin.prod_ofFn,
    Function.comp_apply] using hcrossNat

-- Equality of net signed multiplicities recovers each side on disjoint supports.
private theorem sides_eq_of_cross_add_eq {aPlus aMinus cPlus cMinus : Multiset ℕ}
    (ha : ∀ p ∈ aPlus, p ∉ aMinus) (hc : ∀ p ∈ cPlus, p ∉ cMinus)
    (h : aPlus + cMinus = cPlus + aMinus) : aPlus = cPlus ∧ aMinus = cMinus := by
  have hzero (u v : Multiset ℕ) (huv : ∀ p ∈ u, p ∉ v) (p : ℕ) :
      u.count p = 0 ∨ v.count p = 0 := by
    by_cases hp : p ∈ u
    · exact Or.inr (Multiset.count_eq_zero.mpr (huv p hp))
    · exact Or.inl (Multiset.count_eq_zero.mpr hp)
  have hcounts (p : ℕ) : aPlus.count p = cPlus.count p ∧ aMinus.count p = cMinus.count p := by
    have hsum := congrArg (Multiset.count p) h
    simp only [Multiset.count_add] at hsum
    rcases hzero _ _ ha p with h₁ | h₁ <;> rcases hzero _ _ hc p with h₂ | h₂ <;> omega
  exact ⟨Multiset.ext.mpr fun p ↦ (hcounts p).1, Multiset.ext.mpr fun p ↦ (hcounts p).2⟩

-- Match fibers of positions as in OrderedPrimeTupleDiagonal, which keeps repetitions.
private theorem exists_perm_of_starts_eq {n : ℕ} {u v : Fin n → ℕ}
    (h : starts u = starts v) : ∃ σ : Equiv.Perm (Fin n), v = u ∘ σ := by
  let e (p : ℕ) : {i // v i = p} ≃ {i // u i = p} := by
    have hcount := congrArg (Multiset.count p) h.symm
    simp only [starts, Multiset.coe_count, List.count_ofFn] at hcount
    rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcount
    exact Fintype.equivOfCardEq hcount
  exact ⟨Equiv.ofFiberEquiv e, funext (fun i ↦ (Equiv.ofFiberEquiv_map e i).symm)⟩

private theorem exists_perms_of_mem_intervalFiber {S : Finset ℕ} {d rPlus rMinus : ℕ}
    {X lo hi : ℝ} (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hX : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X)
    (hdiam : hi - lo < X ^ (-(2 * ((rPlus + rMinus : ℕ) : ℤ))))
    {a c : Assignment rPlus rMinus}
    (ha : a ∈ intervalFiber S d rPlus rMinus lo hi) (hc : c ∈ intervalFiber S d rPlus rMinus lo hi) :
    ∃ (σ : Equiv.Perm (Fin rPlus)) (τ : Equiv.Perm (Fin rMinus)),
      c = (a.1 ∘ σ, a.2 ∘ τ) := by
  obtain ⟨⟨haPlus, haMinus⟩, haBand, haDisj⟩ := mem_intervalFiber.mp ha
  obtain ⟨⟨hcPlus, hcMinus⟩, hcBand, hcDisj⟩ := mem_intervalFiber.mp hc
  let u := Fin.append a.1 c.2
  let v := Fin.append c.1 a.2
  have hu : ∀ i, u i ∈ S := append_mem haPlus hcMinus
  have hv : ∀ i, v i ∈ S := append_mem hcPlus haMinus
  have hbound {z : Fin (rPlus + rMinus) → ℕ} (hz : ∀ i, z i ∈ S) : BoundedStarts X d z :=
    fun i ↦ ⟨(hprime _ (hz i)).1.pos, hX _ (hz i)⟩
  have hdiff : frequency d (fun _ ↦ true) v - frequency d (fun _ ↦ true) u =
      signedFrequency d c - signedFrequency d a := by
    dsimp only [u, v, signedFrequency]
    rw [frequency_append, frequency_append]
    ring
  have hnear : |signedFrequency d c - signedFrequency d a| ≤ hi - lo :=
    abs_le.mpr ⟨by linarith only [hcBand.1, haBand.2], by linarith only [hcBand.2, haBand.1]⟩
  have heq : frequency d (fun _ ↦ true) u = frequency d (fun _ ↦ true) v := by
    by_contra hne
    have hsep := spacing_of_ne (k := rPlus + rMinus) hd (fun _ ↦ true) (hbound hu) (hbound hv)
      ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)) (Ne.symm hne)
    rw [hdiff] at hsep
    exact (not_lt_of_ge (hsep.trans hnear)) hdiam
  have hcross := starts_eq_of_frequency_eq hd hprime hu hv heq
  dsimp only [u, v] at hcross
  rw [starts_append, starts_append] at hcross
  have hdisj (z : Assignment rPlus rMinus) (hz : ∀ i j, z.1 i ≠ z.2 j) :
      ∀ p ∈ starts z.1, p ∉ starts z.2 := by
    intro p hp hq
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hq
    exact hz i j (hi.trans hj.symm)
  obtain ⟨hPlus, hMinus⟩ := sides_eq_of_cross_add_eq (hdisj a haDisj) (hdisj c hcDisj) hcross
  obtain ⟨σ, hσ⟩ := exists_perm_of_starts_eq hPlus
  obtain ⟨τ, hτ⟩ := exists_perm_of_starts_eq hMinus
  exact ⟨σ, τ, Prod.ext hσ hτ⟩

/-- In a window strictly shorter than `X ^ (-2 * (rPlus + rMinus))`, there are at
most `rPlus! * rMinus!` assignments of the fixed signed slots with disjoint sign
supports. Repeated starts on one side need not give distinct permutations. -/
public theorem card_intervalFiber_le {S : Finset ℕ} {d rPlus rMinus : ℕ} {X lo hi : ℝ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hX : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X)
    (hdiam : hi - lo < X ^ (-(2 * ((rPlus + rMinus : ℕ) : ℤ)))) :
    (intervalFiber S d rPlus rMinus lo hi).card ≤ rPlus.factorial * rMinus.factorial := by
  classical
  let F := intervalFiber S d rPlus rMinus lo hi
  change F.card ≤ _
  rcases F.eq_empty_or_nonempty with hF | ⟨a, ha⟩
  · simp [hF]
  let reindex (σ : Equiv.Perm (Fin rPlus) × Equiv.Perm (Fin rMinus)) : Assignment rPlus rMinus :=
    (a.1 ∘ σ.1, a.2 ∘ σ.2)
  calc
    F.card ≤ (Finset.univ.image reindex).card := by
      apply Finset.card_le_card
      intro c hc
      obtain ⟨σ, τ, rfl⟩ := exists_perms_of_mem_intervalFiber hd hprime hX hdiam ha hc
      exact Finset.mem_image.mpr ⟨(σ, τ), Finset.mem_univ _, rfl⟩
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin rPlus) × Equiv.Perm (Fin rMinus))).card :=
      Finset.card_image_le
    _ = _ := by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

/-- The same fiber has unconditional product mass at most `rPlus! * rMinus! * b^r`,
where `r = rPlus + rMinus` and each original slot weight is nonnegative and at
most `b`. No probability law conditioned on membership in the fiber is used. -/
public theorem sum_productWeight_intervalFiber_le {S : Finset ℕ} {d rPlus rMinus : ℕ}
    {X lo hi b : ℝ} (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hX : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X)
    (hdiam : hi - lo < X ^ (-(2 * ((rPlus + rMinus : ℕ) : ℤ))))
    (w : ℕ → ℝ) (hb : 0 ≤ b) (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ b) :
    (∑ a ∈ intervalFiber S d rPlus rMinus lo hi, productWeight w a) ≤
      ((rPlus.factorial * rMinus.factorial : ℕ) : ℝ) * b ^ (rPlus + rMinus) := by
  calc
    _ ≤ ∑ _a ∈ intervalFiber S d rPlus rMinus lo hi, b ^ (rPlus + rMinus) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨⟨haPlus, haMinus⟩, _⟩ := mem_intervalFiber.mp ha
      have hslot (i : Fin (rPlus + rMinus)) := hw _ (append_mem haPlus haMinus i)
      calc
        productWeight w a = ∏ i, w (Fin.append a.1 a.2 i) := by
          rw [productWeight, Fin.prod_univ_add]
          simp only [Fin.append_left, Fin.append_right]
        _ ≤ ∏ _i : Fin (rPlus + rMinus), b :=
          Finset.prod_le_prod₀ (fun i _ ↦ (hslot i).1) (fun i _ ↦ (hslot i).2)
        _ = b ^ (rPlus + rMinus) := by simp
    _ = ((intervalFiber S d rPlus rMinus lo hi).card : ℝ) * b ^ (rPlus + rMinus) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (card_intervalFiber_le hd hprime hX hdiam)) (pow_nonneg hb _)

end Masullo.MixedSignPrimeFiber
