module

public import Lemmas.RationalCompletedZetaZeros
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linarith

/-! # Height budgets from dyadic counts and zeta symmetry -/

open Complex Set
open scoped ComplexConjugate

namespace Masullo

private theorem exists_dyadic_height_upper (h : ℝ) : ∃ j : ℕ, h < (2 : ℝ) ^ (j + 1) := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt h (show (1 : ℝ) < 2 by norm_num)
  exact ⟨j, hj.trans_le (by rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j])⟩

/-- A dyadic rate strictly below `2^j` makes the reciprocal-height costs summable. -/
public theorem summable_pi_div_height_of_dyadic_count {ι : Type*} (height : ι → ℝ)
    (hheight : ∀ i, 1 ≤ height i) {C q : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q < 2)
    (hcount : ∀ (j : ℕ) (A : Finset ι), (∀ i ∈ A, height i < (2 : ℝ) ^ (j + 1)) →
      (A.card : ℝ) ≤ C * q ^ j) :
    Summable (fun i ↦ Real.pi / height i) := by
  classical
  let shell (i : ι) := Nat.find (exists_dyadic_height_upper (height i))
  have hhi (i : ι) : height i < (2 : ℝ) ^ (shell i + 1) :=
    Nat.find_spec (exists_dyadic_height_upper (height i))
  have hlo (i : ι) : (2 : ℝ) ^ shell i ≤ height i := by
    cases h : shell i with
    | zero => simpa only [pow_zero] using hheight i
    | succ j =>
      have hj : j < shell i := by rw [h]; exact Nat.lt_succ_self _
      exact le_of_not_gt (Nat.find_min (exists_dyadic_height_upper (height i)) hj)
  have hC : 0 ≤ C := by simpa using hcount 0 ∅ (by simp)
  let B (j : ℕ) : ℝ := Real.pi * C * (q / 2) ^ j
  have hB : Summable B :=
    (summable_geometric_of_lt_one (by positivity) (by linarith : q / 2 < 1)).mul_left _
  have hblock (j : ℕ) (A : Finset ι) (hA : ∀ i ∈ A, shell i = j) :
      ∑ i ∈ A, Real.pi / height i ≤ B j := by
    calc
      _ ≤ ∑ _i ∈ A, Real.pi / (2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (hA i hi ▸ hlo i)
      _ = (A.card : ℝ) * (Real.pi / (2 : ℝ) ^ j) := by simp
      _ ≤ C * q ^ j * (Real.pi / (2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_right (hcount j A fun i hi ↦ hA i hi ▸ hhi i) (by positivity)
      _ = B j := by simp only [B, div_pow]; ring
  apply summable_of_sum_le (c := ∑' j, B j) (fun i ↦ div_nonneg Real.pi_pos.le (by linarith [hheight i]))
  intro A
  calc
    _ = ∑ j ∈ A.image shell, ∑ i ∈ A with shell i = j, Real.pi / height i :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hi ↦ Finset.mem_image_of_mem shell hi) _).symm
    _ ≤ ∑ j ∈ A.image shell, B j :=
      Finset.sum_le_sum fun j _ ↦ hblock j _ (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
    _ ≤ ∑' j, B j := hB.sum_le_tsum _ (fun _ _ ↦ by dsimp [B]; positivity)

open scoped BigOperators in
/-- A summable family has arbitrarily small sum above a high height cutoff. -/
public theorem exists_summable_small_above_height {ι : Type*} (H W : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hW : Summable W) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ Summable (fun i : {i // T < H i} ↦ W i.val) ∧
      (∑' i : {i // T < H i}, W i.val) < ε := by
  classical
  obtain ⟨A, hA⟩ := hW.tsum_vanishing (Iio_mem_nhds hε)
  let T := 1 + ∑ i ∈ A, H i
  have hT : 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hH i)
  let e : {i // T < H i} → ι := Subtype.val
  have he : Function.Injective e := Subtype.val_injective
  have hdis : Disjoint (range e) (↑A : Set ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ hi
    have hle : H (e i) ≤ ∑ k ∈ A, H k := Finset.single_le_sum (fun k _ ↦ hH k) hi
    exact i.property.not_ge (hle.trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨T, hT, hW.comp_injective he, ?_⟩
  have hsmall := hA (range e) hdis
  rwa [tsum_range W he] at hsmall

private def conjZero (ρ : criticalStripZetaZeros) : criticalStripZetaZeros :=
  ⟨conj ρ.val, by
    obtain ⟨h, h₀, h₁⟩ := mem_criticalStripZetaZeros.mp ρ.property
    exact mem_criticalStripZetaZeros.mpr ⟨by simp [h], h₀, h₁⟩⟩

private def reflectZero (ρ : criticalStripZetaZeros) : criticalStripZetaZeros :=
  ⟨1 - conj ρ.val, by
    obtain ⟨_, h₀, h₁⟩ := mem_criticalStripZetaZeros.mp ρ.property
    have hρ₀ : ρ.val ≠ 0 := fun h ↦ by simp [h] at h₀
    have hρ₁ : ρ.val ≠ 1 := fun h ↦ by simp [h] at h₁
    have h₀' : 1 - conj ρ.val ≠ 0 := by
      intro h
      have := congrArg re h
      simp at this
      linarith
    have h₁' : 1 - conj ρ.val ≠ 1 := by
      intro h
      have := congrArg re h
      simp at this
      linarith
    rw [← completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h₀' h₁',
      completedRiemannZeta_one_sub, completedRiemannZeta_conj,
      (completedZeta_eq_zero_iff_mem_criticalStripZetaZeros hρ₀ hρ₁).mpr ρ.property, map_zero]⟩

private def orientZero (p : Bool × Bool) (ρ : criticalStripZetaZeros) : criticalStripZetaZeros :=
  let σ := if p.1 then reflectZero ρ else ρ
  if p.2 then conjZero σ else σ

private theorem orientZero_re (p : Bool × Bool) (ρ : criticalStripZetaZeros) :
    (orientZero p ρ).val.re = if p.1 then 1 - ρ.val.re else ρ.val.re := by
  obtain ⟨l, d⟩ := p
  cases l <;> cases d <;> simp [orientZero, conjZero, reflectZero]

private theorem orientZero_im (p : Bool × Bool) (ρ : criticalStripZetaZeros) :
    (orientZero p ρ).val.im = if p.2 then -ρ.val.im else ρ.val.im := by
  obtain ⟨l, d⟩ := p
  cases l <;> cases d <;> simp [orientZero, conjZero, reflectZero]

private theorem orientZero_injective (p : Bool × Bool) : Function.Injective (orientZero p) := by
  intro ρ σ h
  have hr := congrArg (fun ρ : criticalStripZetaZeros ↦ ρ.val.re) h
  have hi := congrArg (fun ρ : criticalStripZetaZeros ↦ ρ.val.im) h
  simp only [orientZero_re] at hr
  simp only [orientZero_im] at hi
  exact Subtype.ext (Complex.ext (by split_ifs at hr <;> linarith) (by split_ifs at hi <;> linarith))

/-- Each of the four sign sectors embeds in the positive-height right-hand sector. -/
public theorem zetaZero_card_abs_le_four_mul {α T B : ℝ}
    (hcount : ∀ A : Finset criticalStripZetaZeros,
      (∀ ρ ∈ A, 1 / 2 + α ≤ ρ.val.re ∧ 0 < ρ.val.im ∧ ρ.val.im < T) → (A.card : ℝ) ≤ B)
    (A : Finset criticalStripZetaZeros)
    (hA : ∀ ρ ∈ A, α ≤ |(shiftedZetaZero ρ).re| ∧ 0 < |ρ.val.im| ∧ |ρ.val.im| < T) :
    (A.card : ℝ) ≤ 4 * B := by
  classical
  let sign (ρ : criticalStripZetaZeros) : Bool × Bool :=
    (decide (ρ.val.re < 1 / 2), decide (ρ.val.im < 0))
  have hsector (p : Bool × Bool) : ((A.filter fun ρ ↦ sign ρ = p).card : ℝ) ≤ B := by
    let e : criticalStripZetaZeros ↪ criticalStripZetaZeros := ⟨orientZero p, orientZero_injective p⟩
    rw [← Finset.card_map e]
    apply hcount
    intro σ hσ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hσ
    obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hr, h₀, ht⟩ := hA ρ hmem
    simp only [Function.Embedding.coeFn_mk, e, orientZero_re, orientZero_im, sign,
      decide_eq_true_eq]
    constructor
    · have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by simp
      simp only [shiftedZetaZero, sub_re, hhalf] at hr
      split_ifs with h
      · rw [abs_of_neg (sub_neg.mpr h)] at hr
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))] at hr
        linarith
    · split_ifs with h
      · simpa only [abs_of_neg h] using And.intro h₀ ht
      · simpa only [abs_of_nonneg (le_of_not_gt h)] using And.intro h₀ ht
  have hcard : A.card = ∑ p ∈ (Finset.univ : Finset (Bool × Bool)),
      (A.filter fun ρ ↦ sign ρ = p).card := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter A Finset.univ sign).symm
  calc
    _ = ∑ p : Bool × Bool, ((A.filter fun ρ ↦ sign ρ = p).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _p : Bool × Bool, B := Finset.sum_le_sum fun p _ ↦ hsector p
    _ = 4 * B := by simp [Fintype.card_prod]

end Masullo
