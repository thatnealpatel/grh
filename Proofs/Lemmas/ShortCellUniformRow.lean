module

public import Lemmas.ShortCellGramTrace
import all Lemmas.ShortCellTrace
import Mathlib.Tactic.Linarith

/-!
# One short-cell crossing row for all unit inputs

Source: `8058479e:.godel/bob/short-cell-weil-list.md:39–53`, the row selection
following (4). The actual owner-fibre Gram data give a trace bound for the
continuous smeared crossing kernels. Strict slack in that bound selects a
single row before the unit window input is specified. This does not estimate
the discrete unsmeared shifts or their replacement error.

Owning check session: `01a21012-2ca1-71e9-a51f-6efd061fa400`.
-/

open Filter MeasureTheory Set ShortCellCrossing
open scoped Topology

namespace ShortCellTrace

/-- If the limiting trace coefficient is strictly below `N * ρ ^ 2`, then for
any actual Gram data with at least `N > 0` rows, eventually one row has absolute
symmetric crossing form strictly below `ρ * √X` on every unit window input. -/
public theorem eventually_exists_uniform_symmetricForm_lt_of_gram
    {α : Type*} {l : Filter α} {X D L h C : α → ℝ} {C₀ : ℝ} {N : ℕ} {ρ : ℝ}
    (hX : Tendsto X l atTop)
    (hY : Tendsto (fun a ↦ Real.exp (D a) / X a) l (𝓝 1))
    (hsmall : Tendsto (fun a ↦ h a / L a) l (𝓝 0))
    (hC : Tendsto C l (𝓝 C₀)) (hCnonneg : ∀ᶠ a in l, 0 ≤ C a)
    (hN : 0 < N) (hρ : 0 < ρ) (hgap : C₀ < (N : ℝ) * ρ ^ 2) :
    ∀ᶠ a in l, ∀ {J ι : Type*} [Fintype J] [Fintype ι]
      {P : Partition J (L a) (Real.exp (D a)) (h a)} (A : PrimeAssignment P),
      N ≤ Fintype.card ι →
      0 < D a → 0 < L a → L a ≤ Real.exp (D a) → D a / 2 ≤ Real.log (L a) →
      ∀ {S : J → Finset ℤ} {W : J → ℤ → ℝ} {ξ : ℕ → ℂ} {χ : ι → ℤ → ℂ}
        {M B E : J → ℝ} {m : ι → ℝ → ℂ},
        (∀ j, 0 < P.right j - P.left j) →
        (∀ j, ∀ p ∈ A.cellPrimes j, (p.val : ℤ) ∈ S j) →
        (∀ j, ∀ n ∈ S j, 0 ≤ W j n) →
        (∀ j, ∀ p ∈ A.cellPrimes j, W j (p.val : ℤ) = 1) →
        (∀ p : ↥(primes (L a) (Real.exp (D a))), ‖ξ p.val‖ ≤ 1) →
        (∀ j, ∀ p ∈ A.cellPrimes j, Real.log (p.val : ℝ) ≤ M j) →
        (∀ j, 0 ≤ E j) →
        (∀ j i, ∑ n ∈ S j, W j n * ‖χ i n‖ ^ 2 ≤ B j) →
        (∀ j i k, i ≠ k → ‖ShortCellGramAssembly.gram (S j) (W j) χ i k‖ ≤ E j) →
        (∀ j, (M j / (P.right j - P.left j)) * (B j + ((Fintype.card ι - 1 : ℕ) : ℝ) * E j) ≤ C a) →
        (∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ A.gramMoment ξ χ i j) →
        ∃ i : ι, ∀ f : ℝ → ℂ, MemLp f 2 (volume.restrict (Icc 0 (D a))) →
          (∫ x in Icc 0 (D a), ‖f x‖ ^ 2) = 1 →
          |symmetricForm (D a) (L a) (m i) f| < ρ * Real.sqrt (X a) := by
  let ε : ℝ := ((N : ℝ) * ρ ^ 2 - C₀) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hgap)
  have hslack : C₀ + ε < (N : ℝ) * ρ ^ 2 := by
    dsimp only [ε]
    linarith only [hgap]
  filter_upwards [hX.eventually (eventually_gt_atTop 0),
    eventually_kernel_trace_le_of_gram hX hY hsmall hC hCnonneg hε] with a hx ha
  intro J ι _ _ P A hNcard hD hL hLY hhalf S W ξ χ M B E m hwidth hS hW hone hξ hlog hE hdiag
    hoff hcoef hconst
  let : Nonempty ι := Fintype.card_pos_iff.mp (hN.trans_le hNcard)
  let T (i : ι) := ∫ x in leftHalf (D a), ∫ y in rightHalf (D a),
    ‖kernel (D a) (L a) (m i) x y‖ ^ 2
  have htrace : ∑ i, T i ≤ (C₀ + ε) * X a :=
    ha A hD hL hLY hhalf hwidth hS hW hone hξ hlog hE hdiag hoff hcoef hconst
  have hcard : (N : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hNcard
  have hsum : ∑ i, T i < ∑ _i : ι, ρ ^ 2 * X a := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
    exact htrace.trans_lt (mul_lt_mul_of_pos_right (hslack.trans_le
      (mul_le_mul_of_nonneg_right hcard (sq_nonneg ρ))) hx)
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hsum
  have hT : 0 ≤ T i := integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hbound := Real.sqrt_lt_sqrt hT hi
  rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le] at hbound
  obtain ⟨hm, hmi⟩ := step_regular P (hconst i)
  have heq := (integral_sq_kernel hD hL hLY hhalf hmi).2
  refine ⟨i, fun f hf hunit ↦ ?_⟩
  have hform := (abs_symmetricForm_le hD hL hLY hhalf hm hmi hf hunit).2
  rw [← heq] at hform
  exact hform.trans_lt hbound

end ShortCellTrace
