module

public import Lemmas.FiniteShiftSchur
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Finite prime-translation bound with the endpoint weight

Source: `bdd74f2:.godel/adhoc/prime-translation-norm.md`, lines 28–38.
Uses: the whole-block conductor estimate in the same note, lines 52–60, and
`85842a8:.godel/alice/prime-conductor-window.md`, lines 52–62.
Owning session: `01a209a4-4028-76c1-a295-487f5bedcbac`.

Scope: the upper Schur bound from explicit finite majorants for the Chebyshev sum
and its reciprocal-weighted version. No prime number theorem, lower bound, or
asymptotic assertion is used.
-/

open MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

private noncomputable def endpointWeight (D : ℝ) : ℝ → ℝ :=
  (Set.Icc 0 D).indicator (fun x ↦ exp (-x / 2) + exp (-(D - x) / 2))

private theorem endpointWeight_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    endpointWeight D x = exp (-x / 2) + exp (-(D - x) / 2) :=
  Set.indicator_of_mem hx _

private theorem endpointWeight_off {D x : ℝ} (hx : x ∉ Set.Icc 0 D) :
    endpointWeight D x = 0 :=
  Set.indicator_of_notMem hx _

private theorem endpoint_reflect_mem (D x : ℝ) : D - x ∈ Set.Icc 0 D ↔ x ∈ Set.Icc 0 D := by
  simp only [Set.mem_Icc, sub_nonneg, sub_le_self_iff, and_comm]

private theorem endpointWeight_reflect (D x : ℝ) :
    endpointWeight D (D - x) = endpointWeight D x := by
  have hi := endpoint_reflect_mem D x
  by_cases hx : x ∈ Set.Icc 0 D
  · rw [endpointWeight_on (hi.mpr hx), endpointWeight_on hx,
      show D - (D - x) = x by ring, add_comm]
  · rw [endpointWeight_off (mt hi.mp hx), endpointWeight_off hx]

private theorem endpointWeight_forward_term {D x : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hx : x + log n ∈ Set.Icc 0 D) :
    Λ n / sqrt n * endpointWeight D (x + log n) =
      exp (-x / 2) * (Λ n / n) + exp (-(D - x) / 2) * Λ n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hsqrt := Real.sqrt_pos.mpr hn'
  have hexp : exp (log n / 2) = sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn']
    congr 1
    ring
  have hf : exp (-(x + log n) / 2) = exp (-x / 2) / sqrt n := by
    rw [show -(x + log n) / 2 = -x / 2 - log n / 2 by ring, Real.exp_sub, hexp]
  have hg : exp (-(D - (x + log n)) / 2) = exp (-(D - x) / 2) * sqrt n := by
    rw [show -(D - (x + log n)) / 2 = -(D - x) / 2 + log n / 2 by ring, Real.exp_add, hexp]
  rw [endpointWeight_on hx, hf, hg]
  calc
    _ = exp (-x / 2) * (Λ n / (sqrt n) ^ 2) + exp (-(D - x) / 2) * Λ n := by
      field_simp [hsqrt.ne']
    _ = _ := by rw [Real.sq_sqrt hn'.le]

private theorem endpointWeight_forward {D ε C B x : ℝ} (hx : x ∈ Set.Icc 0 D)
    (hψ : ∀ y : ℝ, 1 ≤ y → y ≤ exp D →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ (1 + ε) * y + C)
    (hrec : ∑ n ∈ Finset.Icc 1 ⌊exp D⌋₊, Λ n / (n : ℝ) ≤ B) :
    (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n * endpointWeight D (x + log n)) ≤
      ((1 + ε) * exp (D / 2) + B) * exp (-x / 2) + C * exp (-(D - x) / 2) := by
  let S := Finset.Ico 1 ⌈exp D⌉₊
  let T := Finset.Icc 1 ⌊exp (D - x)⌋₊
  let Sx := S.filter (fun n : ℕ ↦ x + log n ∈ Set.Icc 0 D)
  have hsub : Sx ⊆ T := by
    intro n hn
    obtain ⟨hnS, hshift⟩ := Finset.mem_filter.mp hn
    have hn1 := (Finset.mem_Ico.mp hnS).1
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
    have hlog : log n ≤ D - x := by linarith [hshift.2]
    exact Finset.mem_Icc.mpr ⟨hn1, Nat.le_floor ((Real.log_le_iff_le_exp hn').mp hlog)⟩
  have hy := Real.exp_le_exp.mpr (sub_le_self D hx.1)
  have hy1 : 1 ≤ exp (D - x) := Real.one_le_exp (sub_nonneg.mpr hx.2)
  have hrec' : (∑ n ∈ T, Λ n / (n : ℝ)) ≤ B := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ ↦
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))).trans hrec
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hn1, hn2.trans (Nat.floor_mono hy)⟩
  have hcross : exp (-(D - x) / 2) * exp (D - x) = exp (D / 2) * exp (-x / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (∑ n ∈ S, Λ n / sqrt n * endpointWeight D (x + log n)) =
        ∑ n ∈ Sx, Λ n / sqrt n * endpointWeight D (x + log n) := by
      dsimp only [Sx]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases hz : x + log n ∈ Set.Icc 0 D
      · rw [ite_eq_left hz]
      · rw [ite_eq_right hz, endpointWeight_off hz, mul_zero]
    _ = ∑ n ∈ Sx, (exp (-x / 2) * (Λ n / (n : ℝ)) + exp (-(D - x) / 2) * Λ n) := by
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      obtain ⟨hnS, hnshift⟩ := Finset.mem_filter.mp hn
      exact endpointWeight_forward_term (Finset.mem_Ico.mp hnS).1 hnshift
    -- The inclusive majorant can add indices to the strict outer cutoff.
    _ ≤ ∑ n ∈ T, (exp (-x / 2) * (Λ n / (n : ℝ)) + exp (-(D - x) / 2) * Λ n) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ ↦
        add_nonneg (mul_nonneg (Real.exp_pos _).le
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)))
          (mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)
    _ = exp (-x / 2) * (∑ n ∈ T, Λ n / (n : ℝ)) + exp (-(D - x) / 2) * (∑ n ∈ T, Λ n) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ exp (-x / 2) * B + exp (-(D - x) / 2) * ((1 + ε) * exp (D - x) + C) :=
      add_le_add (mul_le_mul_of_nonneg_left hrec' (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left (hψ _ hy1 hy) (Real.exp_pos _).le)
    _ = (1 + ε) * (exp (-(D - x) / 2) * exp (D - x)) +
        (B * exp (-x / 2) + C * exp (-(D - x) / 2)) := by ring
    _ = _ := by rw [hcross]; ring

private theorem endpointWeight_row {D ε C B x : ℝ} (hx : x ∈ Set.Icc 0 D)
    (hψ : ∀ y : ℝ, 1 ≤ y → y ≤ exp D →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ (1 + ε) * y + C)
    (hrec : ∑ n ∈ Finset.Icc 1 ⌊exp D⌋₊, Λ n / (n : ℝ) ≤ B) :
    (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n *
      (endpointWeight D (x + log n) + endpointWeight D (x - log n))) ≤
      ((1 + ε) * exp (D / 2) + C + B) * endpointWeight D x := by
  have hforward := endpointWeight_forward hx hψ hrec
  have hbackward :
      (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n * endpointWeight D (x - log n)) ≤
        ((1 + ε) * exp (D / 2) + B) * exp (-(D - x) / 2) + C * exp (-x / 2) := by
    -- Reflection turns the backward contributions into forward ones at D - x.
    calc
      _ = ∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n * endpointWeight D (D - x + log n) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [← endpointWeight_reflect D (x - log n),
          show D - (x - log n) = D - x + log n by ring]
      _ ≤ _ := by
        simpa only [show D - (D - x) = x by ring] using
          endpointWeight_forward ((endpoint_reflect_mem D x).mpr hx) hψ hrec
  rw [endpointWeight_on hx]
  simp only [mul_add, Finset.sum_add_distrib]
  calc
    _ ≤ _ := add_le_add hforward hbackward
    _ = _ := by ring

/-- For every complex `L²` input supported almost everywhere on `[0,D]`, the absolute
prime correlations with `1 ≤ n < exp D` satisfy the finite endpoint Schur bound.
`Nat.lt_ceil` encodes the strict cutoff, while the hypotheses use the inclusive
Chebyshev and reciprocal sums via `Nat.le_floor_iff`. The term at `n = 1` is zero. -/
public theorem primeTranslationEndpointSchur {D ε C B : ℝ}
    (hD : 0 < D) (_hε : 0 ≤ ε) (_hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hψ : ∀ y : ℝ, 1 ≤ y → y ≤ exp D →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ (1 + ε) * y + C)
    (hrec : ∑ n ∈ Finset.Icc 1 ⌊exp D⌋₊, Λ n / (n : ℝ) ≤ B)
    {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (huzero : ∀ᵐ x ∂volume, x ∉ Set.Icc 0 D → u x = 0) :
    2 * (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n *
      ∫ x : ℝ, ‖u x‖ * ‖u (x + log n)‖) ≤
      ((1 + ε) * exp (D / 2) + C + B) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
  have hw : Measurable (endpointWeight D) := by
    unfold endpointWeight
    exact (by fun_prop : Measurable (fun x : ℝ ↦ exp (-x / 2) + exp (-(D - x) / 2))).indicator
      measurableSet_Icc
  refine finiteShiftSchur (b := exp (-D)) (B := 2) _ (fun n : ℕ ↦ log n) (fun n ↦ Λ n / sqrt n)
    (fun _ _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    measurableSet_Icc hw (fun _ ↦ endpointWeight_off) (Real.exp_pos _) ?_ ?_ ?_ hu huzero
  · intro x hx
    rw [endpointWeight_on hx]
    have hle : exp (-D) ≤ exp (-x / 2) := Real.exp_le_exp.mpr (by linarith [hx.2, hD])
    exact hle.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · intro x hx
    rw [endpointWeight_on hx]
    have ha : exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1])
    have hb : exp (-(D - x) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.2])
    linarith
  · exact (ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all _ fun _ hx ↦ endpointWeight_row hx hψ hrec)

end Masullo
