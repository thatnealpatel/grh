module

public import Lemmas.SignedEndpointProfile

import all Lemmas.LogRampAbel -- unfold the ramp to compare cutoffs
import all Lemmas.PrimeTranslationEndpointAsymptotic -- reciprocal von Mangoldt bound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

/-! # Uniform log-ramp approximation of the signed endpoint quotient

Source: `6ffb987a:.godel/bob/endpoint-arithmetic-test.md`, lines 5–20.
Used at `b3723e8a:.godel/bob/twist-endpoint-packet.md`, lines 11–17.
Owning check session: `01a20f1a-0f71-75d4-a170-6751dc7ee00a`.

Scope: the positive translation contribution (minus the Weil prime form) on
the modulated endpoint profile, divided by its squared norm. The error is
absolute and uniform in the diameter, modulation, level and character. This
retains all prime powers; it does not estimate a prime-only replacement.
-/

open MeasureTheory
open Real (exp log)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

private theorem strictCut_subset (X : ℝ) :
    Finset.Ico 1 ⌈X⌉₊ ⊆ Finset.Icc 1 ⌊X⌋₊ := by
  intro n hn
  obtain ⟨hn₁, hnX⟩ := Finset.mem_Ico.mp hn
  exact Finset.mem_Icc.mpr ⟨hn₁, Nat.le_floor (Nat.lt_ceil.mp hnX).le⟩

private theorem vonMangoldt_logRamp_le {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 ⌈X⌉₊, Λ n * log (X / n)) ≤ (log 4 + 4) * X := by
  have hint := PrimeSquareRamp.partialSum_div_intervalIntegrable (fun n ↦ Λ n) hX
  simp only [← Chebyshev.psi_eq_sum_Icc] at hint
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n * log (X / n) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (strictCut_subset X) fun n hn _ ↦ ?_
      obtain ⟨hn₁, hnX⟩ := Finset.mem_Icc.mp hn
      have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn₁)
      have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff (zero_le_one.trans hX)).mp hnX
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.log_nonneg ((le_div_iff₀ hn₀).mpr (by simpa only [one_mul] using hnX')))
    -- The inclusive majorant can contain `n = X`; its log weight is then zero.
    _ = PrimeSquareRamp.logRamp (fun n ↦ Λ n) X := by
      have hf : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hX)
      rw [Finset.Icc_eq_cons_Ioc hf, Finset.sum_cons]
      simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_add,
        PrimeSquareRamp.logRamp, mul_comm]
    _ = ∫ t in (1 : ℝ)..X, Chebyshev.psi t / t := by
      rw [PrimeSquareRamp.logRamp_eq_integral _ ArithmeticFunction.map_zero
        ArithmeticFunction.vonMangoldt_apply_one hX]
      simp only [← Chebyshev.psi_eq_sum_Icc]
    _ ≤ ∫ _ in (1 : ℝ)..X, log 4 + 4 := by
      refine intervalIntegral.integral_mono_on hX hint intervalIntegrable_const fun t ht ↦ ?_
      have ht₀ := zero_lt_one.trans_le ht.1
      exact (div_le_iff₀ ht₀).mpr (Chebyshev.psi_le_const_mul_self ht₀.le)
    _ ≤ _ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      calc
        _ ≤ X * (log 4 + 4) := mul_le_mul_of_nonneg_right (sub_le_self X zero_le_one) (by positivity)
        _ = _ := mul_comm _ _

private theorem abs_twisted_sum_le {S : Finset ℕ} {z w : ℕ → ℝ}
    (hz : ∀ n ∈ S, |z n| ≤ 1) (hw : ∀ n ∈ S, 0 ≤ w n) :
    |∑ n ∈ S, Λ n * z n * w n| ≤ ∑ n ∈ S, Λ n * w n := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_nonneg (hw n hn)]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left (hz n hn) ArithmeticFunction.vonMangoldt_nonneg).trans_eq
      (mul_one _)) (hw n hn)

/-- The actual signed endpoint prime quotient is `E` times the normalized
logarithmic ramp mean, up to an absolute `C * (1 + D)` error. The cutoff is
strict even when `X = exp D` is an integer. No primitivity or nonprincipality
assumption is needed, so this includes the source's character class. -/
public theorem signedEndpointProfile_quotient_logRamp :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) {D : ℝ}, 1 ≤ D → ∀ y : ℝ,
      let X := exp D
      let E := exp (D / 2)
      let S := Finset.Ico 1 ⌈X⌉₊
      let u := primeWindowModulate y (signedEndpointProfileVector D)
      let H := X⁻¹ * ∑ n ∈ S, Λ n * (χ (n : ZMod q) * (n : ℂ) ^ (Complex.I * (y : ℂ))).re *
        log (X / n)
      |(-primeWindowSignedForm D (fun i : ↥(S.filter Nat.Prime) ↦ (i : ℕ))
        (fun i ↦ χ ((i : ℕ) : ZMod q)) u).re / ‖u‖ ^ 2 - E * H| ≤ C * (1 + D) := by
  let K : ℝ := log 4 + 4
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨5 * K, by positivity, ?_⟩
  intro q χ D hD y
  have hD' := zero_lt_one.trans_le hD
  dsimp only
  rw [signedEndpointProfile_quotient χ hD' y]
  let X := exp D
  let E := exp (D / 2)
  let S := Finset.Ico 1 ⌈X⌉₊
  let z (n : ℕ) := (χ (n : ZMod q) * (n : ℂ) ^ (Complex.I * (y : ℂ))).re
  let w (n : ℕ) := log (X / n)
  let B := ∑ n ∈ S, Λ n * z n * w n
  let A := 1 - 1 / X + D / E
  let r (n : ℕ) := (2 * (1 - (n : ℝ) / X) + w n / E) / n
  let R := ∑ n ∈ S, Λ n * z n * r n
  let M := B / E
  change |2 / (2 * (1 - 1 / X) + 2 * D / E) * (∑ n ∈ S, Λ n * z n *
    (2 * (1 - (n : ℝ) / X) / n + w n * (1 + 1 / (n : ℝ)) / E)) - E * (X⁻¹ * B)| ≤ _
  have hX : 0 < X := Real.exp_pos _
  have hX₁ : 1 ≤ X := Real.one_le_exp hD'.le
  have hE : 0 < E := Real.exp_pos _
  have hXE : X = E * E := by
    dsimp only [X, E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hterm (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ n ∧ (n : ℝ) < X :=
    ⟨by exact_mod_cast (Finset.mem_Ico.mp hn).1, Nat.lt_ceil.mp (Finset.mem_Ico.mp hn).2⟩
  have hz (n : ℕ) (hn : n ∈ S) : |z n| ≤ 1 := by
    have hn₀ := zero_lt_one.trans_le (hterm n hn).1
    have hphase : ‖(n : ℂ) ^ (Complex.I * (y : ℂ))‖ = 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn₀]
      simp [Complex.mul_re]
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, hphase, mul_one]; exact χ.norm_le_one _)
  have hw (n : ℕ) (hn : n ∈ S) : 0 ≤ w n := by
    obtain ⟨hn₁, hnX⟩ := hterm n hn
    have hn₀ := zero_lt_one.trans_le hn₁
    exact Real.log_nonneg ((le_div_iff₀ hn₀).mpr (by simpa only [one_mul] using hnX.le))
  have hM : |M| ≤ K * E := by
    have hB : |B| ≤ K * X := (abs_twisted_sum_le hz hw).trans (vonMangoldt_logRamp_le hX₁)
    dsimp only [M]
    rw [abs_div, abs_of_pos hE]
    apply (div_le_iff₀ hE).mpr
    rw [hXE] at hB
    simpa only [mul_assoc] using hB
  have hDE : D ≤ 2 * E := by
    have := Real.add_one_le_exp (D / 2)
    change D / 2 + 1 ≤ E at this
    linarith
  have hr (n : ℕ) (hn : n ∈ S) : 0 ≤ r n ∧ r n ≤ 4 / (n : ℝ) := by
    obtain ⟨hn₁, hnX⟩ := hterm n hn
    have hn₀ := zero_lt_one.trans_le hn₁
    have hfrac : (n : ℝ) / X ≤ 1 := (div_le_iff₀ hX).mpr (by simpa only [one_mul] using hnX.le)
    have hwD : w n ≤ D := by
      dsimp only [w]
      rw [Real.log_div hX.ne' hn₀.ne', show log X = D from Real.log_exp D]
      exact sub_le_self _ (Real.log_nonneg hn₁)
    have hwE : w n / E ≤ 2 := (div_le_iff₀ hE).mpr (hwD.trans hDE)
    refine ⟨div_nonneg (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hfrac))
      (div_nonneg (hw n hn) hE.le)) hn₀.le, div_le_div_of_nonneg_right ?_ hn₀.le⟩
    linarith [div_nonneg hn₀.le hX.le]
  have hR : |R| ≤ 4 * K * (1 + D) := calc
    _ ≤ ∑ n ∈ S, Λ n * r n := abs_twisted_sum_le hz fun n hn ↦ (hr n hn).1
    _ ≤ ∑ n ∈ S, 4 * (Λ n / (n : ℝ)) := by
      refine Finset.sum_le_sum fun n hn ↦ ?_
      calc
        _ ≤ Λ n * (4 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (hr n hn).2 ArithmeticFunction.vonMangoldt_nonneg
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (Finset.sum_le_sum_of_subset_of_nonneg (strictCut_subset X) fun n _ _ ↦
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)).trans ?_
      simpa only [K, X, Real.log_exp] using reciprocal_vonMangoldt_le hX₁
  have hA₁ : 1 ≤ A := by
    have hEX : E ≤ X := Real.exp_le_exp.mpr (by linarith)
    have hinv : 1 / X ≤ D / E := (one_div_le_one_div_of_le hE hEX).trans
      (div_le_div_of_nonneg_right hD hE.le)
    dsimp only [A]
    linarith
  have hA := zero_lt_one.trans_le hA₁
  have hcoef₀ : 0 ≤ 1 / A := by positivity
  have hcoef₁ : 1 / A ≤ 1 := (div_le_iff₀ hA).mpr (by simpa only [one_mul] using hA₁)
  have hnorm : |1 / A - 1| ≤ D / E := calc
    _ = (A - 1) * (1 / A) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hcoef₁)]
      field_simp [hA.ne']
      ring
    _ ≤ (A - 1) * 1 := mul_le_mul_of_nonneg_left hcoef₁ (sub_nonneg.mpr hA₁)
    _ ≤ _ := by dsimp only [A]; linarith [show 0 ≤ 1 / X by positivity]
  have hcoef : 2 / (2 * (1 - 1 / X) + 2 * D / E) = 1 / A := by
    rw [show 2 * (1 - 1 / X) + 2 * D / E = 2 * A by dsimp only [A]; ring]
    field_simp [hA.ne']
  have hscale : E * (X⁻¹ * B) = M := by
    rw [hXE]
    dsimp only [M]
    field_simp [hE.ne']
  -- The same-endpoint overlap and the `1/n` cross term both belong to `R`.
  have hsplit : (∑ n ∈ S, Λ n * z n *
      (2 * (1 - (n : ℝ) / X) / n + w n * (1 + 1 / (n : ℝ)) / E)) = M + R := by
    dsimp only [M, B, R]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    dsimp only [r]
    ring
  rw [hcoef, hsplit, hscale]
  calc
    _ = |1 / A * R + (1 / A - 1) * M| := by congr 1; ring
    _ ≤ |1 / A| * |R| + |1 / A - 1| * |M| := by
      simpa only [abs_mul] using abs_add_le (1 / A * R) ((1 / A - 1) * M)
    _ ≤ 1 * (4 * K * (1 + D)) + (D / E) * (K * E) := by
      rw [abs_of_nonneg hcoef₀]
      exact add_le_add (mul_le_mul hcoef₁ hR (abs_nonneg _) zero_le_one)
        (mul_le_mul hnorm hM (abs_nonneg _) (div_nonneg hD'.le hE.le))
    _ ≤ 5 * K * (1 + D) := by
      rw [show D / E * (K * E) = K * D by field_simp [hE.ne']]
      linarith only [hK]

end Masullo
