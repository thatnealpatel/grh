module

public import Lemmas.ReflectedResidueBudget
import Lemmas.ZetaZeroSummability
import Mathlib.Tactic.Linarith

/-!
# Summability of the zeta Poisson mass

Source: `4ad642e:.godel/conjectures/closed/zeta-reflected-residue-harmonic-margin.md`,
lines 50–67, from (2) of `e84c4f3:.godel/bob/endpoint-zero-packets.md` to
“Spend the height term once” in `2f8680b:.godel/alice/single-endpoint-harmonics.md`.

Scope: absolute convergence at `σ = 1 + 1 / log X` for `X > 1` and every real
height `t`, on distinct open critical-strip zeta zeros with their full analytic
orders. This supplies summability in the near-line residue comparisons. The
Hadamard identity and the half-log upper bound are not proved here; the
comparisons still take the half-log estimate as input.

Scope baseline: `ef2e721c96b52c23c964812798938c624ef3f7ff`.
Owning check session: `01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.
-/

namespace ReflectedResidueBudget

open Masullo

/-- For every height and every `X > 1`, the full zeta Poisson mass with actual
multiplicities is summable, by comparison with the centered quadratic weight. -/
public theorem summable_zetaZeroOrder_mul_poissonWeight {X : ℝ} (hX : 1 < X) (t : ℝ) :
    Summable (fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ) := by
  let a : ℝ := 1 / Real.log X
  have ha : 0 < a := div_pos one_pos (Real.log_pos hX)
  let C : ℝ := (2 + 2 * t ^ 2) / a ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine (summable_zetaZeroOrder_div_one_add_norm_sq.mul_left ((1 + a) * (2 + C))).of_nonneg_of_le
    (fun ρ ↦ mul_nonneg (Nat.cast_nonneg _) (poissonWeight_pos hX ρ).le) ?_
  intro ρ
  obtain ⟨_, hβ₀, hβ₁⟩ := mem_criticalStripZetaZeros.mp ρ.property
  let d := 1 + a - (ρ : ℂ).re
  let u := (ρ : ℂ).im - t
  have had : a ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := ha.trans_le had
  have hd' : d ≤ 1 + a := sub_le_self _ hβ₀.le
  -- Bound the centered quadratic weight by the denominator at the new height.
  have hsize : 1 + ‖shiftedZetaZero ρ‖ ^ 2 ≤ 2 + 2 * t ^ 2 + 2 * u ^ 2 := by
    have hre := pow_le_pow_left₀ (abs_nonneg _) (abs_re_shiftedZetaZero_lt ρ).le 2
    rw [sq_abs] at hre
    have him : (shiftedZetaZero ρ).im = u + t := by simp [shiftedZetaZero, u]
    rw [Complex.sq_norm, Complex.normSq_apply, him]
    nlinarith only [hre, sq_nonneg (u - t)]
  have hCa : C * a ^ 2 = 2 + 2 * t ^ 2 := div_mul_cancel₀ _ (pow_ne_zero _ ha.ne')
  have hCd : 2 + 2 * t ^ 2 ≤ C * d ^ 2 := by
    rw [← hCa]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le had 2) hC
  have hdenom : 1 + ‖shiftedZetaZero ρ‖ ^ 2 ≤ (2 + C) * (d ^ 2 + u ^ 2) := by
    nlinarith only [hsize, hCd, sq_nonneg d, mul_nonneg hC (sq_nonneg u)]
  have hkernel : poissonWeight X t ρ ≤
      ((1 + a) * (2 + C)) / (1 + ‖shiftedZetaZero ρ‖ ^ 2) := by
    change d / (d ^ 2 + u ^ 2) ≤ _
    calc
      _ ≤ (1 + a) / (d ^ 2 + u ^ 2) := div_le_div_of_nonneg_right hd' (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hdenom (by positivity)
  calc
    _ ≤ (zetaZeroOrder ρ : ℝ) *
        (((1 + a) * (2 + C)) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg _)
    _ = _ := by
      simp only [div_eq_mul_inv]
      exact mul_left_comm _ _ _

/-- The near-line residue comparison needs only the half-log estimate for the
full Poisson mass, not a separate summability hypothesis. -/
public theorem zeta_nearLine_residue_le_from_halfLog {X c t E : ℝ}
    (hX : 1 < X) (hc : 0 ≤ c) (he : windowError X c < 1)
    (hhalf : (∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ) ≤
      (1 / 2 : ℝ) * Real.log (2 + |t|) + E) :
    zetaNearLineResidueMass X c t ≤
      (Real.cosh c / (1 - windowError X c) ^ 3) * ((Real.log (2 + |t|) + 2 * E) / Real.sqrt X) :=
  zeta_nearLine_residue_le_of_halfLog hX hc he (summable_zetaZeroOrder_mul_poissonWeight hX t) hhalf

/-- The uniform near-line residue comparison, with summability discharged for
the full actual zeta divisor and the half-log estimate still an input. -/
public theorem zeta_nearLine_residue_le_uniform_from_halfLog {X c t E M : ℝ}
    (hX : 1 < X) (hc : 0 ≤ c) (he : windowError X c ≤ 1 / 2) (hE : 0 ≤ E)
    (ht : Real.log (2 + |t|) ≤ M * Real.sqrt X)
    (hhalf : (∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ) ≤
      (1 / 2 : ℝ) * Real.log (2 + |t|) + E) :
    zetaNearLineResidueMass X c t ≤ Real.cosh c * (Real.log (2 + |t|) / Real.sqrt X) +
      Real.cosh c * (24 * windowError X c * M + 16 * E / Real.sqrt X) :=
  zeta_nearLine_residue_le_uniform hX hc he hE ht (summable_zetaZeroOrder_mul_poissonWeight hX t) hhalf

end ReflectedResidueBudget
