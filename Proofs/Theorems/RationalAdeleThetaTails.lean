module

public import Theorems.RationalAdeleClassThetaInversion
import Lemmas.RationalAdeleBoxTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Theta estimates on rational idele classes

Theorem 2.2.3.4(1)–(2), (2.2.3.4)–(2.2.3.5), pp. 82–84, for the
finite translated-box span over ℚ. The large-norm bound uses finite-unit
representatives, not the real projections of arbitrary lifts. The small-norm
bound applies inversion and the absolute Fourier bound one order higher.
For fixed box geometry and bounded Schwartz factors, the bounds are uniform
with threshold one, as in (4)–(5). This does not identify bounded sets of the
adelic LF space. With both zero modes zero, the two powers give log-norm decay.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f[" b "]" => rationalAdeleBoxSum s c b a g

/-- For a fixed box sum the uncorrected theta function has rapid decay
on the large-norm side. -/
public theorem rationalAdeleBoxSum_theta_large_norm (m : ℕ) :
    ∃ K T : ℝ, 0 < K ∧ 1 ≤ T ∧ ∀ d : C, T ≤ ideleClassNorm d →
      ‖rationalAdeleClassTheta f[b] d‖ ≤ K / ideleClassNorm d ^ m := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_absolute_theta_tail s c a g m
    (B := fun i ↦ {b i}) (fun i _ ↦ Bornology.isVonNBounded_singleton (b i))
  refine ⟨K, 1, hK, le_rfl, fun d hd ↦ ?_⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  rw [ideleClassNorm_mk] at hd ⊢
  rw [rationalAdeleClassTheta_mk, rationalAdeleTheta]
  obtain ⟨hs, hbound⟩ := h b (fun _ _ ↦ Set.mem_singleton _) k hd
  exact (norm_tsum_le_tsum_norm hs).trans hbound

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

local notation "f̂[" b "]" => rationalAdeleFourier (rationalAdeleBoxSum s c b a g)

/-- With fixed coefficients, centers, and scales, a single constant works
for all choices of real factors from the indicated bounded sets. The estimates
include norm one and retain both corrections on the small-norm side. -/
public theorem rationalAdeleBoxSum_uniform_theta_tails (m : ℕ) {B : I → Set 𝓢(ℝ, ℂ)}
    (hB : ∀ i ∈ s, Bornology.IsVonNBounded ℂ (B i)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : I → 𝓢(ℝ, ℂ)), (∀ i ∈ s, b i ∈ B i) →
      (∀ d : C, 1 ≤ ideleClassNorm d → ‖rationalAdeleClassTheta f[b] d‖ ≤ K / ideleClassNorm d ^ m) ∧
      (∀ d : C, ideleClassNorm d ≤ 1 →
        ‖rationalAdeleClassTheta f[b] d - (ideleClassNorm d)⁻¹ • f̂[b] 0 + f[b] 0‖ ≤
          K * ideleClassNorm d ^ m) := by
  obtain ⟨Khi, hKhi, hlarge⟩ := rationalAdeleBoxSum_uniform_absolute_theta_tail s c a g m hB
  obtain ⟨Klo, _, hsmall⟩ := rationalAdeleBoxSum_uniform_absolute_fourier_theta_tail s c a g (m + 1) hB
  refine ⟨max Khi Klo, hKhi.trans_le (le_max_left ..), fun b hb ↦ ⟨?_, ?_⟩⟩
  · intro d hd
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
    have hpos := ideleClassNorm_pos (QuotientGroup.mk k)
    rw [ideleClassNorm_mk] at hd hpos ⊢
    rw [rationalAdeleClassTheta_mk, rationalAdeleTheta]
    obtain ⟨hs, hbound⟩ := hlarge b hb k hd
    exact (norm_tsum_le_tsum_norm hs).trans (hbound.trans
      (div_le_div_of_nonneg_right (le_max_left ..) (by positivity)))
  · intro d hd
    have hpos := ideleClassNorm_pos d
    have hFourier : ‖rationalAdeleClassTheta f̂[b] d⁻¹‖ ≤ Klo / (ideleClassNorm d)⁻¹ ^ (m + 1) := by
      rw [← map_inv]
      have ht : 1 ≤ ideleClassNorm d⁻¹ := by rw [map_inv]; exact (one_le_inv₀ hpos).mpr hd
      generalize d⁻¹ = e at ht ⊢
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective e
      rw [ideleClassNorm_mk] at ht ⊢
      rw [rationalAdeleClassTheta_mk, rationalAdeleTheta]
      exact (norm_tsum_le_tsum_norm (hsmall b hb k ht).1).trans (hsmall b hb k ht).2
    have hr : rationalAdeleClassTheta f[b] d - (ideleClassNorm d)⁻¹ • f̂[b] 0 + f[b] 0 =
        (ideleClassNorm d)⁻¹ • rationalAdeleClassTheta f̂[b] d⁻¹ := by
      rw [rationalAdeleBoxSum_theta_inversion_class s c b a g d]
      abel
    rw [hr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    calc
      _ ≤ (ideleClassNorm d)⁻¹ * (Klo / (ideleClassNorm d)⁻¹ ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hFourier (inv_nonneg.mpr hpos.le)
      _ = Klo * ideleClassNorm d ^ m := by
        rw [inv_pow, div_inv_eq_mul, pow_succ]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)

/-- A single log-norm decay constant works on the subfamily with both zero
modes zero, for every rational idele class. -/
public theorem rationalAdeleBoxSum_uniform_theta_log_bound (m : ℕ) {B : I → Set 𝓢(ℝ, ℂ)}
    (hB : ∀ i ∈ s, Bornology.IsVonNBounded ℂ (B i)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : I → 𝓢(ℝ, ℂ)), (∀ i ∈ s, b i ∈ B i) →
      f[b] 0 = 0 → f̂[b] 0 = 0 → ∀ d : C,
        ‖rationalAdeleClassTheta f[b] d‖ ≤ K * Real.exp (-(m : ℝ) * |Real.log (ideleClassNorm d)|) := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_theta_tails s c a g m hB
  refine ⟨K, hK, fun b hb hzero hfzero d ↦ ?_⟩
  obtain ⟨hlarge, hsmall⟩ := h b hb
  have hpos := ideleClassNorm_pos d
  by_cases hd : 1 ≤ ideleClassNorm d
  · rw [abs_of_nonneg (Real.log_nonneg hd), neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log hpos, ← div_eq_mul_inv]
    exact hlarge d hd
  · have hd' := le_of_not_ge hd
    rw [abs_of_nonpos (Real.log_nonpos hpos.le hd'), neg_mul_neg, Real.exp_nat_mul, Real.exp_log hpos]
    simpa only [hfzero, hzero, smul_zero, sub_zero, add_zero] using hsmall d hd'

/-- For a fixed box sum the corrected theta function has rapid decay
on the small-norm side. -/
public theorem rationalAdeleBoxSum_theta_small_norm (m : ℕ) :
    ∃ K T : ℝ, 0 < K ∧ 1 ≤ T ∧ ∀ d : C, ideleClassNorm d ≤ T⁻¹ →
      ‖rationalAdeleClassTheta f[b] d - (ideleClassNorm d)⁻¹ • f̂[b] 0 + f[b] 0‖ ≤
        K * ideleClassNorm d ^ m := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_theta_tails s c a g m
    (B := fun i ↦ {b i}) (fun i _ ↦ Bornology.isVonNBounded_singleton (b i))
  exact ⟨K, 1, hK, le_rfl, by simpa only [inv_one] using (h b (fun _ _ ↦ Set.mem_singleton _)).2⟩

/-- For an individual test with both zero modes zero, (2.2.3.6) holds
throughout the rational idele class group. -/
public theorem rationalAdeleBoxSum_theta_log_bound (m : ℕ)
    (hzero : f[b] 0 = 0) (hfzero : f̂[b] 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : C,
      ‖rationalAdeleClassTheta f[b] d‖ ≤ K * Real.exp (-(m : ℝ) * |Real.log (ideleClassNorm d)|) := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_theta_log_bound s c a g m
    (B := fun i ↦ {b i}) (fun i _ ↦ Bornology.isVonNBounded_singleton (b i))
  exact ⟨K, hK, h b (fun _ _ ↦ Set.mem_singleton _) hzero hfzero⟩

end Masullo
