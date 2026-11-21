module

public import Theorems.RationalAdeleClassThetaInversion
import Lemmas.RationalAdeleBoxTail

/-! # Fixed-test theta estimates on rational idele classes

Theorem 2.2.3.4(1)–(2), (2.2.3.4)–(2.2.3.5), pp. 82–84, for the
finite translated-box span over ℚ. The large-norm bound uses finite-unit
representatives, not the real projections of arbitrary lifts. The small-norm
bound applies inversion and the absolute Fourier bound one order higher.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- For a fixed finite box sum, theta decays faster than any inverse power of
its idelic norm as that norm tends to infinity. -/
public theorem rationalAdeleBoxSum_theta_large_norm (m : ℕ) :
    ∃ K T : ℝ, 0 < K ∧ 1 ≤ T ∧ ∀ d : C, T ≤ ideleClassNorm d →
      ‖rationalAdeleClassTheta f d‖ ≤ K / ideleClassNorm d ^ m := by
  obtain ⟨K, T, hK, hT, h⟩ := rationalAdeleBoxSum_absolute_theta_tail s c b a g m
  refine ⟨K, T, hK, hT, fun d hd ↦ ?_⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  rw [ideleClassNorm_mk] at hd ⊢
  rw [rationalAdeleClassTheta_mk, rationalAdeleTheta]
  exact (norm_tsum_le_tsum_norm (h k hd).1).trans (h k hd).2

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

local notation "f̂" => rationalAdeleFourier f

/-- After subtracting the two zero-mode contributions, the same theta function
is bounded at small norm by every positive integral power of that norm (and
also by a constant, for order zero). -/
public theorem rationalAdeleBoxSum_theta_small_norm (m : ℕ) :
    ∃ K T : ℝ, 0 < K ∧ 1 ≤ T ∧ ∀ d : C, ideleClassNorm d ≤ T⁻¹ →
      ‖rationalAdeleClassTheta f d - (ideleClassNorm d)⁻¹ • f̂ 0 + f 0‖ ≤
        K * ideleClassNorm d ^ m := by
  obtain ⟨K, T, hK, hT, h⟩ := rationalAdeleBoxSum_absolute_fourier_theta_tail s c b a g (m + 1)
  refine ⟨K, T, hK, hT, fun d hd ↦ ?_⟩
  have hpos := ideleClassNorm_pos d
  have hinv : T ≤ (ideleClassNorm d)⁻¹ := by
    simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr (zero_lt_one.trans_le hT)) hpos).2 hd
  have hFourier : ‖rationalAdeleClassTheta f̂ d⁻¹‖ ≤ K / (ideleClassNorm d)⁻¹ ^ (m + 1) := by
    rw [← map_inv]
    have ht : T ≤ ideleClassNorm d⁻¹ := by rwa [map_inv]
    generalize d⁻¹ = e at ht ⊢
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective e
    rw [ideleClassNorm_mk] at ht ⊢
    rw [rationalAdeleClassTheta_mk, rationalAdeleTheta]
    exact (norm_tsum_le_tsum_norm (h k ht).1).trans (h k ht).2
  have hr : rationalAdeleClassTheta f d - (ideleClassNorm d)⁻¹ • f̂ 0 + f 0 =
      (ideleClassNorm d)⁻¹ • rationalAdeleClassTheta f̂ d⁻¹ := by
    rw [rationalAdeleBoxSum_theta_inversion_class s c b a g d]
    abel
  rw [hr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    _ ≤ (ideleClassNorm d)⁻¹ * (K / (ideleClassNorm d)⁻¹ ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left hFourier (inv_nonneg.mpr hpos.le)
    _ = _ := by
      rw [inv_pow, div_inv_eq_mul, pow_succ]
      field_simp

end Masullo
