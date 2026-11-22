module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity

/-! Ideal counting and geometric summation for the finite Hecke right line. -/

open Filter Asymptotics Ideal NumberField IsDedekindDomain
open scoped Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The real-valued residue norm of a finite place. -/
@[expose] public noncomputable def finitePlaceNorm (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  v.asIdeal.absNorm

public theorem two_le_finitePlaceNorm (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ finitePlaceNorm v := by
  unfold finitePlaceNorm
  exact_mod_cast Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)

private theorem idealCard_lSeriesSummable {b : ℝ} (hb : 1 < b) :
    LSeriesSummable (fun n ↦ (Nat.card {J : Ideal (𝓞 K) // absNorm J = n} : ℂ)) b := by
  classical
  let A (n : ℕ) : ℝ := Nat.card {J : Ideal (𝓞 K) // absNorm J = n}
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, A k) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr ?_
    intro n
    simp only [Function.comp_apply, Nat.cast_le, A, ← Nat.cast_sum]
    congr 2
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {J : Ideal (𝓞 K) // absNorm J = 0} by simp,
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := A) ?_
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (by simpa)
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim)

set_option maxHeartbeats 400000 in
/-- Sum over finite places by comparing each residue-norm fiber with the
corresponding integral-ideal fiber. A logarithm costs an arbitrarily small
amount of the strict margin to the line `Re s = 1`. -/
private theorem summable_log_div_rpow_places {a : ℝ} (ha : 1 < a) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) ↦
      Real.log (finitePlaceNorm v) / finitePlaceNorm v ^ a) := by
  let A (n : ℕ) : ℂ := Nat.card {J : Ideal (𝓞 K) // absNorm J = n}
  let b : ℝ := (1 + a) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hs := (idealCard_lSeriesSummable (K := K) hb).abscissaOfAbsConv_le
  have hs' : LSeriesSummable (LSeries.logMul A) (a : ℂ) :=
    LSeriesSummable_logMul_of_lt_re (hs.trans_lt (by simpa using hba))
  let B (n : ℕ) : ℝ := Real.log n / (n : ℝ) ^ a
  have hB (n : ℕ) : 0 ≤ B n := div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  have hsum : Summable (fun n : ℕ ↦
      (Nat.card {J : Ideal (𝓞 K) // absNorm J = n} : ℝ) * B n) := by
    refine hs'.norm.congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, B]
    · rw [LSeries.norm_term_eq, ite_eq_right hn]
      simp only [LSeries.logMul, A, B, Complex.ofReal_re, norm_mul,
        ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n)]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      ring
  let S (n : ℕ) : Set (Ideal (𝓞 K)) := {J | absNorm J = n}
  have hfin (n : ℕ) : Finite (S n) := Ring.HasFiniteQuotients.finite_absNorm_eq n
  have hpart (J : Ideal (𝓞 K)) : ∃! n, J ∈ S n := ⟨absNorm J, rfl, fun _ h ↦ h.symm⟩
  have heq (n : ℕ) : (fun J : S n ↦ B (absNorm J.1)) = fun _ ↦ B n :=
    funext fun J ↦ congrArg B J.2
  have hI : Summable (fun J : Ideal (𝓞 K) ↦ B (absNorm J)) := by
    refine (summable_partition (fun J : Ideal (𝓞 K) ↦ hB (absNorm J)) hpart).2 ⟨?_, ?_⟩
    · intro n
      exact Summable.of_finite
    · exact hsum.congr fun n ↦ by rw [heq n, tsum_const, nsmul_eq_mul]; rfl
  change Summable (fun v : HeightOneSpectrum (𝓞 K) ↦ B (absNorm v.asIdeal))
  exact hI.comp_injective HeightOneSpectrum.asIdeal_injective

set_option maxHeartbeats 400000 in
/-- Geometric summation in the positive power, uniform since each residue
norm is at least two. -/
public theorem summable_finitePlace_log_powers {a : ℝ} (ha : 1 < a) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (finitePlaceNorm p.1) / finitePlaceNorm p.1 ^ (a * (p.2 + 1))) := by
  let t (v : HeightOneSpectrum (𝓞 K)) := Real.log (finitePlaceNorm v) / finitePlaceNorm v ^ a
  let r (v : HeightOneSpectrum (𝓞 K)) := (finitePlaceNorm v ^ a)⁻¹
  let R : ℝ := ((2 : ℝ) ^ a)⁻¹
  have ha0 : 0 < a := by linarith
  have hq (v : HeightOneSpectrum (𝓞 K)) := two_le_finitePlaceNorm v
  have hq0 (v : HeightOneSpectrum (𝓞 K)) : 0 < finitePlaceNorm v := by linarith [hq v]
  have hpow (v) : 0 < finitePlaceNorm v ^ a := Real.rpow_pos_of_pos (hq0 v) _
  have ht (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ t v :=
    div_nonneg (Real.log_nonneg (by linarith [hq v])) (hpow v).le
  have hr (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ r v := inv_nonneg.mpr (hpow v).le
  have hR : R < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) ha0)
  have hrR (v : HeightOneSpectrum (𝓞 K)) : r v ≤ R :=
    inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) (hq v) ha0.le)
  have heq (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
      Real.log (finitePlaceNorm v) / finitePlaceNorm v ^ (a * ((k : ℝ) + 1)) =
        t v * r v ^ k := by
    dsimp [t, r]
    rw [mul_add, mul_one, Real.rpow_add (hq0 v), Real.rpow_mul (hq0 v).le,
      Real.rpow_natCast, inv_pow, div_eq_mul_inv, mul_inv]
    simp only [div_eq_mul_inv]
    rw [mul_comm (((finitePlaceNorm v ^ a) ^ k)⁻¹) _, ← mul_assoc]
  simp_rw [heq]
  refine (summable_prod_of_nonneg (fun p ↦ mul_nonneg (ht p.1) (pow_nonneg (hr p.1) _))).2
    ⟨fun v ↦ (summable_geometric_of_lt_one (hr v) ((hrR v).trans_lt hR)).mul_left (t v), ?_⟩
  change Summable (fun v ↦ ∑' k : ℕ, t v * r v ^ k)
  have hgeom (v) : ∑' k : ℕ, r v ^ k = (1 - r v)⁻¹ :=
    tsum_geometric_of_lt_one (hr v) ((hrR v).trans_lt hR)
  simp_rw [tsum_mul_left, hgeom]
  exact ((summable_log_div_rpow_places (K := K) ha).mul_right (1 - R)⁻¹).of_nonneg_of_le
    (fun v ↦ mul_nonneg (ht v) (inv_nonneg.mpr (by linarith [(hrR v).trans_lt hR])))
    (fun v ↦ mul_le_mul_of_nonneg_left
      (inv_anti₀ (by linarith) (sub_le_sub_left (hrR v) _)) (ht v))

end Masullo
