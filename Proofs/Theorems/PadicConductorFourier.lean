module

public import Theorems.PadicIntegralBallFourier
public import Mathlib.Analysis.Fourier.ZMod

import Lemmas.PadicBallPartition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The primitive conductor shell over `ℚ_[p]`

The negative-sign additive Fourier integral of the inverse character on
`ℤ_[p]ˣ`, extended by zero, is a normalized finite Fourier transform on the
conductor ball. Primitivity and finite Fourier inversion give its exact
nonvanishing shell and the modulus of its central value.
-/

open scoped Padic ZMod
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

local notation "K" => ℚ_[p]
local notation "O" => ℤ_[p]
local notation "d" => ((p : ℚ_[p]) ^ n)
local notation "ρ" => PadicInt.toZModPow (p := p) n

/-- The inverse residue character on the integral ball, extended by zero.
At positive level the character is also zero on the nonunit residues. -/
@[expose] public noncomputable def padicConductorTest (χ : DirichletCharacter ℂ (p ^ n))
    (x : K) : ℂ :=
  if h : ‖x‖ ≤ 1 then χ⁻¹ (ρ ⟨x, h⟩) else 0

/-- The negative-sign Fourier integral with additive integral-ball mass one. -/
@[expose] public noncomputable def padicConductorFourier (χ : DirichletCharacter ℂ (p ^ n))
    (y : K) : ℂ :=
  ∫ x, padicConductorTest p χ x * star (padicStdAddChar p (x * y)) ∂padicAddHaar p

private theorem isUnit_padicResidue (hn : 0 < n) (a : O) :
    IsUnit (ρ a) ↔ IsUnit a := by
  refine ⟨fun hu ↦ ?_, IsUnit.map ρ⟩
  by_contra ha
  have hd : p ^ 1 ∣ p ^ n := pow_dvd_pow p hn
  let r := ZMod.castHom hd (ZMod (p ^ 1))
  have h := hu.map r
  change IsUnit (r (ρ a)) at h
  have he : r (ρ a) = PadicInt.toZModPow 1 a :=
    DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow 1 n hn) a
  rw [he] at h
  obtain ⟨b, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (PadicInt.not_isUnit_iff.mp ha)
  simp only [map_mul, map_natCast] at h
  have hp : ((p : ℕ) : ZMod (p ^ 1)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, pow_one]
  rw [hp, zero_mul] at h
  have : Fact (1 < p ^ 1) := ⟨by simpa using (Fact.out : p.Prime).one_lt⟩
  exact not_isUnit_zero h

/-- At positive level, the test is zero at every point outside the local unit
group, and on the unit group it is the inverse of the reduced character. -/
public theorem padicConductorTest_unit (χ : DirichletCharacter ℂ (p ^ n)) (u : Oˣ) :
    padicConductorTest p χ (u : K) = χ⁻¹ (ρ (u : O)) := by
  have hu : ‖(u : K)‖ ≤ 1 := (u : O).2
  rw [padicConductorTest, dite_eq_left hu]
  rfl

public theorem padicConductorTest_eq_zero_of_norm_ne_one (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) {x : K} (hx : ‖x‖ ≠ 1) :
    padicConductorTest p χ x = 0 := by
  unfold padicConductorTest
  split_ifs with h
  · exact MulChar.map_nonunit _ fun hu ↦ hx <| (PadicInt.norm_coe ⟨x, h⟩).trans <|
      PadicInt.isUnit_iff.mp ((isUnit_padicResidue p hn ⟨x, h⟩).mp hu)
  · rfl

private theorem conj_residuePhase {N : ℕ} [NeZero N] (z : ZMod N) :
    star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  simpa only [Complex.star_def] using (ZMod.stdAddChar.map_neg_eq_conj z).symm

private theorem padicConductorFourier_sum (χ : DirichletCharacter ℂ (p ^ n)) (y : K) :
    padicConductorFourier p χ y =
      ((p : ℂ) ^ n)⁻¹ * (∑ j : ZMod (p ^ n), χ⁻¹ j * star (padicStdAddChar p (j.val * y))) *
        {z : K | ‖z‖ ≤ 1}.indicator (fun _ ↦ (1 : ℂ)) (d * y) := by
  classical
  let C (j : ZMod (p ^ n)) : Set K := {x | ‖d⁻¹ * (x - (j.val : K))‖ ≤ 1}
  let k := fun x : K ↦ star (padicStdAddChar p (x * y))
  have hk : Continuous k :=
    ((continuous_padicStdAddChar p).comp (continuous_id.mul continuous_const)).star
  have hd : d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hcompact (j : ZMod (p ^ n)) : IsCompact (C j) := by
    have hball : C j = Metric.closedBall (j.val : K) ‖d‖ := by
      ext x
      change ‖d⁻¹ * (x - (j.val : K))‖ ≤ 1 ↔ x ∈ Metric.closedBall (j.val : K) ‖d‖
      rw [Metric.mem_closedBall, dist_eq_norm, mul_comm d⁻¹, ← div_eq_mul_inv,
        norm_div, div_le_one₀ (norm_pos_iff.mpr hd)]
    rw [hball]
    exact isCompact_closedBall _ _
  have hmeas (j : ZMod (p ^ n)) : MeasurableSet (C j) := (hcompact j).isClosed.measurableSet
  have hi (j : ZMod (p ^ n)) : Integrable ((C j).indicator k) (padicAddHaar p) :=
    (integrable_indicator_iff (hmeas j)).mpr (hk.continuousOn.integrableOn_compact (hcompact j))
  have hC (j : ZMod (p ^ n)) (x : K) : x ∈ C j ↔ ∃ a : O, (a : K) = x ∧ ρ a = j :=
    padic_residue_coset p n j x
  have hs (x : K) : padicConductorTest p χ x * k x =
      ∑ j : ZMod (p ^ n), χ⁻¹ j * (C j).indicator k x := by
    by_cases h : ‖x‖ ≤ 1
    · let a : O := ⟨x, h⟩
      rw [padicConductorTest, dite_eq_left h, Finset.sum_eq_single (ρ a),
        indicator_of_mem ((hC _ _).mpr ⟨a, rfl, rfl⟩)]
      · intro j _ hj
        have hnot : x ∉ C j := by
          intro hm
          obtain ⟨b, hb, rfl⟩ := (hC _ _).mp hm
          exact hj (congrArg ρ (PadicInt.coe_inj.mp hb))
        rw [indicator_of_notMem hnot, mul_zero]
      · simp
    · rw [padicConductorTest, dite_eq_right h, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hnot : x ∉ C j := by
        rintro hm
        obtain ⟨b, rfl, _⟩ := (hC _ _).mp hm
        exact h b.2
      rw [indicator_of_notMem hnot, mul_zero]
  have hf (j : ZMod (p ^ n)) := padicTranslatedBall_fourier p n (j.val : K) y
  unfold padicConductorFourier
  change (∫ x, padicConductorTest p χ x * k x ∂padicAddHaar p) = _
  simp_rw [hs]
  rw [integral_finsetSum _ (fun j _ ↦ (hi j).const_mul _)]
  simp only [integral_const_mul, integral_indicator (hmeas _)]
  simp only [k, C, hf]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- At an integral scaled frequency, the integral is the counting-measure
DFT of the inverse character times the additive mass of one residue ball. -/
public theorem padicConductorFourier_of_integral (χ : DirichletCharacter ℂ (p ^ n))
    (y : K) (a : O) (ha : (a : K) = d * y) :
    padicConductorFourier p χ y = ((p : ℂ) ^ n)⁻¹ * 𝓕 (χ⁻¹ : DirichletCharacter ℂ (p ^ n)) (ρ a) := by
  have hm : d * y ∈ {z : K | ‖z‖ ≤ 1} := by
    change ‖d * y‖ ≤ 1
    rw [← ha]
    exact a.2
  rw [padicConductorFourier_sum, indicator_of_mem hm, mul_one, ZMod.dft_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : ((j.val * a : O) : K) = d * ((j.val : K) * y) := by
    push_cast
    rw [ha]
    ring
  rw [padicStdAddChar_apply_of_scaled_integral p hj, map_mul, map_natCast, ZMod.natCast_zmod_val,
    conj_residuePhase, smul_eq_mul, mul_comm]

private theorem primitiveDirichletDFT {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (k : ZMod N) :
    𝓕 (χ⁻¹ : DirichletCharacter ℂ N) k = χ k * 𝓕 (χ⁻¹ : DirichletCharacter ℂ N) 1 := by
  have h := hχ.inv
  rw [h.fourierTransform_eq_inv_mul_gaussSum, h.fourierTransform_eq_inv_mul_gaussSum, inv_inv,
    ← mul_assoc, ← map_mul, mul_neg_one]

/-- The counting-measure DFT of an inverse primitive character has modulus
`√N` at `1`. Applying the DFT twice at `-1` gives `N`; covariance and
conjugation identify that double transform with the squared amplitude. -/
public theorem primitiveDirichletDFT_norm_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖𝓕 (χ⁻¹ : DirichletCharacter ℂ N) (1 : ZMod N)‖ = Real.sqrt (N : ℝ) := by
  let A := 𝓕 (χ⁻¹ : DirichletCharacter ℂ N) (1 : ZMod N)
  have hconj : 𝓕 χ (-1 : ZMod N) = star A := by
    simp only [A, ZMod.dft_apply, smul_eq_mul, mul_neg, mul_one, star_sum, star_mul',
      conj_residuePhase, neg_neg, MulChar.star_apply', inv_inv]
  have hdf : 𝓕 (χ⁻¹ : DirichletCharacter ℂ N) = fun k ↦ A * χ k := by
    funext k
    rw [primitiveDirichletDFT χ hχ, mul_comm]
  have hA : A * star A = (N : ℂ) := by
    have h := congrFun (ZMod.dft_dft (χ⁻¹ : DirichletCharacter ℂ N)) (-1 : ZMod N)
    simpa only [hdf, ZMod.dft_const_mul, hconj, neg_neg, map_one, smul_eq_mul, mul_one] using h
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg _), pow_two]
  simpa only [norm_mul, norm_star, Complex.norm_natCast] using congrArg norm hA

private theorem padicConductorDFT_one_ne_zero (χ : DirichletCharacter ℂ (p ^ n))
    (hχ : χ.IsPrimitive) : 𝓕 (χ⁻¹ : DirichletCharacter ℂ (p ^ n)) (1 : ZMod (p ^ n)) ≠ 0 := by
  intro hz
  have hzero : ZMod.dft (χ⁻¹ : DirichletCharacter ℂ (p ^ n)) = 0 := by
    ext k
    rw [primitiveDirichletDFT χ hχ, hz, mul_zero]
    rfl
  rw [← map_zero ZMod.dft] at hzero
  have h := congrFun (ZMod.dft.injective hzero) (1 : ZMod (p ^ n))
  simp at h

/-- The Fourier integral is nonzero exactly on the conductor shell. -/
public theorem padicConductorFourier_ne_zero_iff (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsPrimitive) (y : K) :
    padicConductorFourier p χ y ≠ 0 ↔ ‖d * y‖ = 1 := by
  by_cases h : ‖d * y‖ ≤ 1
  · let a : O := ⟨d * y, h⟩
    rw [padicConductorFourier_of_integral p χ y a rfl, primitiveDirichletDFT χ hχ, mul_ne_zero_iff,
      mul_ne_zero_iff, and_iff_right (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p)))),
      and_iff_left (padicConductorDFT_one_ne_zero p χ hχ), MulChar.apply_ne_zero_iff,
      isUnit_padicResidue p hn, PadicInt.isUnit_iff, ← PadicInt.norm_coe]
  · rw [padicConductorFourier_sum, indicator_of_notMem h, mul_zero]
    exact ⟨fun hz ↦ (hz rfl).elim, fun he ↦ (h he.le).elim⟩

/-- On the conductor shell the value is the central Gauss amplitude times
the original character of the unit, not its inverse. -/
public theorem padicConductorFourier_unit (χ : DirichletCharacter ℂ (p ^ n))
    (hχ : χ.IsPrimitive) (u : Oˣ) :
    padicConductorFourier p χ ((u : K) / d) =
      χ (ρ (u : O)) * padicConductorFourier p χ d⁻¹ := by
  have hd : d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  rw [padicConductorFourier_of_integral p χ _ (u : O) (by field_simp),
    padicConductorFourier_of_integral p χ _ 1 (by simp [hd]),
    map_one, primitiveDirichletDFT χ hχ]
  ring

/-- The central conductor-shell Fourier amplitude has modulus `1 / √(p ^ n)`
for the negative-sign kernel and additive Haar mass one on `ℤ_[p]`.
The modulus identity also holds at level one (`n = 0`). -/
public theorem padicConductorFourier_norm
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsPrimitive) :
    ‖padicConductorFourier p χ d⁻¹‖ = (Real.sqrt ((p : ℝ) ^ n))⁻¹ := by
  have hd : d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  rw [padicConductorFourier_of_integral p χ _ 1 (by simp [hd]), map_one, norm_mul,
    primitiveDirichletDFT_norm_one χ hχ, norm_inv, norm_pow, Complex.norm_natCast, Nat.cast_pow]
  have hpos : 0 < (p : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  nth_rw 1 [← Real.sq_sqrt hpos.le]
  rw [pow_two, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 hpos).ne', mul_one]

end Masullo
