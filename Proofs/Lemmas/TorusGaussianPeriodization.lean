module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Periodization on the coordinate torus

The quotient here is the coordinatewise map `ℝᵈ → (ℝ/ℤ)ᵈ` used by
`UnitAddTorus.mFourier`. The periodization works for any continuous function with sufficient
polynomial decay. In particular it accepts Schwartz functions precomposed with an invertible
real linear change of coordinates via `SchwartzMap.compCLMOfContinuousLinearEquiv`.
-/

open Topology
open scoped SchwartzMap

namespace Masullo

variable {d : Type*}

private def intCoords (d : Type*) : (d → ℤ) →ₗ[ℤ] (d → ℝ) :=
  (Int.castAddHom ℝ).toIntLinearMap.compLeft d

private theorem isEmbedding_intCoords : IsEmbedding (intCoords d) :=
  IsEmbedding.piMap fun _ ↦ Int.isUniformEmbedding_coe_real.isEmbedding

section Summability

variable [Fintype d]

/-- The shifted negative-power weight is summable over the integer coordinate lattice for
exponents below minus the dimension. The shift by `1` includes the zero lattice point. -/
public theorem summable_one_add_norm_intCoords_rpow {r : ℝ} (hr : r < -(Fintype.card d : ℝ)) :
    Summable (fun n : d → ℤ ↦ (1 + ‖(fun i ↦ (n i : ℝ))‖) ^ r) := by
  let e := LinearEquiv.ofInjective (intCoords d) isEmbedding_intCoords.injective
  have he : IsEmbedding e :=
    IsEmbedding.subtypeVal.of_comp_iff.mp isEmbedding_intCoords
  let : DiscreteTopology (LinearMap.range (intCoords d)) :=
    (e.toEquiv.toHomeomorphOfIsInducing he.isInducing).discreteTopology
  have hrank : Module.finrank ℤ (LinearMap.range (intCoords d)) = Fintype.card d :=
    e.finrank_eq.symm.trans (Module.finrank_pi ℤ)
  have hs : Summable (fun n : d → ℤ ↦ ‖intCoords d n‖ ^ r) :=
    e.toEquiv.summable_iff.mpr (ZLattice.summable_norm_rpow _ r (by rwa [hrank]))
  refine hs.of_norm_bounded_eventually ((Filter.eventually_cofinite_ne (0 : d → ℤ)).mono ?_)
  intro n hn
  have hn' : 0 < ‖intCoords d n‖ := norm_pos_iff.mpr <| fun h ↦
    hn (isEmbedding_intCoords.injective (h.trans (map_zero (intCoords d)).symm))
  have hr' : r ≤ 0 := hr.le.trans (neg_nonpos.mpr (Nat.cast_nonneg _))
  change |(1 + ‖intCoords d n‖) ^ r| ≤ ‖intCoords d n‖ ^ r
  rw [abs_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hn' (le_add_of_nonneg_left zero_le_one) hr'

section Decay

variable (f : (d → ℝ) → ℂ) (hf : Continuous f) {k : ℕ} (hk : Fintype.card d < k)
  {C : ℝ} (hdecay : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C)

include hf hdecay

private theorem exists_one_add_norm_pow_mul_le :
    ∃ A ≥ (0 : ℝ), ∀ x, (1 + ‖x‖) ^ k * ‖f x‖ ≤ A := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : d → ℝ) 1).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨2 ^ k * max 0 (max M C), by positivity, fun x ↦ ?_⟩
  by_cases hx : ‖x‖ ≤ 1
  · have hMx : ‖f x‖ ≤ M := hM x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    have hA : ‖f x‖ ≤ max 0 (max M C) := hMx.trans ((le_max_left _ _).trans (le_max_right _ _))
    gcongr
    linarith
  · calc
      (1 + ‖x‖) ^ k * ‖f x‖ ≤ (2 * ‖x‖) ^ k * ‖f x‖ := by
        gcongr
        linarith [lt_of_not_ge hx]
      _ = 2 ^ k * (‖x‖ ^ k * ‖f x‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ k * max 0 (max M C) := by
        gcongr
        exact (hdecay x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Uniform rpow domination of the integer translates on each bounded set of real lifts. -/
public theorem exists_periodization_rpow_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ A ≥ (0 : ℝ), ∀ (x : d → ℝ), ‖x‖ ≤ R → ∀ n : d → ℤ,
      ‖f (x + (fun i ↦ (n i : ℝ)))‖ ≤ A * (1 + ‖(fun i ↦ (n i : ℝ))‖) ^ (-(k : ℝ)) := by
  obtain ⟨A, hA, hAf⟩ := exists_one_add_norm_pow_mul_le f hf hdecay
  refine ⟨(1 + R) ^ k * A, by positivity, fun x hx n ↦ ?_⟩
  change ‖f (x + intCoords d n)‖ ≤ _ * (1 + ‖intCoords d n‖) ^ (-(k : ℝ))
  have hn : ‖intCoords d n‖ ≤ ‖x + intCoords d n‖ + R := by
    simpa only [add_sub_cancel_left] using (norm_sub_le (x + intCoords d n) x).trans
      (add_le_add_right hx _)
  have hbase : 1 + ‖intCoords d n‖ ≤ (1 + R) * (1 + ‖x + intCoords d n‖) := by
    nlinarith [mul_nonneg hR (norm_nonneg (x + intCoords d n))]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc
    ‖f (x + intCoords d n)‖ * (1 + ‖intCoords d n‖) ^ k ≤
        ‖f (x + intCoords d n)‖ * ((1 + R) * (1 + ‖x + intCoords d n‖)) ^ k := by gcongr
    _ = (1 + R) ^ k * ((1 + ‖x + intCoords d n‖) ^ k * ‖f (x + intCoords d n)‖) := by
      rw [mul_pow]
      ring
    _ ≤ (1 + R) ^ k * A := by gcongr; exact hAf _

include hk

/-- The integer translates at a fixed real lift are absolutely summable. -/
public theorem summable_norm_periodization_of_decay (x : d → ℝ) :
    Summable (fun n : d → ℤ ↦ ‖f (x + (fun i ↦ (n i : ℝ)))‖) := by
  obtain ⟨A, _, hA⟩ := exists_periodization_rpow_bound f hf hdecay (norm_nonneg x)
  have h := summable_one_add_norm_intCoords_rpow (neg_lt_neg (Nat.cast_lt.mpr hk))
  exact (h.mul_left A).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hA x le_rfl)

private theorem continuous_periodization_of_decay :
    Continuous (fun x : d → ℝ ↦ ∑' n : d → ℤ, f (x + (fun i ↦ (n i : ℝ)))) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  let R := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨A, _, hA⟩ := exists_periodization_rpow_bound f hf hdecay hR
  have h := summable_one_add_norm_intCoords_rpow (neg_lt_neg (Nat.cast_lt.mpr hk))
  have hOn : ContinuousOn (fun y : d → ℝ ↦ ∑' n : d → ℤ, f (y + intCoords d n))
      (Metric.closedBall 0 R) := continuousOn_tsum
    (fun _ ↦ (hf.comp (continuous_id.add continuous_const)).continuousOn) (h.mul_left A)
    (fun n y hy ↦ hA y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy) n)
  exact hOn.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp [Metric.mem_ball, R]))

end Decay

end Summability

private theorem isOpenQuotientMap_coords :
    IsOpenQuotientMap (fun (x : d → ℝ) i ↦ (x i : UnitAddCircle)) :=
  IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

private def torusQuotient (d : Type*) : C((d → ℝ), UnitAddTorus d) :=
  ⟨_, isOpenQuotientMap_coords.continuous⟩

private theorem isQuotientMap_torusQuotient : IsQuotientMap (torusQuotient d) :=
  isOpenQuotientMap_coords.isQuotientMap

private theorem tsum_periodization_add_int (f : (d → ℝ) → ℂ) (x : d → ℝ) (n : d → ℤ) :
    (∑' m : d → ℤ, f ((x + intCoords d n) + intCoords d m)) =
      ∑' m : d → ℤ, f (x + intCoords d m) := by
  have h := (Equiv.addLeft n).tsum_eq (fun m ↦ f (x + intCoords d m))
  change (∑' m : d → ℤ, f (x + intCoords d (n + m))) = _ at h
  simpa only [map_add, ← add_assoc] using h

private theorem periodization_factorsThrough (f : (d → ℝ) → ℂ) :
    Function.FactorsThrough (fun x ↦ ∑' n : d → ℤ, f (x + intCoords d n)) (torusQuotient d) := by
  intro x y hxy
  have h : ∀ i, ∃ n : ℤ, (n : ℝ) = x i - y i := by
    intro i
    have hi : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun hxy i
    have hz : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    simpa only [zsmul_one] using (AddCircle.coe_eq_zero_iff 1).mp hz
  choose n hn using h
  have hx : x = y + intCoords d n := by
    funext i
    change x i = y i + (n i : ℝ)
    rw [hn i, add_comm (y i), sub_add_cancel]
  rw [hx]
  exact tsum_periodization_add_int f y n

variable [Fintype d]

/-- Descend the sum of the integer translates of a continuous, polynomially decaying function
along the coordinatewise unit-circle quotient. -/
public noncomputable def torusPeriodizationOfDecay (f : (d → ℝ) → ℂ) (hf : Continuous f)
    {k : ℕ} (hk : Fintype.card d < k) {C : ℝ} (hdecay : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C) :
    C(UnitAddTorus d, ℂ) :=
  isQuotientMap_torusQuotient.lift ⟨_, continuous_periodization_of_decay f hf hk hdecay⟩
    (periodization_factorsThrough f)

@[simp]
public theorem torusPeriodizationOfDecay_apply_coe (f : (d → ℝ) → ℂ) (hf : Continuous f)
    {k : ℕ} (hk : Fintype.card d < k) {C : ℝ} (hdecay : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C)
    (x : d → ℝ) :
    torusPeriodizationOfDecay f hf hk hdecay (fun i ↦ (x i : UnitAddCircle)) =
      ∑' n : d → ℤ, f (x + (fun i ↦ (n i : ℝ))) :=
  ContinuousMap.congr_fun (isQuotientMap_torusQuotient.lift_comp
    ⟨_, continuous_periodization_of_decay f hf hk hdecay⟩ (periodization_factorsThrough f)) x

/-- Schwartz translates on the integer coordinate lattice are absolutely summable. -/
public theorem summable_norm_schwartz_add_int_pi (f : 𝓢((d → ℝ), ℂ)) (x : d → ℝ) :
    Summable (fun n : d → ℤ ↦ ‖f (x + (fun i ↦ (n i : ℝ)))‖) :=
  summable_norm_periodization_of_decay f f.continuous (Nat.lt_succ_self _)
    (SchwartzMap.norm_pow_mul_le_seminorm ℂ f (Fintype.card d + 1)) x

/-- Periodize a Schwartz function as a continuous map on the unit additive torus. -/
public noncomputable def torusPeriodization (f : 𝓢((d → ℝ), ℂ)) : C(UnitAddTorus d, ℂ) :=
  torusPeriodizationOfDecay f f.continuous (Nat.lt_succ_self _)
    (SchwartzMap.norm_pow_mul_le_seminorm ℂ f (Fintype.card d + 1))

@[simp]
public theorem torusPeriodization_apply_coe (f : 𝓢((d → ℝ), ℂ)) (x : d → ℝ) :
    torusPeriodization f (fun i ↦ (x i : UnitAddCircle)) =
      ∑' n : d → ℤ, f (x + (fun i ↦ (n i : ℝ))) :=
  torusPeriodizationOfDecay_apply_coe ..

end Masullo
