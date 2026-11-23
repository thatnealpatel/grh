module

public import Theorems.RationalRadialHilbertQuotient
import Props.BoundaryLogJet
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The strict boundary obstruction on the rational radial Hilbert quotient

For the symmetric base `[-α, α]` and the trivial norm-one isotype over
`ℚ`, we use the quotient by the actual half-twisted LF theta range. A
continuous functional agreeing with a boundary Mellin jet on original
compact radial representatives must satisfy the strict Sobolev threshold.
This is a necessary condition for descent, not a trace or a totality result.
-/

open MeasureTheory NumberField Set
open scoped ContDiff

namespace Masullo

private theorem root_sq_eq_logSobolevWeight {α : ℝ} (hab : -α ≤ α) (s x : ℝ) :
    symmetricStripWeightRoot α s x ^ 2 = logSobolevWeight (-α) α s x := by
  simpa only [logSobolevWeight, zero_mul, Real.exp_zero, mul_one, zero_add] using
    symmetricStripWeightRoot_mul_exp_sq (show 0 ≤ α by linarith) s 0 x

private theorem memLp_radialRootMul {α : ℝ} (hab : -α ≤ α) (s : ℝ)
    (u : logWeightedProfiles univ) :
    MemLp (fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * u.val x) 2 volume := by
  have h : Continuous (fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * u.val x) :=
    (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)).mul
      u.property.1.continuous
  rw [memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable]
  refine (integrable_logSobolevWeight_mul_norm_sq (s := s) hab
    ⟨u.property.1, fun w ↦ u.property.2 ⟨w, mem_univ _⟩⟩).congr (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg
    (symmetricStripWeightRoot_pos α s x).le, root_sq_eq_logSobolevWeight hab]

private noncomputable def radialRootOnProfiles {α : ℝ} (hab : -α ≤ α) (s : ℝ) :
    logWeightedProfiles univ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun u := (memLp_radialRootMul hab s u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(memLp_radialRootMul hab s (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memLp_radialRootMul hab s u).toLp _)
        ((memLp_radialRootMul hab s v).toLp _),
      (memLp_radialRootMul hab s u).coeFn_toLp,
      (memLp_radialRootMul hab s v).coeFn_toLp] with x huv h hu hv
    rw [huv, h, Pi.add_apply, hu, hv, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(memLp_radialRootMul hab s (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_radialRootMul hab s u).toLp _),
      (memLp_radialRootMul hab s u).coeFn_toLp] with x hcu h hu
    rw [RingHom.id_apply, hcu, h, Pi.smul_apply, hu, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, mul_left_comm]

private theorem norm_radialRootOnProfiles {α : ℝ} (hab : -α ≤ α) (s : ℝ)
    (u : logWeightedProfiles univ) :
    ‖radialRootOnProfiles hab s u‖ = ‖rationalRadialHilbertInclusion hab s u‖ := by
  let v : logWeightedProfiles (Icc (-α) α) :=
    ⟨u.val, u.property.1, fun w ↦ u.property.2 ⟨w, mem_univ _⟩⟩
  have h : logSobolevAllToLp hab s u = logSobolevToLp hab s v :=
    Lp.ext ((logSobolevAllToLp_ae_eq hab s u).trans (logSobolevToLp_ae_eq hab s v).symm)
  change ‖(memLp_radialRootMul hab s u).toLp _‖ = ‖logSobolevAllToLp hab s u‖
  rw [h, norm_logSobolevToLp, Lp.norm_toLp, (memLp_radialRootMul hab s u).eLpNorm_eq_integral_rpow_norm
    (by norm_num) (by simp), ENNReal.toReal_ofReal (by positivity)]
  norm_num only [ENNReal.toReal_ofNat, ← Real.rpow_natCast _ 2, Nat.cast_ofNat]
  rw [Real.sqrt_eq_rpow, one_div]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  dsimp only
  rw [norm_mul, Real.rpow_two, mul_pow, Complex.norm_real, Real.norm_of_nonneg
    (symmetricStripWeightRoot_pos α s x).le, root_sq_eq_logSobolevWeight hab, Real.rpow_two]

private noncomputable def radialRootIsometry {α : ℝ} (hab : -α ≤ α) (s : ℝ) :
    rationalRadialHilbert hab s →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (radialRootOnProfiles hab s).extendOfIsometry (denseRange_rationalRadialHilbertInclusion hab s)
    (norm_radialRootOnProfiles hab s)

private theorem mem_allWeight_of_compact {u : ℝ → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : u ∈ logWeightedProfiles univ := by
  refine ⟨hu, fun a ↦ ?_⟩
  have hw : ContDiff ℝ ∞ (logStageWeight a) := Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact ⟨hc.mul_left.toSchwartzMap (hw.mul hu), fun _ ↦ rfl⟩

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

set_option linter.concreteInstances false in
/-- If a continuous linear functional on the separated rational radial
Hilbert quotient agrees with the order-`m` boundary Mellin pairing on all
compactly supported original smooth profiles, then `2m + 1 < s`. In
particular agreement is impossible at equality, and even evaluation is
impossible for `s ≤ 1`. No zero of zeta on a prescribed boundary is assumed. -/
public theorem rationalRadialQuotient_boundaryJet_lt {α s : ℝ} (hab : -α ≤ α) (hs : 0 ≤ s)
    {z : ℂ} (hz : |z.re| = α) (m : ℕ)
    (F : rationalRadialHilbertQuotient hab s →L[ℂ] ℂ)
    (hF : ∀ u : logWeightedProfiles univ, HasCompactSupport u.val →
      F (rationalRadialQuotientMap hab s (rationalRadialThetaTestRange.mkQ u)) =
        ∫ x : ℝ, u.val x * ((x : ℂ) ^ m * Complex.exp (z * x))) :
    2 * (m : ℝ) + 1 < s := by
  let e := (radialRootIsometry hab s).equivRange
  let f := (F.comp (rationalRadialQuotientProjection hab s)).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq _ f
  apply (boundaryLogJet_exists_smooth_extension_iff hs hz m).mp
  refine ⟨g, fun u hu hc ↦ ?_⟩
  let U : logWeightedProfiles univ := ⟨u, mem_allWeight_of_compact hu hc⟩
  let y := rationalRadialHilbertInclusion hab s U
  have he : (e y).val = (memLp_radialRootMul hab s U).toLp _ :=
    (radialRootOnProfiles hab s).extendOfIsometry_eq _ _ U
  change g ((memLp_radialRootMul hab s U).toLp _) = _
  rw [← he, hg]
  change F (rationalRadialQuotientProjection hab s (e.symm (e y))) = _
  rw [e.symm_apply_apply]
  simpa only [rationalRadialQuotientMap, hilbertDenseQuotientMap_mk] using hF U hc

end Masullo
