module

public import Lemmas.RationalLocalPrincipalValue
public import Props.RationalFiniteHaar

/-! # Admissibility of rational finite-place radial tests -/

open Function NumberField IsDedekindDomain HeightOneSpectrum Set

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "P[" v "]" => (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℝ)

/-- A compact log profile pulls back to a locally constant compact test.
No regularity of the profile itself is needed at a finite place. -/
public theorem rationalLocalRadialTest_properties (v : V) {F : ℝ → ℂ}
    (hF : HasCompactSupport F) :
    let f := fun y : K[v]ˣ ↦ F (Real.log ‖(y : K[v])‖)
    IsLocallyConstant f ∧ HasCompactSupport f := by
  intro f
  refine ⟨(rationalLocalUnitNorm_isLocallyConstant v).comp (F ∘ Real.log), ?_⟩
  let l := Real.log P[v]
  have hl : 0 < l := Real.log_pos (RationalLocalNormShell.one_lt_prime v)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hF.isBounded
  obtain ⟨M, hM⟩ := exists_nat_ge (R / l)
  let T : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hS (k : ℤ) : IsCompact (rationalLocalNormShell v k) := by
    rw [RationalLocalNormShell.eq_translate]
    exact (isCompact_range_rationalLocalUnitInclusion v).image (continuous_const.mul continuous_id)
  refine HasCompactSupport.of_support_subset_isCompact (T.finite_toSet.isCompact_biUnion (fun k _ ↦ hS k)) ?_
  intro y hy
  have hy' : y ∈ ⋃ k : ℤ, rationalLocalNormShell v k := by
    rw [RationalLocalNormShell.iUnion_eq_univ]
    exact mem_univ y
  obtain ⟨k, hk⟩ := mem_iUnion.mp hy'
  refine mem_iUnion₂.mpr ⟨k, ?_, hk⟩
  have hbound := hR (subset_tsupport _ hy)
  have hlog : |(k : ℝ)| * l ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, RationalLocalNormShell.log_norm hk,
      abs_mul, abs_neg, abs_of_pos (Real.log_pos (RationalLocalNormShell.one_lt_prime v))] using hbound
  have habs : |(k : ℝ)| ≤ M :=
    ((le_div_iff₀ hl).mpr hlog).trans hM
  have habsz : |k| ≤ (M : ℤ) := by exact_mod_cast habs
  simpa only [Finset.mem_coe, T, Finset.mem_Icc, ← abs_le] using habsz

/-- For a radial test, the unit subtraction in (B.4.4.14) removes exactly
its entire norm-one shell, and the square-root weight is unchanged. -/
public theorem rationalLocalRadial_subtraction (v : V) (F : ℝ → ℂ) (y : K[v]ˣ) :
    let f := fun z : K[v]ˣ ↦ F (Real.log ‖(z : K[v])‖)
    (f y - f 1 * rationalLocalUnitIndicator v y) * (↑(Real.sqrt ‖(y : K[v])‖) : ℂ) /
      (↑‖1 - (y : K[v])‖ : ℂ) = rationalLocalRadialSubtracted v F y := by
  intro f
  have hmem := RationalLocalNormShell.mem_unitRange_iff v y
  by_cases hy : ‖(y : K[v])‖ = 1
  · rw [rationalLocalUnitIndicator, indicator_of_mem (hmem.mpr hy), rationalLocalRadialSubtracted,
      ite_eq_left hy]
    simp [f, hy]
  · rw [rationalLocalUnitIndicator, indicator_of_notMem (mt hmem.mp hy), rationalLocalRadialSubtracted,
      ite_eq_right hy]
    simp [f, rationalLocalRadialKernel, Real.sqrt_eq_rpow]

end Masullo
