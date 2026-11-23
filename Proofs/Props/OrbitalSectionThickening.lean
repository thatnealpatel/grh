module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # A compact-unit thickening test for (11.3.2.2)

Replace the two section indicators by the indicator of an open subgroup `V` of a
compact abelian group and use probability Haar. Integrating the product in the
*same* translate variable gives a kernel of height `μ(V)` on each coset, but of
row mass `μ(V)^2`. The normalized action averages over the coset. This is a
normalization test, not an identification with the shell pushforward.
-/

open MeasureTheory Set
open scoped Classical

namespace Masullo.OrbitalSectionThickening

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The left coset `xV`, presented as a preimage under left multiplication by `x⁻¹`. -/
@[expose] public def coset (V : OpenSubgroup G) (x : G) : Set G :=
  (fun y ↦ x⁻¹ * y) ⁻¹' (V : Set G)

/-- On the support of the first indicator, the second is on precisely when
`x⁻¹ * y ∈ V`. Thus the common support in `g` is `Vx⁻¹` or empty. -/
private theorem shared_indicator (V : OpenSubgroup G) (g x y : G) :
    (V : Set G).indicator (1 : G → ℝ) (g * x) * (V : Set G).indicator 1 (g * y) =
      if x⁻¹ * y ∈ V then
        ((fun a ↦ a * x) ⁻¹' (V : Set G)).indicator 1 g
      else 0 := by
  by_cases hx : g * x ∈ (V : Set G)
  · have he : (g * x) * (x⁻¹ * y) = g * y := by simp [mul_assoc]
    have hy : g * y ∈ (V : Set G) ↔ x⁻¹ * y ∈ V := by
      refine ⟨fun hg ↦ ?_, fun hxy ↦ he ▸ V.mul_mem hx hxy⟩
      rw [← he] at hg
      simpa [mul_assoc] using V.mul_mem (V.inv_mem hx) hg
    simp [indicator_apply, hx, hy]
  · simp [indicator_apply, hx]

variable [MeasurableSpace G]

/-- Both indicators are evaluated at translates by the same `g`. -/
@[expose] public noncomputable def kernel (μ : Measure G) (V : OpenSubgroup G) (x y : G) : ℝ :=
  ∫ g, (V : Set G).indicator 1 (g * x) * (V : Set G).indicator 1 (g * y) ∂μ

variable (μ : Measure G) [μ.IsHaarMeasure] (V : OpenSubgroup G)

/-- The subgroup has positive mass, including at index one. -/
public theorem subgroup_mass_pos [IsProbabilityMeasure μ] : 0 < μ.real (V : Set G) :=
  ENNReal.toReal_pos (V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩) (measure_ne_top μ _)

variable [IsTopologicalGroup G] [BorelSpace G]

private theorem measurableSet_coset (x : G) : MeasurableSet (coset V x) :=
  V.isOpen.measurableSet.preimage (continuous_const_mul x⁻¹).measurable

private theorem coset_measure (x : G) : μ (coset V x) = μ (V : Set G) :=
  measure_preimage_mul μ x⁻¹ _

private theorem coset_measureReal (x : G) : μ.real (coset V x) = μ.real (V : Set G) :=
  congrArg ENNReal.toReal (coset_measure μ V x)

/-- The shared-translate integral is `μ(V)` on the coset, and zero off it. -/
public theorem kernel_eq (x y : G) :
    kernel μ V x y = if x⁻¹ * y ∈ V then μ.real (V : Set G) else 0 := by
  have hs := V.isOpen.measurableSet.preimage (continuous_mul_const x).measurable
  simp_rw [kernel, shared_indicator V]
  by_cases h : x⁻¹ * y ∈ V
  · simp_rw [ite_eq_left h]
    simp only [integral_indicator_one hs, measureReal_def, measure_preimage_mul_right]
  · simp [h]

/-- The diagonal has height `μ(V)`, before accounting for the mass of the coset. -/
public theorem kernel_diagonal (x : G) : kernel μ V x x = μ.real (V : Set G) := by
  simp [kernel_eq]

/-- The row is supported on `xV`, which itself has mass `μ(V)`. -/
public theorem kernel_row_mass (x : G) :
    (∫ y, kernel μ V x y ∂μ) = (μ.real (V : Set G)) ^ 2 := by
  have hrow (y : G) : kernel μ V x y = (coset V x).indicator (fun _ ↦ μ.real (V : Set G)) y := by
    rw [kernel_eq, indicator_apply]
    rfl
  simp_rw [hrow]
  rw [integral_indicator_const _ (measurableSet_coset V x), coset_measureReal μ V x,
    smul_eq_mul, pow_two]

variable [IsProbabilityMeasure μ]

/-- In the compact case the index is finite and the probability mass per coset
is the reciprocal of that index. -/
public theorem subgroup_mass_eq_inv_index [CompactSpace G] :
    μ.real (V : Set G) = (V.toSubgroup.index : ℝ)⁻¹ := by
  let : V.toSubgroup.FiniteIndex := V.toSubgroup.finiteIndex_of_finite_quotient
  have h := V.toSubgroup.index_mul_measure V.isOpen.measurableSet μ
  rw [measure_univ] at h
  have hm := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hm
  exact eq_inv_of_mul_eq_one_right hm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dividing by the row mass gives the average against the normalized
restriction of ambient Haar to `xV`. -/
public theorem normalized_kernel_eq_coset_average {f : G → E} (hf : Integrable f μ) (x : G) :
    Integrable (fun y ↦ kernel μ V x y • f y) μ ∧
      ((μ.real (V : Set G)) ^ 2)⁻¹ • (∫ y, kernel μ V x y • f y ∂μ) =
        ⨍ y in coset V x, f y ∂μ := by
  let m := μ.real (V : Set G)
  have hrow : (fun y ↦ kernel μ V x y • f y) = (coset V x).indicator (fun y ↦ m • f y) := by
    funext y
    rw [kernel_eq, indicator_apply]
    by_cases hy : x⁻¹ * y ∈ V <;> simp [coset, hy, m]
  have hs := measurableSet_coset V x
  refine ⟨?_, ?_⟩
  · rw [hrow]
    exact (hf.smul m).integrableOn.integrable_indicator hs
  rw [hrow, integral_indicator hs, integral_smul, setAverage_eq, coset_measureReal μ V x,
    smul_smul, ← inv_pow, pow_two, mul_assoc, inv_mul_cancel₀ (subgroup_mass_pos μ V).ne', mul_one]

variable [CompleteSpace E]

/-- In particular the normalized action fixes every integrable function
constant under right multiplication by elements of `V`. -/
public theorem normalized_kernel_eq_self_of_invariant {f : G → E} (hf : Integrable f μ)
    (hV : ∀ (x : G) (v : V), f (x * (v : G)) = f x) (x : G) :
    ((μ.real (V : Set G)) ^ 2)⁻¹ • (∫ y, kernel μ V x y • f y ∂μ) = f x := by
  rw [(normalized_kernel_eq_coset_average μ V hf x).2]
  have heq : EqOn f (fun _ ↦ f x) (coset V x) := by
    intro y hy
    simpa [mul_assoc] using hV x ⟨x⁻¹ * y, hy⟩
  rw [setAverage_eq, setIntegral_congr_fun (measurableSet_coset V x) heq, ← setAverage_eq]
  have hp : μ (coset V x) ≠ 0 := by
    rw [coset_measure]
    exact V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩
  exact setAverage_const hp (measure_ne_top μ _) _

end Masullo.OrbitalSectionThickening
