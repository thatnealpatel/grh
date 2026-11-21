module

public import Theorems.RationalAdeleIntegralStageHaar
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Real.Sqrt
import Lemmas.RationalLocalAdditiveModulus

/-! # Extending and translating a rational finite-place test -/

open Function Filter NumberField IsDedekindDomain HeightOneSpectrum Set Topology
open scoped Padic

namespace Masullo

variable {V K : Type*} [TopologicalSpace V] [TopologicalSpace K]

private theorem extend_zero_support [T2Space K] {j : V → K} (hj : Continuous j)
    {f : V → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (Function.extend j f (fun _ ↦ 0)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hc.image hj) ?_
  intro x hx
  by_cases he : ∃ a, j a = x ∧ f a ≠ 0
  · obtain ⟨a, rfl, ha⟩ := he
    exact ⟨a, subset_tsupport _ ha, rfl⟩
  · exfalso
    apply hx
    classical
    unfold Function.extend
    split
    · rename_i h
      exact not_ne_iff.mp (fun hn ↦ he ⟨_, h.choose_spec, hn⟩)
    · rfl

private theorem extend_zero_locallyConstant [T2Space K] {j : V → K}
    (hj : IsOpenEmbedding j) {f : V → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : IsLocallyConstant (Function.extend j f (fun _ ↦ 0)) := by
  rw [IsLocallyConstant.iff_eventually_eq] at hf ⊢
  intro x
  by_cases he : x ∈ range j
  · obtain ⟨a, rfl⟩ := he
    rw [← hj.map_nhds_eq a, Filter.eventually_map]
    simpa only [hj.injective.extend_apply] using hf a
  · let S := j '' tsupport f
    have hS : IsClosed S := (hc.image hj.continuous).isClosed
    have hx : x ∈ Sᶜ := fun ⟨a, _, ha⟩ ↦ he ⟨a, ha⟩
    have hzero (y : K) (hy : y ∈ Sᶜ) : Function.extend j f (fun _ ↦ 0) y = 0 := by
      by_cases h : y ∈ range j
      · obtain ⟨a, rfl⟩ := h
        rw [hj.injective.extend_apply]
        exact not_ne_iff.mp (fun hn ↦ hy ⟨a, subset_tsupport _ hn, rfl⟩)
      · exact Function.extend_apply' _ _ _ h
    filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy using (hzero y hy).trans (hzero x hx).symm

local notation "Place" => HeightOneSpectrum (𝓞 ℚ)
local notation "F[" v "]" => adicCompletion ℚ v
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)

local instance (v : Place) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

/-- The norm on the units of a rational finite completion is locally constant. -/
public theorem rationalLocalUnitNorm_isLocallyConstant (v : Place) :
    IsLocallyConstant (fun y : F[v]ˣ ↦ ‖(y : F[v])‖) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have he (a : F[v]) : ‖e a‖ = ‖a‖ := norm_rationalLocal_padicEquiv v a
  have h (a : F[v]ˣ) :
      ∀ᶠ y : ℚ_[(p[v] : ℕ)] in 𝓝 (e a), ‖y‖ = ‖e a‖ := by
    rw [Metric.eventually_nhds_iff_ball]
    refine ⟨‖e a‖, norm_pos_iff.mpr ((map_ne_zero_iff e e.injective).mpr a.ne_zero), ?_⟩
    intro y hy
    have hlt : ‖y - e a‖ < ‖e a‖ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    conv_lhs => rw [← sub_add_cancel y (e a)]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have ht : Tendsto (fun y : F[v]ˣ ↦ e (y : F[v])) (𝓝 a) (𝓝 (e a)) :=
    (e.toHomeomorph.continuous.comp Units.continuous_val).tendsto a
  simpa only [he] using ht.eventually (h a)

/-- Zero extension of the inverse-square-root weighted test, translated by one.
The default value at `x = -1` is zero. -/
@[expose]
public noncomputable def rationalLocalShiftedTest (v : Place) (f : F[v]ˣ → ℂ) (x : F[v]) : ℂ :=
  Function.extend (Units.val : F[v]ˣ → F[v])
    (fun y ↦ f y / (↑(Real.sqrt ‖(y : F[v])‖) : ℂ)) (fun _ ↦ 0) (1 + x)

/-- The actual translated function is an additive test, including at `-1`. -/
public theorem rationalLocalShiftedTest_properties (v : Place) {f : F[v]ˣ → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsLocallyConstant (rationalLocalShiftedTest v f) ∧
      HasCompactSupport (rationalLocalShiftedTest v f) ∧ rationalLocalShiftedTest v f 0 = f 1 := by
  let j : F[v]ˣ → F[v] := Units.val
  let b (y : F[v]ˣ) := f y / (↑(Real.sqrt ‖(y : F[v])‖) : ℂ)
  have hj : IsOpenEmbedding j := Units.isOpenEmbedding_val
  have hb : IsLocallyConstant b := hf.div ((rationalLocalUnitNorm_isLocallyConstant v).comp (fun r ↦ (↑(Real.sqrt r) : ℂ)))
  have hc' : HasCompactSupport b := hc.mono (fun y hy hz ↦ hy (by simp [b, hz]))
  let a : F[v] ≃ₜ F[v] := Homeomorph.addLeft 1
  refine ⟨(extend_zero_locallyConstant hj hb hc').comp_continuous a.continuous,
    (extend_zero_support hj.continuous hc').comp_homeomorph a, ?_⟩
  change Function.extend j b (fun _ ↦ 0) (1 + 0) = _
  rw [add_zero, ← show j 1 = (1 : F[v]) from rfl, hj.injective.extend_apply]
  simp [b]

end Masullo
