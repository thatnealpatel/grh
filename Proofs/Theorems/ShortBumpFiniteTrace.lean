module

public import Theorems.ComplexRadialClassLocal
public import Lemmas.FinitePlaceSupport
public import Theorems.IdeleLogSplit

/-! # The short positive bump has no finite-place trace

The radial norm is strictly between `1` and `2` wherever the bump is
nonzero. At a finite place, there is no such norm shell.
-/

open IsDedekindDomain NumberField

namespace Masullo.ShortPositiveLogBump

variable {K : Type*} [Field K] [NumberField K]

/-- The short log bump on the idèle class group of an arbitrary number field. -/
@[expose] public noncomputable def classTest (c : IdeleClassGroup (𝓞 K) K) : ℂ :=
  profile (Real.log (ideleClassNorm c))

private theorem log_mem_of_ne_zero {c : IdeleClassGroup (𝓞 K) K} (hc : classTest c ≠ 0) :
    Real.log (ideleClassNorm c) ∈ Set.Ioo a b :=
  support_profile_subset fun h ↦ hc (by simp [classTest, h])

/-- The test is zero on the entire norm-one fibre, as required in (12.5.1.3). -/
public theorem classTest_normOne (x : ideleClassNormOne (K := K)) :
    classTest (x : IdeleClassGroup (𝓞 K) K) = 0 := by
  by_contra h
  have hpos := a_pos.trans (log_mem_of_ne_zero h).1
  simp [(mem_ideleClassNormOne _).mp x.property] at hpos

/-- Both integrability and genuine vanishing hold for the local term in
(12.5.1.2): Its integrand is identically zero, not just totalized to zero. -/
public theorem finiteTraceTerm_eq_zero (v : HeightOneSpectrum (𝓞 K)) :
    FiniteTraceTermIntegrable v classTest ∧ finiteTraceTerm v classTest = 0 := by
  have hT : 1 < Real.exp b := Real.one_lt_exp_iff.mpr (a_pos.trans a_lt_b)
  have hq : Real.exp b < (v.asIdeal.absNorm : ℝ) := by
    have h2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    exact ((Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mp b_lt_log_two).trans_le h2
  have hker : finiteTraceKernel v classTest = 0 := by
    funext u
    have hz := finitePlaceRestriction_eq_zero v (Real.exp b) hT hq classTest (fun c hc ↦ by
      obtain ⟨hlo, hhi⟩ := log_mem_of_ne_zero hc
      exact ⟨(inv_lt_one_of_one_lt₀ hT).trans ((Real.log_pos_iff (ideleClassNorm_pos c).le).mp (a_pos.trans hlo)),
        (Real.log_lt_iff_lt_exp (ideleClassNorm_pos c)).mp hhi⟩)
      (fun g hg ↦ classTest_normOne ⟨g, (mem_ideleClassNormOne g).mpr hg⟩) u
    simp only [finiteTraceKernel, hz, zero_mul, zero_div, Pi.zero_apply]
  simp [FiniteTraceTermIntegrable, finiteTraceTerm, hker]

end Masullo.ShortPositiveLogBump
