module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

/-! # Entire division detected by jets

The middle exactness argument in §1.2.1 uses entire division, not division
in a space with strip bounds. A quotient at a divisor point must be filled
in by analytic extension, not by taking the value of Lean's totalized `/`.
-/

open Filter Set
open scoped Topology

namespace Masullo

/-- An entire function belongs to the principal entire-function ideal of a nonzero entire
function exactly when the derivatives below the multiplicity vanish at every generator zero.
This includes the zero numerator and a generator with empty divisor. -/
public theorem entire_mul_iff_vanishing_jets {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) :
    (∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q univ ∧ f = g * q) ↔
      ∀ z : ℂ, g z = 0 → ∀ k < (analyticOrderAt g z).toNat, iteratedDeriv k f z = 0 := by
  have hgfin (z : ℂ) : analyticOrderAt g z ≠ ⊤ :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z fun w ↦ hg w (mem_univ w)).not.mpr hg₀
  have hgord (z : ℂ) : ((analyticOrderAt g z).toNat : ℕ∞) = analyticOrderAt g z :=
    ENat.natCast_toNat (hgfin z)
  constructor
  · rintro ⟨q, hq, rfl⟩ z _
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z (mem_univ z))).mp
    rw [hgord z, analyticOrderAt_mul (hg z (mem_univ z)) (hq z (mem_univ z))]
    exact le_self_add
  · intro hj
    by_cases hf₀ : f = 0
    · exact ⟨0, fun _ _ ↦ analyticAt_const, by simp [hf₀]⟩
    have hford (z : ℂ) : ((analyticOrderAt f z).toNat : ℕ∞) = analyticOrderAt f z :=
      ENat.natCast_toNat <|
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z fun w ↦ hf w (mem_univ w)).not.mpr hf₀
    have hle (z : ℂ) : analyticOrderAt g z ≤ analyticOrderAt f z := by
      by_cases hz : g z = 0
      · rw [← hgord z]
        exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z (mem_univ z))).mpr (hj z hz)
      · rw [(hg z (mem_univ z)).analyticOrderAt_eq_zero.mpr hz]
        exact zero_le
    let q := toMeromorphicNFOn (f / g) univ
    have hm : MeromorphicOn (f / g) univ := hf.meromorphicOn.div hg.meromorphicOn
    have hq : AnalyticOnNhd ℂ q univ := by
      intro z hz
      apply ((meromorphicNFOn_toMeromorphicNFOn (f / g) univ) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
        meromorphicOrderAt_div (hf z hz).meromorphicAt (hg z hz).meromorphicAt,
        (hf z hz).meromorphicOrderAt_eq, (hg z hz).meromorphicOrderAt_eq,
        ← hford z, ← hgord z]
      -- Compare the two finite orders as integers.
      have hle' : (analyticOrderAt g z).toNat ≤ (analyticOrderAt f z).toNat := by
        exact_mod_cast (hgord z).trans_le ((hle z).trans_eq (hford z).symm)
      simp only [ENat.map_natCast]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero, WithTop.coe_le_coe]
      exact sub_nonneg.mpr (by exact_mod_cast hle')
    refine ⟨q, hq, funext fun z ↦ ?_⟩
    have hz : z ∈ (univ : Set ℂ) := mem_univ z
    have hgn : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
      apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hg z hz).meromorphicAt).mp
      rw [(hg z hz).meromorphicOrderAt_eq, ← hgord z, ENat.map_natCast]
      exact WithTop.coe_ne_top
    have heq : f =ᶠ[𝓝[≠] z] g * q := by
      filter_upwards [hgn, hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz] with w hw hqw
      change f w = g w * q w
      rw [show q w = f w / g w from hqw, mul_div_cancel₀ _ hw]
    exact ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hg z hz).mul (hq z hz)).continuousAt |>.mp heq).eq_of_nhds

end Masullo
