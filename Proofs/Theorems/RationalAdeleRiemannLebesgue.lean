module

public import Theorems.RationalAdeleDualPlancherel
import Theorems.RationalAdeleSchwartzDensity
import Lemmas.RationalAdeleSchwartzC0
import Lemmas.RationalAdeleLFStageOperators

/-! # Riemann–Lebesgue on the rational adelic dual

The normalized rational case of Lemma D.1.1.2(1), pp. 746–747:
The Fourier integral of an `L¹` function is continuous and vanishes at
infinity on the full compact-open dual. We use uniform approximation by
the transforms of rational Schwartz tests instead of the cited general
locally compact abelian group theorem.
-/

open NumberField MeasureTheory Filter Topology
open scoped ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => PontryaginDual (Multiplicative A)
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

private theorem frequency_continuous_vanishing {f : A → ℂ} (hf : Integrable f μA) :
    Continuous (rationalAdeleFourier f) ∧ Tendsto (rationalAdeleFourier f) (cocompact A) (𝓝 0) := by
  obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  choose g hg using fun n ↦ exists_rationalAdeleSchwartzLF_L1_approx hf (hε n).1
  let F (n : ℕ) := rationalAdeleFourier (g n).toUnion.val
  have hF (n : ℕ) : Continuous (F n) ∧ Tendsto (F n) (cocompact A) (𝓝 0) := by
    rw [show F n = _ from (rationalAdeleLFFourier_eq (g n)).symm]
    exact rationalAdeleSchwartzLF_continuous_vanishing (rationalAdeleLFFourier (g n))
  have hlim : TendstoUniformly F (rationalAdeleFourier f) atTop := by
    refine EMetric.tendstoUniformly_iff.mpr fun δ hδ ↦ ((tendsto_order.mp hεlim).2 δ hδ).mono ?_
    intro n hn y
    rw [eDist_eq_eNorm_sub]
    exact (eNorm_rationalAdeleFourier_sub_le hf (integrable_rationalAdeleSchwartzLF (g n)) y).trans_lt
      ((hg n).trans hn)
  exact ⟨hlim.continuous ((Eventually.of_forall fun n ↦ (hF n).1).frequently),
    hlim.tendsto_of_eventually_tendsto (Eventually.of_forall fun n ↦ (hF n).2) tendsto_const_nhds⟩

/-- The Fourier integral of every integrable rational adelic function is
continuous and vanishes at infinity on the full compact-open dual. -/
public theorem rationalAdeleDualFourier_continuous_vanishing {f : A → ℂ}
    (hf : Integrable f μA) :
    Continuous (rationalAdeleDualFourier f) ∧
      Tendsto (rationalAdeleDualFourier f) (cocompact D) (𝓝 0) := by
  let e : A ≃ₜ D := rationalAdelePontryaginDualEquiv.toHomeomorph
  have he : rationalAdeleDualFourier f = rationalAdeleFourier f ∘ e.symm := by
    funext χ
    obtain ⟨y, rfl⟩ := e.surjective χ
    rw [Function.comp_apply, e.symm_apply_apply]
    exact rationalAdeleDualFourier_pairing f y
  rw [he]
  obtain ⟨hc, ht⟩ := frequency_continuous_vanishing hf
  exact ⟨hc.comp e.symm.continuous, ht.comp e.symm.map_cocompact.le⟩

end Masullo
