module

public import Props.RationalAdeleSchwartzLF
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Lemmas.RationalAdeleAdditiveModulus
import Lemmas.RationalAdeleSchwartzUniformApprox
import Lemmas.RationalAdeleSchwartzC0
import Theorems.RationalAdeleAddHaar
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UrysohnsLemma

/-! # Rational adelic Schwartz tests separate locally integrable functions -/

open NumberField MeasureTheory Filter Set Topology
open scoped Nat

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] {μ : Measure A} {d : A → ℂ}

private theorem tendsto_mul_test_integral {K : Set A} (hd : IntegrableOn d K μ)
    {v : ℕ → A → ℂ} {w : A → ℂ} {C : ℝ}
    (hv : ∀ n, Continuous (v n)) (hC : ∀ n x, ‖v n x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (w x))) :
    Tendsto (fun n ↦ ∫ x in K, d x * v n x ∂μ) atTop (𝓝 (∫ x in K, d x * w x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖d x‖ * C)
    (fun n ↦ hd.aestronglyMeasurable.mul (hv n).aestronglyMeasurable)
    (hd.norm.mul_const C) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ tendsto_const_nhds.mul (hlim x))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC n x) (norm_nonneg _)

private theorem integral_mul_cc_eq_zero (hd : LocallyIntegrable d μ)
    (h : ∀ g : RationalAdeleSchwartzLF, (∫ x, d x * g.toUnion.val x ∂μ) = 0)
    {f : A → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    (∫ x, d x * f x ∂μ) = 0 := by
  obtain ⟨K, hK, hfK, hgK⟩ := exists_rationalAdeleSchwartzLF_uniform_approx hf hfs
  let ε (n : ℕ) : ℝ := (1 / 2) ^ n
  choose g hg he using fun n ↦ hgK (ε n) (by dsimp [ε]; positivity)
  obtain ⟨B, hB⟩ := hfs.exists_bound_of_continuous hf
  have hc (n : ℕ) : Continuous (g n).toUnion.val :=
    (rationalAdeleSchwartzLF_continuous_vanishing (g n)).1
  have hC (n : ℕ) (x : A) : ‖(g n).toUnion.val x‖ ≤ B + 1 := by
    have hn : ε n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      _ ≤ ‖(g n).toUnion.val x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + B := add_le_add ((he n x).trans hn) (hB x)
      _ = B + 1 := add_comm _ _
  have hlim (x : A) : Tendsto (fun n ↦ (g n).toUnion.val x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (Eventually.of_forall fun n ↦ by rw [dist_eq_norm]; exact he n x)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hlimI := tendsto_mul_test_integral (hd.integrableOn_isCompact hK) hc hC hlim
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hfK x hx, mul_zero])] at hlimI
  have hz (n : ℕ) : (∫ x in K, d x * (g n).toUnion.val x ∂μ) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hg n x hx, mul_zero])]
    exact h (g n)
  exact tendsto_nhds_unique hlimI (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))

/-- If the bilinear pairing of a locally integrable function with every
rational adelic Schwartz test vanishes, the function is zero a.e. -/
public theorem rationalAdeleSchwartzLF_ae_zero_of_forall_integral_mul_eq_zero
    (hd : LocallyIntegrable d μ)
    (h : ∀ g : RationalAdeleSchwartzLF, (∫ x, d x * g.toUnion.val x ∂μ) = 0) : d =ᵐ[μ] 0 := by
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  let : T2Space A := t2Space_rationalAdeles
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hd fun K hK ↦ ?_
  obtain ⟨b, hbK, -, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact_of_isGδ
    hK hK.isClosed.isGδ isClosed_empty (disjoint_empty K)
  let v (n : ℕ) (x : A) : ℂ := (b x : ℂ) ^ (n + 1)
  let w : A → ℂ := K.indicator 1
  have hv (n : ℕ) : Continuous (v n) := (Complex.continuous_ofReal.comp b.continuous).pow _
  have hs (n : ℕ) : HasCompactSupport (v n) := by
    apply hbs.mono
    intro x hx
    by_contra hz
    exact hx (by simp [v, show b x = 0 from Function.notMem_support.mp hz])
  have hC (n : ℕ) (x : A) : ‖v n x‖ ≤ 1 := by
    change ‖(b x : ℂ) ^ (n + 1)‖ ≤ 1
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hb x).1]
    exact pow_le_one₀ (hb x).1 (hb x).2
  have hlim (x : A) : Tendsto (fun n ↦ v n x) atTop (𝓝 (w x)) := by
    by_cases hx : x ∈ K
    · have hx' : b x = 1 := by simpa only [hbK, mem_preimage, mem_singleton_iff] using hx
      simp [v, w, hx, hx']
    · have hlt : b x < 1 := lt_of_le_of_ne (hb x).2 (fun e ↦ hx (by simpa [hbK] using e))
      have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (hb x).1 hlt).comp
        (tendsto_add_atTop_nat 1)
      simpa [v, w, hx, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hlimI := tendsto_mul_test_integral (hd.integrableOn_isCompact hbs) hv hC hlim
  have hz (n : ℕ) : (∫ x in tsupport b, d x * v n x ∂μ) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [v, image_eq_zero_of_notMem_tsupport hx])]
    exact integral_mul_cc_eq_zero hd h (hv n) (hs n)
  have hKw : K ⊆ tsupport b := by
    intro x hx
    apply subset_closure
    simp only [Function.mem_support, ne_eq]
    have hx' : b x = 1 := by simpa only [hbK, mem_preimage, mem_singleton_iff] using hx
    simp [hx']
  have hw : (fun x ↦ d x * w x) = K.indicator d := by
    funext x
    by_cases hx : x ∈ K <;> simp [w, hx]
  rw [hw, integral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
    inter_eq_left.mpr hKw] at hlimI
  exact tendsto_nhds_unique hlimI (tendsto_const_nhds.congr fun n ↦ (hz n).symm)

end Masullo
