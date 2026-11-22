module

import Lemmas.FiniteHeckeRestriction
public import Theorems.FiniteHeckeLocalZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # The positive finite-place input to the global zeta integral

In (3.2.2.6), p. 126, Masullo takes absolute values before factoring the
integral over the ideles. For the standard indicator (3.4.3.7), p. 152,
we evaluate the local absolute integral and bound the products of the
unramified tail factors in the stage order. The local mass is that of the
integral units, as in (A.3.2.2), p. 560, not necessarily one.
This supplies two inputs to the right-half-plane justification requested
on p. 144 for (3.4.1.6), not the global density identity.
Source correspondence is provisional (Markdown and PDF layout).
-/

open Filter IsDedekindDomain NumberField HeightOneSpectrum MeasureTheory Set
open scoped Classical ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "G" v => (adicCompletion K v)ˣ

/-- The trivial-character finite Euler factor at a real argument. -/
@[expose] public noncomputable def finiteHeckeRealEulerFactor (v : Places) (σ : ℝ) : ℝ :=
  (1 - Real.exp (-σ * Real.log (finitePlaceNorm v)))⁻¹

private theorem ofReal_finiteHeckeRealEulerFactor (z : Places → ℂ) (v : Places) (hz : z v = 1)
    (σ : ℝ) : (finiteHeckeRealEulerFactor v σ : ℂ) = finiteHeckeEulerFactor z v σ := by
  simp [finiteHeckeRealEulerFactor, finiteHeckeEulerFactor, finiteHeckeMonomial, hz,
    Complex.ofReal_exp]

private theorem one_le_finiteHeckeRealEulerFactor (v : Places) {σ : ℝ} (hσ : 0 < σ) :
    1 ≤ finiteHeckeRealEulerFactor v σ := by
  have hq : 1 < finitePlaceNorm v := (by norm_num : (1 : ℝ) < 2).trans_le (two_le_finitePlaceNorm v)
  have he : Real.exp (-σ * Real.log (finitePlaceNorm v)) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hσ) (Real.log_pos hq))
  exact (one_le_inv₀ (sub_pos.mpr he)).2 (sub_le_self _ (Real.exp_nonneg _))

/-- The absolute value of the standard local test is the trivial-character
weight at `s.re`, so its integral is the corresponding real Euler factor
scaled by the unit mass. The absolute value removes the character even
if it is ramified; this theorem always uses the test `1_{O_v}`. -/
public theorem finiteHeckeLocalZeta_norm (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (v : Places) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (μ : Measure (G v)) [Measure.IsMulLeftInvariant μ] (hμ : μ (finiteLocalUnitSet v) ≠ ∞)
    {s : ℂ} (hs : 0 < s.re) :
    let F := {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1}.indicator
      (fun x ↦ χ.restrict v (x : v.adicCompletion K) * (‖(x : v.adicCompletion K)‖ : ℂ) ^ s)
    Integrable F μ ∧ (∫ x, ‖F x‖ ∂μ) =
      μ.real (finiteLocalUnitSet v) * finiteHeckeRealEulerFactor v s.re := by
  intro F
  classical
  let χ₀ : HeckeCharacter (𝓞 K) K := 1
  have hr (x : G v) : χ₀.restrict v (x : v.adicCompletion K) = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (1 : HeckeCharacter (𝓞 K) K) _ = 1
    rfl
  have hu : χ₀.IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    (fun x ↦ hr (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom x))
  have hc : finiteHeckeCoefficient χ₀ v = 1 := by
    obtain ⟨p, hp⟩ := (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    rw [finiteHeckeCoefficient, ite_eq_left hu, hu.localValue_eq p hp]
    exact hr (Units.mk0 p hp.ne_zero)
  let F₀ := {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1}.indicator
    (fun x ↦ χ₀.restrict v (x : v.adicCompletion K) * (‖(x : v.adicCompletion K)‖ : ℂ) ^ (s.re : ℂ))
  have hF₀ := finiteHeckeLocalZeta_unramified χ₀ (fun _ ↦ norm_one) v μ hμ hu
    (s := (s.re : ℂ)) hs
  change Integrable F₀ μ ∧ (∫ x, F₀ x ∂μ) = _ at hF₀
  have hnorm (x : G v) : (‖F x‖ : ℂ) = F₀ x := by
    by_cases hx : x ∈ {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1}
    · simp only [F, F₀, indicator_of_mem hx, hr, one_mul, norm_mul,
        norm_heckeRestrict_of_unitary χ hχ v x.ne_zero,
        Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr x.ne_zero),
        Complex.ofReal_cpow (norm_nonneg _)]
    · simp only [F, F₀, indicator_of_notMem hx, norm_zero, Complex.ofReal_zero]
  have hB : MeasurableSet {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1} :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hweight := (continuous_finiteHeckeRestriction χ v).mul
    ((Complex.continuous_ofReal_cpow_const hs).comp (continuous_norm.comp Units.continuous_val))
  have hFmeas : AEStronglyMeasurable F μ := (hweight.measurable.indicator hB).aestronglyMeasurable
  have hFi : Integrable F μ := (integrable_norm_iff hFmeas).mp <| hF₀.1.re.congr <|
    Eventually.of_forall fun x ↦ by
      change (F₀ x).re = ‖F x‖
      rw [← hnorm x, Complex.ofReal_re]
  refine ⟨hFi, Complex.ofReal_injective ?_⟩
  rw [← integral_complex_ofReal, Complex.ofReal_mul,
    ofReal_finiteHeckeRealEulerFactor _ _ hc]
  simpa only [hnorm] using hF₀.2

/-- At `σ > 1` the positive real Euler factors outside a fixed finite set
have a product, and that product bounds every finite partial product.
The omitted places contribute one, so the bound applies to any stage
containing the initial exceptional set without estimating its size. -/
public theorem finiteHeckeRealEulerTail_hasProd (E : Finset Places) {σ : ℝ} (hσ : 1 < σ) :
    let A := fun v : Places ↦ if v ∈ E then (1 : ℝ) else finiteHeckeRealEulerFactor v σ
    HasProd A (∏' v, A v) ∧ ∀ S : Finset Places, (∏ v ∈ S, A v) ≤ ∏' v, A v := by
  classical
  intro A
  let z := fun v : Places ↦ if v ∈ E then (0 : ℂ) else 1
  have hz (v : Places) : ‖z v‖ ≤ 1 := by by_cases hv : v ∈ E <;> simp [z, hv]
  have h (v : Places) : (A v : ℂ) = finiteHeckeEulerFactor z v σ := by
    by_cases hv : v ∈ E
    · simp [A, z, hv, finiteHeckeEulerFactor, finiteHeckeMonomial]
    · simpa only [A, ite_eq_right hv] using
        ofReal_finiteHeckeRealEulerFactor z v (ite_eq_right hv) σ
  have hp := (finiteHeckeEulerFactor_hasProdLocallyUniformlyOn hz).hasProd
    (x := (σ : ℂ)) (show 1 < (σ : ℂ).re from hσ)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hp
  have hprod (S : Finset Places) :
      (∏ v ∈ S, finiteHeckeEulerFactor z v σ).re = ∏ v ∈ S, A v := by
    simp only [← h, ← Complex.ofReal_prod, Complex.ofReal_re]
  have hA : Multipliable A := by
    refine ⟨(∏' v, finiteHeckeEulerFactor z v σ).re, ?_⟩
    simpa only [HasProd, Function.comp_def, hprod] using hr
  have hA₁ (v : Places) : 1 ≤ A v := by
    by_cases hv : v ∈ E
    · simp [A, hv]
    · simpa only [A, ite_eq_right hv] using
        one_le_finiteHeckeRealEulerFactor v (zero_lt_one.trans hσ)
  exact ⟨hA.hasProd, fun _ ↦ hA.prod_le_tprod_of_nonneg
    (fun v _ ↦ zero_le_one.trans (hA₁ v)) (fun v _ ↦ hA₁ v)⟩

end Masullo
