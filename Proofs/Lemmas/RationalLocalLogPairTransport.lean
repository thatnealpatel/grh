module

public import Theorems.PadicLogTestFourier
public import Theorems.RationalLocalHaarDensity
import Lemmas.RationalLocalAdditiveModulus
import Lemmas.RationalLocalNormShell
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Transport of the rational local logarithmic pairing and Haar density -/

open Function NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Padic ENNReal

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "P[" v "]" => ((p[v] : ℕ) : ℝ)
local notation "ν[" v "]" => rationalLocalFieldAddHaar v

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

/-- The integrand `J(ξ) û(ξ)`, using unit-ball additive Haar and the conjugate
standard character in the actual completion at `v`. -/
@[expose]
public noncomputable def rationalLocalLogFourierIntegrand (v : V) (u : K[v] → ℂ) (ξ : K[v]) : ℂ :=
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let χ := @padicStdAddChar (p[v] : ℕ) ⟨(p[v]).property⟩
  (↑(Real.log ‖ξ‖ / Real.log P[v]) : ℂ) * ∫ x, u x * star (χ (e (x * ξ))) ∂ν[v]

/-- The checked off-zero identity expressed in the value coordinate of the
finite completion, not in a separately normalized copy of `ℚ_[p]`. -/
public theorem rationalLocalLogFourier_off_zero (v : V) {u : K[v] → ℂ} (hu : IsLocallyConstant u)
    (hc : HasCompactSupport u) (h₀ : u 0 = 0) :
    Integrable (rationalLocalLogFourierIntegrand v u) ν[v] ∧
      Integrable (fun x ↦ u x / (↑‖x‖ : ℂ)) ν[v] ∧
      (∫ ξ, rationalLocalLogFourierIntegrand v u ξ ∂ν[v]) =
        -((↑(1 - P[v]⁻¹) : ℂ)⁻¹) * ∫ x, u x / (↑‖x‖ : ℂ) ∂ν[v] := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let j : MeasurableEmbedding (e : K[v] → ℚ_[(p[v] : ℕ)]) := e.toHomeomorph.measurableEmbedding
  have hn (x : K[v]) : ‖e x‖ = ‖x‖ := norm_rationalLocal_padicEquiv v x
  let μ := padicAddHaar (p[v] : ℕ)
  have he : MeasurePreserving e ν[v] μ := by
    refine ⟨j.measurable, ?_⟩
    change (μ.comap e).map e = μ
    rw [j.map_comap, e.surjective.range_eq, Measure.restrict_univ]
  let q : ℚ_[(p[v] : ℕ)] → ℂ := u ∘ e.symm
  obtain ⟨hF, hG, hpair⟩ := padicTest_log_fourier_off_zero (p[v] : ℕ) q
    (hu.comp_continuous e.toHomeomorph.symm.continuous) (hc.comp_homeomorph e.toHomeomorph.symm)
    (by simpa [q] using h₀)
  let F (η : ℚ_[(p[v] : ℕ)]) : ℂ := (↑(Real.log ‖η‖ / Real.log P[v]) : ℂ) *
    ∫ z, q z * star (padicStdAddChar (p[v] : ℕ) (z * η)) ∂μ
  let G (z : ℚ_[(p[v] : ℕ)]) : ℂ := q z / (↑‖z‖ : ℂ)
  have hFE : rationalLocalLogFourierIntegrand v u = F ∘ e := by
    funext ξ
    change (↑(Real.log ‖ξ‖ / Real.log P[v]) : ℂ) * _ = _
    simp only [comp_apply, F, hn]
    congr 1
    rw [← he.integral_comp j (fun z ↦ q z * star (padicStdAddChar (p[v] : ℕ) (z * e ξ)))]
    simp only [q, comp_apply, e.symm_apply_apply, map_mul]
    rfl
  have hGE : (fun x ↦ u x / (↑‖x‖ : ℂ)) = G ∘ e := by
    funext x
    simp only [comp_apply, G, q, e.symm_apply_apply, hn]
  rw [hFE, hGE]
  refine ⟨(he.integrable_comp_emb j).mpr (show Integrable F μ from hF),
    (he.integrable_comp_emb j).mpr (show Integrable G μ from hG), ?_⟩
  exact (he.integral_comp j F).trans (hpair.trans (congrArg _ (he.integral_comp j G).symm))

/-- Bochner form of (A.3.2.3) for a function in the value coordinate:
its additive integrand is obtained by dividing by the field norm. -/
public theorem rationalLocalHaar_integral_density (v : V) [MeasurableSpace (K[v]ˣ)]
    [BorelSpace (K[v]ˣ)] (H : K[v] → ℂ)
    (hH : Integrable (fun y ↦ H y / (↑‖y‖ : ℂ)) ν[v]) :
    Integrable (fun y : K[v]ˣ ↦ H y) (rationalLocalMultiplicativeHaar v) ∧
      (∫ y : K[v]ˣ, H y ∂rationalLocalMultiplicativeHaar v) =
        ((↑(1 - P[v]⁻¹) : ℂ)⁻¹) * ∫ y, H y / (↑‖y‖ : ℂ) ∂ν[v] := by
  let j : K[v]ˣ → K[v] := Units.val
  let hj : MeasurableEmbedding j := Units.isOpenEmbedding_val.measurableEmbedding
  let ρ := ν[v].restrict ({0}ᶜ)
  let w (y : K[v]) := ENNReal.ofReal ‖y‖⁻¹
  let c := ENNReal.ofReal (1 - P[v]⁻¹)
  have hc : 0 < 1 - P[v]⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (RationalLocalNormShell.one_lt_prime v))
  have hw : Measurable w := continuous_norm.measurable.inv.ennreal_ofReal
  have hw' : ∀ᵐ y ∂ρ, w y < ∞ := ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)
  have hpoint (y : K[v]) : (w y).toReal • H y = H y / (↑‖y‖ : ℂ) := by
    rw [Complex.real_smul, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _)),
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  constructor
  · change Integrable (H ∘ j) _
    rw [← hj.integrable_map_iff, map_rationalLocalMultiplicativeHaar_val v]
    apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')
    rw [integrable_withDensity_iff_integrable_smul' hw hw']
    simp_rw [hpoint]
    exact hH.integrableOn
  · rw [← hj.integral_map H, map_rationalLocalMultiplicativeHaar_val v]
    change (∫ y, H y ∂c⁻¹ • (ρ.withDensity w)) = _
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hw hw']
    simp_rw [hpoint]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := ({0} : Set K[v])ᶜ)
      (by
        intro y hy
        have hz : y = 0 := by simpa using hy
        simp [hz])]
    rw [Complex.real_smul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le, Complex.ofReal_inv]

end Masullo
