module

public import Theorems.RationalAdeleDual
public import Theorems.RationalAdeleL1L2Fourier
import Lemmas.RationalAdeleAdditiveModulus
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Plancherel measure on the full rational adelic dual

The pairing transports the unit-strip additive Haar measure to the Plancherel
measure on the compact-open dual (Example A.3.1.8, p. 558). This realizes
(D.1.1.9)–(D.1.1.10), p. 747, over `ℚ`, using the project's diagonal character
and the conjugated Fourier kernel.
-/

open MeasureTheory NumberField
open scoped ComplexConjugate ENNReal

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => PontryaginDual (Multiplicative A)
local notation "μA" => rationalAdeleAddHaar
local notation "e" => rationalAdelePontryaginDualEquiv

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace D] [BorelSpace D]

private def dualHomeomorph : A ≃ₜ D :=
  show A ≃ₜ Additive D from rationalAdelePontryaginDualEquiv.toHomeomorph

/-- The additive Haar measure of unit strip mass, transported to the full
compact-open character group by the rational adelic pairing. -/
@[expose] public def rationalAdeleDualHaar : Measure D :=
  Measure.map (fun y ↦ (e y).toMul) μA

local notation "μD" => rationalAdeleDualHaar

private theorem pairing_measurePreserving : MeasurePreserving dualHomeomorph μA μD :=
  dualHomeomorph.continuous.measurable.measurePreserving μA

private theorem pairing_symm_measurePreserving : MeasurePreserving dualHomeomorph.symm μD μA :=
  dualHomeomorph.toMeasurableEquiv.measurePreserving_symm μA

public instance rationalAdeleDualHaar_isHaarMeasure : Measure.IsHaarMeasure μD := by
  have hadd : Measure.IsAddHaarMeasure (G := Additive D) (Measure.map (e : A → Additive D) μA) :=
    (e).toAddEquiv.isAddHaarMeasure_map μA (e).continuous (e).symm.continuous
  exact {
    map_mul_left_eq_self := hadd.map_add_left_eq_self
    toIsFiniteMeasureOnCompacts := hadd.toIsFiniteMeasureOnCompacts
    toIsOpenPosMeasure := hadd.toIsOpenPosMeasure }

omit [MeasurableSpace D] [BorelSpace D] [BorelSpace A] in
/-- The normalized Fourier integral on the full dual, with the conjugated
character convention of (D.1.1.4). -/
@[expose] public def rationalAdeleDualFourier (f : A → ℂ) (χ : D) : ℂ :=
  ∫ x, f x * conj (χ (Multiplicative.ofAdd x) : ℂ) ∂μA

local notation "F̂" => rationalAdeleDualFourier

omit [MeasurableSpace D] [BorelSpace D] in
/-- Evaluating at a pairing character recovers the adelic-frequency integral. -/
public theorem rationalAdeleDualFourier_pairing (f : A → ℂ) (y : A) :
    F̂ f (e y).toMul = rationalAdeleFourier f y := by
  simp only [rationalAdeleDualFourier, rationalAdeleFourier,
    rationalAdelePontryaginDualEquiv_apply, mul_comm y]

omit [MeasurableSpace D] [BorelSpace D] in
private theorem dualFourier_eq_comp (f : A → ℂ) :
    F̂ f = rationalAdeleFourier f ∘ dualHomeomorph.symm := by
  funext χ
  obtain ⟨y, rfl⟩ := dualHomeomorph.surjective χ
  rw [Function.comp_apply, dualHomeomorph.symm_apply_apply]
  exact rationalAdeleDualFourier_pairing f y

private def dualL2Transport : Lp ℂ 2 μA ≃ₗᵢ[ℂ] Lp ℂ 2 μD :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ _ pairing_symm_measurePreserving) (by
      intro u
      refine ⟨Lp.compMeasurePreserving _ pairing_measurePreserving u, ?_⟩
      change Lp.compMeasurePreserving _ pairing_symm_measurePreserving
        (Lp.compMeasurePreserving _ pairing_measurePreserving u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      simp only [show dualHomeomorph ∘ dualHomeomorph.symm = id from
        funext dualHomeomorph.apply_symm_apply, Lp.compMeasurePreserving_id_apply])

/-- The normalized Fourier integral extends to a complex-linear isometric
equivalence onto `L²` of the full compact-open dual. -/
public def rationalAdeleDualL2Fourier : Lp ℂ 2 μA ≃ₗᵢ[ℂ] Lp ℂ 2 μD :=
  rationalAdeleL2Fourier.trans dualL2Transport

/-- The dual-valued unitary agrees almost everywhere with the Fourier integral
on every `L¹ ∩ L²` input. -/
public theorem rationalAdeleDualL2Fourier_ae_eq_integral {f : A → ℂ}
    (hf₁ : Integrable f μA) (hf₂ : MemLp f 2 μA) :
    (rationalAdeleDualL2Fourier (hf₂.toLp f) : D → ℂ) =ᵐ[μD] F̂ f := by
  rw [dualFourier_eq_comp]
  exact (Lp.coeFn_compMeasurePreserving _ pairing_symm_measurePreserving).trans
    ((rationalAdeleL2Fourier_ae_eq_integral hf₁ hf₂).comp_tendsto
      pairing_symm_measurePreserving.quasiMeasurePreserving.tendsto_ae)

/-- Parseval on all integrable square-integrable representatives, with the
output norm taken on the full compact-open dual. -/
public theorem eLpNorm_rationalAdeleDualFourier_two {f : A → ℂ}
    (hf₁ : Integrable f μA) (hf₂ : MemLp f 2 μA) : eLpNorm (F̂ f) 2 μD = eLpNorm f 2 μA := by
  rw [← eLpNorm_congr_ae (rationalAdeleDualL2Fourier_ae_eq_integral hf₁ hf₂), ← Lp.eNorm_def,
    rationalAdeleDualL2Fourier.eNorm_map, Lp.eNorm_toLp]

/-- Agreement with the integral on `L¹ ∩ L²` determines the unitary among all
continuous maps with this domain and codomain. -/
public theorem rationalAdeleDualL2Fourier_unique {T : Lp ℂ 2 μA → Lp ℂ 2 μD} (hT : Continuous T)
    (h : ∀ (f : A → ℂ), Integrable f μA → ∀ hf : MemLp f 2 μA,
      (T (hf.toLp f) : D → ℂ) =ᵐ[μD] F̂ f) :
    T = (rationalAdeleDualL2Fourier : Lp ℂ 2 μA → Lp ℂ 2 μD) := by
  refine denseRange_rationalAdeleSchwartzToL2.equalizer hT rationalAdeleDualL2Fourier.continuous
    (funext fun f ↦ ?_)
  have hae := rationalAdeleSchwartzToL2_ae_eq f
  have hf₁ := integrable_rationalAdeleSchwartzLF f
  have hf₂ := (Lp.memLp (rationalAdeleSchwartzToL2 f)).ae_eq hae
  -- Rewrite the core class as the class of its Schwartz representative.
  have he : hf₂.toLp f.toUnion.val = rationalAdeleSchwartzToL2 f := by
    apply Lp.ext
    exact hf₂.coeFn_toLp.trans hae.symm
  simp only [Function.comp_apply, ← he]
  exact Lp.ext ((h _ hf₁ hf₂).trans (rationalAdeleDualL2Fourier_ae_eq_integral hf₁ hf₂).symm)

/-- No other Haar measure on the full dual gives Parseval for all `L¹ ∩ L²`
inputs for the fixed unit-strip normalization upstairs. -/
public theorem rationalAdeleDualHaar_unique (ν : Measure D) [ν.IsHaarMeasure]
    (h : ∀ f : A → ℂ, Integrable f μA → MemLp f 2 μA → eLpNorm (F̂ f) 2 ν = eLpNorm f 2 μA) :
    ν = μD := by
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  let : SecondCountableTopology D := dualHomeomorph.symm.secondCountableTopology
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  let : LocallyCompactSpace D := dualHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  let : T2Space A := t2Space_rationalAdeles
  let C : Set A := rationalAdeleClosedUnitStrip
  let f : A → ℂ := C.indicator (fun _ ↦ 1)
  have hC : MeasurableSet C := rationalAdeleClosedUnitStrip.isCompact.isClosed.measurableSet
  have hmass : μA C = 1 := rationalAdeleAddHaar_closedUnitStrip
  have hf (p : ℝ≥0∞) : MemLp f p μA :=
    memLp_indicator_const p hC.nullMeasurableSet 1 (Or.inr (hmass.trans_ne ENNReal.one_ne_top))
  have hf₁ := memLp_one_iff_integrable.mp (hf 1)
  have hnorm : eLpNorm f 2 μA = 1 := by
    rw [eLpNorm_indicator_const hC.nullMeasurableSet two_ne_zero ENNReal.ofNat_ne_top, hmass]
    simp
  have hnormD := (eLpNorm_rationalAdeleDualFourier_two hf₁ (hf 2)).trans hnorm
  have hmD : AEStronglyMeasurable (F̂ f) μD :=
    (Lp.memLp _).aestronglyMeasurable.congr (rationalAdeleDualL2Fourier_ae_eq_integral hf₁ (hf 2))
  let c := Measure.haarScalarFactor ν μD
  have hc : ν = c • μD := Measure.isMulLeftInvariant_eq_smul ν μD
  have hscale := (h f hf₁ (hf 2)).trans hnorm
  rw [hc, eLpNorm_smul_measure_of_ne_top' ENNReal.ofNat_ne_top c _ hmD, hnormD] at hscale
  change (↑(c ^ (2 : ℝ≥0∞).toReal⁻¹) : ℝ≥0∞) * 1 = 1 at hscale
  rw [mul_one, ENNReal.coe_eq_one] at hscale
  have hc1 : c = 1 :=
    (NNReal.strictMono_rpow_of_pos (show 0 < (2 : ℝ≥0∞).toReal⁻¹ by norm_num)).injective
      (hscale.trans (NNReal.one_rpow _).symm)
  rw [hc, hc1, one_smul]

end
end Masullo
