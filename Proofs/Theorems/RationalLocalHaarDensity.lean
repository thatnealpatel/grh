module

public import Theorems.RationalLocalMultiplicativeHaar
public import Theorems.RationalAdeleIntegralStageHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
import Lemmas.RationalLocalHaarDensity
import Mathlib.MeasureTheory.Group.Measure

/-!
# The additive density of rational finite-place multiplicative Haar

Lemma A.3.2.3, (A.3.2.3)–(4), p. 560, obtains the density by
invariance under multiplication and the difference of the masses of the
integer and maximal-ideal balls. We check the measure identity in the
value coordinate of the actual rational local completion. The coefficient
is the reciprocal of the additive mass of its integral units, because the
local discriminant normalization over `ℚ_[p]` gives unit mass one.
Locators follow the pinned text extraction.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped ENNReal

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "G[" v "]" => (K[v])ˣ
local notation "P[" v "]" => (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℝ)

variable (v : V) [MeasurableSpace (G[v])] [BorelSpace (G[v])]

/-- Rational finite-place case of (A.3.2.3), as a Borel measure on the
field supported off zero in the sense that the singleton has mass zero. -/
public theorem map_rationalLocalMultiplicativeHaar_val :
    (rationalLocalMultiplicativeHaar v).map (Units.val : G[v] → K[v]) =
      (ENNReal.ofReal (1 - P[v]⁻¹))⁻¹ •
        (((rationalLocalFieldAddHaar v).restrict ({0}ᶜ)).withDensity
          (fun x ↦ ENNReal.ofReal ‖x‖⁻¹)) := by
  let S := range (rationalLocalUnitInclusion v)
  let c := ENNReal.ofReal (1 - P[v]⁻¹)
  let ρ := RationalLocalHaarDensity.onUnits v
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr
    (sub_pos.mpr (inv_lt_one_of_one_lt₀ (RationalLocalNormShell.one_lt_prime v)))).ne'
  have hmass : (c⁻¹ • ρ) S = 1 := by
    rw [smul_apply, smul_eq_mul, RationalLocalHaarDensity.onUnits_unitMass,
      ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top]
  let : ρ.IsMulLeftInvariant := RationalLocalHaarDensity.onUnits_mulLeftInvariant v
  have : (c⁻¹ • ρ).IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior _ S
      (isCompact_range_rationalLocalUnitInclusion v)
      (by rw [(isOpenEmbedding_rationalLocalUnitInclusion v).isOpen_range.interior_eq]; exact range_nonempty _)
      (hmass ▸ one_ne_zero) (hmass ▸ ENNReal.one_ne_top)
  -- Haar uniqueness applies after checking both invariance and the unit mass.
  let j : MeasurableEmbedding (Units.val : G[v] → K[v]) :=
    Units.isOpenEmbedding_val.measurableEmbedding
  rw [rationalLocalMultiplicativeHaar_eq v (c⁻¹ • ρ) hmass, Measure.map_smul _ j.measurable.aemeasurable]
  dsimp only [ρ, RationalLocalHaarDensity.onUnits]
  rw [j.map_comap,
    RationalLocalHaarDensity.range_val, restrict_withDensity (measurableSet_singleton 0).compl]

end Masullo
