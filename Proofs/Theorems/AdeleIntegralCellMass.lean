module

public import Theorems.AdeleFundamentalDomain
public import Theorems.AdeleRestrictedProductHaar

import Lemmas.AdeleIntegralCellMass

/-! # Mass one for the global additive adelic cell

In the global part of Lemma A.3.1.3, p. 556, Masullo cancels the Archimedean
trace covolume against the product of the finite integer masses from
Definition A.3.1.2. Use the full cell of `AdeleFundamentalDomain` instead of
(A.2.1.1), and apply the actual stage-comap formula to its rectangle. The
upstairs measure is the same one as in `adeleBox_fourier_integral`; neither
its measure nor either factor is rescaled. The Borel counting-quotient
formula is a separate step toward Definition A.3.1.1, p. 555. This does not
address the S-local equality of Lemma A.3.1.3. Source readings are
provisional (pinned Markdown and numbered PDF layout).
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical ENNReal InnerProductSpace Masullo.AdeleStage

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A" => AdeleRing (𝓞 K) K

/-- The full integral adelic cell has mass one for every measure with the
cofinal stage comaps used by the global box Fourier theorem. -/
public theorem adeleIntegralCell_mass_one (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S) :
    μ (adeleIntegralCell K) = 1 := by
  obtain ⟨E', hE'⟩ := exists_finiteCompletionIntegerMass_exceptions K
  let S := E ∪ E'
  have hS (v : V) (hv : v ∉ S) : finiteCompletionIntegerMass K v = 1 := by
    by_contra h
    exact hv (Finset.mem_union_right E ((hE' v).mpr h))
  -- Use a stage containing both the comap threshold and every nontrivial integer mass.
  have hstage := hμ S Finset.subset_union_left
  rw [adeleIntegralCell, ← image_adeleStageIntegerRectangle K _ S,
    ← (measurableEmbedding_adeleFiniteStageEmbedding K S).comap_apply, hstage,
    adeleFiniteStageHaar_integerRectangle K _ S hS]
  -- The actual rectangle masses in this stage are reciprocal in trace normalization.
  let τ := archimedeanTraceMeasure K
  let : τ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul volume (by simp) (by finiteness)
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [ENNReal.toReal_mul, (archimedeanIntegralCell_traceMass K).1,
    (finiteIntegerBox_stageMass K S hS).1]
  exact mul_inv_cancel₀ (ZLattice.covolume_ne_zero (archimedeanIdealLattice K 1) τ)

end Masullo
