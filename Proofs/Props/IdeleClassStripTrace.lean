module

public import Lemmas.IdeleClassStripDivisor
public import Lemmas.IdeleClassTraceLocal
public import Theorems.IdeleClassCharacterComponent
public import Theorems.IdeleClassWeil
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Masullo's open-strip trace formula

Statement of Theorem 12.5.1.1, (12.5.1.1–3), pp. 519–520. The window
restricts the spectral side only. No trace identity is asserted as a theorem.
-/

open NumberField MeasureTheory TopologicalSpace
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Classical ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)

/-- A compactly supported Bruhat test on the idele classes. In a translated
idelic neighborhood it is a smooth function of the Archimedean coordinates
alone: The finite coordinates can vary throughout that neighborhood. -/
@[expose] public def IsIdeleClassTest (φ : C → ℂ) : Prop :=
  HasCompactSupport φ ∧ ∀ c : C,
    ∃ f : mixedEmbedding.mixedSpace K → ℂ, ContDiff ℝ ∞ f ∧
      ∀ᶠ x : IdeleGroup (𝓞 K) K in 𝓝 1,
        φ (c * QuotientGroup.mk x) = f (InfiniteAdeleRing.ringEquiv_mixedSpace K x.val.1)

/-- The unconjugated Mellin pairing on the quotient Tamagawa measure.
In log coordinates this is Lebesgue measure times Haar on the norm-one
classes, whose mass is (A.3.2.1), not in general one. -/
@[expose] public noncomputable def ideleClassMellin (φ : C → ℂ) (c : HeckeCharacter (𝓞 K) K) : ℂ :=
  letI : MeasurableSpace C := borel _
  letI : MeasurableSpace C₁ := borel _
  letI : BorelSpace C₁ := ⟨rfl⟩
  letI : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
  letI : T2Space C₁ := compactHausdorff_ideleClassNormOne.2
  let m := ENNReal.ofReal (dedekindZeta_residue K) • Measure.haarMeasure (⊤ : PositiveCompacts C₁)
  let τ := ideleClassLogSplit (ideleClassLogSection (w₀ : InfinitePlace K))
    (ideleClassLogNorm_section w₀)
  ∫ g : C, φ g * c g ∂((logVolume.prod m).map τ)

/-- The fixed-width identity. The two polar Mellin values minus the geometric
side are the sum over distinct interior zeros, with full multiplicity. -/
@[expose] public def IdeleClassStripTrace (K : Type*) [Field K] [NumberField K] (α : ℝ) : Prop :=
  ∀ φ : IdeleClassGroup (𝓞 K) K → ℂ, IsIdeleClassTest φ →
    (∀ x : ideleClassNormOne (K := K), φ x = 0) →
    ∃ A : InfinitePlace K → ℂ,
      (∀ v, HasArchimedeanTraceValue v φ (A v)) ∧
      (∀ v, FiniteTraceTermIntegrable v φ) ∧
      Function.HasFiniteSupport (fun v ↦ finiteTraceTerm v φ) ∧
      HasSum (fun z : OpenStripHeckeZero K α ↦
        (z.order : ℂ) * ideleClassMellin φ (z.character * ideleClassNormPower (-1 / 2)))
        (ideleClassMellin φ (ideleClassNormPower (1 / 2)) +
          ideleClassMellin φ (ideleClassNormPower (-1 / 2)) - (∑ v, A v) - ∑' v, finiteTraceTerm v φ)

/-- Masullo's Theorem 12.5.1.1 for `K`, as a proposition, not a proof.
No identity at width zero or with boundary zeros is part of the claim. -/
@[expose] public def IdeleClassTraceFormula (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ α : ℝ, 0 < α → IdeleClassStripTrace K α

end Masullo
