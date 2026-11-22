module

public import Lemmas.FiniteCompletionTraceAnnihilator
import Lemmas.AddSubgroupCharIntegral
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Positive local Fourier integral of a translated finite box -/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical Masullo Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "χ" => fun x : F ↦ padicStdAddChar p (Algebra.trace ℚ_[p] F x)

/-- With the positive finite kernel, the Fourier integral on `a + b O` is
its centered Haar mass times the phase at `a` on the annihilator, and zero
elsewhere. The local Haar measure need not be normalized. -/
public theorem finiteCompletion_box_fourier [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (a b z : F) (hb : b ≠ 0) :
    (∫ t in (a + ·) '' (b • (O : Set F)), χ (z * t) ∂μ) =
      if ∀ t : O, χ (z * (b * (t : F))) = 1 then
        χ (z * a) * (μ.real (b • (O : Set F)) : ℂ) else 0 := by
  classical
  let ψ (t : F) := χ (z * t)
  have hadd (s t : F) : ψ (s + t) = ψ s * ψ t := by
    simp only [ψ, mul_add, map_add, AddChar.map_add_eq_mul]
  let S := (O).toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft b)
  have hS : (S : Set F) = b • (O : Set F) := rfl
  have hm : MeasurableSet (b • (O : Set F)) :=
    (Homeomorph.mulLeft₀ b hb).measurableEmbedding.measurableSet_image'
      (Valued.isOpen_valuationSubring F).measurableSet
  have ht : MeasurableSet ((a + ·) '' (b • (O : Set F))) :=
    (Homeomorph.addLeft a).measurableEmbedding.measurableSet_image' hm
  have hcenter := addSubgroup_integral_star_char S (hS ▸ hm) μ (fun t ↦ star (ψ t))
    (fun s t ↦ by rw [hadd, star_mul, mul_comm])
  have hann : (∀ t ∈ S, star (ψ t) = 1) ↔ ∀ t : O, ψ (b * (t : F)) = 1 := by
    constructor
    · intro h t
      have he := h (b * (t : F)) ⟨t, t.property, rfl⟩
      simpa using congrArg star he
    · rintro h _ ⟨t, ht', rfl⟩
      change star (ψ (b * t)) = 1
      rw [h ⟨t, ht'⟩, star_one]
  rw [hann, hS] at hcenter
  simp only [star_star] at hcenter
  change (∫ t in _, ψ t ∂μ) = _
  calc
    _ = ψ a * (∫ t in b • (O : Set F), ψ t ∂μ) := by
      rw [← integral_indicator ht, ← integral_indicator hm,
        ← integral_add_left_eq_self (μ := μ) _ a, ← integral_const_mul]
      congr 1
      funext t
      have hmem : a + t ∈ (a + ·) '' (b • (O : Set F)) ↔ t ∈ b • (O : Set F) :=
        ⟨fun ⟨s, hs, he⟩ ↦ (add_left_cancel he) ▸ hs, fun h ↦ ⟨t, h, rfl⟩⟩
      by_cases h : t ∈ b • (O : Set F)
      · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h, hadd]
      · rw [Set.indicator_of_notMem (mt hmem.mp h), Set.indicator_of_notMem h, mul_zero]
    _ = _ := by
      rw [hcenter]
      split_ifs <;> simp [ψ]

end Masullo
