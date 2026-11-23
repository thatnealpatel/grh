module

public import Props.IdeleClassStripTrace
public import Theorems.RationalRadialStripTrace
import Lemmas.RationalRadialClassMellin
import Lemmas.RationalRadialClassLocal
import Lemmas.RationalRadialClassTest
import Lemmas.RationalRadialStripIndex

/-! # Rational radial specialization of the idèle-class strip trace -/

open Filter MeasureTheory NumberField Set IsDedekindDomain
open scoped Classical ContDiff Topology

namespace Masullo

section

set_option linter.concreteInstances false
variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

local notation "φ[" F "]" => (fun c : RationalIdeleClasses ↦ F (Real.log (ideleClassNorm c)))

/-- The full idèle-class identity implies its rational radial specialization without
widening the strip or including its boundary zeros. -/
public theorem rationalRadialStripTrace_of_ideleClassStripTrace {a : ℝ} (ha : 0 < a)
    (h : IdeleClassStripTrace ℚ a) : RationalRadialStripTrace a := by
  borelize RationalIdeleClasses
  apply (rationalRadialStripTrace_iff ha).2
  apply zeros_mem_strip_of_positive_radial_trace ha
  intro F hf hc ht
  have h₀ : F 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ (lt_irrefl 0) (ht h))
  obtain ⟨R, hR, _, _, hs⟩ := h φ[F] (isIdeleClassTest_rationalRadial hf hc) (fun x ↦ by
    rw [(mem_ideleClassNormOne _).mp x.property, Real.log_one, h₀])
  refine ⟨R Rat.infinitePlace, (hasArchimedeanTraceValue_rationalRadial_iff hf hc ht _).mp (hR _), ?_⟩
  -- Orthogonality kills the other summands, not the underlying Hecke zeros.
  let t (z : OpenStripHeckeZero ℚ a) :=
    (z.order : ℂ) * ideleClassMellin φ[F] (z.character * ideleClassNormPower (-1 / 2))
  let S : Set (OpenStripHeckeZero ℚ a) :=
    {z | ∀ x : ideleClassNormOne (K := ℚ), z.character (x : _) = 1}
  have htS : Function.support t ⊆ S := by
    intro z hz x
    by_contra hx
    apply hz
    dsimp only [t]
    rw [rational_ideleClassMellin_eq_zero_of_nontrivial hf.continuous hc _ ⟨x, by
      simpa only [ContinuousMonoidHom.mul_apply, ideleClassNormPower_on_normOne, mul_one] using hx⟩, mul_zero]
  have hsub := (hasSum_subtype_iff_of_support_subset htS).mpr hs
  have hr := (rationalRadialStripIndexEquiv a).hasSum_iff.mpr hsub
  have hp₁ := rational_ideleClassMellin_normPower hf.continuous hc 1
  have hp₀ := rational_ideleClassMellin_normPower hf.continuous hc 0
  norm_num at hp₁ hp₀
  rw [Fintype.sum_subsingleton _ Rat.infinitePlace,
    hp₁, neg_div, hp₀, add_comm (rationalIdeleRadialMellin F 1)] at hr
  simp_rw [finiteTraceTerm_rationalRadial _ F] at hr
  refine hr.congr_fun fun ρ ↦ ?_
  symm
  change t ((rationalRadialStripIndexEquiv a) ρ).val = _
  simp only [t, rationalRadialStripIndexEquiv_apply_order, rationalRadialStripIndexEquiv_apply_character]
  congr 1
  rw [← rational_ideleClassMellin_normPower hf.continuous hc]
  congr 1
  ext c
  simp only [ContinuousMonoidHom.mul_apply, ideleClassNormPower_apply]
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos c).ne')]
  congr 1
  ring

end

/-- Conditional implication from the rational trace formula at all positive widths.
This does not assert the trace formula itself. -/
public theorem riemannHypothesis_of_ideleClassTraceFormula
    (h : IdeleClassTraceFormula ℚ) : RiemannHypothesis := by
  let : MeasurableSpace RationalIdeleClasses := borel _
  let : BorelSpace RationalIdeleClasses := ⟨rfl⟩
  exact riemannHypothesis_iff_rationalRadialStripTrace.mpr fun a ha ↦
    rationalRadialStripTrace_of_ideleClassStripTrace ha (h a ha)

end Masullo
