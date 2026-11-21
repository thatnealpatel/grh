module

public import Theorems.RationalAdeleFourierInversion

/-! # Annihilator support and translation invariance

Lemma D.1.5.2(3), p. 761, relates subgroup invariance to Fourier support
on the annihilator. Translation of the conjugated Fourier integral gives
the forward implication. For the converse, `L¹` injectivity gives invariance
a.e. for each translation, even without integrability on the dual. With
both integrability hypotheses the positive-kernel inverse is pointwise
invariant. The manuscript's pointwise claim for the original input requires
continuity of that representative, as in rational adelic Fourier inversion.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => PontryaginDual (Multiplicative A)
local notation "μA" => rationalAdeleAddHaar
local notation "μD" => rationalAdeleDualHaar
local notation "F̂" => rationalAdeleDualFourier

set_option linter.concreteInstances false

/-- The full-dual characters trivial on the additive subgroup `H`. -/
@[expose] public def rationalAdeleDualAnnihilator (H : AddSubgroup A) : Set D :=
  {χ | ∀ h ∈ H, χ (Multiplicative.ofAdd h) = 1}

/-- The annihilator is closed in the compact-open topology. -/
public theorem isClosed_rationalAdeleDualAnnihilator (H : AddSubgroup A) :
    IsClosed (rationalAdeleDualAnnihilator H) := by
  have heq : rationalAdeleDualAnnihilator H =
      ⋂ h : H, {χ : D | χ (Multiplicative.ofAdd (h : A)) = 1} := by
    ext χ
    simp [rationalAdeleDualAnnihilator]
  rw [heq]
  exact isClosed_iInter fun h ↦
    isClosed_eq (continuous_eval_const (F := Multiplicative A →ₜ* Circle) _) continuous_const

variable [MeasurableSpace A] [BorelSpace A]

-- Translating the input by `+h` gives the original (not conjugated) phase.
private theorem fourier_translate (f : A → ℂ) (h : A) (χ : D) :
    F̂ (fun x ↦ f (x + h)) χ = F̂ f χ * (χ (Multiplicative.ofAdd h) : ℂ) := by
  let k (x : A) : ℂ := f (x + h) * conj (χ (Multiplicative.ofAdd x) : ℂ)
  change (∫ x, k x ∂μA) = _
  rw [← integral_add_right_eq_self (μ := μA) k (-h), rationalAdeleDualFourier,
    ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  have hneg : χ (Multiplicative.ofAdd (-h)) = (χ (Multiplicative.ofAdd h))⁻¹ :=
    map_inv χ (Multiplicative.ofAdd h)
  have hadd : χ (Multiplicative.ofAdd (x + -h)) =
      χ (Multiplicative.ofAdd x) * χ (Multiplicative.ofAdd (-h)) :=
    map_mul χ (Multiplicative.ofAdd x) (Multiplicative.ofAdd (-h))
  dsimp only [k]
  rw [add_assoc, neg_add_cancel, add_zero, hadd, Circle.coe_mul, map_mul, hneg,
    Circle.coe_inv_eq_conj, starRingEnd_self_apply, mul_assoc]

/-- A rational adelic `L¹` input is invariant a.e. under each translation
by `H` exactly when its Fourier integral is supported on the annihilator.
The exceptional null set may depend on the translation. -/
public theorem rationalAdeleDualFourier_support_iff_ae_invariant {f : A → ℂ}
    (hf : Integrable f μA) (H : AddSubgroup A) :
    tsupport (F̂ f) ⊆ rationalAdeleDualAnnihilator H ↔
      ∀ h ∈ H, (fun x ↦ f (x + h)) =ᵐ[μA] f := by
  constructor
  · intro hs h hh
    let : MeasurableSpace D := borel D
    let : BorelSpace D := ⟨rfl⟩
    refine rationalAdeleDualFourier_injective
      ((measurePreserving_add_right μA h).integrable_comp_of_integrable hf) hf ?_
    funext χ
    rw [fourier_translate]
    by_cases hz : F̂ f χ = 0
    · simp [hz]
    · have hχ : χ (Multiplicative.ofAdd h) = 1 := hs (subset_tsupport _ hz) h hh
      simp [hχ]
  · intro hi
    apply closure_minimal _ (isClosed_rationalAdeleDualAnnihilator H)
    intro χ hχ h hh
    have heq : F̂ (fun x ↦ f (x + h)) χ = F̂ f χ :=
      integral_congr_ae ((hi h hh).mono fun x hx ↦ congrArg
        (fun z : ℂ ↦ z * conj (χ (Multiplicative.ofAdd x) : ℂ)) hx)
    rw [fourier_translate] at heq
    exact Circle.coe_injective (mul_left_cancel₀ hχ (heq.trans (mul_one _).symm))

/-- For continuous integrable inputs the invariance criterion holds pointwise. -/
public theorem rationalAdeleDualFourier_support_iff_invariant {f : A → ℂ}
    (hf : Integrable f μA) (hc : Continuous f) (H : AddSubgroup A) :
    tsupport (F̂ f) ⊆ rationalAdeleDualAnnihilator H ↔
      ∀ h ∈ H, ∀ x, f (x + h) = f x := by
  rw [rationalAdeleDualFourier_support_iff_ae_invariant hf H]
  exact ⟨fun hi h hh ↦ congrFun (Measure.eq_of_ae_eq (hi h hh)
    (hc.comp (continuous_id.add continuous_const)) hc),
    fun hi h hh ↦ Filter.Eventually.of_forall (hi h hh)⟩

variable [MeasurableSpace D] [BorelSpace D]

/-- If the Fourier transform is integrable and supported on the annihilator,
its inverse integral is an everywhere `H`-invariant continuous representative
of the input. No pointwise invariance of an arbitrary representative is needed. -/
public theorem rationalAdeleDualFourier_inverse_invariant {f : A → ℂ}
    (hf : Integrable f μA) (hFf : Integrable (F̂ f) μD) {H : AddSubgroup A}
    (hs : tsupport (F̂ f) ⊆ rationalAdeleDualAnnihilator H) :
    let u := rationalAdeleDualFourierInverse (F̂ f)
    Continuous u ∧ u =ᵐ[μA] f ∧ ∀ h ∈ H, ∀ x, u (x + h) = u x := by
  dsimp only
  obtain ⟨hc, hae, _⟩ := rationalAdeleDualFourier_inversion hf hFf
  refine ⟨hc, hae, fun h hh x ↦ ?_⟩
  -- As in D.1.5.2(3), the inverse's kernel only matters on the annihilator.
  unfold rationalAdeleDualFourierInverse
  apply integral_congr_ae
  filter_upwards with χ
  by_cases hz : F̂ f χ = 0
  · simp [hz]
  · have hχ : χ (Multiplicative.ofAdd h) = 1 := hs (subset_tsupport _ hz) h hh
    have hadd : χ (Multiplicative.ofAdd (x + h)) =
        χ (Multiplicative.ofAdd x) * χ (Multiplicative.ofAdd h) :=
      map_mul χ (Multiplicative.ofAdd x) (Multiplicative.ofAdd h)
    rw [hadd, hχ, mul_one]

end Masullo
