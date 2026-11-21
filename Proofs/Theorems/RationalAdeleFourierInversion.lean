module

public import Theorems.RationalAdeleRiemannLebesgue
import Theorems.RationalAdeleFourierTestInversion
import Lemmas.RationalAdeleSchwartzSeparation

/-! # Fourier inversion and uniqueness on the rational adelic dual

In Lemma D.1.1.2(5), (D.1.1.11), p. 747, Masullo cites
Deitmar–Echterhoff, Theorem 3.5.8, for inversion when the input and its
transform are integrable. The positive-kernel inverse is continuous, but
an arbitrary integrable representative need not be. We repair the claim
by giving equality a.e. for every representative and pointwise equality
for continuous representatives. The checked proof uses bilinear test
inversion and separation by rational adelic Schwartz tests. For the
injectivity in D.1.1.2(2), Masullo cites Deitmar–Echterhoff, Corollary 3.3.4;
here it follows by applying inversion to a difference with zero transform.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => PontryaginDual (Multiplicative A)
local notation "μA" => rationalAdeleAddHaar
local notation "μD" => rationalAdeleDualHaar
local notation "F" => rationalAdeleFourier
local notation "F̂" => rationalAdeleDualFourier

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace D] [BorelSpace D]

/-- The inverse integral uses the original character, not its conjugate,
and the transported Plancherel measure on the full compact-open dual. -/
public noncomputable def rationalAdeleDualFourierInverse (g : D → ℂ) (x : A) : ℂ :=
  ∫ χ, g χ * (χ (Multiplicative.ofAdd x) : ℂ) ∂μD

private noncomputable def pairingHomeomorph : A ≃ₜ D :=
  show A ≃ₜ Additive D from rationalAdelePontryaginDualEquiv.toHomeomorph

private theorem pairing_measurePreserving : MeasurePreserving pairingHomeomorph μA μD :=
  pairingHomeomorph.continuous.measurable.measurePreserving μA

private theorem dual_inverse_eq_reflected {f : A → ℂ} (x : A) :
    rationalAdeleDualFourierInverse (F̂ f) x = F (F f) (-x) := by
  unfold rationalAdeleDualFourierInverse
  rw [← pairing_measurePreserving.integral_comp pairingHomeomorph.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with y
  change F̂ f (rationalAdelePontryaginDualEquiv y).toMul *
    (((rationalAdelePontryaginDualEquiv y).toMul (Multiplicative.ofAdd x) : Circle) : ℂ) = _
  rw [rationalAdeleDualFourier_pairing, rationalAdelePontryaginDualEquiv_apply, mul_neg,
    AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_rationalAdeleAddChar _)]
  simp

omit [MeasurableSpace D] [BorelSpace D] in
private theorem continuous_frequency {p : A → ℂ} (hp : Integrable p μA) :
    Continuous (F p) := by
  have h : F p = F̂ p ∘ pairingHomeomorph :=
    funext fun y ↦ (rationalAdeleDualFourier_pairing p y).symm
  rw [h]
  exact (rationalAdeleDualFourier_continuous_vanishing hp).1.comp pairingHomeomorph.continuous

/-- If `f` and its full-dual transform are integrable, the inverse Fourier
integral is a continuous representative of `f`. The equality is everywhere
if the original representative is continuous. -/
public theorem rationalAdeleDualFourier_inversion {f : A → ℂ}
    (hf : Integrable f μA) (hFf : Integrable (F̂ f) μD) :
    Continuous (rationalAdeleDualFourierInverse (F̂ f)) ∧
      rationalAdeleDualFourierInverse (F̂ f) =ᵐ[μA] f ∧
      (Continuous f → rationalAdeleDualFourierInverse (F̂ f) = f) := by
  have hfreq : Integrable (F f) μA := by
    have hcomp := (pairing_measurePreserving.integrable_comp_emb
      pairingHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr hFf
    exact hcomp.congr (Filter.Eventually.of_forall fun y ↦ rationalAdeleDualFourier_pairing f y)
  let u := rationalAdeleDualFourierInverse (F̂ f)
  have hu : u = fun x ↦ F (F f) (-x) := funext dual_inverse_eq_reflected
  have huc : Continuous u := by
    rw [hu]
    exact (continuous_frequency hfreq).comp continuous_neg
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  have hloc : LocallyIntegrable (u - f) μA := huc.locallyIntegrable.sub hf.locallyIntegrable
  have hz := rationalAdeleSchwartzLF_ae_zero_of_forall_integral_mul_eq_zero hloc (fun g ↦ by
    obtain ⟨hi, hj, he⟩ := rationalAdeleFourier_test_inversion hf hfreq g
    simp only [Pi.sub_apply, hu, sub_mul]
    rw [integral_sub hi hj, he, sub_self])
  have hae : u =ᵐ[μA] f := hz.mono fun x hx ↦ sub_eq_zero.mp hx
  exact ⟨huc, hae, fun hc ↦ Measure.eq_of_ae_eq hae huc hc⟩

/-- Normalized Fourier uniqueness on the full rational adelic dual for
integrable functions. No integrability of their common transform is needed. -/
public theorem rationalAdeleDualFourier_injective {f g : A → ℂ}
    (hf : Integrable f μA) (hg : Integrable g μA) (h : F̂ f = F̂ g) : f =ᵐ[μA] g := by
  have hz : F̂ (f - g) = 0 := by
    funext χ
    let k (x : A) := conj (χ (Multiplicative.ofAdd x) : ℂ)
    have hc : Continuous k := Complex.continuous_conj.comp
      (continuous_subtype_val.comp χ.continuous)
    have hi {p : A → ℂ} (hp : Integrable p μA) : Integrable (fun x ↦ p x * k x) μA :=
      hp.mul_bdd hc.aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun x ↦ by simp [k])
    change (∫ x, (f x - g x) * k x ∂μA) = 0
    simp only [sub_mul]
    rw [integral_sub (hi hf) (hi hg)]
    exact sub_eq_zero.mpr (congrFun h χ)
  have hinv := (rationalAdeleDualFourier_inversion (hf.sub hg) (hz ▸ integrable_zero _ _ _)).2.1
  rw [hz] at hinv
  have h' : rationalAdeleDualFourierInverse (0 : D → ℂ) = 0 := by
    funext x
    simp [rationalAdeleDualFourierInverse]
  rw [h'] at hinv
  exact hinv.mono fun x hx ↦ sub_eq_zero.mp hx.symm

end Masullo
