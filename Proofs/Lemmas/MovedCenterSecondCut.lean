module

public import Lemmas.ThreeSiteMomentCompletion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The moved-center second cut and its joint slack

Source: `e97a8a47:.godel/bob/joint-tail-deletion-33.md:34–76` (see also `9d0e1e0`).
Consumers: `ad99c73:.godel/bob/three-midpoints-deletion-33.md:7–14` and
`58e1e35:.godel/bob/three-midpoints-deletion-33.md:52–61`.
Owning check session: `01a20e90-1953-703f-a5c5-0300053aba36`.

Scope: the price on the frequency side, for a finite measure on `ℝ` and finitely many
second-reply sites. Use the source's already normalized `V_B` for `V`; the sign of the
actual first field `-V_B` at `3t` does not change its square or disk. Use `unfoldedMeasure`
(the Cauchy law of scale `1/2`) for `μ`, `Finset.Icc (-1 : ℤ) 1` for the three sites,
`s j = 6/25 + j * (13/25)`, and feed the real angular Laurent majorant to `q` after
composition with `x ↦ (13/25) * x`. This majorant is measurable by continuity.
The common unit phase in `H` preserves its norm, so majorizing the angular Laurent
sum gives the required majorization of `H`. First replies use values of the respective
normalized fields `V_A`, `V_B` at their selected frequencies, not almost-everywhere
evaluations. The joint row takes `M - 8/9` for `surplus` and does not re-normalize
either the measure or the first-cut right sides.

The disk and the same vanishing second reply at every site give the quadratic budget.
The polarization and joint slacks need no admissibility or pointwise bounds on the
center, only `L²(μ)`. This does not compute the physical slab primitives, take atom
suprema, or verify any numerical exclusion.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Masullo.MovedCenterSecondCut

open ThreeSiteMomentCompletion (phase)

/-- The real-coefficient sum of the positive site phases. -/
@[expose] public noncomputable def siteWeight {ι : Type*} (J : Finset ι)
    (s coeff : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ j ∈ J, (coeff j : ℂ) * phase (s j) x

/-- The frequency integrand of `Q`. -/
@[expose] public noncomputable def quadraticIntegrand (q : ℝ → ℝ) (H V : ℝ → ℂ)
    (x : ℝ) : ℝ :=
  q x * ‖V x‖ ^ 2 + (H x * V x ^ 2).re

/-- The quadratic cost, integrated in the given measure with no scale factor. -/
@[expose] public noncomputable def quadratic (μ : Measure ℝ) (q : ℝ → ℝ)
    (H V : ℝ → ℂ) : ℝ :=
  ∫ x, quadraticIntegrand q H V x ∂μ

/-- The real polarization integrand, with conjugation only in the norm-square term. -/
@[expose] public noncomputable def polarIntegrand (q : ℝ → ℝ) (H Z V : ℝ → ℂ)
    (x : ℝ) : ℝ :=
  q x * (conj (Z x) * V x).re + (H x * Z x * V x).re

/-- The integrated real polarization, with the center in the first slot. -/
@[expose] public noncomputable def polar (μ : Measure ℝ) (q : ℝ → ℝ)
    (H Z V : ℝ → ℂ) : ℝ :=
  ∫ x, polarIntegrand q H Z V x ∂μ

private theorem measurable_phase (s : ℝ) : Measurable (phase s) := by
  unfold phase
  fun_prop

private theorem norm_phase (s x : ℝ) : ‖phase s x‖ = 1 := by
  simp [phase, Complex.norm_exp_mul_I]

private theorem measurable_siteWeight {ι : Type*} (J : Finset ι) (s coeff : ι → ℝ) :
    Measurable (siteWeight J s coeff) :=
  Finset.measurable_sum J fun j _ ↦ measurable_const.mul (measurable_phase (s j))

private theorem ae_norm_majorant_le {μ : Measure ℝ} {q : ℝ → ℝ} {H : ℝ → ℂ} {B : ℝ}
    (hmajor : ∀ᵐ x ∂μ, ‖H x‖ ≤ q x) (hbound : ∀ᵐ x ∂μ, q x ≤ B) :
    ∀ᵐ x ∂μ, ‖q x‖ ≤ B := by
  filter_upwards [hmajor, hbound] with x hx hb
  rwa [Real.norm_eq_abs, abs_of_nonneg ((norm_nonneg _).trans hx)]

/-- A bounded majorant makes the quadratic integrand integrable for every `L²` field. -/
public theorem integrable_quadraticIntegrand {μ : Measure ℝ} {q : ℝ → ℝ}
    {H V : ℝ → ℂ} {B : ℝ} (hq : AEStronglyMeasurable q μ) (hH : AEStronglyMeasurable H μ)
    (hmajor : ∀ᵐ x ∂μ, ‖H x‖ ≤ q x) (hbound : ∀ᵐ x ∂μ, q x ≤ B)
    (hV : MemLp V 2 μ) : Integrable (quadraticIntegrand q H V) μ := by
  have hsq := hV.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hVsq : Integrable (fun x ↦ V x ^ 2) μ := by
    refine hsq.mono (hV.aestronglyMeasurable.pow 2) (ae_of_all _ fun x ↦ ?_)
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hHB : ∀ᵐ x ∂μ, ‖H x‖ ≤ B := by
    filter_upwards [hmajor, hbound] with x hx hb using hx.trans hb
  exact (hsq.bdd_mul hq (ae_norm_majorant_le hmajor hbound)).add (hVsq.bdd_mul hH hHB).re

/-- The majorization gives positivity for any field, without a disk condition on it.
For `L²` fields and a bounded measurable majorant, `integrable_quadraticIntegrand`
ensures this is the sign of an integrable cost. -/
public theorem quadratic_nonneg {μ : Measure ℝ} {q : ℝ → ℝ} {H V : ℝ → ℂ}
    (hmajor : ∀ᵐ x ∂μ, ‖H x‖ ≤ q x) : 0 ≤ quadratic μ q H V := by
  apply integral_nonneg_of_ae
  filter_upwards [hmajor] with x hx
  have h : -(H x * V x ^ 2).re ≤ q x * ‖V x‖ ^ 2 := by
    calc
      _ ≤ ‖-(H x * V x ^ 2)‖ := by simpa only [Complex.neg_re] using
        (Complex.re_le_norm (-(H x * V x ^ 2)))
      _ = ‖H x‖ * ‖V x‖ ^ 2 := by rw [norm_neg, norm_mul, norm_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  exact neg_le_iff_add_nonneg.mp h

private theorem two_mul_polarIntegrand (q : ℝ → ℝ) (H Z V : ℝ → ℂ) (x : ℝ) :
    2 * polarIntegrand q H Z V x = quadraticIntegrand q H V x +
      quadraticIntegrand q H Z x - quadraticIntegrand q H (V - Z) x := by
  simp only [polarIntegrand, quadraticIntegrand, Pi.sub_apply, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The polarization integrand is integrable and the exact real polarization identity
holds for any two `L²` fields, including centers that are not admissible laws. -/
public theorem polarization {μ : Measure ℝ} {q : ℝ → ℝ} {H Z V : ℝ → ℂ} {B : ℝ}
    (hq : AEStronglyMeasurable q μ) (hH : AEStronglyMeasurable H μ)
    (hmajor : ∀ᵐ x ∂μ, ‖H x‖ ≤ q x) (hbound : ∀ᵐ x ∂μ, q x ≤ B)
    (hZ : MemLp Z 2 μ) (hV : MemLp V 2 μ) :
    Integrable (polarIntegrand q H Z V) μ ∧
      2 * polar μ q H Z V = quadratic μ q H V + quadratic μ q H Z - quadratic μ q H (V - Z) := by
  have hQV := integrable_quadraticIntegrand hq hH hmajor hbound hV
  have hQZ := integrable_quadraticIntegrand hq hH hmajor hbound hZ
  have hQD := integrable_quadraticIntegrand hq hH hmajor hbound (hV.sub hZ)
  refine ⟨(((hQV.add hQZ).sub hQD).const_mul (1 / 2)).congr ?_, ?_⟩
  · exact ae_of_all _ fun x ↦ by
      change (1 / 2) * (_ + _ - _) = polarIntegrand q H Z V x
      rw [← two_mul_polarIntegrand]
      ring
  · unfold polar quadratic
    rw [← integral_const_mul]
    simp_rw [two_mul_polarIntegrand]
    rw [integral_sub (f := fun x ↦ quadraticIntegrand q H V x + quadraticIntegrand q H Z x)
      (hQV.add hQZ) hQD, integral_add hQV hQZ]

private theorem ae_caps_of_disk {μ : Measure ℝ} {V n : ℝ → ℂ}
    (hdisk : ∀ᵐ x ∂μ, ‖n x - V x ^ 2‖ ≤ 1 - ‖V x‖ ^ 2) :
    ∀ᵐ x ∂μ, ‖V x‖ ≤ 1 ∧ ‖n x‖ ≤ 1 := by
  filter_upwards [hdisk] with x hx
  have hs : ‖V x‖ ^ 2 ≤ 1 := sub_nonneg.mp ((norm_nonneg _).trans hx)
  refine ⟨(sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hs), ?_⟩
  calc
    ‖n x‖ = ‖(n x - V x ^ 2) + V x ^ 2‖ := by rw [sub_add_cancel]
    _ ≤ ‖n x - V x ^ 2‖ + ‖V x ^ 2‖ := norm_add_le _ _
    _ ≤ 1 := by rw [norm_pow]; linarith only [hx]

private theorem integral_siteWeight_re_eq_zero {ι : Type*} {μ : Measure ℝ}
    (J : Finset ι) (s coeff : ι → ℝ) {n : ℝ → ℂ} (hn : Integrable n μ)
    (hzero : ∀ j ∈ J, (∫ x, phase (s j) x * n x ∂μ).re = 0) :
    (∫ x, (siteWeight J s coeff x * n x).re ∂μ) = 0 := by
  have hsite (j : ι) : Integrable (fun x ↦ phase (s j) x * n x) μ :=
    hn.bdd_mul (measurable_phase _).aestronglyMeasurable (ae_of_all _ fun x ↦ (norm_phase _ x).le)
  have hsum (x : ℝ) : (siteWeight J s coeff x * n x).re =
      ∑ j ∈ J, coeff j * (phase (s j) x * n x).re := by
    simp only [siteWeight, Finset.sum_mul, Complex.re_sum, mul_assoc, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsiteRe (j : ι) : Integrable (fun x ↦ (phase (s j) x * n x).re) μ := (hsite j).re
  simp_rw [hsum]
  rw [integral_finsetSum J (fun j _ ↦ (hsiteRe j).const_mul (coeff j))]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hr : (∫ x, (phase (s j) x * n x).re ∂μ) = (∫ x, phase (s j) x * n x ∂μ).re :=
    integral_re (hsite j)
  rw [integral_const_mul, hr, hzero j hj, mul_zero]

/-- The actual disk and one simultaneous second field with vanishing real replies at
all sites force `Q(V) ≤ ∫ q`. Neither that bound nor integrability of the replies is
assumed. -/
public theorem quadratic_le_of_second_reply {ι : Type*} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (J : Finset ι) (s coeff : ι → ℝ) {q : ℝ → ℝ} {B : ℝ} {V n : ℝ → ℂ}
    (hq : AEStronglyMeasurable q μ) (hV : AEStronglyMeasurable V μ)
    (hn : AEStronglyMeasurable n μ) (hmajor : ∀ᵐ x ∂μ, ‖siteWeight J s coeff x‖ ≤ q x)
    (hbound : ∀ᵐ x ∂μ, q x ≤ B) (hdisk : ∀ᵐ x ∂μ, ‖n x - V x ^ 2‖ ≤ 1 - ‖V x‖ ^ 2)
    (hzero : ∀ j ∈ J, (∫ x, phase (s j) x * n x ∂μ).re = 0) :
    quadratic μ q (siteWeight J s coeff) V ≤ ∫ x, q x ∂μ := by
  let H := siteWeight J s coeff
  have hH := (measurable_siteWeight J s coeff).aestronglyMeasurable (μ := μ)
  have hcaps := ae_caps_of_disk hdisk
  have hVL2 : MemLp V 2 μ := MemLp.of_bound hV 1 (hcaps.mono fun _ hx ↦ hx.1)
  have hnL1 : Integrable n μ := Integrable.of_bound hn 1 (hcaps.mono fun _ hx ↦ hx.2)
  have hqL1 := Integrable.of_bound hq B (ae_norm_majorant_le hmajor hbound)
  have hHB : ∀ᵐ x ∂μ, ‖H x‖ ≤ B := by
    filter_upwards [hmajor, hbound] with x hx hb using hx.trans hb
  have hHn : Integrable (fun x ↦ (H x * n x).re) μ := (hnL1.bdd_mul hH hHB).re
  have hpoint : ∀ᵐ x ∂μ, quadraticIntegrand q H V x ≤ q x + (H x * n x).re := by
    filter_upwards [hmajor, hdisk] with x hx hd
    have hr : 0 ≤ 1 - ‖V x‖ ^ 2 := (norm_nonneg _).trans hd
    have h : (H x * (V x ^ 2 - n x)).re ≤ q x * (1 - ‖V x‖ ^ 2) := calc
      _ ≤ ‖H x * (V x ^ 2 - n x)‖ := Complex.re_le_norm _
      _ = ‖H x‖ * ‖n x - V x ^ 2‖ := by rw [norm_mul, norm_sub_rev]
      _ ≤ ‖H x‖ * (1 - ‖V x‖ ^ 2) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ q x * (1 - ‖V x‖ ^ 2) := mul_le_mul_of_nonneg_right hx hr
    rw [mul_sub, Complex.sub_re, mul_sub, mul_one] at h
    unfold quadraticIntegrand
    linarith only [h]
  calc
    quadratic μ q H V ≤ ∫ x, q x + (H x * n x).re ∂μ :=
      integral_mono_ae (integrable_quadraticIntegrand hq hH hmajor hbound hVL2)
        (hqL1.add hHn) hpoint
    _ = ∫ x, q x ∂μ := by
      rw [integral_add hqL1 hHn, integral_siteWeight_re_eq_zero J s coeff hnL1 hzero, add_zero]

/-- The response in a normalized first direction `γ` to the field's value at its site. -/
@[expose] public noncomputable def firstReply (γ value : ℂ) : ℝ := (conj γ * value).re

private theorem firstReply_le_one {γ value : ℂ} (hγ : ‖γ‖ = 1) (hvalue : ‖value‖ ≤ 1) :
    firstReply γ value ≤ 1 := by
  calc
    _ ≤ ‖conj γ * value‖ := Complex.re_le_norm _
    _ = ‖value‖ := by rw [norm_mul, Complex.norm_conj, hγ, one_mul]
    _ ≤ 1 := hvalue

/-- The raw joint price adds exactly the first-cut slacks, the second-budget slack,
and the distance cost. In particular the joint upper row retains the first slacks
and `σ Q(V - Z)`, and the raw second constant is `σ (∫ q + Q(Z))`.
`value i` is the actual field value at first-cut site `i`, so its cap is imposed at
that site, independently of the almost-everywhere disk hypotheses. -/
public theorem joint_row {ι κ : Type*} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (J : Finset ι) (s coeff : ι → ℝ) (I : Finset κ) (weight : κ → ℝ) (γ value : κ → ℂ)
    (surplus : ℝ) {σ B : ℝ} {q : ℝ → ℝ} {V n Z : ℝ → ℂ}
    (hq : AEStronglyMeasurable q μ) (hV : AEStronglyMeasurable V μ)
    (hn : AEStronglyMeasurable n μ) (hZ : MemLp Z 2 μ)
    (hmajor : ∀ᵐ x ∂μ, ‖siteWeight J s coeff x‖ ≤ q x) (hbound : ∀ᵐ x ∂μ, q x ≤ B)
    (hdisk : ∀ᵐ x ∂μ, ‖n x - V x ^ 2‖ ≤ 1 - ‖V x‖ ^ 2)
    (hzero : ∀ j ∈ J, (∫ x, phase (s j) x * n x ∂μ).re = 0)
    (hweight : ∀ i ∈ I, 0 ≤ weight i) (hγ : ∀ i ∈ I, ‖γ i‖ = 1)
    (hvalue : ∀ i ∈ I, ‖value i‖ ≤ 1) (hσ : 0 ≤ σ) :
    let H := siteWeight J s coeff
    let d := ∫ x, q x ∂μ
    let slack := ∑ i ∈ I, weight i * (1 - firstReply (γ i) (value i))
    let raw := surplus + (∑ i ∈ I, weight i) + σ * (d + quadratic μ q H Z) -
      (∑ i ∈ I, weight i * firstReply (γ i) (value i)) - 2 * σ * polar μ q H Z V
    raw = surplus + slack + σ * (d - quadratic μ q H V) + σ * quadratic μ q H (V - Z) ∧
      surplus + σ * quadratic μ q H (V - Z) + slack ≤ raw ∧ surplus ≤ raw := by
  dsimp only
  have hVL2 : MemLp V 2 μ := MemLp.of_bound hV 1 ((ae_caps_of_disk hdisk).mono fun _ hx ↦ hx.1)
  have hH := (measurable_siteWeight J s coeff).aestronglyMeasurable (μ := μ)
  have hpol := (polarization hq hH hmajor hbound hZ hVL2).2
  have hQ := quadratic_le_of_second_reply J s coeff hq hV hn hmajor hbound hdisk hzero
  have hfirst : 0 ≤ ∑ i ∈ I, weight i * (1 - firstReply (γ i) (value i)) :=
    Finset.sum_nonneg fun i hi ↦
      mul_nonneg (hweight i hi) (sub_nonneg.mpr (firstReply_le_one (hγ i hi) (hvalue i hi)))
  have hsum : (∑ i ∈ I, weight i * (1 - firstReply (γ i) (value i))) =
      (∑ i ∈ I, weight i) - (∑ i ∈ I, weight i * firstReply (γ i) (value i)) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hcost : 0 ≤ σ * quadratic μ q (siteWeight J s coeff) (V - Z) :=
    mul_nonneg hσ (quadratic_nonneg hmajor)
  have hbudget := mul_nonneg hσ (sub_nonneg.mpr hQ)
  have hpolσ := congrArg (fun r : ℝ ↦ σ * r) hpol
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    linear_combination -hpolσ
  · linarith only [hbudget, hsum, hpolσ]
  · linarith only [hfirst, hcost, hbudget, hsum, hpolσ]

end Masullo.MovedCenterSecondCut
