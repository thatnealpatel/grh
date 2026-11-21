module

public import Lemmas.RealLogFourierContact

/-! # The real additive log distribution and its contact term

Masullo (B.4.4.1)–(B.4.4.2), pp. 619–620, defines the real local term by
pairing the negative logarithm with the standard additive Fourier transform,
then translating the multiplicative identity to zero. Off that identity,
Connes, Appendix II (34)–(36), uses normalized multiplicative Haar. The
extracted cutoff in (B.4.3.13) instead displays full real multiplicative Haar.
The computation below fixes the off-identity coefficient directly from the
additive definition. The zero-value case needs no gap in the support and
is the remainder after subtraction of a test with value one at the identity.
The unit-radius subtraction below calibrates that scalar contribution.
-/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- The zero-value remainder in Connes, Appendix II (34), with the
standard additive `2π` transform and Lebesgue measure. No vanishing on
a neighborhood is needed when all the indicated pairings are absolute. -/
public theorem real_log_fourier_of_zero {u : ℝ → ℂ} (hu : Continuous u)
    (hzero : u 0 = 0) (hi : Integrable u) (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 u ξ))
    (hright : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) = (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  have hv : Continuous (𝓕 u) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  -- Represent the logarithm by a subtracted Cauchy kernel with absolute Fubini.
  calc
    _ = ∫ a in Ioi (0 : ℝ), ∫ ξ,
          ((RealLogFourier.cauchy a ξ - RealLogFourier.cauchy a 1 : ℝ) : ℂ) * 𝓕 u ξ :=
        RealLogFourier.log_pairing_eq_cauchy hv hlog
    -- Fourier inversion at zero cancels the constant in each scale slice.
    _ = ∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, RealLogFourier.laplaceProfile a z * u z :=
        setIntegral_congr_fun measurableSet_Ioi fun a ha ↦
          RealLogFourier.cauchy_sub_pairing_eq_laplace hu hi huf hzero ha
    -- In space, integrating the Laplace kernel in scale produces the half factor.
    _ = _ := RealLogFourier.laplace_integral_eq_half hu hright

/-- With the standard additive `2π` Fourier convention and Lebesgue measure,
the negative logarithm has off-zero kernel `1 / (2 |z|)`. Here `u` is a
smooth compactly supported additive test that vanishes near zero. Both
pairings are absolutely integrable. -/
public theorem real_log_fourier_off_zero {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hgap : ∃ ε > 0, ∀ z, |z| < ε → u z = 0) :
    Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 u ξ) ∧
      Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) ∧
      -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) = (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hgap⟩ := hgap
  let v := hc.toSchwartzMap hu
  have hzero : u 0 = 0 := hgap 0 (by simpa using hε)
  have hright := RealLogFourier.integrable_div_abs hu.continuous hc hε hgap
  exact ⟨RealLogFourier.log_fourier_integrable v, hright,
    real_log_fourier_of_zero hu.continuous hzero v.integrable
      ((𝓕 v).integrable) (RealLogFourier.log_fourier_integrable v) hright⟩

/-- The real additive principal value with its contact term (Connes, Appendix II
(34)–(35); Masullo (B.4.4.1), pp. 619–620). Masullo's additive definition fixes
Lebesgue measure and the standard `2π` transform; the extracted full-Haar
coefficient in (B.4.3.13) does not agree with that definition. Here the
spatial term uses the half-weighted kernel and subtracts at radius one. -/
public theorem real_log_fourier_unit_subtraction (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) ∧
      Integrable (RealLogFourier.unitSubtraction u) ∧
      -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) =
        (1 / 2 : ℂ) * (∫ z, RealLogFourier.unitSubtraction u z) +
          ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * u 0 := by
  let G := RealLogFourier.laplaceProfile 1
  let r (z : ℝ) := u z - u 0 * G z
  have hG : Integrable G := RealLogFourier.laplaceProfile_integrable one_pos
  have hGcont : Continuous G := by unfold G RealLogFourier.laplaceProfile; fun_prop
  have hrcont : Continuous r := u.continuous.sub (hGcont.const_mul _)
  have hr : Integrable r := u.integrable.sub (hG.const_mul _)
  have hrzero : r 0 = 0 := by simp [r, G, RealLogFourier.laplaceProfile]
  obtain ⟨hGfourier, hGlog, hGlog0⟩ := RealLogFourier.laplace_log_fourier_contact
  have huf : Integrable (𝓕 (u : ℝ → ℂ)) := (𝓕 u).integrable
  have hlog := RealLogFourier.log_fourier_integrable u
  have hf (ξ : ℝ) : 𝓕 r ξ = 𝓕 (u : ℝ → ℂ) ξ - u 0 * 𝓕 G ξ := by
    apply eq_sub_of_add_eq
    exact (RealLogFourier.fourier_remainder_add hr (fun z ↦ by dsimp [r]; ring) ξ).symm
  have hf' (ξ : ℝ) : (Real.log |ξ| : ℂ) * 𝓕 r ξ =
      (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ - u 0 * ((Real.log |ξ| : ℂ) * 𝓕 G ξ) := by
    rw [hf]; ring
  have hrlog := (hlog.sub (hGlog.const_mul (u 0))).congr (.of_forall fun x ↦ (hf' x).symm)
  have hrdiv := RealLogFourier.remainder_div_integrable u.continuous u.differentiable.differentiableAt
    u.integrable
  -- The zero-value theorem applies even though the comparator has a cusp.
  have hremain := real_log_fourier_of_zero hrcont hrzero hr
    ((huf.sub (hGfourier.const_mul (u 0))).congr (.of_forall fun x ↦ (hf x).symm)) hrlog hrdiv
  have hT : (∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 r ξ) = ∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ := by
    simp_rw [hf']
    rw [integral_sub hlog (hGlog.const_mul (u 0)), integral_const_mul, hGlog0, mul_zero, sub_zero]
  obtain ⟨hPG, hPGval⟩ := RealLogFourier.laplace_unitSubtraction_contact
  -- Instead of Connes's Gaussian evaluation, subtract the scale-one Laplace
  -- profile. Its Fourier moment is zero and its spatial value is `-log(2π)-γ`.
  have hp (z : ℝ) := RealLogFourier.unitSubtraction_eq_remainder (u : ℝ → ℂ) z
  refine ⟨hlog, (hrdiv.add (hPG.const_mul (u 0))).congr (.of_forall fun z ↦ (hp z).symm), ?_⟩
  rw [← hT, hremain]
  simp_rw [hp]
  rw [integral_add hrdiv (hPG.const_mul (u 0)), integral_const_mul]
  rw [mul_add, mul_left_comm (1 / 2 : ℂ), hPGval]
  push_cast
  ring

/-- The shrinking-cutoff form of the real additive principal value, with the
standard `2π` Fourier transform. Connes (34)–(35) supplies the normalized
cutoff; the extracted Masullo (B.4.3.13) instead has twice its magnitude.
The annulus correction and absolute unit-subtracted identity give the
limit without changing the additive pairing of (B.4.4.1). -/
public theorem real_log_fourier_cutoff (u : 𝓢(ℝ, ℂ)) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) {z | ε ≤ |z|}) ∧
      Tendsto (fun ε : ℝ ↦ (1 / 2 : ℂ) * (∫ z in {z | ε ≤ |z|}, u z / ((|z| : ℝ) : ℂ)) +
        (Real.log ε : ℂ) * u 0) (𝓝[Ioi 0] 0)
        (𝓝 (-(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) -
          ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * u 0)) := by
  obtain ⟨_, hsub, hvalue⟩ := real_log_fourier_unit_subtraction u
  refine ⟨fun ε hε ↦ RealLogFourier.integrableOn_div_abs_cutoff u.integrable hε, ?_⟩
  rw [hvalue, add_sub_cancel_right]
  -- The removed part of the absolute density tends to zero.
  refine ((RealLogFourier.tendsto_integral_abs_cutoff hsub).const_mul (1 / 2 : ℂ)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)]
    with ε hε hε₁
  -- The inverse-radius integral on the annulus is `-2 log ε`.
  exact (RealLogFourier.cutoff_eq_unitSubtraction u.integrable hsub hε hε₁.le).symm

end Masullo
