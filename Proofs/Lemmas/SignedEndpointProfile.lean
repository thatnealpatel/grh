module

public import Lemmas.PrimeTranslationProfileApproximation
public import Lemmas.PrimeWindowModulation
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import all Lemmas.PrimeWindowCorrectedLimit -- reindex the existing prime-power form
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Exact signed prime quotient on the modulated endpoint profile

Source: `6ffb987a:.godel/bob/endpoint-arithmetic-test.md`, lines 3–18.
Owning check session: `01a20ec7-4115-7a16-8368-f5947df6f1f0`.

Scope: the fixed positive diameter, full-line `L²` zero extension of the sum of
endpoint exponentials, its exact overlap, and the resulting character-twisted
prime-translation quotient. The positive translation part is the negative of
the existing Weil prime form. No arithmetic estimate or positivity of the Weil
form is asserted.
-/

open MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate InnerProductSpace

namespace Masullo

local notation "𝓗" => Lp ℂ 2 (volume : Measure ℝ)
local notation "cut" D:max => Finset.Ico 1 ⌈exp D⌉₊

private noncomputable def endpointRaw (D x : ℝ) : ℝ :=
  exp (-x / 2) + exp (-(D - x) / 2)

/-- The sum of the two endpoint exponentials on `[0,D]`, zero elsewhere. -/
@[expose] public noncomputable def signedEndpointProfile (D : ℝ) : ℝ → ℝ :=
  (Set.Icc 0 D).indicator (fun x ↦ exp (-x / 2) + exp (-(D - x) / 2))

/-- This is the same sum of left and reflected profiles as in the untwisted model. -/
public theorem signedEndpointProfile_eq_endpointSum (D x : ℝ) :
    signedEndpointProfile D x = primeTranslationProfile D x + primeTranslationReflectedProfile D x := by
  have hflip : D - x ∈ Set.Icc 0 D ↔ x ∈ Set.Icc 0 D := by
    simp only [Set.mem_Icc, sub_nonneg, sub_le_self_iff, and_comm]
  unfold signedEndpointProfile primeTranslationReflectedProfile primeTranslationProfile
  by_cases hx : x ∈ Set.Icc 0 D
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem (hflip.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h ↦ hx (hflip.mp h)), add_zero]

private theorem signedEndpointProfile_memLp (D : ℝ) :
    MemLp (fun x ↦ (signedEndpointProfile D x : ℂ)) 2 volume := by
  have heq : (fun x ↦ (signedEndpointProfile D x : ℂ)) =
      (Set.Icc 0 D).indicator (fun x ↦ (endpointRaw D x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc 0 D <;> simp [signedEndpointProfile, endpointRaw, hx]
  rw [heq, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc 0 D)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine MemLp.of_bound (by unfold endpointRaw; fun_prop) 2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have ha : exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1])
  have hb : exp (-(D - x) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.2])
  rw [Complex.norm_real, Real.norm_of_nonneg (by unfold endpointRaw; positivity), endpointRaw]
  linarith

/-- The supported endpoint test in the full-line complex `L²` model. -/
public noncomputable def signedEndpointProfileVector (D : ℝ) : 𝓗 :=
  (signedEndpointProfile_memLp D).toLp _

public theorem signedEndpointProfileVector_ae (D : ℝ) :
    signedEndpointProfileVector D =ᵐ[volume] fun x ↦ (signedEndpointProfile D x : ℂ) :=
  (signedEndpointProfile_memLp D).coeFn_toLp

public theorem signedEndpointProfileVector_supported (D : ℝ) :
    PrimeWindowSupported D (signedEndpointProfileVector D) := by
  filter_upwards [signedEndpointProfileVector_ae D] with x hx hxD
  simp [hx, signedEndpointProfile, hxD]

private theorem overlap_support {D t x : ℝ} (ht : 0 ≤ t) :
    (x ∈ Set.Icc 0 D ∧ x + t ∈ Set.Icc 0 D) ↔ x ∈ Set.Icc 0 (D - t) := by
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨⟨hx, _⟩, ⟨_, hxt⟩⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨hx, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem overlap_integral_on {D t : ℝ} (ht : 0 ≤ t) :
    (∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + t)) =
      ∫ x in Set.Icc 0 (D - t), endpointRaw D x * endpointRaw D (x + t) := by
  have hoff : ∀ x : ℝ, x ∉ Set.Icc 0 (D - t) →
      signedEndpointProfile D x * signedEndpointProfile D (x + t) = 0 := by
    intro x hx
    by_cases hxD : x ∈ Set.Icc 0 D
    · have hxt : x + t ∉ Set.Icc 0 D := fun h ↦ hx ((overlap_support ht).mp ⟨hxD, h⟩)
      simp [signedEndpointProfile, hxt]
    · simp [signedEndpointProfile, hxD]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (Filter.Eventually.of_forall hoff)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  obtain ⟨hxD, hxt⟩ := (overlap_support ht).mpr hx
  simp [signedEndpointProfile, endpointRaw, hxD, hxt]

-- The two same-endpoint terms vary with `x`; the two cross terms are constant.
private theorem endpointRaw_mul_shift (D t x : ℝ) :
    endpointRaw D x * endpointRaw D (x + t) =
      (exp (-t / 2) * exp (-x) + exp (-t / 2 - (D - t)) * exp x) +
        (exp (t / 2) + exp (-t / 2)) / exp (D / 2) := by
  have h₁ : exp (-x / 2) * exp (-(x + t) / 2) = exp (-t / 2) * exp (-x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ : exp (-(D - x) / 2) * exp (-(D - (x + t)) / 2) =
      exp (-t / 2 - (D - t)) * exp x := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₃ : exp (-x / 2) * exp (-(D - (x + t)) / 2) = exp (t / 2) / exp (D / 2) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have h₄ : exp (-(D - x) / 2) * exp (-(x + t) / 2) = exp (-t / 2) / exp (D / 2) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [endpointRaw, endpointRaw, add_mul, mul_add, mul_add, h₁, h₂, h₃, h₄, add_div]
  ring

/-- For a nonnegative shift at most `D`, the full-line real correlation is the
integral on `[0,D-t]`. The formula includes `t = D`, with zero integral over
its singleton overlap. -/
public theorem signedEndpointProfile_overlap {D t : ℝ} (ht : 0 ≤ t) (htD : t ≤ D) :
    (∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + t)) =
      2 * exp (-t / 2) * (1 - exp (-(D - t))) +
        (D - t) * (exp (t / 2) + exp (-t / 2)) / exp (D / 2) := by
  rw [overlap_integral_on ht, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (sub_nonneg.mpr htD)]
  simp_rw [endpointRaw_mul_shift]
  have h₁ : IntervalIntegrable (fun x : ℝ ↦ exp (-t / 2) * exp (-x)) volume 0 (D - t) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x : ℝ ↦ exp (-t / 2 - (D - t)) * exp x) volume 0 (D - t) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h₁.add h₂) intervalIntegrable_const,
    intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg exp,
    integral_exp, integral_exp, intervalIntegral.integral_const]
  simp only [neg_zero, Real.exp_zero, sub_zero, smul_eq_mul]
  have hright : exp (-t / 2 - (D - t)) * (exp (D - t) - 1) =
      exp (-t / 2) * (1 - exp (-(D - t))) := by
    rw [sub_eq_add_neg, Real.exp_add, mul_assoc, mul_sub, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, mul_one]
  rw [hright]
  ring

/-- At or beyond the support diameter, the correlation vanishes. -/
public theorem signedEndpointProfile_overlap_eq_zero {D t : ℝ} (ht : 0 ≤ t) (hDt : D ≤ t) :
    (∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + t)) = 0 := by
  rcases hDt.eq_or_lt with rfl | hDt
  · rw [signedEndpointProfile_overlap ht le_rfl]
    simp
  · rw [overlap_integral_on ht, Set.Icc_eq_empty_of_lt (sub_neg.mpr hDt), setIntegral_empty]

/-- The real overlap computes the actual complex `L²` translated pairing. -/
public theorem signedEndpointProfile_inner_translate (D t : ℝ) :
    ⟪signedEndpointProfileVector D, primeWindowTranslate t (signedEndpointProfileVector D)⟫_ℂ =
      (↑(∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + t) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (↑(signedEndpointProfile D x * signedEndpointProfile D (x + t) : ℝ) : ℂ) := by
      have hshift := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp
        (signedEndpointProfileVector_ae D)
      apply integral_congr_ae
      filter_upwards [primeWindowTranslate_ae t (signedEndpointProfileVector D),
        signedEndpointProfileVector_ae D, hshift] with x hT hx hxt
      change signedEndpointProfileVector D (x + t) = (signedEndpointProfile D (x + t) : ℂ) at hxt
      rw [RCLike.inner_apply, hT, hx, hxt, Complex.conj_ofReal, Complex.ofReal_mul, mul_comm]
    _ = _ := integral_ofReal (𝕜 := ℂ)
      (f := fun x ↦ signedEndpointProfile D x * signedEndpointProfile D (x + t))

/-- The squared norm of the modulated endpoint test, with `X = exp D` and
`E = exp (D / 2)`. -/
public theorem signedEndpointProfile_norm_sq {D : ℝ} (hD : 0 ≤ D) (y : ℝ) :
    ‖primeWindowModulate y (signedEndpointProfileVector D)‖ ^ 2 =
      2 * (1 - 1 / exp D) + 2 * D / exp (D / 2) := by
  have hT : primeWindowTranslate 0 (signedEndpointProfileVector D) = signedEndpointProfileVector D :=
    Lp.ext (by simpa only [add_zero] using primeWindowTranslate_ae 0 (signedEndpointProfileVector D))
  have h := signedEndpointProfile_inner_translate D 0
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (signedEndpointProfileVector D)
  change _ = ((‖signedEndpointProfileVector D‖ : ℝ) : ℂ) ^ (2 : ℕ) at hself
  rw [← Complex.ofReal_pow] at hself
  rw [hT, hself, signedEndpointProfile_overlap le_rfl hD] at h
  rw [norm_primeWindowModulate, Complex.ofReal_injective h]
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, sub_zero, Real.exp_neg, one_div]
  ring

private theorem phase_log_nat (y : ℝ) {n : ℕ} (hn : 0 < n) :
    primeWindowPhase y (log (n : ℝ)) = (n : ℂ) ^ (Complex.I * (y : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [primeWindowPhase, Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  ring

-- The adjoint term contributes the complex conjugate, including when `a = 0`.
private theorem shiftForm_endpoint (D y t : ℝ) (a : ℂ) :
    primeWindowShiftForm t a (primeWindowModulate y (signedEndpointProfileVector D)) =
      (↑(2 * (a * primeWindowPhase y t).re *
        (∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + t)) : ℝ) : ℂ) := by
  let v := signedEndpointProfileVector D
  have hb : ⟪v, primeWindowTranslate (-t) v⟫_ℂ = conj ⟪v, primeWindowTranslate t v⟫_ℂ := by
    rw [primeWindowTranslate_adjoint (-t), neg_neg, inner_conj_symm]
  rw [primeWindowShiftForm_modulate, primeWindowShiftForm, hb, ← map_mul, Complex.add_conj,
    signedEndpointProfile_inner_translate]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private theorem overlap_div_sqrt {D : ℝ} {n : ℕ} (hn : n ∈ cut D) :
    (∫ x, signedEndpointProfile D x * signedEndpointProfile D (x + log (n : ℝ))) / sqrt (n : ℝ) =
      2 * (1 - (n : ℝ) / exp D) / n + log (exp D / n) * (1 + 1 / (n : ℝ)) / exp (D / 2) := by
  obtain ⟨hn₁, hnX⟩ := Finset.mem_Ico.mp hn
  have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hn₀ := zero_lt_one.trans_le hn₁'
  have ht := Real.log_nonneg hn₁'
  have htD := (Real.log_lt_iff_lt_exp hn₀).mpr (Nat.lt_ceil.mp hnX)
  have hroot : exp (log (n : ℝ) / 2) = sqrt (n : ℝ) := by
    rw [Real.exp_half, Real.exp_log hn₀]
  have htX : exp (-(D - log (n : ℝ))) = (n : ℝ) / exp D := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hn₀]
  have hlen : D - log (n : ℝ) = log (exp D / n) := by
    rw [Real.log_div (Real.exp_ne_zero _) hn₀.ne', Real.log_exp]
  have hsame : (sqrt (n : ℝ))⁻¹ / sqrt (n : ℝ) = 1 / (n : ℝ) := by
    rw [div_eq_mul_inv, ← mul_inv, ← pow_two, Real.sq_sqrt hn₀.le, one_div]
  have hcross : (sqrt (n : ℝ) + (sqrt (n : ℝ))⁻¹) / sqrt (n : ℝ) = 1 + 1 / (n : ℝ) := by
    rw [add_div, div_self (Real.sqrt_pos.mpr hn₀).ne', hsame]
  rw [signedEndpointProfile_overlap ht htD.le, htX, hlen,
    show -log (n : ℝ) / 2 = -(log (n : ℝ) / 2) by ring, Real.exp_neg, hroot]
  calc
    _ = 2 * (1 - (n : ℝ) / exp D) * ((sqrt (n : ℝ))⁻¹ / sqrt (n : ℝ)) +
        log (exp D / n) / exp (D / 2) *
          ((sqrt (n : ℝ) + (sqrt (n : ℝ))⁻¹) / sqrt (n : ℝ)) := by ring
    _ = _ := by rw [hsame, hcross]; ring

private theorem neg_character_signedForm_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (D : ℝ) (u : 𝓗) :
    -primeWindowSignedForm D (fun i : ↥((cut D).filter Nat.Prime) ↦ (i : ℕ))
      (fun i ↦ χ ((i : ℕ) : ZMod q)) u =
        ∑ n ∈ cut D, (↑(Λ n / sqrt (n : ℝ)) : ℂ) *
          primeWindowShiftForm (log (n : ℝ)) (χ (n : ZMod q)) u := by
  rw [primeWindowSignedForm, neg_neg]
  simpa only [primeWindowPowerWeight, Nat.cast_pow, map_pow] using
    (sum_primePowers D fun n ↦ primeWindowShiftForm (log (n : ℝ)) (χ (n : ZMod q)) u)

/-- The exact fixed-diameter prime quotient on `exp(I*y*x) w(x)`.
`Finset.Ico 1 ⌈X⌉₊` is the strict cutoff `1 ≤ n < X`. The left side is the
positive translation part, i.e. minus the existing negative Weil prime form.
This holds for every character, including vanishing coefficients at primes
not coprime to the level; no primitivity or nonprincipality is needed for the
identity. -/
public theorem signedEndpointProfile_quotient {q : ℕ} (χ : DirichletCharacter ℂ q)
    {D : ℝ} (hD : 0 < D) (y : ℝ) :
    let X := exp D
    let E := exp (D / 2)
    let N := 2 * (1 - 1 / X) + 2 * D / E
    let u := primeWindowModulate y (signedEndpointProfileVector D)
    (-primeWindowSignedForm D (fun i : ↥((Finset.Ico 1 ⌈X⌉₊).filter Nat.Prime) ↦ (i : ℕ))
      (fun i ↦ χ ((i : ℕ) : ZMod q)) u).re / ‖u‖ ^ 2 =
        2 / N * ∑ n ∈ Finset.Ico 1 ⌈X⌉₊,
          Λ n * (χ (n : ZMod q) * (n : ℂ) ^ (Complex.I * (y : ℂ))).re *
            (2 * (1 - (n : ℝ) / X) / n + log (X / n) * (1 + 1 / (n : ℝ)) / E) := by
  dsimp only
  rw [neg_character_signedForm_eq_sum, Complex.re_sum, signedEndpointProfile_norm_sq hD.le,
    Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn₀ : 0 < n := (Finset.mem_Ico.mp hn).1
  rw [shiftForm_endpoint, phase_log_nat y hn₀, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← overlap_div_sqrt hn]
  ring

end Masullo
