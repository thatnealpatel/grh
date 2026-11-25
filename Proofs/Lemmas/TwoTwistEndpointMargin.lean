module

public import Lemmas.EndpointGammaQuotient
public import Lemmas.PrimeRampReplacement
public import Lemmas.SignedEndpointRamp

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

/-! # Finite two-twist endpoint margin at height zero

Source: `2e2ceda6749e:.godel/bob/power-radius-endpoint.md`, lines 23–27.
Selection pin: `082a89e67352a18e3f534bc75a2d45807b145771`.
Owning check session: `01a2102d-ae00-70d1-a793-4b136b9edf79`.

This is the finite transfer from a common prime-ramp product-mean margin to the
actual unmodulated quotients, each at its own diameter and conductor. The
arithmetic margin is an input; there is no assertion about its availability,
about modulated tests, or about a uniform power radius.
-/

open Real (exp log)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

/-- The normalized endpoint form at height zero: log conductor, the Gamma
quotient of the character's parity, and the signed prime form divided by the
squared norm of the same test. The prime cutoff is strictly below `exp D`. -/
@[expose] public noncomputable def heightZeroEndpointQuotient {c : ℕ}
    (χ : DirichletCharacter ℂ c) (D : ℝ) : ℝ := by
  classical
  let P := (Finset.Ico 1 ⌈exp D⌉₊).filter Nat.Prime
  let u := primeWindowModulate 0 (signedEndpointProfileVector D)
  exact log (χ.conductor : ℝ) + signedEndpointGammaQuotient D 0 (if χ.Even then 0 else 1) +
    (primeWindowSignedForm D (fun p : ↥P ↦ (p : ℕ)) (fun p ↦ χ ((p : ℕ) : ZMod c)) u).re /
      ‖u‖ ^ 2

/-- The finite prime ramp with weights `log p * log (X / p) / X` for `p < X`. -/
@[expose] public noncomputable def heightZeroPrimeRampMean (X : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (primeRampSupport X).filter Nat.Prime, (log (p : ℝ) * log (X / p) / X) * f p

/-- One-sided transfer cost in units of `E = exp (D / 2)`. The terms pay for
the prime-form to log-ramp replacement and the Gamma quotient (retaining its
`log 2` main term), then for changing cutoff and discarding higher prime
powers at the common cutoff. -/
@[expose] public noncomputable def heightZeroEndpointMarginError (Cprime Cgamma X D : ℝ) : ℝ :=
  (Cprime * (1 + D) + Cgamma - log 2) / exp (D / 2) +
    3 * (log 4 + 4) * |log (exp D / X)| +
    (log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3)

private theorem primeRampSupport_eq_Ico (X : ℝ) : primeRampSupport X = Finset.Ico 1 ⌈X⌉₊ := by
  ext n
  rw [mem_primeRampSupport, Finset.mem_Ico, Nat.lt_ceil]

private noncomputable def endpointVonMangoldtRamp (X : ℝ) (z : ℕ → ℂ) : ℂ :=
  ∑ n ∈ primeRampSupport X, (vonMangoldtRampWeight X n : ℂ) * z n

private theorem re_sub_le_of_norm_sub_le {a b : ℂ} {r : ℝ} (h : ‖a - b‖ ≤ r) :
    a.re - b.re ≤ r :=
  le_of_abs_le (by simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (a - b)).trans h)

private theorem endpointVonMangoldtRamp_cutoff_prime_le {X Y : ℝ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) {z : ℕ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1) :
    (endpointVonMangoldtRamp Y z).re - heightZeroPrimeRampMean X (fun p ↦ (z p).re) ≤
      3 * (log 4 + 4) * |log (Y / X)| +
        (log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3) := by
  have hX₀ := zero_lt_one.trans_le hX
  have hY₀ := zero_lt_one.trans_le hY
  have hK : 0 ≤ 3 * (log 4 + 4) := by positivity
  have hcut : ‖endpointVonMangoldtRamp Y z - endpointVonMangoldtRamp X z‖ ≤
      3 * (log 4 + 4) * |log (Y / X)| := by
    rcases le_total X Y with hXY | hYX
    · have h := vonMangoldtRamp_twist_cutoff_le hX hXY hz
      rw [one_mul] at h
      exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hK)
    · rw [norm_sub_rev]
      have h := vonMangoldtRamp_twist_cutoff_le hY hYX hz
      rw [one_mul] at h
      refine h.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans_eq ?_) hK)
      rw [Real.log_div hY₀.ne' hX₀.ne', Real.log_div hX₀.ne' hY₀.ne', abs_sub_comm]
  have hprime := vonMangoldtRamp_twist_prime_le hX hz
  rw [one_mul] at hprime
  have hp : (endpointVonMangoldtRamp X z).re - heightZeroPrimeRampMean X (fun p ↦ (z p).re) ≤
      (log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3) := by
    simpa only [endpointVonMangoldtRamp, heightZeroPrimeRampMean, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using re_sub_le_of_norm_sub_le hprime
  linarith only [re_sub_le_of_norm_sub_le hcut, hp]

private theorem heightZeroEndpointQuotient_lower :
    ∃ Cprime Cgamma : ℝ, 0 < Cprime ∧ 0 < Cgamma ∧
      ∀ {c : ℕ} (χ : DirichletCharacter ℂ c) {A X D : ℝ}, 0 < A → 1 ≤ X → 1 ≤ D →
        exp (D / 2) = A * log (χ.conductor : ℝ) →
        1 / A - heightZeroPrimeRampMean X (fun p ↦ (χ (p : ZMod c)).re) -
          heightZeroEndpointMarginError Cprime Cgamma X D ≤
          heightZeroEndpointQuotient χ D / exp (D / 2) := by
  obtain ⟨Cprime, hCprime, hRamp⟩ := signedEndpointProfile_quotient_logRamp
  obtain ⟨Cgamma, hCgamma, hGamma⟩ := signedEndpointGammaQuotient_uniform
  refine ⟨Cprime, Cgamma, hCprime, hCgamma, ?_⟩
  intro c χ A X D hA hX hD hscale
  classical
  let E := exp (D / 2)
  let z (n : ℕ) := χ (n : ZMod c)
  let P := (Finset.Ico 1 ⌈exp D⌉₊).filter Nat.Prime
  let u := primeWindowModulate 0 (signedEndpointProfileVector D)
  let T := (-primeWindowSignedForm D (fun p : ↥P ↦ (p : ℕ)) (fun p ↦ z p) u).re / ‖u‖ ^ 2
  let κ : Fin 2 := if χ.Even then 0 else 1
  -- The ramp estimate is for minus the signed prime form; the full quotient adds it back with the opposite sign.
  have hQ : heightZeroEndpointQuotient χ D =
      log (χ.conductor : ℝ) + signedEndpointGammaQuotient D 0 κ - T := by
    unfold heightZeroEndpointQuotient T
    rw [Complex.neg_re, neg_div, sub_neg_eq_add]
  have hE : 0 < E := Real.exp_pos _
  have hconst : (1 / A) * E = log (χ.conductor : ℝ) := by
    change (1 / A) * exp (D / 2) = _
    rw [hscale]
    field_simp [hA.ne']
  have hY : 1 ≤ exp D := Real.one_le_exp (zero_le_one.trans hD)
  have hz (n : ℕ) : ‖z n‖ ≤ 1 := χ.norm_le_one _
  have htransfer := mul_le_mul_of_nonneg_left (endpointVonMangoldtRamp_cutoff_prime_le hX hY hz) hE.le
  -- At height zero the phase is one, and the ramp estimate is at this endpoint's own cutoff.
  have hr := hRamp χ hD 0
  dsimp only at hr
  simp only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one] at hr
  change |T - E * _| ≤ _ at hr
  have hMean : (endpointVonMangoldtRamp (exp D) z).re =
      (exp D)⁻¹ * ∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n * (z n).re * log (exp D / n) := by
    unfold endpointVonMangoldtRamp
    rw [vonMangoldtRamp_twist_re_eq, primeRampSupport_eq_Ico]
  rw [← hMean] at hr
  have hg := (hGamma D 0 κ hD).2
  simp only [abs_zero, add_zero] at hg
  have hg₀ : log 2 - Cgamma ≤ signedEndpointGammaQuotient D 0 κ := by
    linarith only [(abs_le.mp hg).1]
  apply (le_div_iff₀ hE).mpr
  rw [sub_mul, sub_mul, hconst, hQ]
  have herr : heightZeroEndpointMarginError Cprime Cgamma X D * E =
      Cprime * (1 + D) + Cgamma - log 2 +
        E * (3 * (log 4 + 4) * |log (exp D / X)| +
          (log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3)) := by
    unfold heightZeroEndpointMarginError
    rw [add_mul, add_mul, div_mul_cancel₀ _ hE.ne']
    ring
  rw [herr]
  change log (χ.conductor : ℝ) - heightZeroPrimeRampMean X (fun p ↦ (z p).re) * E - _ ≤ _
  linarith only [(abs_le.mp hr).2, htransfer, hg₀]

private theorem abs_add_le_one_add_mul {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a + b| ≤ 1 + a * b := by
  obtain ⟨haLow, haHigh⟩ := abs_le.mp ha
  obtain ⟨hbLow, hbHigh⟩ := abs_le.mp hb
  have hup := mul_nonneg (sub_nonneg.mpr haHigh) (sub_nonneg.mpr hbHigh)
  have hdown : 0 ≤ (1 + a) * (1 + b) := mul_nonneg (by linarith only [haLow]) (by linarith only [hbLow])
  exact abs_le.mpr ⟨by linarith only [hdown], by linarith only [hup]⟩

private theorem twoTwist_primeRampMean_le {q c₁ c₂ : ℕ} (ξ : DirichletCharacter ℂ q)
    (χ₁ : DirichletCharacter ℂ c₁) (χ₂ : DirichletCharacter ℂ c₂) {f₁ f₂ : ℕ → ℝ}
    (hf₁ : ∀ p, p.Prime → |f₁ p| ≤ 1) (hf₂ : ∀ p, p.Prime → |f₂ p| ≤ 1)
    (hχ₁ : ∀ p : ℕ, p.Prime → χ₁ (p : ZMod c₁) = ξ (p : ZMod q) * (f₁ p : ℂ))
    (hχ₂ : ∀ p : ℕ, p.Prime → χ₂ (p : ZMod c₂) = ξ (p : ZMod q) * (f₂ p : ℂ))
    {X : ℝ} (hX : 1 ≤ X) :
    heightZeroPrimeRampMean X (fun p ↦ (χ₁ (p : ZMod c₁)).re) +
      heightZeroPrimeRampMean X (fun p ↦ (χ₂ (p : ZMod c₂)).re) ≤
    heightZeroPrimeRampMean X (fun _ ↦ 1) + heightZeroPrimeRampMean X (fun p ↦ f₁ p * f₂ p) := by
  simp only [heightZeroPrimeRampMean, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  obtain ⟨hpX, hpPrime⟩ := Finset.mem_filter.mp hp
  have hp_lt := (mem_primeRampSupport.mp hpX).2
  have hp₁ : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
  have hp₀ := zero_lt_one.trans hp₁
  have hw : 0 < log (p : ℝ) * log (X / p) / X :=
    div_pos (mul_pos (Real.log_pos hp₁) (Real.log_pos ((one_lt_div hp₀).mpr hp_lt)))
      (zero_lt_one.trans_le hX)
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hw.le
  rw [hχ₁ p hpPrime, hχ₂ p hpPrime]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← mul_add]
  calc
    _ ≤ |(ξ (p : ZMod q)).re * (f₁ p + f₂ p)| := le_abs_self _
    _ ≤ |f₁ p + f₂ p| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        ((Complex.abs_re_le_norm _).trans (ξ.norm_le_one _))
    _ ≤ _ := abs_add_le_one_add_mul (hf₁ p hpPrime) (hf₂ p hpPrime)

/-- If the prime mass plus the signed product mean at one common cutoff is
strictly below `2 / A` after paying both transfer costs, the actual height-zero
endpoint quotients cannot both be nonpositive. Each uses its own cutoff
`exp Dᵢ = (A * log cᵢ)^2`. Matching to the base is required only on primes;
the real factors may vanish there. -/
public theorem twoTwist_heightZeroEndpointQuotient_pos_of_margin :
    ∃ Cprime Cgamma : ℝ, 0 < Cprime ∧ 0 < Cgamma ∧
      ∀ {q c₁ c₂ : ℕ} (ξ : DirichletCharacter ℂ q)
        (χ₁ : DirichletCharacter ℂ c₁) (χ₂ : DirichletCharacter ℂ c₂),
        χ₁.IsPrimitive → χ₂.IsPrimitive →
        ∀ {f₁ f₂ : ℕ → ℝ},
          (∀ p, p.Prime → |f₁ p| ≤ 1) → (∀ p, p.Prime → |f₂ p| ≤ 1) →
          (∀ p : ℕ, p.Prime → χ₁ (p : ZMod c₁) = ξ (p : ZMod q) * (f₁ p : ℂ)) →
          (∀ p : ℕ, p.Prime → χ₂ (p : ZMod c₂) = ξ (p : ZMod q) * (f₂ p : ℂ)) →
          ∀ {A X D₁ D₂ : ℝ}, 0 < A → 1 ≤ X → 1 ≤ D₁ → 1 ≤ D₂ →
            exp (D₁ / 2) = A * log (c₁ : ℝ) → exp (D₂ / 2) = A * log (c₂ : ℝ) →
            heightZeroPrimeRampMean X (fun _ ↦ 1) +
                heightZeroPrimeRampMean X (fun p ↦ f₁ p * f₂ p) +
                heightZeroEndpointMarginError Cprime Cgamma X D₁ +
                heightZeroEndpointMarginError Cprime Cgamma X D₂ < 2 / A →
            0 < heightZeroEndpointQuotient χ₁ D₁ ∨ 0 < heightZeroEndpointQuotient χ₂ D₂ := by
  obtain ⟨Cprime, Cgamma, hCprime, hCgamma, hlower⟩ := heightZeroEndpointQuotient_lower
  refine ⟨Cprime, Cgamma, hCprime, hCgamma, ?_⟩
  intro q c₁ c₂ ξ χ₁ χ₂ hprim₁ hprim₂ f₁ f₂ hf₁ hf₂ hχ₁ hχ₂ A X D₁ D₂ hA hX hD₁ hD₂ hE₁ hE₂ hmargin
  have h₁ := hlower χ₁ hA hX hD₁ (by rwa [show χ₁.conductor = c₁ from hprim₁])
  have h₂ := hlower χ₂ hA hX hD₂ (by rwa [show χ₂.conductor = c₂ from hprim₂])
  have hsum := twoTwist_primeRampMean_le ξ χ₁ χ₂ hf₁ hf₂ hχ₁ hχ₂ hX
  by_contra! hnonpos
  have hq₁ := div_nonpos_of_nonpos_of_nonneg hnonpos.1 (Real.exp_pos (D₁ / 2)).le
  have hq₂ := div_nonpos_of_nonpos_of_nonneg hnonpos.2 (Real.exp_pos (D₂ / 2)).le
  rw [show (2 : ℝ) = 1 + 1 by norm_num, add_div] at hmargin
  linarith only [h₁, h₂, hq₁, hq₂, hsum, hmargin]

end Masullo
