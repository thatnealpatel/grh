module

public import Lemmas.RationalLocalLogPairTransport
public import Lemmas.RationalLocalShiftedTest
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The shifted finite-place Fourier pairing over the rationals

Lemma B.4.4.3, (B.4.4.5), p. 620, compares the finite-place principal
value with the ordinary multiplicative Haar integral on tests vanishing
at one. Its proof, (B.4.4.7)–(8), p. 621, applies the restriction of the
logarithmic Fourier distribution to the translated test and changes
variables by `y = 1 + x`. In Lean `rationalLocalShiftedTest_properties`
checks the required additive test conditions, including extension across
`x = -1`; `rationalLocalLogFourier_off_zero` supplies the restriction by
transporting the direct rational ball computation, rather than assuming
(B.4.3.5). The final conversion uses the independently proved (A.3.2.3)
in Bochner form. Locators follow pinned text extraction.
-/

open Function NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "P[" v "]" => (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℝ)
local notation "ν[" v "]" => rationalLocalFieldAddHaar v

/-- Rational case of (B.4.4.5). The two integrands are absolutely integrable,
and the sign is the unit-mass case of (B.4.4.1), not the canonical modulated
Haar normalization of (B.4.4.3). -/
public theorem rationalLocalShifted_log_fourier (v : V) [MeasurableSpace (K[v]ˣ)]
    [BorelSpace (K[v]ˣ)] (f : K[v]ˣ → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (h₁ : f 1 = 0) :
    let F := rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v f)
    let H (y : K[v]ˣ) := f y * (↑(Real.sqrt ‖(y : K[v])‖) : ℂ) / (↑‖1 - (y : K[v])‖ : ℂ)
    Integrable F ν[v] ∧ Integrable H (rationalLocalMultiplicativeHaar v) ∧
      -(∫ ξ, F ξ ∂ν[v]) = ∫ y, H y ∂rationalLocalMultiplicativeHaar v := by
  let u := rationalLocalShiftedTest v f
  let H (y : K[v]ˣ) := f y * (↑(Real.sqrt ‖(y : K[v])‖) : ℂ) / (↑‖1 - (y : K[v])‖ : ℂ)
  let j : K[v]ˣ → K[v] := Units.val
  let H₀ := Function.extend j H (fun _ ↦ 0)
  obtain ⟨hu, hcu, hu₀⟩ := rationalLocalShiftedTest_properties v hf hc
  -- (B.4.4.7)–(8): The translated test vanishes at zero, so there is no
  -- contact term in the logarithmic pairing.
  obtain ⟨hF, hG, hpair⟩ := rationalLocalLogFourier_off_zero v hu hcu (hu₀.trans h₁)
  have h₀ : ¬∃ y, j y = 0 := fun ⟨y, hy⟩ ↦ y.ne_zero hy
  -- Translate the additive integral, then recognize the inverse-norm density.
  have hA (y : K[v]) : u (y - 1) / (↑‖y - 1‖ : ℂ) = H₀ y / (↑‖y‖ : ℂ) := by
    have hshift : 1 + (y - 1) = y := by ring
    change Function.extend j _ (fun _ ↦ 0) (1 + (y - 1)) / _ = _
    rw [hshift]
    by_cases hy : y = 0
    · rw [hy, Function.extend_apply' _ _ _ h₀]
      simp
    · let z := Units.mk0 y hy
      have hz : j z = y := rfl
      rw [← hz, Units.val_injective.extend_apply]
      unfold H₀
      rw [Units.val_injective.extend_apply]
      change f z / (↑(Real.sqrt ‖y‖) : ℂ) / (↑‖y - 1‖ : ℂ) = H z / (↑‖y‖ : ℂ)
      have hs : (↑(Real.sqrt ‖y‖) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)).ne'
      by_cases h : y = 1
      · simp [H, z, h]
      · have hd : (↑‖y - 1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
        have hs₂ : (↑(Real.sqrt ‖y‖) : ℂ) ^ 2 = (↑‖y‖ : ℂ) := by
          exact_mod_cast Real.sq_sqrt (norm_nonneg y)
        change _ = (f z * (↑(Real.sqrt ‖y‖) : ℂ) / (↑‖1 - y‖ : ℂ)) / (↑‖y‖ : ℂ)
        rw [norm_sub_rev (1 : K[v]) y, ← hs₂]
        field_simp
  let a : K[v] ≃ₜ K[v] := Homeomorph.addLeft 1
  have ha : MeasurePreserving a ν[v] ν[v] := measurePreserving_add_left _ _
  have htranslate : (fun x ↦ u x / (↑‖x‖ : ℂ)) = (fun y ↦ H₀ y / (↑‖y‖ : ℂ)) ∘ a := by
    funext x
    simpa [a, add_comm (1 : K[v]) x] using hA (1 + x)
  rw [htranslate] at hG hpair
  have ht := (ha.integrable_comp_emb a.measurableEmbedding).mp hG
  have hpaired := hpair.trans
    (congrArg (fun I : ℂ ↦ -((↑(1 - P[v]⁻¹) : ℂ)⁻¹) * I)
      (ha.integral_comp a.measurableEmbedding (fun y ↦ H₀ y / (↑‖y‖ : ℂ))))
  obtain ⟨hH, hHaar⟩ := rationalLocalHaar_integral_density v H₀ ht
  have hval (z : K[v]ˣ) : H₀ z = H z := Units.val_injective.extend_apply _ _ z
  simp_rw [hval] at hH hHaar
  refine ⟨hF, hH, ?_⟩
  exact (congrArg Neg.neg hpaired).trans (by rw [neg_mul, neg_neg, hHaar])

end Masullo
