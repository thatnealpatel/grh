module

public import Theorems.RationalAdeleBoxThetaInversion
import Lemmas.RationalIdeleReal
import Mathlib.Analysis.PSeries

/-! # Absolute tail estimates for samples of rational adelic boxes -/

open NumberField IsDedekindDomain Set
open scoped SchwartzMap FourierTransform ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "ι" => algebraMap ℚ A
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

private theorem norm_pos (k : J) : 0 < ideleNorm k :=
  ideleClassNorm_mk k ▸ ideleClassNorm_pos (QuotientGroup.mk k)

private theorem exists_clear_finite_denominators (a : A) :
    ∃ D : ℕ, 0 < D ∧ (D : A) * a ∈ rationalIntegralAdeles := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integral a
  have hmul : (q.den : A) * ι q = (q.num : A) := by
    simpa only [map_natCast, map_mul, map_intCast] using congrArg ι q.den_mul_eq_num
  refine ⟨q.den, q.den_pos, ?_⟩
  have h := rationalIntegralAdeles.add_mem (rationalIntegralAdeles.nsmul_mem hq q.den)
    (intCast_mem_rationalIntegralAdeles q.num)
  simpa only [nsmul_eq_mul, mul_sub, hmul, sub_add_cancel] using h

private theorem real_mul_sub (x y a : A) :
    rationalAdeleReal (x * y - a) = rationalAdeleReal x * rationalAdeleReal y - rationalAdeleReal a := by
  simp only [rationalAdeleReal_apply]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  exact (map_sub e _ _).trans (congrArg (· - e (a.1 Rat.infinitePlace)) (map_mul e _ _))

private theorem schwartz_tail_term (b : 𝓢(ℝ, ℂ)) (m : ℕ) {x u : ℝ} {n : ℤ}
    (hu : 1 ≤ u) (hx : 2 * |x| ≤ u) (hn : n ≠ 0) :
    ‖b (u * n - x)‖ ≤ (SchwartzMap.seminorm ℝ (m + 2) 0 b + 1) * 2 ^ (m + 2) /
      (u ^ m * |(n : ℝ)| ^ 2) := by
  have hn₁ : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hun : u ≤ u * |(n : ℝ)| := le_mul_of_one_le_right (by positivity) hn₁
  have hnu : |(n : ℝ)| ≤ u * |(n : ℝ)| := le_mul_of_one_le_left (abs_nonneg _) hu
  have harg : u * |(n : ℝ)| ≤ 2 * |u * n - x| := by
    have h := abs_add_le (u * n - x) x
    rw [sub_add_cancel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ u)] at h
    linarith
  have hp : u ^ m * |(n : ℝ)| ^ 2 ≤ (2 * |u * n - x|) ^ (m + 2) := by
    rw [pow_add]
    gcongr
    · exact hun.trans harg
    · exact hnu.trans harg
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ ‖b (u * n - x)‖ * (2 * |u * n - x|) ^ (m + 2) := by gcongr
    _ = 2 ^ (m + 2) * (|(u * n - x)| ^ (m + 2) * ‖b (u * n - x)‖) := by rw [mul_pow]; ring
    _ ≤ 2 ^ (m + 2) * (SchwartzMap.seminorm ℝ (m + 2) 0 b + 1) := by
      gcongr
      have h := b.le_seminorm ℝ (m + 2) 0 (u * n - x)
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_zero] at h
      linarith
    _ = _ := mul_comm _ _

/-- Normalize the dilation at the finite places. All surviving nonzero indices
in the normalized orbit lie in `(1/D)ℤ`, where `D` depends only on the center
in box coordinates. Transport the integer majorant back to the original orbit. -/
private theorem exists_box_tail_majorant (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (m : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      (∃ u : ℚˣ → ℝ, Summable u ∧ (∀ q, ‖rationalAdeleBox b a g (ιˣ q * k : J)‖ ≤ u q) ∧
        (∑' q, u q) ≤ C / ideleNorm k ^ m) := by
  classical
  let a' : A := (↑g⁻¹ : A) * a
  obtain ⟨D, hD, ha⟩ := exists_clear_finite_denominators a'
  let L : ℝ := ideleNorm g * D
  let x := rationalAdeleReal a'
  have hL : 0 < L := mul_pos (norm_pos g) (Nat.cast_pos.mpr hD)
  let B : ℝ := (SchwartzMap.seminorm ℝ (m + 2) 0 b + 1) * 2 ^ (m + 2) * L ^ m
  have hB : 0 < B := by
    have : 0 ≤ SchwartzMap.seminorm ℝ (m + 2) 0 b := apply_nonneg _ _
    dsimp [B]
    positivity
  let ρ : ℤ → ℝ := fun n ↦ |(n : ℝ)| ^ (-(2 : ℝ))
  have hρ : Summable ρ := Real.summable_abs_int_rpow one_lt_two
  let T := max 1 (L * max 1 (2 * |x|))
  refine ⟨B * (∑' n, ρ n) + 1, T, ?_, le_max_left .., fun k hk ↦ ?_⟩
  · have : 0 ≤ ∑' n, ρ n := tsum_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
    positivity
  let t := ideleNorm k / L
  have ht : max 1 (2 * |x|) ≤ t := (le_div_iff₀ hL).2 (by
    rw [mul_comm]; exact (le_max_right ..).trans hk)
  obtain ⟨r, hr, hf⟩ := exists_rational_principal_mul_norm_section (g⁻¹ * k)
  let h := ιˣ r * (g⁻¹ * k)
  have hreal : rationalAdeleReal (h : A) = ideleNorm k / ideleNorm g := by
    calc
      rationalAdeleReal (h : A) = rationalIdeleReal h := by
        rw [rationalAdeleReal_apply, rationalIdeleReal]
      _ = _ := by rw [show rationalIdeleReal h = _ from hr, map_mul, map_inv, div_eq_inv_mul]
  have hsample (q : ℚˣ) :
      rationalAdeleBox b a g (ιˣ (q * r) * k : J) = rationalAdeleUnramified b ((h : A) * ι (q : ℚ) - a') := by
    unfold rationalAdeleBox
    congr 1
    simp only [a', h, map_mul, Units.val_mul, mul_sub]
    change (↑g⁻¹ : A) * (ι (q : ℚ) * ↑(ιˣ r) * ↑k) - (↑g⁻¹ : A) * a = _
    ring
  -- Extend the integer p-series bound by zero off the lattice.
  let j : ℤ → ℚ := Int.cast
  have hj : Function.Injective j := Int.cast_injective
  let v : ℚ → ℝ := fun Q ↦ if Q ∈ range j then (B / ideleNorm k ^ m) * ρ (Function.invFun j Q) else 0
  have hvj (n : ℤ) : v (j n) = (B / ideleNorm k ^ m) * ρ n := by
    simp only [v, mem_range_self, ite_true, Function.leftInverse_invFun hj n]
  have hv0 (Q : ℚ) : 0 ≤ v Q := by
    have := norm_pos k
    dsimp only [v]
    split_ifs
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)
    · rfl
  have hvzero (Q : ℚ) (hQ : Q ∉ range j) : v Q = 0 := ite_eq_right hQ
  have hv : Summable v := (hj.summable_iff hvzero).1 (by
    change Summable (fun n ↦ v (j n))
    simp only [hvj]
    exact hρ.mul_left _)
  let e : ℚˣ ≃ ℚˣ := Equiv.mulRight r⁻¹
  let idx : ℚˣ → ℚ := fun q ↦ D * (e q : ℚ)
  have hi : Function.Injective idx := fun _ _ he ↦
    e.injective (Units.val_injective (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hD.ne') he))
  refine ⟨v ∘ idx, hv.comp_injective hi, fun q ↦ ?_, ?_⟩
  · let Q : ℚ := (e q : ℚ)
    have heq : e q * r = q := by simp [e]
    have hsamp := hsample (e q)
    rw [heq] at hsamp
    rw [hsamp, rationalAdeleUnramified]
    change ‖Set.indicator rationalIntegralAdeles (fun y : A ↦ b (rationalAdeleReal y))
      ((h : A) * ι Q - a')‖ ≤ v (D * Q)
    by_cases hs : (h : A) * ι Q - a' ∈ rationalIntegralAdeles
    · rw [indicator_of_mem hs]
      -- Clear the center denominator and cancel the finite units of `h`.
      have hprod : (h : A) * ι (D * Q) ∈ rationalIntegralAdeles := by
        have hsum := rationalIntegralAdeles.add_mem (rationalIntegralAdeles.nsmul_mem hs D) ha
        convert hsum using 1
        simp only [nsmul_eq_mul, map_mul, map_natCast]
        ring
      have hdiag : ι (D * Q) ∈ rationalIntegralAdeles := by
        intro p
        have hp := hprod p
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hp ⊢
        change Valued.v ((h : A).2 p * (ι (D * Q)).2 p) ≤ 1 at hp
        have hh : Valued.v ((h : A).2 p) = 1 := hf p
        rwa [map_mul, hh, one_mul] at hp
      obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff _).1 hdiag
      have hn0 : n ≠ 0 := by
        intro hzero
        rw [hzero, Int.cast_zero, mul_eq_zero] at hn
        exact hn.elim (Nat.cast_ne_zero.mpr hD.ne') (e q).ne_zero
      have hcast : (D : ℝ) * (Q : ℝ) = (n : ℝ) := by exact_mod_cast hn
      have harg : rationalAdeleReal ((h : A) * ι Q - a') = t * (n : ℝ) - x := by
        rw [real_mul_sub, hreal, rationalAdeleReal_algebraMap, ← hcast]
        dsimp [t, L, x]
        have hg := (norm_pos g).ne'
        have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
        field_simp
      rw [harg, hn, hvj]
      apply (schwartz_tail_term b m ((le_max_left ..).trans ht) ((le_max_right ..).trans ht) hn0).trans_eq
      have hk' := (norm_pos k).ne'
      have hn' : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn0)
      dsimp only [B, ρ, t]
      rw [Real.rpow_neg (abs_nonneg _) 2, Real.rpow_two, div_pow]
      field_simp
    · rw [indicator_of_notMem hs, norm_zero]
      exact hv0 _
  · calc
      _ ≤ ∑' Q, v Q :=
        Summable.tsum_le_tsum_of_inj idx hi (fun Q _ ↦ hv0 Q) (fun _ ↦ le_rfl)
          (hv.comp_injective hi) hv
      _ = ∑' n, (B / ideleNorm k ^ m) * ρ n := by
        rw [← hj.tsum_eq (f := v) (fun Q hQ ↦ by
          by_contra hQr
          exact hQ (hvzero Q hQr))]
        exact tsum_congr hvj
      _ ≤ _ := by
        rw [tsum_mul_left, div_mul_eq_mul_div]
        have := norm_pos k
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-- A finite envelope of boxes bounds the absolute orbit series at large norm. -/
private theorem exists_tail_of_box_envelope {I : Type*} (s : Finset I) (w : I → ℝ)
    (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J) (f : A → ℂ) (m : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ y, ‖f y‖ ≤ ∑ i ∈ s, w i * ‖rationalAdeleBox (b i) (a i) (g i) y‖) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖f (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖f (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  classical
  choose C T hC hT h using fun i ↦ exists_box_tail_majorant (b i) (a i) (g i) m
  have hC₀ : 0 ≤ ∑ i ∈ s, w i * C i := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (hC i).le
  have hT₀ : 0 ≤ ∑ i ∈ s, T i := Finset.sum_nonneg fun i _ ↦ zero_le_one.trans (hT i)
  refine ⟨(∑ i ∈ s, w i * C i) + 1, (∑ i ∈ s, T i) + 1, by positivity, by linarith, ?_⟩
  intro k hk
  have hbox (i : I) (hi : i ∈ s) :
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleBox (b i) (a i) (g i) (ιˣ q * k : J)‖) ∧
        (∑' q : ℚˣ, ‖rationalAdeleBox (b i) (a i) (g i) (ιˣ q * k : J)‖) ≤ C i / ideleNorm k ^ m := by
    have hle : T i ≤ ∑ j ∈ s, T j := Finset.single_le_sum (fun j _ ↦ zero_le_one.trans (hT j)) hi
    obtain ⟨u, hu, hub, hsum⟩ := h i k (by linarith)
    have hs := hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hub
    exact ⟨hs, (hs.tsum_le_tsum hub hu).trans hsum⟩
  let v (i : I) (q : ℚˣ) := w i * ‖rationalAdeleBox (b i) (a i) (g i) (ιˣ q * k : J)‖
  have hv (i : I) (hi : i ∈ s) : Summable (v i) := (hbox i hi).1.mul_left _
  have hs : Summable (fun q ↦ ∑ i ∈ s, v i q) := summable_sum hv
  have hsf := hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦ hf (ιˣ q * k : J))
  refine ⟨hsf, ?_⟩
  calc
    _ ≤ ∑' q, ∑ i ∈ s, v i q := hsf.tsum_le_tsum (fun q ↦ hf (ιˣ q * k : J)) hs
    _ = ∑ i ∈ s, w i * ∑' q : ℚˣ, ‖rationalAdeleBox (b i) (a i) (g i) (ιˣ q * k : J)‖ := by
      rw [Summable.tsum_finsetSum hv]
      simp only [v, tsum_mul_left]
    _ ≤ ∑ i ∈ s, (w i * C i) / ideleNorm k ^ m := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hbox i hi).2 (hw i)
    _ ≤ _ := by
      rw [← Finset.sum_div]
      have := norm_pos k
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- The sum of absolute spatial samples has rapid decay at large idelic norm. -/
public theorem rationalAdeleBoxSum_absolute_theta_tail (m : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖f (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖f (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  apply exists_tail_of_box_envelope s (fun i ↦ ‖c i‖) b a g f m (fun _ ↦ norm_nonneg _)
  intro y
  simp only [rationalAdeleBoxSum, ← norm_mul]
  exact norm_sum_le _ _

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

/-- The sum of absolute Fourier samples has rapid decay at large idelic norm.
The unit-modulus translation phases leave an envelope of centered dual boxes. -/
public theorem rationalAdeleBoxSum_absolute_fourier_theta_tail (m : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleFourier f (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleFourier f (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  apply exists_tail_of_box_envelope s (fun i ↦ ‖c i‖ * ideleNorm (g i))
    (fun i ↦ 𝓕 (b i)) 0 (fun i ↦ (g i)⁻¹) (rationalAdeleFourier f) m
    (fun i ↦ mul_nonneg (norm_nonneg _) (norm_pos (g i)).le)
  intro y
  rw [rationalAdeleFourier, integral_rationalAdeleBoxSum_mul_conj_char]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_mul, norm_smul, Real.norm_of_nonneg (norm_pos (g i)).le, norm_mul,
    Complex.norm_conj, norm_rationalAdeleAddChar, one_mul, ← mul_assoc,
    rationalAdeleBox, inv_inv, Pi.zero_apply, sub_zero]

end Masullo
