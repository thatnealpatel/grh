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

private theorem real_mul_sub (x y a : A) :
    rationalAdeleReal (x * y - a) = rationalAdeleReal x * rationalAdeleReal y - rationalAdeleReal a := by
  simp only [rationalAdeleReal_apply]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  exact (map_sub e _ _).trans (congrArg (· - e (a.1 Rat.infinitePlace)) (map_mul e _ _))

private theorem schwartz_tail_term (b : 𝓢(ℝ, ℂ)) (m : ℕ) {x u L P : ℝ} {n : ℤ}
    (hu : 1 ≤ u) (hL : 0 < L) (hn : n ≠ 0)
    (h₀ : SchwartzMap.seminorm ℂ 0 0 b ≤ P) (hp : SchwartzMap.seminorm ℂ (m + 2) 0 b ≤ P) :
    ‖b (u / L * n - x)‖ ≤ P * (L * (1 + |x|)) ^ (m + 2) / (u ^ m * |(n : ℝ)| ^ 2) := by
  let y := u / L * (n : ℝ) - x
  let M := max 1 |y|
  have hn₁ : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hu₀ := zero_lt_one.trans_le hu
  have hM : 1 ≤ M := le_max_left ..
  have harg : u / L * |(n : ℝ)| ≤ (1 + |x|) * M := by
    have ht := abs_add_le y x
    rw [show y + x = u / L * (n : ℝ) by simp [y], abs_mul,
      abs_of_pos (div_pos hu₀ hL)] at ht
    calc
      _ ≤ |y| + |x| := ht
      _ ≤ M + |x| * M := add_le_add (le_max_right ..) (le_mul_of_one_le_right (abs_nonneg _) hM)
      _ = _ := by ring
  have hscale : u * |(n : ℝ)| ≤ L * (1 + |x|) * M := by
    calc
      _ = L * (u / L * |(n : ℝ)|) := by field_simp
      _ ≤ L * ((1 + |x|) * M) := mul_le_mul_of_nonneg_left harg hL.le
      _ = _ := by ring
  have hw : u ^ m * |(n : ℝ)| ^ 2 ≤ (L * (1 + |x|) * M) ^ (m + 2) := by
    rw [pow_add]
    gcongr
    · exact (le_mul_of_one_le_right hu₀.le hn₁).trans hscale
    · exact (le_mul_of_one_le_left (abs_nonneg _) hu).trans hscale
  have hb : M ^ (m + 2) * ‖b y‖ ≤ P := by
    by_cases h : |y| ≤ 1
    · simpa only [M, max_eq_left h, one_pow, one_mul] using
        (by simpa using (b.le_seminorm ℂ 0 0 y) : ‖b y‖ ≤ SchwartzMap.seminorm ℂ 0 0 b).trans h₀
    · rw [show M = |y| from max_eq_right (le_of_not_ge h)]
      exact (by simpa [Real.norm_eq_abs] using (b.le_seminorm ℂ (m + 2) 0 y) :
        |y| ^ (m + 2) * ‖b y‖ ≤ SchwartzMap.seminorm ℂ (m + 2) 0 b).trans hp
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ ‖b y‖ * (L * (1 + |x|) * M) ^ (m + 2) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = (L * (1 + |x|)) ^ (m + 2) * (M ^ (m + 2) * ‖b y‖) := by rw [mul_pow]; ring
    _ ≤ _ := by rw [mul_comm P]; gcongr

/-- Normalize the dilation at the finite places. All surviving nonzero indices
lie in `(1/D)ℤ`, where `D` depends only on the center in box coordinates.
Two uniformly bounded seminorms give a common absolute sum bound, including
at idelic norm one. -/
private theorem exists_box_tail_majorant {B : Set 𝓢(ℝ, ℂ)} (hB : Bornology.IsVonNBounded ℂ B)
    (a : A) (g : J) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ B, ∀ k : J, 1 ≤ ideleNorm k →
      ∃ u : ℚˣ → ℝ, Summable u ∧ (∀ q, ‖rationalAdeleBox b a g (ιˣ q * k : J)‖ ≤ u q) ∧
        (∑' q, u q) ≤ C / ideleNorm k ^ m := by
  classical
  let a' : A := (↑g⁻¹ : A) * a
  obtain ⟨D, hD, ha⟩ := exists_nat_mul_mem_rationalIntegralAdeles a'
  let L : ℝ := ideleNorm g * D
  let x := rationalAdeleReal a'
  have hL : 0 < L := mul_pos (norm_pos g) (Nat.cast_pos.mpr hD)
  have hseminorm := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hB
  obtain ⟨P₀, hP₀, h₀⟩ := hseminorm (0, 0)
  obtain ⟨Pₘ, _, hₘ⟩ := hseminorm (m + 2, 0)
  let P := max P₀ Pₘ
  let M : ℝ := P * (L * (1 + |x|)) ^ (m + 2)
  have hM : 0 < M := mul_pos (hP₀.trans_le (le_max_left ..)) (by positivity)
  let ρ : ℤ → ℝ := fun n ↦ |(n : ℝ)| ^ (-(2 : ℝ))
  have hρ : Summable ρ := Real.summable_abs_int_rpow one_lt_two
  refine ⟨M * (∑' n, ρ n) + 1, ?_, fun b hb k hk ↦ ?_⟩
  · have : 0 ≤ ∑' n, ρ n := tsum_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
    positivity
  let t := ideleNorm k / L
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
  let v : ℚ → ℝ := fun Q ↦ if Q ∈ range j then (M / ideleNorm k ^ m) * ρ (Function.invFun j Q) else 0
  have hvj (n : ℤ) : v (j n) = (M / ideleNorm k ^ m) * ρ n := by
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
      have hb₀ : SchwartzMap.seminorm ℂ 0 0 b ≤ P := (h₀ b hb).le.trans (le_max_left ..)
      have hbₘ : SchwartzMap.seminorm ℂ (m + 2) 0 b ≤ P := (hₘ b hb).le.trans (le_max_right ..)
      apply (schwartz_tail_term b m hk hL hn0 hb₀ hbₘ).trans_eq
      dsimp only [M, ρ]
      rw [Real.rpow_neg (abs_nonneg _) 2, Real.rpow_two, ← div_eq_mul_inv, div_div]
    · rw [indicator_of_notMem hs, norm_zero]
      exact hv0 _
  · calc
      _ ≤ ∑' Q, v Q :=
        Summable.tsum_le_tsum_of_inj idx hi (fun Q _ ↦ hv0 Q) (fun _ ↦ le_rfl)
          (hv.comp_injective hi) hv
      _ = ∑' n, (M / ideleNorm k ^ m) * ρ n := by
        rw [← hj.tsum_eq (f := v) (fun Q hQ ↦ by
          by_contra hQr
          exact hQ (hvzero Q hQr))]
        exact tsum_congr hvj
      _ ≤ _ := by
        rw [tsum_mul_left, div_mul_eq_mul_div]
        have := norm_pos k
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-- A finite envelope of boxes bounds the absolute orbit series uniformly on the
specified product of bounded Schwartz sets. -/
private theorem exists_tail_of_box_envelope {I : Type*} (s : Finset I) (w : I → ℝ)
    (B : I → Set 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J) (m : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hB : ∀ i ∈ s, Bornology.IsVonNBounded ℂ (B i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : I → 𝓢(ℝ, ℂ)), (∀ i ∈ s, b i ∈ B i) →
      ∀ f : A → ℂ, (∀ y, ‖f y‖ ≤ ∑ i ∈ s, w i * ‖rationalAdeleBox (b i) (a i) (g i) y‖) →
      ∀ k : J, 1 ≤ ideleNorm k →
        Summable (fun q : ℚˣ ↦ ‖f (ιˣ q * k : J)‖) ∧
        (∑' q : ℚˣ, ‖f (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  classical
  have hchoice (i : I) : ∃ C : ℝ, 0 < C ∧ ∀ b ∈ B i, i ∈ s → ∀ k : J, 1 ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleBox b (a i) (g i) (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleBox b (a i) (g i) (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
    by_cases hi : i ∈ s
    · obtain ⟨C, hC, h⟩ := exists_box_tail_majorant (hB i hi) (a i) (g i) m
      refine ⟨C, hC, fun b hb _ k hk ↦ ?_⟩
      obtain ⟨u, hu, hub, hsum⟩ := h b hb k hk
      have hs := hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hub
      exact ⟨hs, (hs.tsum_le_tsum hub hu).trans hsum⟩
    · exact ⟨1, zero_lt_one, fun _ _ his ↦ (hi his).elim⟩
  choose C hC h using hchoice
  have hC₀ : 0 ≤ ∑ i ∈ s, w i * C i := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (hC i).le
  refine ⟨(∑ i ∈ s, w i * C i) + 1, by positivity, fun b hb f hf k hk ↦ ?_⟩
  have hbox (i : I) (hi : i ∈ s) := h i (b i) (hb i hi) hi k hk
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

/-- Common large-norm bound for the absolute spatial samples, at threshold one. -/
public theorem rationalAdeleBoxSum_uniform_absolute_theta_tail (m : ℕ) {B : I → Set 𝓢(ℝ, ℂ)}
    (hB : ∀ i ∈ s, Bornology.IsVonNBounded ℂ (B i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : I → 𝓢(ℝ, ℂ)), (∀ i ∈ s, b i ∈ B i) → ∀ k : J, 1 ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleBoxSum s c b a g (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleBoxSum s c b a g (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  obtain ⟨K, hK, h⟩ := exists_tail_of_box_envelope s (fun i ↦ ‖c i‖) B a g m (fun _ ↦ norm_nonneg _) hB
  refine ⟨K, hK, fun b hb ↦ h b hb (rationalAdeleBoxSum s c b a g) ?_⟩
  intro y
  simp only [rationalAdeleBoxSum, ← norm_mul]
  exact norm_sum_le _ _

/-- The large-norm absolute spatial bound for an individual test. -/
public theorem rationalAdeleBoxSum_absolute_theta_tail (m : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleBoxSum s c b a g (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleBoxSum s c b a g (ιˣ q * k : J)‖) ≤ C / ideleNorm k ^ m := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_absolute_theta_tail s c a g m
    (B := fun i ↦ {b i}) (fun i _ ↦ Bornology.isVonNBounded_singleton (b i))
  exact ⟨K, 1, hK, le_rfl, h b (fun _ _ ↦ mem_singleton _)⟩

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

/-- Common large-norm bound for the absolute Fourier samples, at threshold one.
The unit-modulus translation phases leave an envelope of centered dual boxes. -/
public theorem rationalAdeleBoxSum_uniform_absolute_fourier_theta_tail (m : ℕ) {B : I → Set 𝓢(ℝ, ℂ)}
    (hB : ∀ i ∈ s, Bornology.IsVonNBounded ℂ (B i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : I → 𝓢(ℝ, ℂ)), (∀ i ∈ s, b i ∈ B i) → ∀ k : J, 1 ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleFourier (rationalAdeleBoxSum s c b a g) (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleFourier (rationalAdeleBoxSum s c b a g) (ιˣ q * k : J)‖) ≤
        C / ideleNorm k ^ m := by
  let F : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℂ _
  obtain ⟨K, hK, h⟩ := exists_tail_of_box_envelope s (fun i ↦ ‖c i‖ * ideleNorm (g i))
    (fun i ↦ F '' B i) 0 (fun i ↦ (g i)⁻¹) m
    (fun i ↦ mul_nonneg (norm_nonneg _) (norm_pos (g i)).le) (fun i hi ↦ (hB i hi).image F)
  refine ⟨K, hK, fun b hb ↦ h (fun i ↦ 𝓕 (b i)) (fun i hi ↦ ⟨b i, hb i hi, rfl⟩)
    (rationalAdeleFourier (rationalAdeleBoxSum s c b a g)) ?_⟩
  intro y
  rw [rationalAdeleFourier, integral_rationalAdeleBoxSum_mul_conj_char]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_mul, norm_smul, Real.norm_of_nonneg (norm_pos (g i)).le, norm_mul,
    Complex.norm_conj, norm_rationalAdeleAddChar, one_mul, ← mul_assoc,
    rationalAdeleBox, inv_inv, Pi.zero_apply, sub_zero]

/-- The large-norm absolute Fourier bound for an individual test. -/
public theorem rationalAdeleBoxSum_absolute_fourier_theta_tail (m : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ k : J, T ≤ ideleNorm k →
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleFourier (rationalAdeleBoxSum s c b a g) (ιˣ q * k : J)‖) ∧
      (∑' q : ℚˣ, ‖rationalAdeleFourier (rationalAdeleBoxSum s c b a g) (ιˣ q * k : J)‖) ≤
        C / ideleNorm k ^ m := by
  obtain ⟨K, hK, h⟩ := rationalAdeleBoxSum_uniform_absolute_fourier_theta_tail s c a g m
    (B := fun i ↦ {b i}) (fun i _ ↦ Bornology.isVonNBounded_singleton (b i))
  exact ⟨K, 1, hK, le_rfl, h b (fun _ _ ↦ mem_singleton _)⟩

end Masullo
