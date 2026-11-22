module

public import Theorems.IdeleHeckeGaussian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import all Theorems.ComplexGaussianMellin
import all Theorems.RealGaussianMellin
import Mathlib.MeasureTheory.Group.Integral

/-! # The trivial-character Archimedean Gaussian

The local Gaussian pair theorems specify the chosen parameters by the
Mellin integral, not by the character's pointwise restriction. For the
trivial character, a sign change or a rotation negates the integral's
integrand if the chosen parameter is nonzero. Haar invariance then
contradicts nonvanishing of the local Gamma factor.
-/

open Complex MeasureTheory NumberField InfinitePlace.Completion
open scoped Classical ComplexConjugate ContDiff

namespace Masullo

variable {K : Type*} [Field K]

local notation "χ₁" => (1 : HeckeCharacter (𝓞 K) K)

section ChosenParameters

variable [NumberField K]

private theorem localHeckeGammaFactor_at_one_ne_zero
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (v : InfinitePlace K) : localHeckeGammaFactor χ hχ v 1 ≠ 0 := by
  have hs : 0 < (1 : ℂ).re := by simp
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨b, τ, _, _, h⟩ := localHeckeGammaFactor_real χ hχ hv
    rw [h]
    exact (logDeriv_archimedeanGammaFactor_eq_integral (by norm_num : (0 : ℝ) < 2)
      (Nat.cast_nonneg b) hs (B := Real.pi) (τ := τ)).1
  · obtain ⟨n, τ, _, h⟩ := localHeckeGammaFactor_complex χ hχ hv
    rw [h]
    exact (logDeriv_archimedeanGammaFactor_eq_integral (one_pos : (0 : ℝ) < 1)
      (by positivity : (0 : ℝ) ≤ (n.natAbs : ℝ) / 2) hs (B := 2 * Real.pi) (τ := τ)).1

private theorem exists_norm_one_pow_eq_neg_one (m : ℕ) (hm : m ≠ 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a ^ m = -1 := by
  let θ : ℝ := Real.pi / m
  refine ⟨exp ((θ : ℂ) * I), norm_exp_ofReal_mul_I θ, ?_⟩
  rw [← exp_nat_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul]
  have hθ : (m : ℝ) * θ = Real.pi := by
    dsimp [θ]
    field_simp
  rw [hθ, exp_pi_mul_I]

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- The parity actually selected by `archimedeanHeckeGaussian` at a real place. -/
public theorem realCompletionGaussianPair_trivial_choose {v : InfinitePlace K} (hv : v.IsReal) :
    (realCompletionGaussianPair χ₁ (by simp) hv).choose = 0 := by
  let h := realCompletionGaussianPair χ₁ (by simp) hv
  let b := h.choose
  have hb_le : b ≤ 1 := h.choose_spec.1
  by_contra hb
  have hb_one : b = 1 := by
    change b ≠ 0 at hb
    omega
  let f (u : v.Completionˣ) :=
    realZetaGaussian b (extensionEmbeddingOfIsReal hv u.val) *
      (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ (1 : ℂ))
  let a : v.Completionˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hz : (∫ u, f u ∂realCompletionHaar hv) = 0 := by
    apply integral_eq_zero_of_mul_left_eq_neg (g := a)
    intro u
    simp [f, a, hb_one, realZetaGaussian, neg_mul]
  have heq : (∫ u, f u ∂realCompletionHaar hv) = localHeckeGammaFactor χ₁ (by simp) v 1 := by
    dsimp only [f, b]
    simpa only [ContinuousMonoidHom.coe_one, Pi.one_apply, mul_one] using
      (h.choose_spec.2 1 (by simp)).2
  exact localHeckeGammaFactor_at_one_ne_zero χ₁ (by simp) v (heq.symm.trans hz)

/-- The weight actually selected by `archimedeanHeckeGaussian` at a complex place. -/
public theorem complexCompletionGaussianPair_trivial_choose {v : InfinitePlace K}
    (hv : v.IsComplex) : (complexCompletionGaussianPair χ₁ (by simp) hv).choose = 0 := by
  let h := complexCompletionGaussianPair χ₁ (by simp) hv
  let n := h.choose
  by_contra hn
  change n ≠ 0 at hn
  obtain ⟨a, hanorm, hapow⟩ := exists_norm_one_pow_eq_neg_one n.natAbs (by omega)
  have ha : a ≠ 0 := by intro h; simp [h] at hanorm
  let e := ringEquivComplexOfIsComplex hv
  let r : v.Completionˣ := Units.mk0 (e.symm a) ((map_ne_zero e.symm).mpr ha)
  have hr : extensionEmbedding v r.val = a := e.apply_symm_apply a
  have hrnorm : ‖r.val‖ = 1 := by
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) r.val, hr, hanorm]
  have hconj : conj a ^ n.natAbs = -1 := by rw [← map_pow, hapow, map_neg, map_one]
  have hg (u : v.Completionˣ) :
      complexZetaGaussian n (extensionEmbedding v (r * u).val) =
        -complexZetaGaussian n (extensionEmbedding v u.val) := by
    rw [Units.val_mul, map_mul, hr]
    unfold complexZetaGaussian
    rw [norm_mul, hanorm, one_mul]
    split_ifs with hsign
    · have hnat : n.toNat = n.natAbs := by omega
      simp only [hnat, map_mul, mul_pow, hconj, mul_neg, neg_mul, one_mul]
    · simp only [mul_pow, hapow, mul_neg, neg_mul, one_mul]
  let f (u : v.Completionˣ) :=
    complexZetaGaussian n (extensionEmbedding v u.val) *
      (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ (1 : ℂ))
  have hz : (∫ u, f u ∂complexCompletionHaar hv) = 0 := by
    apply integral_eq_zero_of_mul_left_eq_neg (g := r)
    intro u
    dsimp only [f]
    rw [hg u, Units.val_mul, norm_mul, hrnorm, one_mul, neg_mul]
  have heq : (∫ u, f u ∂complexCompletionHaar hv) = localHeckeGammaFactor χ₁ (by simp) v 1 := by
    dsimp only [f, n]
    simpa only [ContinuousMonoidHom.coe_one, Pi.one_apply, mul_one] using
      (h.choose_spec 1 (by simp)).2
  exact localHeckeGammaFactor_at_one_ne_zero χ₁ (by simp) v (heq.symm.trans hz)

end ChosenParameters

/-- The additive Gaussian, including its value at the origin. This is the
extension used for a smooth additive test, not extension by zero. -/
@[expose] public noncomputable def archimedeanHeckeGaussianTrivialAdditive
    (v : InfinitePlace K) (x : v.Completion) : ℂ :=
  if hv : v.IsReal then
    realZetaGaussian 0 (extensionEmbeddingOfIsReal hv x)
  else
    complexZetaGaussian 0 (extensionEmbedding v x)

/-- The normalized radial formula on the entire additive completion. -/
public theorem archimedeanHeckeGaussianTrivialAdditive_apply (v : InfinitePlace K)
    (x : v.Completion) : archimedeanHeckeGaussianTrivialAdditive v x =
      if v.IsReal then
        exp (-(Real.pi * ‖x‖ ^ 2 : ℝ))
      else
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * exp (-(2 * Real.pi * ‖x‖ ^ 2 : ℝ)) := by
  by_cases hv : v.IsReal
  · have hn : ‖extensionEmbeddingOfIsReal hv x‖ = ‖x‖ :=
      (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _
    have hs : (extensionEmbeddingOfIsReal hv x) ^ 2 = ‖x‖ ^ 2 := by
      rw [← hn, Real.norm_eq_abs, sq_abs]
    rw [archimedeanHeckeGaussianTrivialAdditive, dite_eq_left hv, ite_eq_left hv,
      realZetaGaussian, pow_zero, one_mul, hs]
  · have hn : ‖extensionEmbedding v x‖ = ‖x‖ :=
      (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _
    rw [archimedeanHeckeGaussianTrivialAdditive, dite_eq_right hv, ite_eq_right hv,
      complexZetaGaussian, hn]
    simp

/-- The additive test is smooth in the real completion coordinate, including at zero. -/
public theorem contDiff_archimedeanHeckeGaussianTrivialAdditive_real {v : InfinitePlace K}
    (hv : v.IsReal) : ContDiff ℝ ∞ (fun x : ℝ ↦
      archimedeanHeckeGaussianTrivialAdditive v ((ringEquivRealOfIsReal hv).symm x)) := by
  have h (x : ℝ) : extensionEmbeddingOfIsReal hv ((ringEquivRealOfIsReal hv).symm x) = x :=
    (ringEquivRealOfIsReal hv).apply_symm_apply x
  simp only [archimedeanHeckeGaussianTrivialAdditive, dite_eq_left hv, h,
    realZetaGaussian, pow_zero, one_mul]
  have hd : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.pi * x ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hd).neg.cexp

/-- The additive test is smooth in the complex completion coordinate as a real map. -/
public theorem contDiff_archimedeanHeckeGaussianTrivialAdditive_complex {v : InfinitePlace K}
    (hv : v.IsComplex) : ContDiff ℝ ∞ (fun x : ℂ ↦
      archimedeanHeckeGaussianTrivialAdditive v ((ringEquivComplexOfIsComplex hv).symm x)) := by
  have h (x : ℂ) : extensionEmbedding v ((ringEquivComplexOfIsComplex hv).symm x) = x :=
    (ringEquivComplexOfIsComplex hv).apply_symm_apply x
  simp only [archimedeanHeckeGaussianTrivialAdditive,
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hv), h, complexZetaGaussian,
    le_refl, ite_true, Int.toNat_zero, pow_zero, mul_one, ← normSq_eq_norm_sq, normSq_apply]
  have hre : ContDiff ℝ ∞ (fun x : ℂ ↦ x.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun x : ℂ ↦ x.im) := Complex.imCLM.contDiff
  have hd : ContDiff ℝ ∞ (fun x : ℂ ↦ 2 * Real.pi * (x.re * x.re + x.im * x.im)) :=
    contDiff_const.mul ((hre.mul hre).add (him.mul him))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd).neg.cexp

/-- The value at zero of the smooth additive test is the local prefactor. -/
public theorem archimedeanHeckeGaussianTrivialAdditive_zero (v : InfinitePlace K) :
    archimedeanHeckeGaussianTrivialAdditive v 0 =
      if v.IsReal then 1 else ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
  by_cases hv : v.IsReal <;> simp [archimedeanHeckeGaussianTrivialAdditive_apply, hv]

variable [NumberField K] in
/-- The Archimedean tensor has value `(1 / (2π)) ^ r₂` at its additive origin. -/
public theorem archimedeanHeckeGaussianTrivialAdditive_prod_zero :
    (∏ v : InfinitePlace K, archimedeanHeckeGaussianTrivialAdditive v 0) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ InfinitePlace.nrComplexPlaces K := by
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  have hre (v : {v : InfinitePlace K // v.IsReal}) :
      archimedeanHeckeGaussianTrivialAdditive v.val 0 = 1 := by
    rw [archimedeanHeckeGaussianTrivialAdditive_zero, ite_eq_left v.property]
  have hco (v : {v : InfinitePlace K // v.IsComplex}) :
      archimedeanHeckeGaussianTrivialAdditive v.val 0 = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [archimedeanHeckeGaussianTrivialAdditive_zero,
      ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr v.property)]
  simp only [hre, hco, Finset.prod_const, Finset.card_univ, one_pow, one_mul,
    InfinitePlace.nrComplexPlaces]

section Restriction

variable [NumberField K] [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- The additive test restricts to the actual chosen Gaussian on the units. -/
public theorem archimedeanHeckeGaussianTrivialAdditive_coe (v : InfinitePlace K)
    (u : v.Completionˣ) : archimedeanHeckeGaussianTrivialAdditive v u.val =
      archimedeanHeckeGaussian χ₁ (by simp) v u := by
  by_cases hv : v.IsReal
  · rw [archimedeanHeckeGaussianTrivialAdditive, archimedeanHeckeGaussian, dite_eq_left hv,
      dite_eq_left hv, realCompletionGaussianPair_trivial_choose]
  · rw [archimedeanHeckeGaussianTrivialAdditive, archimedeanHeckeGaussian, dite_eq_right hv,
      dite_eq_right hv, complexCompletionGaussianPair_trivial_choose]

/-- The trivial-character Gaussian on the units, with the complex prefactor `1 / (2π)`. -/
public theorem archimedeanHeckeGaussian_trivial_apply (v : InfinitePlace K) (u : v.Completionˣ) :
    archimedeanHeckeGaussian χ₁ (by simp) v u =
      if v.IsReal then
        exp (-(Real.pi * ‖u.val‖ ^ 2 : ℝ))
      else
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * exp (-(2 * Real.pi * ‖u.val‖ ^ 2 : ℝ)) := by
  rw [← archimedeanHeckeGaussianTrivialAdditive_coe, archimedeanHeckeGaussianTrivialAdditive_apply]

/-- The literal zero extension through the units inclusion is the
punctured radial formula, not the everywhere Gaussian. -/
public theorem archimedeanHeckeGaussian_trivial_extend_zero (v : InfinitePlace K) :
    Function.extend (Units.val : v.Completionˣ → v.Completion)
        (archimedeanHeckeGaussian χ₁ (by simp) v) (fun _ ↦ 0) =
      ({0}ᶜ : Set v.Completion).indicator (fun x ↦
        if v.IsReal then
          exp (-(Real.pi * ‖x‖ ^ 2 : ℝ))
        else
          ((1 / (2 * Real.pi) : ℝ) : ℂ) * exp (-(2 * Real.pi * ‖x‖ ^ 2 : ℝ))) := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact u.ne_zero hu)]
    simp
  · let u := Units.mk0 x hx
    change Function.extend _ _ _ u.val = _
    rw [Function.Injective.extend_apply Units.val_injective, archimedeanHeckeGaussian_trivial_apply,
      Set.indicator_of_mem (by simpa using hx)]
    rfl

end Restriction

end Masullo
