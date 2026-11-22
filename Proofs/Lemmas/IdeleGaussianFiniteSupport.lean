module

public import Theorems.IdeleHeckeGaussian
public import Theorems.IdeleIdealClass
import all Theorems.ComplexGaussianMellin
import all Theorems.RealGaussianMellin

/-! # Finite support of the trivial-character idelic Gaussian -/

open IsDedekindDomain MeasureTheory NumberField
open InfinitePlace.Completion
open scoped Classical ComplexConjugate nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

private theorem fractionalIdeal_le_one_iff_count_nonneg {j : J} (hj : j ≠ 0) :
    j ≤ 1 ↔ ∀ v : V, 0 ≤ FractionalIdeal.count K v j := by
  constructor
  · intro h v
    simpa only [FractionalIdeal.count_one] using FractionalIdeal.count_mono K v hj h
  · intro h
    have hs : Function.HasFiniteMulSupport
        (fun v : V ↦ (v.asIdeal : J) ^ FractionalIdeal.count K v j) := by
      change {v : V | ¬ (v.asIdeal : J) ^ FractionalIdeal.count K v j = 1}.Finite
      apply Filter.eventually_cofinite.mp
      filter_upwards [FractionalIdeal.finite_factors j] with v hv
      rw [hv, zpow_zero]
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hj, finprod_eq_prod _ hs]
    apply Finset.prod_le_one₀ (fun _ _ ↦ FractionalIdeal.zero_le _)
    intro v _
    rw [← Int.toNat_of_nonneg (h v), zpow_natCast]
    exact pow_le_one₀ (FractionalIdeal.zero_le _) FractionalIdeal.coeIdeal_le_one

private theorem norm_finite_le_one_iff (g : I) :
    (∀ v : V, ‖(g : A).2 v‖ ≤ 1) ↔ (finiteIdeleIdeal K (ideleFinitePart g) : J) ≤ 1 := by
  rw [fractionalIdeal_le_one_iff_count_nonneg (finiteIdeleIdeal K (ideleFinitePart g)).ne_zero]
  apply forall_congr'
  intro v
  -- The prime-ideal exponent is minus the logarithm of the local valuation.
  rw [count_finiteIdeleIdeal, le_neg, neg_zero, ← WithZero.log_one,
    WithZero.log_le_log (finiteIdele_valuation_ne_zero _ _) one_ne_zero, ideleFinitePart_apply]
  exact Valued.toNormedField.norm_le_one_iff

private theorem diag_mul_mem_inverse_finiteIdeleIdeal_iff (b : I) (a : Kˣ) :
    (∀ v : V, ‖(↑(d a * b) : A).2 v‖ ≤ 1) ↔
      (a : K) ∈ (finiteIdeleIdeal K (ideleFinitePart b) : J)⁻¹ := by
  let j := finiteIdeleIdeal K (ideleFinitePart b)
  have hd : ideleFinitePart (d a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a := by
    apply Units.ext
    apply DFunLike.ext
    intro v
    rw [ideleFinitePart_apply, FiniteAdeleRing.unitEmbedding_apply]
    rfl
  rw [norm_finite_le_one_iff, map_mul (ideleFinitePart (K := K)), hd, map_mul,
    Units.val_mul, finiteIdeleIdeal_unitEmbedding, ← FractionalIdeal.spanSingleton_le_iff_mem]
  change FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * (j : J) ≤ 1 ↔
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) ≤ (j : J)⁻¹
  constructor
  · intro h
    have h' := mul_le_mul_left h (j : J)⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ j.ne_zero, mul_one, one_mul] at h'
  · intro h
    have h' := mul_le_mul_left h (j : J)
    rwa [inv_mul_cancel₀ j.ne_zero] at h'

/-- The finite coordinates of the adelic product of `x` and `b` are integral exactly
when `x` belongs to the inverse of the fractional ideal of the finite part of `b`.
This applies also to `x = 0`, where the product is an adele, not an idele. -/
public theorem finite_integrality_iff_mem_inverse_finiteIdeleIdeal (b : I) (x : K) :
    (∀ v : V, ‖algebraMap K (F v) x * (b : A).2 v‖ ≤ 1) ↔
      x ∈ (finiteIdeleIdeal K (ideleFinitePart b) : J)⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, zero_mul, norm_zero, zero_le_one, implies_true, true_iff]
    exact FractionalIdeal.zero_mem _
  · exact diag_mul_mem_inverse_finiteIdeleIdeal_iff b (Units.mk0 x hx)

private theorem finiteHeckeGaussian_one (v : V) (u : (F v)ˣ) :
    finiteHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) v u =
      if ‖(u : F v)‖ ≤ 1 then 1 else 0 := by
  have hu : (1 : HeckeCharacter (𝓞 K) K).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro y
    change (1 : HeckeCharacter (𝓞 K) K).restrict v
      (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom y : (F v)ˣ) = 1
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  rw [finiteHeckeGaussian, ite_eq_left hu]

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

private theorem archimedeanHeckeGaussian_ne_zero
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (v : InfinitePlace K) (u : v.Completionˣ) : archimedeanHeckeGaussian χ hχ v u ≠ 0 := by
  rw [archimedeanHeckeGaussian]
  split
  next hv =>
    rw [realZetaGaussian]
    have hz := (map_ne_zero (extensionEmbeddingOfIsReal hv)).mpr u.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hz)) (Complex.exp_ne_zero _)
  next =>
    rw [complexZetaGaussian]
    have hz := (map_ne_zero (extensionEmbedding v)).mpr u.ne_zero
    have hc : (↑(1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))
    apply mul_ne_zero (mul_ne_zero hc ?_) (Complex.exp_ne_zero _)
    split
    · exact pow_ne_zero _ ((map_ne_zero (starRingEnd ℂ)).mpr hz)
    · exact pow_ne_zero _ hz

private theorem ideleHeckeGaussian_one_eq_if_integral (T : Finset V) (g : I) :
    ideleHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) T g =
      if ∀ v : V, ‖(g : A).2 v‖ ≤ 1 then
        ∏ v, archimedeanHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) v
          (ideleInfiniteCoordinates K g v)
      else 0 := by
  have hf (v : V) :
      finiteHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) v (ideleFiniteCoordinate K g v) =
        if ‖(g : A).2 v‖ ≤ 1 then 1 else 0 :=
    finiteHeckeGaussian_one v (ideleFiniteCoordinate K g v)
  unfold ideleHeckeGaussian ideleZetaTest
  simp only [hf]
  by_cases h : ∀ v : V, ‖(g : A).2 v‖ ≤ 1
  · rw [ite_eq_left h, ite_eq_left (fun v _ ↦ h v),
      Finset.prod_eq_one (fun v _ ↦ ite_eq_left (h v)), mul_one]
  · rw [ite_eq_right h]
    split
    next ht =>
      obtain ⟨v, hv⟩ := not_forall.mp h
      have hvT : v ∈ T := by
        by_contra hn
        exact hv (ht v hn)
      rw [Finset.prod_eq_zero hvT (ite_eq_right hv), mul_zero]
    next => rfl

/-- The actual trivial-character Gaussian on a diagonal translate is the Archimedean
product on the inverse fractional ideal and zero off it, independently of `T`. -/
public theorem ideleHeckeGaussian_one_diagonal_eq (T : Finset V) (b : I) (a : Kˣ) :
    ideleHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) T (d a * b) =
      if (a : K) ∈ (finiteIdeleIdeal K (ideleFinitePart b) : J)⁻¹ then
        ∏ v, archimedeanHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) v
          (ideleInfiniteCoordinates K (d a * b) v)
      else 0 := by
  rw [ideleHeckeGaussian_one_eq_if_integral]
  exact if_congr (finite_integrality_iff_mem_inverse_finiteIdeleIdeal b (a : K)) rfl rfl

/-- For an actual diagonal summand of the trivial-character Gaussian, nonvanishing
is precisely membership in the inverse fractional ideal. The finite integrality
criterion itself also applies at zero (`finite_integrality_iff_mem_inverse_finiteIdeleIdeal`). -/
public theorem ideleHeckeGaussian_one_diagonal_ne_zero_iff (T : Finset V) (b : I) (a : Kˣ) :
    ideleHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) T (d a * b) ≠ 0 ↔
      (a : K) ∈ (finiteIdeleIdeal K (ideleFinitePart b) : J)⁻¹ := by
  rw [ideleHeckeGaussian_one_diagonal_eq]
  by_cases ha : (a : K) ∈ (finiteIdeleIdeal K (ideleFinitePart b) : J)⁻¹
  · rw [ite_eq_left ha]
    refine ⟨fun _ ↦ ha, fun _ ↦ Finset.prod_ne_zero_iff.mpr ?_⟩
    intro v _
    exact archimedeanHeckeGaussian_ne_zero (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one)
      v (ideleInfiniteCoordinates K (d a * b) v)
  · simp [ha]

end Masullo
