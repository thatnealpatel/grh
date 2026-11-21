module

public import Theorems.RationalAdeleBoxSumPoisson
import Lemmas.RationalAdeleAffineIntegral

/-! # Theta inversion for finite sums of rational adelic boxes

This is the pointwise identity of Theorem 2.2.3.2, p. 82, for the algebraic
span of the translated generators of Example 2.1.3.1 over ℚ. It does not
assert continuity in the idele parameter or identify the full Schwartz–Bruhat space.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ι" => algebraMap ℚ A
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "χ" => rationalAdeleAddChar
local notation "μA" => rationalAdeleAddHaar

/-- The rational adelic theta sum, omitting the zero term. -/
@[expose] public noncomputable def rationalAdeleTheta (f : A → ℂ) (k : J) : ℂ :=
  ∑' q : ℚˣ, f ((ιˣ q * k : J) : A)

private theorem tsum_eq_zero_add_units (f : ℚ → ℂ) (hf : Summable f) :
    (∑' q, f q) = f 0 + ∑' q : ℚˣ, f q := by
  let S : Set ℚ := (↑({0} : Finset ℚ) : Set ℚ)ᶜ
  let e : ℚˣ ≃ S := unitsEquivNeZero.trans (Equiv.subtypeEquivRight (fun q ↦ by simp [S]))
  calc
    (∑' q, f q) = f 0 + ∑' q : S, f q := by
      simpa only [Finset.sum_singleton] using (hf.sum_add_tsum_compl (s := ({0} : Finset ℚ))).symm
    _ = _ := congrArg (f 0 + ·) (e.tsum_eq (fun q : S ↦ f q)).symm

private theorem principal_mul (q : ℚˣ) (k : J) : ((ιˣ q * k : J) : A) = (k : A) * ι (q : ℚ) := by
  change ι (q : ℚ) * (k : A) = _
  exact mul_comm _ _

set_option linter.concreteInstances false

section

variable [MeasurableSpace A] [BorelSpace A]

/-- The negative-sign Fourier integral with normalized additive adelic Haar. -/
@[expose] public noncomputable def rationalAdeleFourier (f : A → ℂ) (y : A) : ℂ :=
  ∫ z, f z * conj (χ (z * y)) ∂μA

private theorem fourier_dilate (f : A → ℂ) (k : J) (y : A) :
    rationalAdeleFourier (fun z ↦ f ((k : A) * z)) y =
      (ideleNorm k)⁻¹ • rationalAdeleFourier f ((↑(k⁻¹) : A) * y) := by
  unfold rationalAdeleFourier
  rw [integral_rationalAdele_affine _ 0 k⁻¹, map_inv]
  simp only [zero_add, ← mul_assoc, Units.mul_inv, one_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z ↦ by simp only [mul_comm (↑(k⁻¹) : A) z]

end

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ))
  (a : I → A) (g : I → J) (k : J)

local notation "f" => rationalAdeleBoxSum s c b a g
local notation "fₖ" => rationalAdeleBoxSum s c b (fun i ↦ ((k⁻¹ : J) : A) * a i) (fun i ↦ k⁻¹ * g i)

private theorem boxSum_dilate (z : A) : fₖ z = f ((k : A) * z) := by
  unfold rationalAdeleBoxSum
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  simp only [rationalAdeleBox, mul_inv_rev, inv_inv, Units.val_mul]
  rw [mul_assoc, mul_sub, ← mul_assoc (k : A), Units.mul_inv, one_mul]

variable [MeasurableSpace A] [BorelSpace A]

private theorem summable_dilated_diagonal :
    Summable (fun q : ℚ ↦ ‖f ((k : A) * ι q)‖) ∧
      Summable (fun q : ℚ ↦ ‖rationalAdeleFourier f ((↑(k⁻¹) : A) * ι q)‖) := by
  have h := (rationalAdeleBoxSum_periodization s c b
    (fun i ↦ (↑(k⁻¹) : A) * a i) (fun i ↦ k⁻¹ * g i)).1 0
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, zero_add, rationalDiagonalEquiv_apply, boxSum_dilate]
      using rationalDiagonalEquiv.summable_iff.mpr h
  · have hfour : Summable (fun q : ℚ ↦ ‖rationalAdeleFourier fₖ (ι q)‖) :=
      summable_norm_rationalAdeleBoxSum_fourier s c b _ _
    have hk : ideleNorm k ≠ 0 :=
      (ideleClassNorm_mk k ▸ ideleClassNorm_pos (QuotientGroup.mk k)).ne'
    apply (summable_mul_left_iff (norm_ne_zero_iff.mpr (inv_ne_zero hk))).mp
    simpa only [funext (boxSum_dilate s c b a g k), fourier_dilate, norm_smul] using hfour

/-- Both nonzero theta sums in the inversion formula converge absolutely. -/
public theorem summable_norm_rationalAdeleBoxSum_theta :
    Summable (fun q : ℚˣ ↦ ‖f ((ιˣ q * k : J) : A)‖) ∧
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleFourier f ((ιˣ q * k⁻¹ : J) : A)‖) := by
  obtain ⟨hs, ht⟩ := summable_dilated_diagonal s c b a g k
  constructor
  · simpa only [Function.comp_def, principal_mul, unitsEquivNeZero_apply_coe] using
      unitsEquivNeZero.summable_iff.mpr (hs.subtype (· ≠ 0))
  · simpa only [Function.comp_def, principal_mul, unitsEquivNeZero_apply_coe] using
      unitsEquivNeZero.summable_iff.mpr (ht.subtype (· ≠ 0))

variable [MeasurableSpace Cq] [BorelSpace Cq]

/-- At every rational idele, the theta sum of a finite box sum is the scaled
Fourier theta sum at the inverse idele, plus the scaled Fourier zero mode,
minus the original zero mode. -/
public theorem rationalAdeleBoxSum_theta_inversion :
    rationalAdeleTheta f k =
      (ideleNorm k)⁻¹ • rationalAdeleTheta (rationalAdeleFourier f) k⁻¹ +
        (ideleNorm k)⁻¹ • rationalAdeleFourier f 0 - f 0 := by
  -- Apply Poisson at zero to the dilated sum, then reindex the additive diagonal.
  have h := (hasSum_rationalAdeleBoxSum_poisson s c b
    (fun i ↦ (↑(k⁻¹) : A) * a i) (fun i ↦ k⁻¹ * g i) 0).tsum_eq
  simp only [zero_add, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  change (∑' d : rationalDiagonal, fₖ (d : A)) = (∑' q : ℚ, rationalAdeleFourier fₖ (ι q)) at h
  rw [← rationalDiagonalEquiv.tsum_eq (fun d ↦ fₖ (d : A))] at h
  simp only [rationalDiagonalEquiv_apply, funext (boxSum_dilate s c b a g k), fourier_dilate] at h
  obtain ⟨hs, ht⟩ := summable_dilated_diagonal s c b a g k
  -- Separate both zero modes before converting the remaining terms to rational units.
  rw [ht.of_norm.tsum_const_smul, tsum_eq_zero_add_units _ hs.of_norm,
    tsum_eq_zero_add_units _ ht.of_norm, smul_add] at h
  simp only [map_zero, mul_zero] at h
  simp only [rationalAdeleTheta, principal_mul]
  rw [eq_sub_iff_add_eq, add_comm _ (f 0)]
  exact h.trans (add_comm _ _)

end Masullo
