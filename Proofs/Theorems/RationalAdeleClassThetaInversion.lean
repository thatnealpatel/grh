module

public import Theorems.RationalAdeleBoxThetaInversion
import Props.RationalAdeleBoxOrbits
import Mathlib.Topology.Algebra.Group.Units

/-! # Theta inversion on rational idele classes

For finite sums of translated adelic boxes over ℚ, Theorem 2.2.3.2, p. 82,
is an identity on the idele class group with both theta functions continuous.
The continuity of the Fourier theta function follows from pointwise inversion,
without assuming stability of the box span under the Fourier transform.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "P" => IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ

/-- Multiplication by a principal idele only permutes the nonzero rational indices. -/
public theorem rationalAdeleTheta_principal_mul (f : A → ℂ) (r : ℚˣ) (k : J) :
    rationalAdeleTheta f (ιˣ r * k) = rationalAdeleTheta f k := by
  simpa only [rationalAdeleTheta, Equiv.coe_mulRight, map_mul, mul_assoc] using
    (Equiv.mulRight r).tsum_eq (fun q : ℚˣ ↦ f ((ιˣ q * k : J) : A))

/-- The nonzero rational orbit sum, as a function on the idele class group. -/
public noncomputable def rationalAdeleClassTheta (f : A → ℂ) : C → ℂ :=
  Quotient.lift (rationalAdeleTheta f) (by
    intro k l hkl
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (QuotientGroup.leftRel_apply.mp hkl)
    have he : l = ιˣ r * k := by rw [hr, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [he, rationalAdeleTheta_principal_mul])

@[simp] public theorem rationalAdeleClassTheta_mk (f : A → ℂ) (k : J) :
    rationalAdeleClassTheta f (QuotientGroup.mk k) = rationalAdeleTheta f k := by
  unfold rationalAdeleClassTheta
  rfl

private theorem continuous_classTheta_of_continuous {f : A → ℂ}
    (h : Continuous (rationalAdeleTheta f)) : Continuous (rationalAdeleClassTheta f) :=
  (QuotientGroup.isQuotientMap_mk P).continuous_iff.mpr h

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- The spatial theta function of a finite box sum is continuous on idele classes. -/
public theorem continuous_rationalAdeleClassTheta_boxSum : Continuous (rationalAdeleClassTheta f) := by
  apply continuous_classTheta_of_continuous
  have h := (continuous_rationalAdeleBoxSum_orbit s c b a g).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : J ↦ (0 : A))))
  convert h using 1
  funext k
  simp only [rationalAdeleTheta, Function.comp_apply, rationalAdeleOrbitTerm, add_zero]
  congr 1
  funext q
  change f (ιˣ q * k : J) = f ((k : A) * algebraMap ℚ A (q : ℚ))
  rw [Units.val_mul]
  exact congrArg f (mul_comm _ _)

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

local notation "f̂" => rationalAdeleFourier f

/-- The Fourier theta function is also continuous on idele classes. -/
public theorem continuous_rationalAdeleClassTheta_fourier_boxSum :
    Continuous (rationalAdeleClassTheta f̂) := by
  apply continuous_classTheta_of_continuous
  have hs (k : J) : rationalAdeleTheta f̂ k = (ideleNorm k)⁻¹ •
      (rationalAdeleTheta f k⁻¹ - ideleNorm k • f̂ 0 + f 0) := by
    have h := rationalAdeleBoxSum_theta_inversion s c b a g k⁻¹
    rw [map_inv, inv_inv, inv_inv, eq_sub_iff_add_eq] at h
    rw [sub_add_eq_add_sub, h]
    have hk : ideleNorm k ≠ 0 := (ideleClassNorm_mk k ▸ ideleClassNorm_pos (QuotientGroup.mk k)).ne'
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [funext hs]
  have hθ : Continuous (fun k : J ↦ rationalAdeleTheta f k⁻¹) :=
    (continuous_rationalAdeleClassTheta_boxSum s c b a g).comp
      (QuotientGroup.continuous_mk.comp continuous_inv)
  have hn : Continuous (fun k : J ↦ (ideleNorm k)⁻¹) :=
    continuous_ideleNorm.inv₀ fun k ↦ (ideleClassNorm_mk k ▸ ideleClassNorm_pos (QuotientGroup.mk k)).ne'
  exact hn.smul ((hθ.sub (continuous_ideleNorm.smul continuous_const)).add continuous_const)

/-- Masullo's theta inversion on the rational idele class group, for the finite
translated-box span. The two theta functions are continuous by the preceding theorems. -/
public theorem rationalAdeleBoxSum_theta_inversion_class (k : C) :
    rationalAdeleClassTheta f k =
      (ideleClassNorm k)⁻¹ • rationalAdeleClassTheta f̂ k⁻¹ +
        (ideleClassNorm k)⁻¹ • f̂ 0 - f 0 := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  rw [← show QuotientGroup.mk (k⁻¹) = (QuotientGroup.mk k : C)⁻¹ from rfl]
  simpa only [rationalAdeleClassTheta_mk, ideleClassNorm_mk] using
    rationalAdeleBoxSum_theta_inversion s c b a g k

end Masullo
