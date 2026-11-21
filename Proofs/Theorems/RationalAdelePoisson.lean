module

public import Theorems.RationalAdeleClassFourierBasis
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise Poisson summation on the rational adeles

Orthogonality and uniform density reconstruct continuous functions on the
compact quotient from absolutely summable Fourier coefficients. Applying the
checked Weil comparison gives the rational counting-series form of Theorem
D.1.2.7(3), p. 749, with explicit absolute convergence of the periodization.
This route does not identify the ambient adelic dual or use Plancherel.
-/

open NumberField MeasureTheory Topology
open scoped ComplexConjugate InnerProductSpace

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → Cq)
local notation "ι" => algebraMap ℚ A

local instance : CompactSpace Cq := compactSpace_rationalAdeleClasses

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

local notation "μ" => rationalAdeleClassHaar
local notation "T" => ContinuousMap.toLp 2 μ ℂ
local notation "χ" => rationalAdeleClassCharMap

/-- The Fourier coefficient on the quotient, using the conjugated character. -/
@[expose] public noncomputable def rationalAdeleClassFourierCoeff (g : C(Cq, ℂ)) (r : ℚ) : ℂ :=
  ∫ c, g c * conj (rationalAdeleClassChar r c) ∂μ

private theorem inner_char (g : C(Cq, ℂ)) (r : ℚ) :
    ⟪T (χ r), T g⟫_ℂ = rationalAdeleClassFourierCoeff g r := by
  simp only [ContinuousMap.inner_toLp, rationalAdeleClassFourierCoeff,
    rationalAdeleClassCharMap_apply]

private theorem eq_zero_of_inner_char_eq_zero (h : C(Cq, ℂ))
    (hh : ∀ r : ℚ, ⟪T (χ r), T h⟫_ℂ = 0) : h = 0 := by
  -- The L² pairing against h is continuous for the sup norm.
  let F : C(Cq, ℂ) →L[ℂ] ℂ := (innerSL ℂ (T h)).comp T
  have hspan : Submodule.span ℂ (Set.range χ) ≤ LinearMap.ker F.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    change ⟪T h, T (χ r)⟫_ℂ = 0
    rw [← inner_conj_symm, hh, map_zero]
  have hclosed : IsClosed (LinearMap.ker F.toLinearMap : Set C(Cq, ℂ)) :=
    isClosed_eq F.continuous continuous_const
  have hmem : h ∈ LinearMap.ker F.toLinearMap :=
    closure_minimal hspan hclosed (by rw [closure_span_rationalAdeleClassCharMap]; trivial)
  have hzero : T h = 0 := inner_self_eq_zero.mp hmem
  exact (ContinuousMap.toLp_injective μ) (hzero.trans (map_zero T).symm)

/-- Absolute summability of the Fourier coefficients of a continuous quotient
function gives convergence of its Fourier series in the sup norm. -/
public theorem hasSum_rationalAdeleClassFourier (g : C(Cq, ℂ))
    (hg : Summable (fun r ↦ ‖rationalAdeleClassFourierCoeff g r‖)) :
    HasSum (fun r ↦ rationalAdeleClassFourierCoeff g r • χ r) g := by
  let b := rationalAdeleClassFourierCoeff g
  let u : ℚ → C(Cq, ℂ) := fun r ↦ b r • χ r
  have hχ (r : ℚ) : ‖χ r‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).mpr fun c ↦ by
      rw [rationalAdeleClassCharMap_apply, norm_rationalAdeleClassChar]
  have hu : Summable u := hg.of_norm_bounded fun r ↦ by
    rw [show u r = b r • χ r by rfl, norm_smul]
    calc
      ‖b r‖ * ‖χ r‖ ≤ ‖b r‖ * 1 := mul_le_mul_of_nonneg_left (hχ r) (norm_nonneg _)
      _ = ‖b r‖ := mul_one _
  -- Pair the uniform limit with each character and use orthogonality.
  let v := ∑' r, u r
  have hcoeff (s : ℚ) : ⟪T (χ s), T v⟫_ℂ = b s := by
    let F : C(Cq, ℂ) →L[ℂ] ℂ := (innerSL ℂ (T (χ s))).comp T
    have hterm (r : ℚ) : F (u r) = b r * (if r = s then 1 else 0) := by
      rw [show u r = b r • χ r by rfl, map_smul]
      change b r * ⟪T (χ s), T (χ r)⟫_ℂ = _
      simp only [ContinuousMap.inner_toLp, rationalAdeleClassCharMap_apply,
        integral_rationalAdeleClassChar_mul_conj]
    have hs := (F.hasSum hu.hasSum).tsum_eq
    change (∑' r, F (u r)) = ⟪T (χ s), T v⟫_ℂ at hs
    rw [← hs, tsum_congr hterm, tsum_eq_single s]
    · simp
    · intro r hrs
      simp [hrs]
  have hv : v - g = 0 := eq_zero_of_inner_char_eq_zero (v - g) fun s ↦ by
    rw [map_sub, inner_sub_right, hcoeff, inner_char, sub_self]
  have hsum : HasSum u v := hu.hasSum
  rw [sub_eq_zero.mp hv] at hsum
  exact hsum

/-- The rational pointwise Poisson formula with explicit absolute summability
of the fibers and the Fourier samples, and continuity of the periodization. -/
public theorem hasSum_rationalAdele_poisson {f : A → ℂ}
    (hf : Measurable f) (hfi : Integrable f rationalAdeleAddHaar)
    (hfib : ∀ a : A, Summable (fun d : rationalDiagonal ↦ ‖f (a + (d : A))‖))
    (hper : Continuous (rationalAdeleComplexPeriodization f))
    (hfour : Summable (fun r : ℚ ↦
      ‖∫ a, f a * conj (rationalAdeleAddChar (a * ι r)) ∂rationalAdeleAddHaar‖))
    (x : A) :
    HasSum (fun d : rationalDiagonal ↦ f (x + (d : A)))
      (∑' r : ℚ, (∫ a, f a * conj (rationalAdeleAddChar (a * ι r)) ∂rationalAdeleAddHaar) *
        rationalAdeleAddChar (x * ι r)) := by
  let g : C(Cq, ℂ) := ⟨rationalAdeleComplexPeriodization f, hper⟩
  have hcoeff (r : ℚ) : rationalAdeleClassFourierCoeff g r =
      ∫ a, f a * conj (rationalAdeleAddChar (a * ι r)) ∂rationalAdeleAddHaar :=
    integral_rationalAdeleComplexPeriodization_mul_conj_char hf hfi r
  have hs := hasSum_rationalAdeleClassFourier g (by simpa only [hcoeff] using hfour)
  have hx := ((ContinuousMap.evalCLM ℂ (π x)).hasSum hs).tsum_eq
  change (∑' r, (rationalAdeleClassFourierCoeff g r • χ r) (π x)) =
    rationalAdeleComplexPeriodization f (π x) at hx
  simp only [ContinuousMap.smul_apply, smul_eq_mul, rationalAdeleClassCharMap_apply,
    hcoeff, rationalAdeleClassChar_mk, rationalAdeleComplexPeriodization_mk] at hx
  exact hx.symm ▸ (hfib x).of_norm.hasSum

end Masullo
