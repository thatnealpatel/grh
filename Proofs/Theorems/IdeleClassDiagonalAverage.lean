module

public import Theorems.IdeleClassConvolutionKernel
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Shrinking Haar boxes on the class-group diagonal

In Masullo §1.2.1(4), p. 15, the support gap removes the regular convolution
kernel from sufficiently small diagonal averages. This is separate from the
existence of the spectral diagonal and its trace interpretation.
-/

open Filter MeasureTheory NumberField Set
open scoped Masullo Pointwise Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K

/-- The translated product box about `(x, x)` used for the class-Haar average. -/
@[expose] public noncomputable def ideleClassDiagonalBox (x : C) (U : Set C) : Set (C × C) :=
  (x • U) ×ˢ (x • U)

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)]

/-- The set integral divided by the product measure's mass of the box.
For an analytic average the box must have positive finite mass and the
kernel must be integrable on it; this definition uses Lean's totalized
real measure, division and Bochner integral. -/
@[expose] public noncomputable def ideleClassDiagonalAverage
    (μ : Measure C) (U : Set C) (k : C × C → ℂ) (x : C) : ℂ :=
  let B := ideleClassDiagonalBox x U
  (∫ p in B, k p ∂(μ.prod μ)) / ((μ.prod μ).real B : ℂ)

variable [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  (μ : Measure (IdeleClassGroup (𝓞 K) K))

/-- The box mass is the square of the unshifted factor's Haar mass, as in
Definition 12.1.1.1 and its product use on pp. 498–499. -/
public theorem ideleClassDiagonalBox_measure [μ.IsHaarMeasure] [SFinite μ] (x : C) (U : Set C) :
    (μ.prod μ) (ideleClassDiagonalBox x U) = μ U ^ 2 := by
  rw [ideleClassDiagonalBox, Measure.prod_prod, measure_smul μ x U, pow_two]

/-- On eventually small boxes the difference kernel has exactly the
negative spectral average. No integrability or spectral representation
is needed for this equality of totalized integrals: the two integrands
agree on the entire box after negating the spectral kernel. -/
public theorem ideleClassDiagonalAverage_sub_eventually_eq_neg {φ : C → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    (U : ℕ → Set C) (hU : ∀ n, MeasurableSet (U n))
    (hshrink : ∀ V ∈ 𝓝 (1 : C), ∀ᶠ n in atTop, U n ⊆ V)
    (k : C × C → ℂ) (x : C) :
    (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun p ↦ φ (p.1 / p.2) - k p) x)
      =ᶠ[atTop] (fun n ↦ -ideleClassDiagonalAverage μ (U n) k x) := by
  let W : Set (C × C) := {p | ideleClassNorm (x * p.1) < (1 + ε) * ideleClassNorm (x * p.2)}
  have hcont : Continuous (fun u : C ↦ ideleClassNorm (x * u)) :=
    continuous_ideleClassNorm.comp (show Continuous (fun u : C ↦ x * u) by fun_prop)
  have hOpen : IsOpen W := isOpen_lt (hcont.comp continuous_fst)
    (continuous_const.mul (hcont.comp continuous_snd))
  have hdiag : ((1, 1) : C × C) ∈ W := by
    change ideleClassNorm (x * 1) < (1 + ε) * ideleClassNorm (x * 1)
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right (lt_add_of_pos_right 1 hε) (ideleClassNorm_pos (x * 1)))
  obtain ⟨V₁, hV₁, V₂, hV₂, hW⟩ := mem_nhds_prod_iff.mp (hOpen.mem_nhds hdiag)
  filter_upwards [hshrink V₁ hV₁, hshrink V₂ hV₂] with n hn₁ hn₂
  have hB : MeasurableSet (ideleClassDiagonalBox x (U n)) :=
    ((hU n).const_smul x).prod ((hU n).const_smul x)
  have heq : EqOn (fun p : C × C ↦ φ (p.1 / p.2) - k p) (fun p ↦ -k p)
      (ideleClassDiagonalBox x (U n)) := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    obtain ⟨u, hu, rfl⟩ := mem_smul_set.mp hy
    obtain ⟨v, hv, rfl⟩ := mem_smul_set.mp hz
    have h := hW (show (u, v) ∈ V₁ ×ˢ V₂ from ⟨hn₁ hu, hn₂ hv⟩)
    have hlt : ideleClassNorm (x * u) < (1 + ε) * ideleClassNorm (x * v) := h
    simp only [smul_eq_mul, ideleClass_convolution_kernel_eq_zero_of_norm_le hφ hlt.le, zero_sub]
  simp only [ideleClassDiagonalAverage, setIntegral_congr_fun hB heq, integral_neg, neg_div]

/-- Each finite limit of the spectral averages gives the opposite limit
of the difference averages, and conversely. This does not assert regularity
at any point without regularity of the spectral term there. -/
public theorem ideleClassDiagonalAverage_sub_tendsto_iff {φ : C → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    (U : ℕ → Set C) (hU : ∀ n, MeasurableSet (U n))
    (hshrink : ∀ V ∈ 𝓝 (1 : C), ∀ᶠ n in atTop, U n ⊆ V)
    (k : C × C → ℂ) (x : C) (L : ℂ) :
    Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun p ↦ φ (p.1 / p.2) - k p) x)
      atTop (𝓝 (-L)) ↔
    Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) k x) atTop (𝓝 L) := by
  have heq := ideleClassDiagonalAverage_sub_eventually_eq_neg μ hε hφ U hU hshrink k x
  constructor
  · intro h
    simpa only [neg_neg] using (h.congr' heq).neg
  · intro h
    exact h.neg.congr' heq.symm

end Masullo
