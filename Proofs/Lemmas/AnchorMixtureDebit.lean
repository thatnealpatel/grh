module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Anchor debits for shared-key mixtures

Source: `e79d9290:.godel/bob/six-release-support-33.md`, lines 39–79, and
`e79d9290:.godel/bob/check-six-release-support-33.py`, lines 109–126.
These files agree at scan pin `7f6ac23` and selection base `aaf7e47`.
Owning check session: `01a20ff6-8a18-70ab-866d-9f5902b34d4c`.

This gives the discount comparison and the resulting strict bound on a single common
profile. It uses finite shared keys, unit anchor directions, and a common real positive
semidefinite quadratic form, allowing a kernel. It does not certify the numeric witness,
original price feasibility, or mixtures with different keys or forms.
-/

open scoped BigOperators ComplexConjugate

namespace AnchorMixtureDebit

variable {ι κ E Profile : Type*} [Fintype ι] [Fintype κ] [AddCommGroup E] [Module ℝ E]

/-- The center with weights `w`; at zero total weight the inverse convention gives zero. -/
noncomputable def barycenter (w : ι → ℝ) (Z : ι → E) : E :=
  (∑ i, w i)⁻¹ • ∑ i, w i • Z i

/-- Raw disk weight less the norm sum after compression at each shared key. -/
noncomputable def diskDiscount (θ s : ι → ℝ) (W : ι → κ → ℂ) : ℝ :=
  (∑ i, θ i * s i) - ∑ k, ‖∑ i, θ i • W i k‖

/-- The constant quadratic loss from recentering at the `θ i * σ i` barycenter. -/
noncomputable def quadraticDiscount (θ σ : ι → ℝ) (Z : ι → E) (Q : QuadraticForm ℝ E) : ℝ :=
  ∑ i, (θ i * σ i) * Q (Z i - barycenter (fun j ↦ θ j * σ j) Z)

/-- Replacing the mixed norms by anchor projections and the mixed center by `Z₀`
gives this debit for each individual price. -/
noncomputable def anchorDebit (s : ι → ℝ) (W : ι → κ → ℂ) (σ : ι → ℝ) (Z : ι → E)
    (Q : QuadraticForm ℝ E) (γ : κ → ℂ) (Z₀ : E) (i : ι) : ℝ :=
  s i - (∑ k, (conj (γ k) * W i k).re) + σ i * Q (Z i - Z₀)

private theorem weighted_projection_le_norm (θ : ι → ℝ) (g : ℂ) (hg : ‖g‖ = 1)
    (w : ι → ℂ) : (∑ i, θ i * (conj g * w i).re) ≤ ‖∑ i, θ i • w i‖ := by
  let L := Complex.reLm.comp (LinearMap.mulLeft ℝ (conj g))
  change (∑ i, θ i • L (w i)) ≤ _
  calc
    (∑ i, θ i • L (w i)) = L (∑ i, θ i • w i) := by simp only [map_sum, map_smul]
    _ ≤ ‖conj g * ∑ i, θ i • w i‖ := Complex.re_le_norm _
    _ = ‖∑ i, θ i • w i‖ := by rw [Complex.norm_mul, Complex.norm_conj, hg, one_mul]

private theorem variance_le (Q : QuadraticForm ℝ E) (hQ : ∀ x, 0 ≤ Q x)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (Z : ι → E) (Z₀ : E) :
    (∑ i, w i * Q (Z i - barycenter w Z)) ≤ ∑ i, w i * Q (Z i - Z₀) := by
  let A := ∑ i, w i
  let C := barycenter w Z
  change (∑ i, w i * Q (Z i - C)) ≤ _
  by_cases hA : A = 0
  · -- Every recentering weight vanishes, regardless of the chosen center.
    have hw₀ (i : ι) : w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hw j)).mp hA i (Finset.mem_univ i)
    simp only [hw₀, zero_mul, Finset.sum_const_zero, le_refl]
  · have hcenter : A • C = ∑ i, w i • Z i := by
      change A • (A⁻¹ • ∑ i, w i • Z i) = _
      rw [smul_smul, mul_inv_cancel₀ hA, one_smul]
    have hcentered : ∑ i, w i • (Z i - C) = 0 := by
      rw [show (∑ i, w i • (Z i - C)) = (∑ i, w i • Z i) - A • C by
        simp only [smul_sub, Finset.sum_sub_distrib, A, Finset.sum_smul], hcenter, sub_self]
    -- The cross term in the quadratic expansion vanishes by linearity in `Z i - C`.
    have hpolar : ∑ i, w i * Q.polarBilin (Z i - C) (C - Z₀) = 0 := by
      let L := Q.polarBilin.flip (C - Z₀)
      change ∑ i, w i • L (Z i - C) = 0
      simp only [← map_smul, ← map_sum, hcentered, map_zero]
    have hexpand : (∑ i, w i * Q (Z i - Z₀)) =
        (∑ i, w i * Q (Z i - C)) + ∑ i, w i * Q (C - Z₀) := by
      calc
        (∑ i, w i * Q (Z i - Z₀)) = ∑ i,
            (w i * Q (Z i - C) + w i * Q (C - Z₀) +
              w i * Q.polarBilin (Z i - C) (C - Z₀)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [show Z i - Z₀ = (Z i - C) + (C - Z₀) by abel,
            show Q ((Z i - C) + (C - Z₀)) = _ from QuadraticMap.map_add Q _ _]
          simp only [QuadraticMap.polarBilin_apply_apply, mul_add]
        _ = _ := by simp only [Finset.sum_add_distrib, hpolar, add_zero]
    rw [hexpand]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (hQ _))

/-- The joint compression and recentering discount is at most the convex average of
individual anchor debits. Unit directions are sufficient; the source obtains them by
normalizing the nonzero anchor vectors at the shared keys. -/
theorem joint_discount_le_weighted_debit (θ s : ι → ℝ) (W : ι → κ → ℂ)
    (σ : ι → ℝ) (Z : ι → E) (Q : QuadraticForm ℝ E) (γ : κ → ℂ) (Z₀ : E)
    (hθ : ∀ i, 0 ≤ θ i) (_hθsum : ∑ i, θ i = 1) (hσ : ∀ i, 0 ≤ σ i)
    (hQ : ∀ x, 0 ≤ Q x) (hγ : ∀ k, ‖γ k‖ = 1) :
    diskDiscount θ s W + quadraticDiscount θ σ Z Q ≤
      ∑ i, θ i * anchorDebit s W σ Z Q γ Z₀ i := by
  have hdisk : (∑ i, θ i * ∑ k, (conj (γ k) * W i k).re) ≤
      ∑ k, ‖∑ i, θ i • W i k‖ := by
    calc
      (∑ i, θ i * ∑ k, (conj (γ k) * W i k).re) =
          ∑ k, ∑ i, θ i * (conj (γ k) * W i k).re := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦
        weighted_projection_le_norm θ (γ k) (hγ k) (fun i ↦ W i k)
  have hquad := variance_le Q hQ (fun i ↦ θ i * σ i) (fun i ↦ mul_nonneg (hθ i) (hσ i)) Z Z₀
  have hdebit : (∑ i, θ i * anchorDebit s W σ Z Q γ Z₀ i) =
      (∑ i, θ i * s i) - (∑ i, θ i * ∑ k, (conj (γ k) * W i k).re) +
        ∑ i, (θ i * σ i) * Q (Z i - Z₀) := by
    simp only [anchorDebit, mul_add, mul_sub, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  unfold diskDiscount quadraticDiscount
  rw [hdebit]
  exact add_le_add (sub_le_sub_left hdisk _) hquad

/-- At the same profile `H`, strict individual raw-minus-debit bounds imply the
same strict bound on the mixed raw evaluation minus the two discounts. Zero convex
coefficients are allowed: the weights summing to one guarantees one positive term. -/
theorem mixed_raw_sub_discount_gt (θ s : ι → ℝ) (W : ι → κ → ℂ)
    (σ : ι → ℝ) (Z : ι → E) (Q : QuadraticForm ℝ E) (γ : κ → ℂ) (Z₀ : E)
    (hθ : ∀ i, 0 ≤ θ i) (hθsum : ∑ i, θ i = 1) (hσ : ∀ i, 0 ≤ σ i)
    (hQ : ∀ x, 0 ≤ Q x) (hγ : ∀ k, ‖γ k‖ = 1)
    (P : ι → Profile → ℝ) (H : Profile) (L : ℝ)
    (hraw : ∀ i, L < P i H - anchorDebit s W σ Z Q γ Z₀ i) :
    L < (∑ i, θ i * P i H) - (diskDiscount θ s W + quadraticDiscount θ σ Z Q) := by
  have hpos : ∃ i, 0 < θ i := by
    by_contra! hn
    have hz (i : ι) : θ i = 0 := le_antisymm (hn i) (hθ i)
    simp only [hz, Finset.sum_const_zero, zero_ne_one] at hθsum
  obtain ⟨i, hi⟩ := hpos
  calc
    L = ∑ j, θ j * L := by rw [← Finset.sum_mul, hθsum, one_mul]
    _ < ∑ j, θ j * (P j H - anchorDebit s W σ Z Q γ Z₀ j) := by
      exact Finset.sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (hraw j).le (hθ j))
        ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hraw i) hi⟩
    _ = (∑ j, θ j * P j H) - ∑ j, θ j * anchorDebit s W σ Z Q γ Z₀ j := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ _ := sub_le_sub_left (joint_discount_le_weighted_debit θ s W σ Z Q γ Z₀
      hθ hθsum hσ hQ hγ) _

end AnchorMixtureDebit
