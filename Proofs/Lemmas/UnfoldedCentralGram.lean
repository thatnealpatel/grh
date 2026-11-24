module

public import Lemmas.ThreeSiteMomentCompletion
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The unfolded three-site central Gram solve

Source: `3042a1a9262e:.godel/bob/unfolded-deletion-33.md:24–35`.
Consumer: `c6f94db30246:.godel/bob/priced-deletion-33.md:23–29`.
Owning check session: `01a20db3-6987-747d-9d8d-903a502adedd`.

Scope: for a measurable first field with a strict almost-everywhere norm bound under
`unfoldedMeasure`, the real convolution matrix `R_(j-i)` on `{-1, 0, 1}` at spacing
`13/25` dominates `(1 - β²)` times the unweighted Gram matrix and is positive definite.
It gives one exact real central correction for every real residual. This does not assert a
global bound on the corrected Laurent multiplier or verify any numerical certificate.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace Masullo.ThreeSiteMomentCompletion

/-- The three signed indices of the unfolded completion. -/
public abbrev CentralSite := ↥(Finset.Icc (-1 : ℤ) 1)

/-- The matrix of the actual disk-radius replies, row `j` and column `i`. -/
@[expose] public noncomputable def unfoldedCentralGram (m : ℝ → ℂ) :
    Matrix CentralSite CentralSite ℝ :=
  Matrix.of fun j i ↦ radiusReply unfoldedMeasure m (13 / 25) ((j : ℤ) - (i : ℤ))

/-- The squared modulus of the real-coefficient central Laurent sum, at angle `θ`,
written as the sum of squares of its cosine and sine components. -/
@[expose] public noncomputable def centralEnergy (v : CentralSite → ℝ) (θ : ℝ) : ℝ :=
  (∑ i, v i * Real.cos (((i : ℤ) : ℝ) * θ)) ^ 2 +
    (∑ i, v i * Real.sin (((i : ℤ) : ℝ) * θ)) ^ 2

private theorem centralEnergy_nonneg (v : CentralSite → ℝ) (θ : ℝ) :
    0 ≤ centralEnergy v θ :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem weightedEnergy_eq_sum (m : ℝ → ℂ) (v : CentralSite → ℝ) (x : ℝ) :
    centralEnergy v ((13 / 25) * x) * (1 - ‖m x‖ ^ 2) =
      ∑ j, ∑ i, v j * (v i * (Real.cos ((((j : ℤ) - (i : ℤ) : ℤ) : ℝ) * (13 / 25) * x) *
        (1 - ‖m x‖ ^ 2))) := by
  have hcos (j i : CentralSite) :
      Real.cos ((((j : ℤ) - (i : ℤ) : ℤ) : ℝ) * (13 / 25) * x) =
        Real.cos (((j : ℤ) : ℝ) * ((13 / 25) * x)) *
          Real.cos (((i : ℤ) : ℝ) * ((13 / 25) * x)) +
        Real.sin (((j : ℤ) : ℝ) * ((13 / 25) * x)) *
          Real.sin (((i : ℤ) : ℝ) * ((13 / 25) * x)) := by
    rw [Int.cast_sub, mul_assoc, sub_mul, Real.cos_sub]
  simp only [centralEnergy, pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    hcos]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring

private theorem unfoldedMeasure_finite : IsFiniteMeasure unfoldedMeasure := by
  rw [unfoldedMeasure_eq_cauchy]
  infer_instance

private theorem unfoldedMeasure_openPos : unfoldedMeasure.IsOpenPosMeasure := by
  have hscale : (1 / 2 : NNReal) ≠ 0 := by norm_num
  have hs : {x : ℝ | ProbabilityTheory.cauchyPDF 0 (1 / 2) x ≠ 0} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, ProbabilityTheory.cauchyPDF_def,
      ENNReal.ofReal_ne_zero_iff]
    exact ProbabilityTheory.cauchyPDF_pos 0 hscale x
  refine ⟨fun U hU hn hnull ↦ ?_⟩
  rw [unfoldedMeasure_eq_cauchy, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 hscale,
    withDensity_apply_eq_zero (ProbabilityTheory.measurable_cauchyPDF 0 _), hs,
    Set.univ_inter] at hnull
  exact (hU.measure_pos volume hn).ne' hnull

private theorem integrable_radiusIntegrand {m : ℝ → ℂ} (hm : Measurable m)
    (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ 1) (d : ℤ) :
    Integrable (fun x ↦ Real.cos ((d : ℝ) * (13 / 25) * x) * (1 - ‖m x‖ ^ 2))
      unfoldedMeasure := by
  let := unfoldedMeasure_finite
  have hf : Measurable (fun x ↦ Real.cos ((d : ℝ) * (13 / 25) * x) * (1 - ‖m x‖ ^ 2)) := by
    fun_prop
  refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
  filter_upwards [hb] with x hx
  have hs := (sq_le_sq₀ (norm_nonneg (m x)) zero_le_one).2 hx
  rw [one_pow] at hs
  have hr : 0 ≤ 1 - ‖m x‖ ^ 2 := sub_nonneg.mpr hs
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_of_le_one_left hr (Real.abs_cos_le_one _)).trans (sub_le_self _ (sq_nonneg _))

private theorem integrable_weightedEnergy {m : ℝ → ℂ} (hm : Measurable m)
    (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ 1) (v : CentralSite → ℝ) :
    Integrable (fun x ↦ centralEnergy v ((13 / 25) * x) * (1 - ‖m x‖ ^ 2)) unfoldedMeasure := by
  simp_rw [weightedEnergy_eq_sum]
  exact integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun i _ ↦
    ((integrable_radiusIntegrand hm hb ((j : ℤ) - (i : ℤ))).const_mul (v i)).const_mul (v j)

/-- Quadratic form of the actual `radiusReply` matrix, with no rescaling of the measure. -/
public theorem unfoldedCentralGram_quadratic_eq_integral {m : ℝ → ℂ} (hm : Measurable m)
    (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ 1) (v : CentralSite → ℝ) :
    v ⬝ᵥ (unfoldedCentralGram m *ᵥ v) =
      ∫ x, centralEnergy v ((13 / 25) * x) * (1 - ‖m x‖ ^ 2) ∂unfoldedMeasure := by
  have hterm (j i : CentralSite) :=
    ((integrable_radiusIntegrand hm hb ((j : ℤ) - (i : ℤ))).const_mul (v i)).const_mul (v j)
  symm
  simp_rw [weightedEnergy_eq_sum]
  rw [integral_finsetSum Finset.univ fun j _ ↦
    integrable_finsetSum Finset.univ fun i _ ↦ hterm j i]
  simp only [dotProduct, mulVec, Finset.mul_sum, unfoldedCentralGram, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun i _ ↦ hterm j i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, radiusReply, mul_comm (v i)]

private theorem norm_zero_le_one : ∀ᵐ x ∂unfoldedMeasure, ‖(fun _ : ℝ ↦ (0 : ℂ)) x‖ ≤ 1 :=
  ae_of_all _ fun _ ↦ by simp

private theorem integrable_unweightedEnergy (v : CentralSite → ℝ) :
    Integrable (fun x ↦ centralEnergy v ((13 / 25) * x)) unfoldedMeasure := by
  simpa using integrable_weightedEnergy measurable_const norm_zero_le_one v

private theorem unweighted_quadratic_eq (v : CentralSite → ℝ) :
    v ⬝ᵥ (unfoldedCentralGram (fun _ ↦ 0) *ᵥ v) =
      ∫ x, centralEnergy v ((13 / 25) * x) ∂unfoldedMeasure := by
  simpa using unfoldedCentralGram_quadratic_eq_integral measurable_const norm_zero_le_one v

/-- On every real vector the weighted form dominates `1 - β²` times its unweighted form.
The zero first field in the latter form makes its disk radius identically one. -/
public theorem unfoldedCentralGram_quadratic_lower {m : ℝ → ℂ} (hm : Measurable m)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ β)
    (v : CentralSite → ℝ) :
    (1 - β ^ 2) * (v ⬝ᵥ (unfoldedCentralGram (fun _ ↦ 0) *ᵥ v)) ≤
      v ⬝ᵥ (unfoldedCentralGram m *ᵥ v) := by
  have hb₁ := hb.mono fun _ hx ↦ hx.trans hβ₁.le
  rw [unweighted_quadratic_eq, unfoldedCentralGram_quadratic_eq_integral hm hb₁,
    ← integral_const_mul]
  refine integral_mono_ae ((integrable_unweightedEnergy v).const_mul _)
    (integrable_weightedEnergy hm hb₁ v) ?_
  filter_upwards [hb] with x hx
  rw [mul_comm (1 - β ^ 2)]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left ((sq_le_sq₀ (norm_nonneg _) hβ₀).2 hx) 1)
    (centralEnergy_nonneg _ _)

private def siteOfFin (i : Fin 3) : CentralSite :=
  ⟨(i.val : ℤ) - 1, Finset.mem_Icc.mpr (by have := i.isLt; omega)⟩

private noncomputable def siteEquiv : Fin 3 ≃ CentralSite :=
  Equiv.ofBijective siteOfFin ⟨by
    intro i j hij
    have he : (i.val : ℤ) - 1 = (j.val : ℤ) - 1 := congrArg Subtype.val hij
    exact Fin.ext (by omega), by
    intro j
    have hj := Finset.mem_Icc.mp j.property
    let k := ((j : ℤ) + 1).toNat
    have hk : k < 3 := by dsimp [k]; omega
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    change (k : ℤ) - 1 = (j : ℤ)
    dsimp [k]
    omega⟩

@[simp] private theorem siteEquiv_zero : (siteEquiv 0 : ℤ) = -1 := rfl
@[simp] private theorem siteEquiv_one : (siteEquiv 1 : ℤ) = 0 := rfl
@[simp] private theorem siteEquiv_two : (siteEquiv 2 : ℤ) = 1 := rfl

private theorem sum_centralSite (f : CentralSite → ℝ) :
    ∑ i, f i = f (siteEquiv 0) + f (siteEquiv 1) + f (siteEquiv 2) := by
  rw [← Fintype.sum_equiv siteEquiv (fun i ↦ f (siteEquiv i)) f (fun _ ↦ rfl), Fin.sum_univ_three]

-- At angles 0, π and π/2, vanishing gives respectively the sum of all coefficients,
-- the middle coefficient minus the two outer ones, and the difference of the outer ones.
private theorem centralEnergy_nonzero {v : CentralSite → ℝ} (hv : v ≠ 0) :
    ∃ θ : ℝ, centralEnergy v θ ≠ 0 := by
  by_contra! h
  have hparts (θ : ℝ) :
      (∑ i, v i * Real.cos (((i : ℤ) : ℝ) * θ)) = 0 ∧
        (∑ i, v i * Real.sin (((i : ℤ) : ℝ) * θ)) = 0 := by
    have hsum := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp (h θ)
    exact ⟨sq_eq_zero_iff.mp hsum.1, sq_eq_zero_iff.mp hsum.2⟩
  have h₀ : v (siteEquiv 0) + v (siteEquiv 1) + v (siteEquiv 2) = 0 := by
    have h₀ := (hparts 0).1
    rw [sum_centralSite] at h₀
    simpa using h₀
  have hπ : -(v (siteEquiv 0)) + v (siteEquiv 1) - v (siteEquiv 2) = 0 := by
    have hπ := (hparts Real.pi).1
    rw [sum_centralSite] at hπ
    simpa [sub_eq_add_neg] using hπ
  have hπ₂ : -(v (siteEquiv 0)) + v (siteEquiv 2) = 0 := by
    have hπ₂ := (hparts (Real.pi / 2)).2
    rw [sum_centralSite] at hπ₂
    simpa using hπ₂
  have hv₀ : v (siteEquiv 0) = 0 := by linarith only [h₀, hπ, hπ₂]
  have hv₁ : v (siteEquiv 1) = 0 := by linarith only [h₀, hπ, hπ₂]
  have hv₂ : v (siteEquiv 2) = 0 := by linarith only [h₀, hπ, hπ₂]
  apply hv
  funext j
  obtain ⟨i, rfl⟩ := siteEquiv.surjective j
  change v (siteEquiv i) = 0
  fin_cases i <;> assumption

private theorem unweighted_quadratic_pos {v : CentralSite → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (unfoldedCentralGram (fun _ ↦ 0) *ᵥ v) := by
  let := unfoldedMeasure_openPos
  rw [unweighted_quadratic_eq]
  refine (integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x ↦ centralEnergy_nonneg v _)
    (integrable_unweightedEnergy v)).mpr ?_
  have hc : Continuous (fun x : ℝ ↦ centralEnergy v ((13 / 25) * x)) := by
    unfold centralEnergy
    fun_prop
  obtain ⟨θ, hθ⟩ := centralEnergy_nonzero hv
  refine hc.isOpen_support.measure_pos unfoldedMeasure ⟨θ / (13 / 25), ?_⟩
  change centralEnergy v ((13 / 25) * (θ / (13 / 25))) ≠ 0
  rwa [mul_div_cancel₀ θ (by norm_num)]

/-- Positive definiteness of the weighted, real three-site convolution matrix. -/
public theorem unfoldedCentralGram_posDef {m : ℝ → ℂ} (hm : Measurable m)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ β) :
    (unfoldedCentralGram m).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext j i
    rw [Matrix.conjTranspose_apply, star_trivial]
    change radiusReply unfoldedMeasure m (13 / 25) ((i : ℤ) - (j : ℤ)) =
      radiusReply unfoldedMeasure m (13 / 25) ((j : ℤ) - (i : ℤ))
    rw [show (i : ℤ) - (j : ℤ) = -((j : ℤ) - (i : ℤ)) by omega]
    simp only [radiusReply, Int.cast_neg, neg_mul, Real.cos_neg]
  · intro v hv
    have hβ : 0 < 1 - β ^ 2 := sub_pos.mpr (by simpa using (sq_lt_sq₀ hβ₀ zero_le_one).mpr hβ₁)
    simpa only [star_trivial] using (mul_pos hβ (unweighted_quadratic_pos hv)).trans_le
      (unfoldedCentralGram_quadratic_lower hm hβ₀ hβ₁ hb v)

/-- A row of the Gram system is the original convolution at that signed site. -/
public theorem unfoldedCentralGram_mulVec_apply (m : ℝ → ℂ) (v : CentralSite → ℝ)
    (j : CentralSite) :
    (unfoldedCentralGram m *ᵥ v) j =
      ∑ i : CentralSite, v i * radiusReply unfoldedMeasure m (13 / 25) ((j : ℤ) - (i : ℤ)) := by
  simp only [mulVec, dotProduct, unfoldedCentralGram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Every real residual on the three signed sites has exactly one real central correction. -/
public theorem existsUnique_unfolded_centralCorrection {m : ℝ → ℂ} (hm : Measurable m)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ β)
    (r : CentralSite → ℝ) :
    ∃! v : CentralSite → ℝ, ∀ j : CentralSite,
      (∑ i : CentralSite, v i * radiusReply unfoldedMeasure m (13 / 25) ((j : ℤ) - (i : ℤ))) =
        r j := by
  let A := (unfoldedCentralGram m).mulVecLin
  have hinj : Function.Injective A := (injective_iff_map_eq_zero A).mpr fun v hv ↦ by
    by_contra hv₀
    have hpos := (unfoldedCentralGram_posDef hm hβ₀ hβ₁ hb).dotProduct_mulVec_pos hv₀
    change unfoldedCentralGram m *ᵥ v = 0 at hv
    rw [hv, dotProduct_zero] at hpos
    exact (lt_irrefl _) hpos
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) r
  have heq (w : CentralSite → ℝ) : (∀ j : CentralSite,
      (∑ i : CentralSite, w i * radiusReply unfoldedMeasure m (13 / 25) ((j : ℤ) - (i : ℤ))) =
        r j) ↔ A w = r := by
    rw [funext_iff]
    simp only [A, Matrix.mulVecLin_apply, unfoldedCentralGram_mulVec_apply]
  exact ⟨v, (heq v).mpr hv, fun w hw ↦ hinj (((heq w).mp hw).trans hv.symm)⟩

/-- Adding a correction only at the three central indices makes the existing unfolded
completion convolution hold exactly. The finite baseline range must contain those indices
(as does `Finset.Icc (-192) 192`); no bound on the corrected multiplier is asserted. -/
public theorem existsUnique_unfolded_centralCompletion {m : ℝ → ℂ} (hm : Measurable m)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hb : ∀ᵐ x ∂unfoldedMeasure, ‖m x‖ ≤ β)
    (K : Finset ℤ) (hK : Finset.Icc (-1 : ℤ) 1 ⊆ K) (v₀ : ℤ → ℝ) :
    ∃! δ : CentralSite → ℝ, ∀ j ∈ Finset.Icc (-1 : ℤ) 1,
      (∑ k ∈ K, (v₀ k + (if hk : k ∈ Finset.Icc (-1 : ℤ) 1 then δ ⟨k, hk⟩ else 0)) *
        radiusReply unfoldedMeasure m (13 / 25) (j - k)) =
        centerReply unfoldedMeasure m (6 / 25) (13 / 25) j := by
  let S := Finset.Icc (-1 : ℤ) 1
  let R := radiusReply unfoldedMeasure m (13 / 25)
  let T := centerReply unfoldedMeasure m (6 / 25) (13 / 25)
  let extend (δ : CentralSite → ℝ) (k : ℤ) := if hk : k ∈ S then δ ⟨k, hk⟩ else 0
  let r (j : CentralSite) := T j - ∑ k ∈ K, v₀ k * R ((j : ℤ) - k)
  change ∃! δ : CentralSite → ℝ, ∀ j ∈ S,
    (∑ k ∈ K, (v₀ k + extend δ k) * R (j - k)) = T j
  refine (existsUnique_congr ?_).mp (existsUnique_unfolded_centralCorrection hm hβ₀ hβ₁ hb r)
  intro δ
  have hδ (j : ℤ) : (∑ k ∈ K, extend δ k * R (j - k)) =
      ∑ i : CentralSite, δ i * R (j - (i : ℤ)) := by
    calc
      _ = ∑ k ∈ S, extend δ k * R (j - k) := by
        symm
        refine Finset.sum_subset hK fun k _ hk ↦ ?_
        simp only [extend, dite_eq_right hk, zero_mul]
      _ = _ := by
        rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [show extend δ (i : ℤ) = δ i by
          unfold extend
          rw [dite_eq_left i.property]]
  have hsum (j : ℤ) : (∑ k ∈ K, (v₀ k + extend δ k) * R (j - k)) =
      (∑ k ∈ K, v₀ k * R (j - k)) + ∑ i : CentralSite, δ i * R (j - (i : ℤ)) := by
    simp only [add_mul, Finset.sum_add_distrib, hδ]
  change (∀ j : CentralSite, (∑ i : CentralSite, δ i * R ((j : ℤ) - (i : ℤ))) = r j) ↔ _
  constructor
  · intro h j hj
    rw [hsum, add_comm]
    exact eq_sub_iff_add_eq.mp (h ⟨j, hj⟩)
  · intro h j
    apply eq_sub_iff_add_eq.mpr
    rw [← add_comm, ← hsum]
    exact h j j.property

end Masullo.ThreeSiteMomentCompletion
