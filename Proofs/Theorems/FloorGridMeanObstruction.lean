module

public import Lemmas.FloorGridLevels
public import Lemmas.FloorGridLocalSplit
public import Lemmas.FloorGridPhaseMean
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The two-leg phase mean on the rational floor grids

The detail spaces use the whole-line weighted metric. The phase mean, in
contrast, is the flat average over one phase period. Its Riesz vector on
one finite level need not be bounded as the levels increase.
-/

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace ContDiff

namespace Masullo

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Ambient vector representing `L` on `S` only. -/
private noncomputable def levelVector (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    (L : E →L[ℝ] ℝ) : E := S.starProjection ((InnerProductSpace.toDual ℝ E).symm L)

private theorem levelVector_mem (S : Submodule ℝ E) [FiniteDimensional ℝ S] (L : E →L[ℝ] ℝ) :
    levelVector S L ∈ S := S.starProjection_apply_mem _

private theorem levelVector_inner (S : Submodule ℝ E) [FiniteDimensional ℝ S] (L : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ S) : ⟪levelVector S L, x⟫ = L x := by
  let u : S := ⟨x, hx⟩
  exact (S.inner_orthogonalProjectionOnto_eq_of_mem_right u _).trans
    InnerProductSpace.toDual_symm_apply

/-- Parseval on the detail, using agreement of the two means only on the old level. -/
private theorem detail_sum_sq {S V : Submodule ℝ E} [FiniteDimensional ℝ S] [FiniteDimensional ℝ V]
    (hSV : S ≤ V) (L M : E →L[ℝ] ℝ) (hLM : ∀ x ∈ S, L x = M x)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ (V ⊓ Sᗮ : Submodule ℝ E)) :
    ∑ i, M (B i : E) ^ 2 = ‖levelVector V M‖ ^ 2 - ‖levelVector S L‖ ^ 2 := by
  let s := levelVector S L
  let v := levelVector V M
  have hs : s ∈ S := levelVector_mem _ _
  have hv : v ∈ V := levelVector_mem _ _
  have hd : v - s ∈ Sᗮ := (S.mem_orthogonal' _).2 fun x hx ↦ by
    rw [inner_sub_left, levelVector_inner V M (hSV hx), levelVector_inner S L hx, hLM x hx, sub_self]
  let d : (V ⊓ Sᗮ : Submodule ℝ E) := ⟨v - s, V.sub_mem hv (hSV hs), hd⟩
  have hdiag (i : ι) : M (B i : E) = ⟪d, B i⟫ := by
    change M (B i : E) = ⟪v - s, (B i : E)⟫
    rw [inner_sub_left, (S.mem_orthogonal _).1 (B i).property.2 s hs, sub_zero]
    exact (levelVector_inner V M (B i).property.1).symm
  simp_rw [hdiag]
  rw [B.sum_sq_inner_left]
  change ‖v - s‖ ^ 2 = ‖v‖ ^ 2 - ‖s‖ ^ 2
  have hperp := (S.mem_orthogonal' _).1 hd s hs
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hperp
  rw [norm_sub_sq_real]; linarith

end Hilbert

local notation "H" => Lp ℝ 2 (volume : Measure ℝ)

variable (a : ℝ) (ha : a < 1 / 2)

/-- New directions at one refinement in the absorbed physical metric. -/
public noncomputable abbrev floorGridDetail (j : ℕ) : Submodule ℝ H :=
  floorGridLevel a ha (j + 1) ⊓ (floorGridLevel a ha j)ᗮ

/-- The actual terminal projection increment, not a residual of unnormalized columns. -/
public theorem floorGridDetail_projection (j : ℕ) (x : H) :
    (floorGridDetail a ha j).starProjection x =
      (floorGridLevel a ha (j + 1)).starProjection x - (floorGridLevel a ha j).starProjection x := by
  let S := floorGridLevel a ha j
  let V := floorGridLevel a ha (j+1)
  have hSV : S ≤ V := floorGridLevel_le_succ a ha j
  have hV : x - V.starProjection x ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hS : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨V.sub_mem (V.starProjection_apply_mem x) (hSV (S.starProjection_apply_mem x)), ?_⟩
    change V.starProjection x - S.starProjection x ∈ Sᗮ
    rw [show V.starProjection x - S.starProjection x =
      (x - S.starProjection x) - (x - V.starProjection x) by abel]
    exact (Sᗮ).sub_mem hS (Submodule.orthogonal_le hSV hV)
  · apply ((floorGridDetail a ha j).mem_orthogonal' _).2
    intro u hu
    have h₁ := (V.mem_orthogonal' _).1 hV u hu.1
    have h₂ := (S.mem_orthogonal _).1 hu.2 _ (S.starProjection_apply_mem x)
    change ⟪x - (V.starProjection x - S.starProjection x), u⟫ = 0
    rw [inner_sub_left] at h₁
    rw [inner_sub_left, inner_sub_left]; linarith

/-- The finite-level squared norm of the flat mean in the physical metric. -/
public noncomputable def floorGridMeanEnergy (j : ℕ) : ℝ :=
  ‖levelVector (floorGridLevel a ha j) (floorGridPhaseMean a j)‖ ^ 2

private theorem phaseMean_agrees {j J : ℕ} (h : j ≤ J) :
    ∀ x ∈ floorGridLevel a ha j, floorGridPhaseMean a j x = floorGridPhaseMean a J x := by
  change floorGridLevel a ha j ≤ LinearMap.eqLocus
    (floorGridPhaseMean a j).toLinearMap (floorGridPhaseMean a J).toLinearMap
  apply (floorGridLevel_le_iff a ha j _).2
  intro k _ _
  exact (floorGridPhaseMean_column a ha j j k le_rfl).trans
    (floorGridPhaseMean_column a ha j J k h).symm

/-- The index-two test has fixed mean but vanishing physical norm. -/
public theorem tendsto_floorGridMeanEnergy : Tendsto (floorGridMeanEnergy a ha) atTop atTop := by
  let t (j : ℕ) := levelVector (floorGridLevel a ha j) (floorGridPhaseMean a j)
  have ht : Tendsto (fun j ↦ ‖t j‖) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    let C := max b 1
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right ..)
    have he := (tendsto_floorGridColumn_two_norm a ha).eventually_lt_const
      (show 0 < (1/2 : ℝ) / C by positivity)
    filter_upwards [he, eventually_ge_atTop 1] with j hj hj₁
    have hcol := floorGridColumn_two_mem_floorGridLevel a ha hj₁
    have hcs := real_inner_le_norm (t j) (floorGridColumn a ha j 2)
    rw [show ⟪t j, floorGridColumn a ha j 2⟫ = 1/2 from
      (levelVector_inner _ _ hcol).trans (floorGridPhaseMean_column_two a ha j j le_rfl)] at hcs
    by_contra! hsmall
    have hbound := mul_le_mul_of_nonneg_right (hsmall.le.trans (le_max_left b 1))
      (norm_nonneg (floorGridColumn a ha j 2))
    have hlt := (lt_div_iff₀ hC).1 hj
    linarith [mul_comm C ‖floorGridColumn a ha j 2‖]
  change Tendsto (fun j ↦ ‖t j‖ ^ 2) atTop atTop
  simpa only [sq] using ht.atTop_mul_atTop₀ ht

/-- The sum of the literal mean–mean convolution pairings on *any* physical detail basis. -/
public theorem floorGridDetail_meanPair_sum {ρ b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) (j : ℕ) {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ (floorGridDetail a ha j)) :
    ∑ i, floorGridMeanPair a ρ b (floorGridPhaseMean a (j+1) (B i : H)) =
      floorGridMeanCoeff a ρ b * (floorGridMeanEnergy a ha (j+1) - floorGridMeanEnergy a ha j) := by
  simp_rw [floorGridMeanPair_eq a ρ _ hb hcb]
  rw [← Finset.mul_sum]
  exact congrArg _ (detail_sum_sq (floorGridLevel_le_succ a ha j) _ _
    (phaseMean_agrees a ha (Nat.le_succ j)) B)

/-- Matrix of the cutoff convolution tested on a physical detail basis. In particular,
the two occurrences of `floorGridPhysicalProfile` undo the absorbed weight before convolution. -/
@[expose] public noncomputable def floorGridDetailMatrix (ρ b : ℝ → ℝ) (j : ℕ)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ (floorGridDetail a ha j)) : Matrix ι ι ℝ :=
  fun i l ↦ ∫ x, ρ x * floorGridMeanWeight a x * floorGridPhysicalProfile a (B i : H) x *
    (∫ z, deriv b z * floorGridPhysicalProfile a (B l : H) (x - z))

/-- Exact finite trace split. No trace-class limit is assumed: The second summand
still includes both mixed terms as well as the centered–centered term. -/
public theorem floorGridDetail_trace_split {ρ b : ℝ → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (hb : ContDiff ℝ 1 b) (hcb : HasCompactSupport b) (j : ℕ)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ (floorGridDetail a ha j)) :
    (floorGridDetailMatrix a ha ρ b j B).trace =
      floorGridMeanCoeff a ρ b * (floorGridMeanEnergy a ha (j+1) - floorGridMeanEnergy a ha j) +
        ∑ i, floorGridCenteredPair a ρ b (B i : H) (floorGridPhaseMean a (j+1) (B i : H)) := by
  change (∑ i, floorGridFullPair a ρ b (B i : H)) = _
  rw [← floorGridDetail_meanPair_sum a ha hb hcb j B, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ floorGridFullPair_split a (B i : H) _ hρ hcρ hb hcb

/-- Sum the two-leg contributions on an orthonormal basis of each detail from `j` to `j+n`.
The basis choice is immaterial by `floorGridDetail_meanPair_sum`. -/
@[expose] public noncomputable def floorGridMeanPartial (ρ b : ℝ → ℝ) (j n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ∑ i, floorGridMeanPair a ρ b (floorGridPhaseMean a (j+k+1)
    (stdOrthonormalBasis ℝ (floorGridDetail a ha (j+k)) i : H))

/-- Exact telescoping before any position or level limit. -/
public theorem floorGridMeanPartial_eq (ρ : ℝ → ℝ) {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) (j n : ℕ) :
    floorGridMeanPartial a ha ρ b j n = floorGridMeanCoeff a ρ b *
      (floorGridMeanEnergy a ha (j+n) - floorGridMeanEnergy a ha j) := by
  unfold floorGridMeanPartial
  simp_rw [floorGridDetail_meanPair_sum a ha hb hcb, ← Finset.mul_sum]
  simpa only [Nat.add_assoc, Nat.add_zero] using congrArg (floorGridMeanCoeff a ρ b * ·)
    (Finset.sum_range_sub (fun k ↦ floorGridMeanEnergy a ha (j+k)) n)

/-- For the derivative probe the separated mean–mean sums tend to minus infinity,
even with fixed cutoff and starting level. -/
public theorem tendsto_floorGridMeanPartial_atBot {ρ b : ℝ → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hρ₀ : 0 ≤ ρ) (hρne : ρ ≠ 0)
    (hb : ContDiff ℝ 1 b) (hcb : HasCompactSupport b) (hb₀ : 0 ≤ b) (hbne : b ≠ 0) (j : ℕ) :
    Tendsto (floorGridMeanPartial a ha ρ b j) atTop atBot := by
  have h := (tendsto_floorGridMeanEnergy a ha).comp (tendsto_add_atTop_nat j)
  have hd := tendsto_atTop_add_const_right _ (-(floorGridMeanEnergy a ha j)) h
  have hn := floorGridMeanCoeff_neg a hρ hcρ hρ₀ hρne hb.continuous hcb hb₀ hbne
  change Tendsto (fun n ↦ floorGridMeanPartial a ha ρ b j n) atTop atBot
  simpa only [floorGridMeanPartial_eq a ha ρ hb hcb, Function.comp_apply, Nat.add_comm j,
    sub_eq_add_neg] using hd.const_mul_atTop_of_neg hn

/-- One admissible bump used also as cutoff refutes separate convergence at every
fixed width, however small, and from every starting level. -/
public theorem exists_floorGridMeanPartial_counterexample :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Set.Ioo 0 (Real.log 2) ∧ 0 ≤ b ∧ b ≠ 0 ∧ (∫ z, deriv b z) = 0 ∧
      ∀ (a : ℝ) (ha : a < 1 / 2) (j : ℕ),
        Tendsto (floorGridMeanPartial a ha b b j) atTop atBot := by
  obtain ⟨b, hb, hcb, hs, h₀, hne⟩ := exists_floorGridMeanBump
  have hb₁ : ContDiff ℝ 1 b := hb.of_le (by simp)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun z ↦ (hb₁.differentiable one_ne_zero z).hasDerivAt)
    (hb₁.continuous_deriv_one.integrable_of_hasCompactSupport hcb.deriv)
    (hb.continuous.integrable_of_hasCompactSupport hcb)
  exact ⟨b, hb, hcb, hs, h₀, hne, hzero, fun a ha j ↦ tendsto_floorGridMeanPartial_atBot a ha
    hb.continuous hcb h₀ hne hb₁ hcb h₀ hne j⟩

end Masullo
