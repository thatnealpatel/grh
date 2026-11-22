module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Completeness of the Schwartz space on the real line

Each weighted derivative of a Cauchy filter converges in a bounded-continuous-function
space. The uniform limit theorem for derivatives identifies the unweighted limits as
successive derivatives of a single smooth function. The weighted limits identify its
Schwartz decay and give convergence in every Schwartz seminorm.
-/

open Filter SchwartzMap
open scoped SchwartzMap ContDiff Topology BoundedContinuousFunction

namespace Masullo

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def weightedIteratedDeriv (k n : ℕ) (f : 𝓢(ℝ, F)) : ℝ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ |x| ^ k • iteratedDeriv n f x)
    ((continuous_abs.pow k).smul
      (ContDiff.continuous_iteratedDeriv n (f.smooth ⊤) (mod_cast le_top)))
    (SchwartzMap.seminorm ℝ k n f) (fun x ↦ by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) k)]
        using f.le_seminorm' ℝ k n x)

private theorem weightedIteratedDeriv_apply (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    weightedIteratedDeriv k n f x = |x| ^ k • iteratedDeriv n f x := rfl

private theorem norm_weightedIteratedDeriv (k n : ℕ) (f : 𝓢(ℝ, F)) :
    ‖weightedIteratedDeriv k n f‖ = SchwartzMap.seminorm ℝ k n f := by
  have h (x : ℝ) : ‖weightedIteratedDeriv k n f x‖ = |x| ^ k * ‖iteratedDeriv n f x‖ := by
    rw [weightedIteratedDeriv_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine le_antisymm ?_ ?_
  · exact (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).2 fun x ↦
      (h x).trans_le (f.le_seminorm' ℝ k n x)
  · exact f.seminorm_le_bound' ℝ k n (norm_nonneg _) fun x ↦
      (h x).symm.trans_le (BoundedContinuousFunction.norm_coe_le_norm _ x)

private noncomputable def weightedIteratedDerivCLM (k n : ℕ) :
    𝓢(ℝ, F) →L[ℝ] (ℝ →ᵇ F) :=
  SchwartzMap.mkCLMtoNormedSpace (weightedIteratedDeriv k n)
    (fun f g ↦ by
      ext x
      change |x| ^ k • iteratedDeriv n ((f : ℝ → F) + (g : ℝ → F)) x = _
      rw [iteratedDeriv_add (f.contDiffAt n) (g.contDiffAt n), smul_add, add_apply, weightedIteratedDeriv_apply,
        weightedIteratedDeriv_apply])
    (fun c f ↦ by
      ext x
      change |x| ^ k • iteratedDeriv n (c • (f : ℝ → F)) x = _
      rw [iteratedDeriv_const_smul_field]
      exact smul_comm (|x| ^ k) c _)
    ⟨{(k, n)}, 1, zero_le_one, fun f ↦ by
      simp [norm_weightedIteratedDeriv, schwartzSeminormFamily_apply]⟩

/-- The ordinary Schwartz space on the real line with complete normed codomain
is complete in its Schwartz seminorm uniformity. -/
public theorem completeSpace_schwartzLine [CompleteSpace F] : CompleteSpace 𝓢(ℝ, F) := by
  classical
  refine ⟨fun {l} hl ↦ ?_⟩
  let : NeBot l := hl.1
  let A (k n : ℕ) := weightedIteratedDerivCLM (F := F) k n
  have hC (k n : ℕ) : ∃ g : ℝ →ᵇ F, Tendsto (A k n) l (𝓝 g) :=
    CompleteSpace.complete ((hl.map (A k n).uniformContinuous))
  choose g hg using hC
  have hx (k n : ℕ) (x : ℝ) :
      Tendsto (fun f : 𝓢(ℝ, F) ↦ |x| ^ k • iteratedDeriv n f x) l (𝓝 (g k n x)) :=
    ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto (g k n)).comp (hg k n)
  have hweight (k n : ℕ) (x : ℝ) : g k n x = |x| ^ k • g 0 n x := by
    apply tendsto_nhds_unique (hx k n x)
    simpa only [pow_zero, one_smul, Function.comp_def] using
      ((continuous_const_smul (|x| ^ k)).tendsto (g 0 n x)).comp (hx 0 n x)
  have hunif (n : ℕ) : TendstoUniformly (fun f : 𝓢(ℝ, F) ↦ iteratedDeriv n f) (g 0 n) l := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hg 0 n)
    convert h using 1
    funext f x
    change iteratedDeriv n f x = |x| ^ 0 • iteratedDeriv n f x
    rw [pow_zero, one_smul]
  have hderiv (n : ℕ) (x : ℝ) : HasDerivAt (g 0 n) (g 0 (n + 1) x) x := by
    refine hasDerivAt_of_tendstoUniformly (hunif (n + 1)) ?_ (hunif n).tendsto_at x
    refine Eventually.of_forall fun f y ↦ ?_
    rw [iteratedDeriv_succ]
    exact ((f.smooth ⊤).differentiable_iteratedDeriv n
      (by exact_mod_cast ENat.natCast_lt_top n) y).hasDerivAt
  have hit (n : ℕ) : iteratedDeriv n (g 0 0) = g 0 n := by
    induction n with
    | zero => rw [iteratedDeriv_zero]
    | succ n ih => rw [iteratedDeriv_succ, ih]; exact funext fun x ↦ (hderiv n x).deriv
  have hs : ContDiff ℝ ∞ (g 0 0) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [hit]
    exact fun x ↦ (hderiv n x).differentiableAt
  let f : 𝓢(ℝ, F) :=
    { toFun := g 0 0
      smooth' := hs
      decay' := fun k n ↦ ⟨‖g k n‖, fun x ↦ by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit, Real.norm_eq_abs]
        convert BoundedContinuousFunction.norm_coe_le_norm (g k n) x using 1
        rw [hweight k n x, norm_smul, Real.norm_of_nonneg (by positivity)]⟩ }
  have hf (k n : ℕ) : A k n f = g k n := by
    ext x
    change |x| ^ k • iteratedDeriv n (g 0 0) x = g k n x
    rw [hit, hweight k n x]
  refine ⟨f, (schwartz_withSeminorms ℝ ℝ F).tendsto_nhds id f |>.2 ?_⟩
  rintro ⟨k, n⟩ ε hε
  have h := (tendsto_iff_norm_sub_tendsto_zero.1 (hg k n)).eventually (gt_mem_nhds hε)
  simpa only [schwartzSeminormFamily_apply, id_eq, ← norm_weightedIteratedDeriv,
    ← show ∀ f, A k n f = weightedIteratedDeriv k n f from fun _ ↦ rfl,
    map_sub, hf] using h

end Masullo
