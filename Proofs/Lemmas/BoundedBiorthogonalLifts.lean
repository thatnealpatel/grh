module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Bounded biorthogonal lifts need not be Schauder basic

In the Schauder case of Masullo, *The Music of the Primes*, Lemma 10.4.2.5,
printed/PDF pp. 461–462, the pointwise choices establish (10.4.2.17)–(18).
They do not make the chosen lifts a Schauder basis of their **norm-closed** span.
The example below has norm-one quotient vectors and norm-one lifts. Take the
manuscript's `F` to be the whole space, so `F₀ = E₀` and `F/F₀ = E/E₀`, and take
`r = 1`, `r' = 5/4`, `ε = 1/4`. No kernel corrections to the lifts are needed
for the estimates in the proof. The averages of the lifts approximate a
nonzero kernel vector, on which every pulled-back coefficient is zero.
The pulled-back functionals even form a Schauder basis of their own
norm-closed linear span: adjoints of the standard coordinate truncations on
`ℓ²` are contractions and are eventually the identity on each finite
combination of coordinates. This convergence extends to their norm-closed
span in the dual and transports isometrically under pullback by the quotient
map. It does not give convergence on the primal closed span of the lifts.
(This dual-space observation is not formalized below.)

This refutes the inference about the selected sequence, not the existential
assertion that there are good lifts. In this example `(eₙ, 0)` are good lifts.
-/

open scoped lp

noncomputable section

namespace Masullo.BoundedBiorthogonalLifts

public abbrev H := ℓ²(ℕ, ℂ)
public abbrev E := H × ℂ

private def first : E →L[ℂ] H := ContinuousLinearMap.fst ℂ H ℂ

/-- The closed subspace by which we quotient. -/
public def E₀ : Submodule ℂ E := first.ker

public instance : IsClosed (E₀ : Set E) := first.isClosed_ker

/-- The quotient map for `E₀`. -/
@[expose] public def q : E →L[ℂ] (E ⧸ E₀) := E₀.mkQL

private def firstLift : (E ⧸ E₀) →L[ℂ] H := E₀.liftQL first le_rfl

private theorem firstLift_mk (z : E) : firstLift (Submodule.Quotient.mk z) = z.1 :=
  Submodule.liftQ_apply E₀ first.toLinearMap z

private theorem firstLift_norm (x : E ⧸ E₀) : ‖firstLift x‖ = ‖x‖ := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨z, rfl, hz⟩ := Submodule.Quotient.norm_mk_lt x hδ
    rw [firstLift_mk]
    exact (le_max_left ‖z.1‖ ‖z.2‖).trans hz.le
  · refine Submodule.Quotient.induction_on E₀ x ?_
    intro z
    rw [firstLift_mk]
    have eq : (Submodule.Quotient.mk (z.1, 0) : E ⧸ E₀) = Submodule.Quotient.mk z := by
      apply (Submodule.Quotient.eq E₀).mpr
      change z.1 - z.1 = 0
      exact sub_self _
    rw [← eq]
    simpa [Prod.norm_def] using Submodule.Quotient.norm_mk_le E₀ (z.1, 0)

/-- The quotient norm is exactly the norm of the first component. -/
public def quotientIso : (E ⧸ E₀) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective ⟨firstLift.toLinearMap, firstLift_norm⟩ fun y =>
    ⟨Submodule.Quotient.mk (y, 0), firstLift_mk (y, 0)⟩

@[simp] public theorem quotientIso_q (z : E) : quotientIso (q z) = z.1 := firstLift_mk z

private def hilbertBasis : HilbertBasis ℕ ℂ H :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)

private def hBasis : SchauderBasis ℂ H := hilbertBasis.toSchauderBasis

/-- The standard Schauder basis transported to the quotient. -/
public def quotientBasis : SchauderBasis ℂ (E ⧸ E₀) where
  basis n := quotientIso.symm (hBasis n)
  coord n := (hBasis.coord n).comp quotientIso.toLinearIsometry.toContinuousLinearMap
  ortho i j := by
    change hBasis.coord i (quotientIso (quotientIso.symm (hBasis j))) = _
    rw [quotientIso.apply_symm_apply]
    exact hBasis.ortho i j
  expansion x := by
    change HasSum (fun n => hBasis.coord n (quotientIso x) • quotientIso.symm (hBasis n)) x _
    have h := (hBasis.expansion (quotientIso x)).mapL
      quotientIso.symm.toLinearIsometry.toContinuousLinearMap
    simpa only [LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, map_smul, quotientIso.symm_apply_apply] using h

/-- The selected lifts, with the same second component in every index. -/
public def u (n : ℕ) : E := (hBasis n, 1)

@[simp] public theorem q_u (n : ℕ) : q (u n) = quotientBasis n := by
  apply quotientIso.injective
  change quotientIso (q (u n)) = quotientIso (quotientIso.symm (hBasis n))
  rw [quotientIso_q, quotientIso.apply_symm_apply]
  rfl

@[simp] public theorem norm_quotientBasis (n : ℕ) : ‖quotientBasis n‖ = 1 := by
  change ‖quotientIso.symm (hilbertBasis n)‖ = 1
  rw [quotientIso.symm.norm_map]
  exact hilbertBasis.orthonormal.norm_eq_one n

@[simp] public theorem norm_u (n : ℕ) : ‖u n‖ = 1 := by
  simp [u, Prod.norm_def, show ‖hBasis n‖ = 1 from hilbertBasis.orthonormal.norm_eq_one n]

/-- The continuous coefficients used by the lifting argument. -/
@[expose] public def pullback (n : ℕ) : E →L[ℂ] ℂ := (quotientBasis.coord n).comp q

@[simp] public theorem pullback_u (i j : ℕ) :
    pullback i (u j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [pullback] using quotientBasis.ortho i i
  · simpa [pullback, hij, Pi.single_apply, Ne.symm hij] using quotientBasis.ortho i j

/-- The ambient norm closure of the linear span of the specified lifts. -/
@[expose] public def V : Submodule ℂ E := (Submodule.span ℂ (Set.range u)).topologicalClosure

private theorem norm_sq_sum (n : ℕ) : ‖∑ j ∈ Finset.range n, hBasis j‖ ^ 2 = (n : ℝ) := by
  change ‖∑ j ∈ Finset.range n, hilbertBasis j‖ ^ 2 = _
  rw [@norm_sq_eq_re_inner ℂ]
  have h := hilbertBasis.orthonormal.inner_sum (fun _ => (1 : ℂ)) (fun _ => 1) (Finset.range n)
  simpa using congrArg Complex.re h

private theorem missing_mem : ((0, 1) : E) ∈ V := by
  change ((0, 1) : E) ∈ closure (Submodule.span ℂ (Set.range u) : Set E)
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt ((δ ^ 2)⁻¹)
  have hn' : (0 : ℝ) < n := (by positivity : 0 < (δ ^ 2)⁻¹) |>.trans hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by exact_mod_cast hn'))
  let avg : E := (n : ℂ)⁻¹ • ∑ j ∈ Finset.range n, u j
  refine ⟨avg, Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    Submodule.subset_span (Set.mem_range_self j)), ?_⟩
  have hsnd : avg.2 = 1 := by
    change (n : ℂ)⁻¹ * (∑ j ∈ Finset.range n, u j).2 = 1
    rw [Prod.snd_sum]
    simpa [u] using inv_mul_cancel₀ hnC
  have hfst : ‖avg.1‖ ^ 2 = (n : ℝ)⁻¹ := by
    change ‖(n : ℂ)⁻¹ • (∑ j ∈ Finset.range n, u j).1‖ ^ 2 = _
    rw [Prod.fst_sum, norm_smul, norm_inv, Complex.norm_natCast, mul_pow]
    change ((n : ℝ)⁻¹) ^ 2 * ‖∑ j ∈ Finset.range n, hBasis j‖ ^ 2 = _
    rw [norm_sq_sum]
    field_simp [ne_of_gt hn']
  have hsmall : ‖avg.1‖ < δ := by
    have hsq : (n : ℝ)⁻¹ < δ ^ 2 := (inv_lt_comm₀ hn' (by positivity)).mpr hn
    nlinarith [norm_nonneg avg.1]
  rw [dist_comm, dist_eq_norm, Prod.norm_def]
  change max ‖avg.1 - 0‖ ‖avg.2 - 1‖ < δ
  simp [hsnd, hsmall]

/-- A nonzero element of the closed span annihilated by every pulled-back functional. -/
public def missing : V := ⟨(0, 1), missing_mem⟩

@[simp] public theorem missing_ne_zero : missing ≠ 0 := by
  intro h
  have : (1 : ℂ) = 0 := congrArg (fun z : V => z.val.2) h
  exact one_ne_zero this

@[simp] public theorem q_missing : q (missing : E) = 0 := by
  apply quotientIso.injective
  rw [quotientIso_q, map_zero]
  rfl

@[simp] public theorem pullback_missing (i : ℕ) : pullback i (missing : E) = 0 := by
  simp [pullback]

/-- Applying the pulled-back coordinates to a purported expansion forces every
coefficient to be zero. Thus the missing vector has no expansion in these lifts. -/
public theorem no_expansion (a : ℕ → ℂ) :
    ¬ HasSum (fun n => a n • u n) (missing : E) (SummationFilter.conditional ℕ) := by
  intro h
  have ha (i : ℕ) : a i = 0 := by
    have h₁ := h.map (pullback i) (pullback i).continuous
    have h₂ : HasSum (fun j => if i = j then a i else 0) (a i)
        (SummationFilter.conditional ℕ) := hasSum_ite_eq' i (a i) _
    have hh : HasSum (fun j => if i = j then a i else 0) 0 (SummationFilter.conditional ℕ) := by
      rw [pullback_missing] at h₁
      convert h₁ using 1
      funext j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    exact h₂.unique hh
  have hz : HasSum (fun n => a n • u n) (0 : E) (SummationFilter.conditional ℕ) := by
    simp [ha]
  exact missing_ne_zero (Subtype.ext (h.unique hz))

/-- No Schauder basis of the closed span has the specified lifts as its vectors. -/
public theorem not_schauderBasic :
    ¬ ∃ b : SchauderBasis ℂ V, ∀ n, (b n : E) = u n := by
  rintro ⟨b, hb⟩
  apply no_expansion (fun n => b.coord n missing)
  simpa only [Submodule.subtypeL_apply, SetLike.val_smul, hb] using
    (b.expansion missing).mapL V.subtypeL

end Masullo.BoundedBiorthogonalLifts
