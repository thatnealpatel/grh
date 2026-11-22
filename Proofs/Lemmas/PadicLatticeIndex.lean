module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Determinant and lattice index over the p-adic integers

The local discriminant scales in Masullo (A.3.1.2), p. 556, and
(A.3.2.2), p. 560, use the norm on the base field. This project lemma
computes that norm for a lattice inclusion of full rank by counting its
cokernel. Identifying the trace lattice and the different is separate.
-/

open Module Submodule

namespace Masullo

variable {p : ℕ} [Fact p.Prime]

private theorem norm_eq_inv_card_quotient_span {a : ℤ_[p]} (ha : a ≠ 0) :
    ‖a‖ = (Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) : ℝ)⁻¹ := by
  have hassoc : Associated a ((p : ℤ_[p]) ^ a.valuation) := by
    refine ⟨(PadicInt.unitCoeff ha)⁻¹, ?_⟩
    nth_rewrite 1 [PadicInt.unitCoeff_spec ha]
    simp [mul_comm, mul_left_comm]
  let g : ℤ_[p] →+* ZMod (p ^ a.valuation) := PadicInt.toZModPow a.valuation
  have hker : RingHom.ker g = Ideal.span ({a} : Set ℤ_[p]) :=
    (PadicInt.ker_toZModPow _).trans (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm
  let e := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective g))
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod, PadicInt.norm_eq_zpow_neg_valuation ha,
    Nat.cast_pow, zpow_neg, zpow_natCast]

/-- The norm of the determinant of a full-rank endomorphism of a finite
free `ℤ_[p]`-lattice is the reciprocal of the index of its image. -/
public theorem padicInt_norm_det_eq_inv_card_quotient_range {M : Type*}
    [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (f : M →ₗ[ℤ_[p]] M) (hf : Function.Injective f) :
    ‖LinearMap.det f‖ = (Nat.card (M ⧸ LinearMap.range f) : ℝ)⁻¹ := by
  classical
  let N := LinearMap.range f
  let e : M ≃ₗ[ℤ_[p]] N := LinearEquiv.ofInjective f hf
  let b := Module.Free.chooseBasis ℤ_[p] M
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let bM := smithNormalFormTopBasis b h
  let bN := smithNormalFormBotBasis b h
  let g := N.subtype ∘ₗ (bM.equiv bN (Equiv.refl _)).toLinearMap
  have hg (i) : g (bM i) = a i • bM i := by
    change (bM.equiv bN (Equiv.refl _) (bM i) : M) = _
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    exact smithNormalFormBotBasis_def b h i
  have hmatrix : LinearMap.toMatrix bM bM g = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, hg, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hdet : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix bM, hmatrix, Matrix.det_diagonal]
  have hfg : Associated (LinearMap.det f) (LinearMap.det g) :=
    LinearMap.associated_det_comp_equiv N.subtype e (bM.equiv bN (Equiv.refl _))
  obtain ⟨u, hu⟩ := hfg
  have hnorm : ‖LinearMap.det f‖ = ‖LinearMap.det g‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, mul_one]
  have hcard : Nat.card (M ⧸ N) =
      ∏ i, Nat.card (ℤ_[p] ⧸ Ideal.span ({a i} : Set ℤ_[p])) :=
    (Nat.card_congr (N.quotientEquivPiSpan b h).toEquiv).trans Nat.card_pi
  change ‖LinearMap.det f‖ = (Nat.card (M ⧸ N) : ℝ)⁻¹
  rw [hnorm, hdet, norm_prod, hcard, Nat.cast_prod, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ ↦
    norm_eq_inv_card_quotient_span (smithNormalFormCoeffs_ne_zero b h i)

end Masullo
