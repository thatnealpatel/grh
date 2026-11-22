module

public import Lemmas.FiniteHeckeRestriction
import Lemmas.ComplexMultiplicativeNeighborhood
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Principal units in the kernel of a finite Hecke restriction

Masullo describes the finite local unit group in §3.1.2.1, PDF p. 120, and
uses the inverse local character on that group in (3.4.3.8), PDF p. 152
(provisional Markdown and layout reading). To decompose that test into ball
indicators, we prove here that the actual restricted character is trivial on
a sufficiently small ball about `1`.
-/

open Filter IsDedekindDomain NumberField Set Topology

namespace Masullo

/-- No nontrivial subgroup of `ℂˣ` is contained in the radius `1/2` ball about `1`. -/
private theorem complex_subgroup_eq_one (H : Subgroup ℂˣ)
    (h : ∀ u ∈ H, ‖(u : ℂ) - 1‖ < 1 / 2) {u : ℂˣ} (hu : u ∈ H) : u = 1 := by
  apply Units.ext
  apply complex_eq_one_of_norm_pow_sub_one_lt
  intro n
  simpa only [Units.val_pow_eq_pow_val] using h (u ^ n) (H.pow_mem hu n)

section Ultrametric

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

private theorem norm_eq_one_of_norm_sub_one_lt_one {x : F} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h : ‖x + (-1 : F)‖ < max ‖x‖ ‖(-1 : F)‖ := by
    simpa only [← sub_eq_add_neg, norm_neg, norm_one] using hx.trans_le (le_max_right ‖x‖ 1)
  simpa only [norm_neg, norm_one] using IsUltrametricDist.norm_eq_of_add_norm_lt_max h

/-- In an ultrametric field, the radius `r ≤ 1` open ball about `1` forms a subgroup of units. -/
private def principalUnitSubgroup {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < r}
  one_mem' := by simpa only [Set.mem_ofPred_eq, Units.val_one, sub_self, norm_zero] using hr
  mul_mem' {x y} hx hy := by
    change ‖(x : F) - 1‖ < r at hx
    change ‖(y : F) - 1‖ < r at hy
    change ‖(x : F) * (y : F) - 1‖ < r
    rw [show (x : F) * (y : F) - 1 = (x : F) * ((y : F) - 1) + ((x : F) - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)
    rwa [norm_mul, norm_eq_one_of_norm_sub_one_lt_one (hx.trans_le hr₁), one_mul]
  inv_mem' {x} hx := by
    change ‖(x : F) - 1‖ < r at hx
    change ‖((x⁻¹ : Fˣ) : F) - 1‖ < r
    rw [Units.val_inv_eq_inv_val,
      show (x : F)⁻¹ - 1 = (x : F)⁻¹ * (1 - (x : F)) by
        rw [mul_sub, mul_one, inv_mul_cancel₀ x.ne_zero],
      norm_mul, norm_inv, norm_eq_one_of_norm_sub_one_lt_one (hx.trans_le hr₁), inv_one, one_mul,
      norm_sub_rev]
    exact hx

end Ultrametric

variable {K : Type*} [Field K] [NumberField K]

/-- Every finite Hecke restriction is trivial on a sufficiently small additive ball about `1`.
Continuity puts the image of a principal-unit subgroup in a complex ball small enough
that it cannot contain a nontrivial subgroup. -/
public theorem finiteHeckeRestriction_eq_one_near_one (χ : HeckeCharacter (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ x : v.adicCompletion K, ‖x - 1‖ < ε → χ.restrict v x = 1 := by
  let F := v.adicCompletion K
  let f : Fˣ →* ℂˣ := (χ.restrict v).toUnitHom
  have hf : Continuous (f : Fˣ → ℂˣ) := by
    apply (Units.isEmbedding_val₀ (G₀ := ℂ)).isInducing.continuous_iff.mpr
    exact continuous_finiteHeckeRestriction χ v
  let U : Set ℂˣ := Units.val ⁻¹' Metric.ball (1 : ℂ) (1 / 2)
  have hU : U ∈ 𝓝 (1 : ℂˣ) := by
    apply Units.continuous_val.continuousAt.preimage_mem_nhds
    exact Metric.ball_mem_nhds (1 : ℂ) (by norm_num)
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : Fˣ) :=
    hf.continuousAt.preimage_mem_nhds (by rwa [map_one])
  -- Pull the additive neighborhood basis at `1` back to the completion units.
  have hb := (Units.isEmbedding_val₀ (G₀ := F)).isInducing.basis_nhds
    (Metric.nhds_basis_ball (x := ((1 : Fˣ) : F)))
  obtain ⟨r, hr, hsub⟩ := hb.mem_iff.mp hpre
  let ε := min r 1
  have hε : 0 < ε := lt_min hr zero_lt_one
  have hε₁ : ε ≤ 1 := min_le_right r 1
  let H : Subgroup Fˣ := principalUnitSubgroup hε hε₁
  have himage : ∀ u ∈ H.map f, ‖(u : ℂ) - 1‖ < 1 / 2 := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    have ha' : ‖(a : F) - 1‖ < r :=
      (show ‖(a : F) - 1‖ < ε from ha).trans_le (min_le_left r 1)
    have hmem : f a ∈ U := hsub (by
      simpa only [Function.comp_apply, mem_preimage, Metric.mem_ball, Units.val_one, dist_eq_norm]
        using ha')
    simpa only [U, mem_preimage, Metric.mem_ball, dist_eq_norm] using hmem
  refine ⟨ε, hε, hε₁, fun x hx ↦ ?_⟩
  have hx₀ : x ≠ 0 := norm_ne_zero_iff.mp (by
    rw [norm_eq_one_of_norm_sub_one_lt_one (hx.trans_le hε₁)]
    exact one_ne_zero)
  let a : Fˣ := Units.mk0 x hx₀
  have ha : a ∈ H := hx
  have hone : f a = 1 :=
    complex_subgroup_eq_one (H.map f) himage (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  calc
    χ.restrict v x = (f a : ℂ) := (MulChar.coe_toUnitHom (χ.restrict v) a).symm
    _ = 1 := congrArg Units.val hone

end Masullo
