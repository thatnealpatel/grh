module

public import Theorems.IdeleScalarLogSection
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# An Archimedean lower bound for the scalar section

This replaces the pointwise estimate used in (2.2.3.10), PDF p. 84.
Boundedness alone does not bound the coordinates of the multiplying ideles
away from zero. Here compactness in the units topology bounds the inverse
coordinates. In place of the diagonal section used in (2.2.3.10), we use
Lemma A.2.2.4, PDF p. 547: At idelic norm `t`, its ordinary dilation is
`t^(1 / [K : ℚ])`, not `t`.
-/

open NumberField
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

private theorem norm_principal_scalar_infinite (a : Kˣ) (x : Multiplicative ℝ) (b : I)
    (v : InfinitePlace K) :
    ‖(d a * ideleScalarLogSection x * b).val.1 v‖ =
      v (a : K) * Real.exp (x.toAdd / (Module.finrank ℚ K : ℝ)) * ‖b.val.1 v‖ := by
  have hprincipal : ‖(d a).val.1 v‖ = v (a : K) := by
    change ‖algebraMap K v.Completion (a : K)‖ = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, AbsoluteValue.Completion.norm_coe]
    rfl
  have hscalar : ‖(ideleScalarLogSection (K := K) x).val.1 v‖ =
      Real.exp (x.toAdd / (Module.finrank ℚ K : ℝ)) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
      ideleScalarLogSection_infinite, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  change ‖((d a).val.1 v * (ideleScalarLogSection x).val.1 v) * b.val.1 v‖ = _
  rw [norm_mul, norm_mul, hprincipal, hscalar]

private theorem exists_mixedEmbedding_nat_mul_norm_eq (a : K) (m : ℕ) :
    ∃ v : InfinitePlace K, ‖mixedEmbedding K ((m : K) * a)‖ = (m : ℝ) * v a := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun v : InfinitePlace K ↦ mixedEmbedding.normAtPlace v (mixedEmbedding K ((m : K) * a)))
  exact ⟨v, by rw [hv, mixedEmbedding.normAtPlace_apply, map_mul, v.map_natCast]⟩

private theorem exists_pos_le_infinite_coordinates {C : Set I₁} (hC : IsCompact C) :
    ∃ r : ℝ, 0 < r ∧ ∀ b ∈ C, ∀ v : InfinitePlace K, r ≤ ‖(b : I).val.1 v‖ := by
  have hcont (v : InfinitePlace K) : Continuous (fun b : I₁ ↦ ‖((b : I)⁻¹).val.1 v‖) :=
    ((continuous_apply v).comp (continuous_fst.comp
      (Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val)))).norm
  have hlocal (v : InfinitePlace K) : ∃ M : ℝ, ∀ b ∈ C, ‖((b : I)⁻¹).val.1 v‖ ≤ M := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image (hcont v).continuousOn
    exact ⟨M, fun b hb ↦ hM ⟨b, hb, rfl⟩⟩
  choose M hM using hlocal
  obtain ⟨U, hU⟩ := (Set.finite_range M).bddAbove
  let B := max 1 U
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left 1 U)
  refine ⟨1 / B, one_div_pos.mpr hB, fun b hb v ↦ (div_le_iff₀ hB).mpr ?_⟩
  have hinv : ‖((b : I)⁻¹).val.1 v‖ ≤ B :=
    (hM v b hb).trans ((hU (Set.mem_range_self v)).trans (le_max_right 1 U))
  have hmul : (b : I).val.1 v * ((b : I)⁻¹).val.1 v = 1 :=
    congrArg (fun z : A ↦ z.1 v) (b : I).mul_inv
  calc
    1 = ‖(b : I).val.1 v‖ * ‖((b : I)⁻¹).val.1 v‖ := by rw [← norm_mul, hmul, norm_one]
    _ ≤ ‖(b : I).val.1 v‖ * B := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)

/-- On a compact set of norm-one ideles, some Archimedean coordinate of each
principal translate of the scalar section bounds the scaled mixed norm from below.
The positive constant is uniform in the translate, the compact representative,
and the scalar parameter, which can have any real logarithm. -/
public theorem exists_infinite_coordinate_ge_scaled_mixedEmbedding
    {C : Set I₁} (hC : IsCompact C) {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ C, ∀ (x : Multiplicative ℝ) (a : Kˣ),
      ∃ v : InfinitePlace K,
        c * Real.exp (x.toAdd / (Module.finrank ℚ K : ℝ)) *
          ‖mixedEmbedding K ((m : K) * (a : K))‖ ≤
        ‖(d a * ideleScalarLogSection x * (b : I)).val.1 v‖ := by
  obtain ⟨r, hr, hcoord⟩ := exists_pos_le_infinite_coordinates hC
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨r / (m : ℝ), div_pos hr hmR, fun b hb x a ↦ ?_⟩
  obtain ⟨v, hv⟩ := exists_mixedEmbedding_nat_mul_norm_eq (a : K) m
  refine ⟨v, ?_⟩
  rw [norm_principal_scalar_infinite, hv]
  let t := Real.exp (x.toAdd / (Module.finrank ℚ K : ℝ))
  calc
    r / (m : ℝ) * t * ((m : ℝ) * v (a : K)) = v (a : K) * t * r := by
      field_simp [hmR.ne']
    _ ≤ v (a : K) * t * ‖(b : I).val.1 v‖ :=
      mul_le_mul_of_nonneg_left (hcoord b hb v) (mul_nonneg (apply_nonneg v _) (Real.exp_pos _).le)

end Masullo
