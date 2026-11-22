module

public import Theorems.IdeleHeckeGaussian
import Theorems.IdeleClassGaussianSupport
import Lemmas.IdeleHeckeGaussianDecay
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-! # Absolute convergence of the diagonal Hecke Gaussian series

For a fixed idele, the finite support conditions put the contributing diagonal
indices in a single fractional lattice. A positive lower bound for the norms
of its Archimedean coordinates suffices to compare the Gaussian with a
summable inverse power on the integer lattice, at any idelic norm.
-/

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "Λ" => mixedEmbedding.integerLattice K

private theorem exists_infinite_coordinate_ge_fixed_mixedEmbedding (g : I) {m : ℕ}
    (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Kˣ, ∃ v : InfinitePlace K,
      c * ‖mixedEmbedding K ((m : K) * (a : K))‖ ≤ ‖(d a * g).val.1 v‖ := by
  classical
  obtain ⟨w, hw⟩ := Finite.exists_min (fun v : InfinitePlace K ↦ ‖g.val.1 v‖)
  have hmul : g.val.1 w * (g⁻¹).val.1 w = 1 :=
    congrArg (fun z : AdeleRing (𝓞 K) K ↦ z.1 w) g.mul_inv
  have hr : 0 < ‖g.val.1 w‖ := norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hmul)
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨‖g.val.1 w‖ / m, div_pos hr hmR, fun a ↦ ?_⟩
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun v : InfinitePlace K ↦ mixedEmbedding.normAtPlace v (mixedEmbedding K ((m : K) * (a : K))))
  have hprincipal : ‖(d a).val.1 v‖ = v (a : K) := by
    change ‖algebraMap K v.Completion (a : K)‖ = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, AbsoluteValue.Completion.norm_coe]
    rfl
  refine ⟨v, ?_⟩
  change _ ≤ ‖(d a).val.1 v * g.val.1 v‖
  rw [hv, mixedEmbedding.normAtPlace_apply, map_mul, v.map_natCast, norm_mul, hprincipal]
  calc
    ‖g.val.1 w‖ / (m : ℝ) * ((m : ℝ) * v (a : K)) = v (a : K) * ‖g.val.1 w‖ := by
      field_simp [hmR.ne']
    _ ≤ v (a : K) * ‖g.val.1 v‖ := mul_le_mul_of_nonneg_left (hw v) (apply_nonneg v _)

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- At every fixed idele, the diagonal series of the corrected Hecke Gaussian
is absolutely convergent. -/
public theorem summable_norm_ideleHeckeGaussian_diagonal
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ z : IdeleClassGroup (𝓞 K) K, ‖χ z‖ = 1)
    (T : Finset V) (g : I) :
    Summable fun a : Kˣ ↦ ‖ideleHeckeGaussian χ hχ T (d a * g)‖ := by
  classical
  let F (a : Kˣ) := ‖ideleHeckeGaussian χ hχ T (d a * g)‖
  obtain ⟨m, hm, hden⟩ := exists_uniform_denominator_of_isCompact ({g} : Set I) isCompact_singleton
  -- Only indices cleared by `m` occur in the support.
  have hmem (a : support F) : mixedEmbedding K ((m : K) * ((a : Kˣ) : K)) ∈ Λ := by
    obtain ⟨y, hy⟩ := hden g (mem_singleton g) a
      (norm_finite_le_one_of_ideleHeckeGaussian_ne_zero χ hχ T (norm_ne_zero_iff.mp a.property))
    exact ⟨y, congrArg (mixedEmbedding K) hy⟩
  let e (a : support F) : Λ := ⟨mixedEmbedding K ((m : K) * ((a : Kˣ) : K)), hmem a⟩
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hmK (mixedEmbedding_injective K (congrArg Subtype.val h))
  obtain ⟨c, hc, hlower⟩ := exists_infinite_coordinate_ge_fixed_mixedEmbedding g hm
  let p := Module.finrank ℤ Λ + 1
  obtain ⟨A, _, hgauss⟩ := exists_ideleHeckeGaussian_norm_mul_pow_le χ hχ T p
  let W (z : Λ) := (‖z‖ ^ p)⁻¹
  have hW : Summable W := by
    have hp : (Module.finrank ℤ Λ : ℝ) < p := by exact_mod_cast Nat.lt_succ_self _
    simpa only [W, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast] using
      (ZLattice.summable_norm_rpow (L := Λ) (-(p : ℝ)) (neg_lt_neg hp))
  -- The actual Gaussian is dominated by the pullback of the lattice majorant.
  have hmajor (a : support F) : F a ≤ (A / c ^ p) * W (e a) := by
    obtain ⟨v, hv⟩ := hlower a
    have hz : 0 < ‖e a‖ := by
      apply norm_pos_iff.mpr
      intro h
      have hh : mixedEmbedding K ((m : K) * ((a : Kˣ) : K)) = 0 := congrArg Subtype.val h
      exact mul_ne_zero hmK (Units.ne_zero (a : Kˣ))
        (mixedEmbedding_injective K (hh.trans (map_zero _).symm))
    have H : F a * (c ^ p * ‖e a‖ ^ p) ≤ A := calc
      _ = F a * (c * ‖e a‖) ^ p := by rw [mul_pow]
      _ ≤ F a * ‖(d (a : Kˣ) * g).val.1 v‖ ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) hv _)
          (norm_nonneg _)
      _ ≤ A := hgauss _ v
    have h := (le_div_iff₀ (by positivity : 0 < c ^ p * ‖e a‖ ^ p)).mpr H
    simpa only [W, div_eq_mul_inv, mul_inv, mul_assoc] using h
  have hs : Summable (fun a : support F ↦ F a) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hmajor ((hW.mul_left _).comp_injective he)
  exact (hasSum_subtype_support.mp hs.hasSum).summable

end Masullo
