module

public import Lemmas.FiniteCompletionPadic
import Lemmas.FiniteCompletionCompact
import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module

/-! # The integral lattice in a finite completion

The local trace determinant used in (A.3.2.2), p. 560, needs a finite
free `ℤ_[p]`-module whose basis becomes a `ℚ_[p]`-basis of the actual
completion. We supply that lattice for the canonical maps. Computing
the determinant and comparing it with the global different are separate.
-/

open Filter IsDedekindDomain NumberField Set Topology
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "ιO" => IsScalarTower.toAlgHom ℤ_[p] O F

omit [NumberField K] in
private theorem norm_basePrime_lt_one : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (p).property.one_lt)

/-- The integer ring is finite over the base integers. Compactness bounds
its basis coordinates, so rescaling embeds it into a finite free module. -/
public theorem finiteCompletionIntegers_moduleFinite : Module.Finite ℤ_[p] O := by
  classical
  let _ := finiteCompletion_moduleFinite v
  let _ := compactSpace_finiteCompletionIntegers K v
  let b := Module.finBasis ℚ_[p] F
  let c (i : Fin (Module.finrank ℚ_[p] F)) : F →ₗ[ℚ_[p]] ℚ_[p] := b.coord i
  have hbound (i) : ∃ r : ℝ, ∀ x : O, ‖c i (x : F)‖ ≤ r := by
    have hc : Continuous (fun x : O ↦ ‖c i (x : F)‖) :=
      ((c i).continuous_of_finiteDimensional.comp continuous_subtype_val).norm
    obtain ⟨r, hr⟩ := (isCompact_range hc).bddAbove
    exact ⟨r, fun x ↦ hr (mem_range_self x)⟩
  have hscale (i) : ∃ a : ℚ_[p], a ≠ 0 ∧ ∀ x : O, ‖a * c i (x : F)‖ ≤ 1 := by
    obtain ⟨r, hr⟩ := hbound i
    let R := max r 1
    have hR : 0 < R := zero_lt_one.trans_le (le_max_right ..)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hR) (norm_basePrime_lt_one v)
    refine ⟨((p : ℕ) : ℚ_[p]) ^ n, pow_ne_zero _ (by exact_mod_cast (p).property.ne_zero), ?_⟩
    intro x
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ n * R :=
        mul_le_mul_of_nonneg_left ((hr x).trans (le_max_left ..)) (by positivity)
      _ ≤ 1 := by simpa [inv_mul_cancel₀ hR.ne'] using
        mul_le_mul_of_nonneg_right hn.le hR.le
  choose a ha hsmall using hscale
  let f : O →ₗ[ℤ_[p]] Fin (Module.finrank ℚ_[p] F) → ℤ_[p] :=
    { toFun := fun x i ↦ ⟨a i * c i (x : F), hsmall i x⟩
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        change a i * c i ((x : F) + (y : F)) = a i * c i (x : F) + a i * c i (y : F)
        rw [map_add, mul_add]
      map_smul' := by
        intro r x
        funext i
        apply Subtype.ext
        change a i * c i ((ιO).toLinearMap (r • x)) = (r : ℚ_[p]) * (a i * c i (x : F))
        rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[p] r, map_smul, smul_eq_mul,
          mul_left_comm]
        rfl }
  refine Module.Finite.of_injective f (fun x y h ↦ Subtype.ext ?_)
  apply b.ext_elem
  intro i
  exact mul_left_cancel₀ (ha i) (congrArg (fun z ↦ (z i : ℚ_[p])) h)

/-- The finite integral lattice is free because it is torsion-free over a PID. -/
public theorem finiteCompletionIntegers_moduleFree : Module.Free ℤ_[p] O := by
  let _ := finiteCompletionIntegers_moduleFinite v
  have : Module.IsTorsionFree ℤ_[p] O := Module.IsTorsionFree.of_smul_eq_zero fun r x h ↦ by
    rw [Algebra.smul_def, mul_eq_zero] at h
    refine h.imp (fun hr ↦ ?_) id
    have hF := congrArg (fun t : O ↦ (t : F)) hr
    change finiteCompletionPadicMap v (r : ℚ_[p]) = 0 at hF
    exact PadicInt.coe_eq_zero.mp ((finiteCompletionPadicMap v).injective
      (hF.trans (map_zero _).symm))
  infer_instance

/-- Inverting the nonzero base integers in the integral lattice gives the
actual completion, so a basis of the lattice localizes to a field basis. -/
public theorem finiteCompletionIntegers_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid O ((ℤ_[p])⁰)) F := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, fun {x y} h ↦ ⟨1, ?_⟩⟩
  · rintro ⟨_, r, hr, rfl⟩
    rw [← IsScalarTower.algebraMap_apply]
    change IsUnit (finiteCompletionPadicMap v (r : ℚ_[p]))
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero (finiteCompletionPadicMap v)).2 (by
      simpa only [ne_eq, PadicInt.coe_eq_zero] using nonZeroDivisors.ne_zero hr))
  · intro z
    have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_basePrime_lt_one v)
    have hm := (((continuous_finiteCompletionPadicMap v).tendsto _).comp ht).const_mul z
    have hO : (O : Set F) ∈ 𝓝 (z * finiteCompletionPadicMap v 0) := by
      rw [map_zero, mul_zero]
      exact (Valued.isOpen_valuationSubring F).mem_nhds (zero_mem O)
    obtain ⟨n, hn⟩ := (hm.eventually hO).exists
    let r := ((p : ℕ) : ℤ_[p]) ^ n
    have hr : r ∈ (ℤ_[p])⁰ := mem_nonZeroDivisors_of_ne_zero <|
      pow_ne_zero _ (by exact_mod_cast (p).property.ne_zero)
    refine ⟨⟨⟨_, hn⟩, ⟨algebraMap ℤ_[p] O r, ⟨r, hr, rfl⟩⟩⟩, ?_⟩
    change z * (finiteCompletionPadicIntMap v r : F) = _
    rw [coe_finiteCompletionPadicIntMap, PadicInt.coe_pow, PadicInt.coe_natCast]
    rfl
  · change (x : F) = (y : F) at h
    simpa using (Subtype.ext h : x = y)

end Masullo
