module

public import Theorems.RationalAdeleClassFourier
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Group.Integral

/-!
# Density and orthogonality of the rational adele class characters

The rational frequencies give a uniformly dense span of continuous functions on
`𝔸ℚ / ℚ` and are orthonormal for the normalized quotient Haar measure. This
provides a quotient-only route toward the rational case of Theorem D.1.2.7(3),
without an identification of the ambient adelic dual.
-/

open NumberField MeasureTheory Topology
open scoped ComplexConjugate Pointwise

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → Cq)
local notation "ι" => algebraMap ℚ A

local instance : CompactSpace Cq := compactSpace_rationalAdeleClasses

/-- The rational frequency character as a continuous function on the quotient. -/
public noncomputable def rationalAdeleClassCharMap (r : ℚ) : C(Cq, ℂ) :=
  ⟨rationalAdeleClassChar r, continuous_rationalAdeleClassChar r⟩

private theorem charMap_zero : rationalAdeleClassCharMap 0 = 1 := by
  ext c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  change rationalAdeleClassChar 0 (π a) = 1
  rw [rationalAdeleClassChar_mk, map_zero, mul_zero, AddChar.map_zero_eq_one]

private theorem charMap_add (r s : ℚ) : rationalAdeleClassCharMap (r + s) =
    rationalAdeleClassCharMap r * rationalAdeleClassCharMap s := by
  ext c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  change rationalAdeleClassChar (r + s) (π a) =
    rationalAdeleClassChar r (π a) * rationalAdeleClassChar s (π a)
  simp only [rationalAdeleClassChar_mk, map_add, mul_add, AddChar.map_add_eq_mul]

private theorem charMap_neg (r : ℚ) : rationalAdeleClassCharMap (-r) =
    star (rationalAdeleClassCharMap r) := by
  ext c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  change rationalAdeleClassChar (-r) (π a) = conj (rationalAdeleClassChar r (π a))
  simp only [rationalAdeleClassChar_mk, map_neg, mul_neg, AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (norm_rationalAdeleAddChar _)

private noncomputable abbrev charSpan : Submodule ℂ C(Cq, ℂ) :=
  Submodule.span ℂ (Set.range rationalAdeleClassCharMap)

private theorem char_mem_span (r : ℚ) : rationalAdeleClassCharMap r ∈ charSpan :=
  Submodule.subset_span (Set.mem_range_self r)

private noncomputable def charAlgebra : StarSubalgebra ℂ C(Cq, ℂ) where
  carrier := charSpan
  add_mem' := charSpan.add_mem
  mul_mem' {f g} hf hg := by
    have h := Submodule.mul_mem_mul hf hg
    change f * g ∈ charSpan * charSpan at h
    refine (show charSpan * charSpan ≤ charSpan from ?_) h
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨r, rfl⟩, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨r + s, charMap_add r s⟩
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one, ← charMap_zero]
    exact charSpan.smul_mem z (char_mem_span 0)
  star_mem' {f} hf := by
    induction hf using Submodule.span_induction with
    | mem _ h =>
        obtain ⟨r, rfl⟩ := h
        rw [← charMap_neg]
        exact char_mem_span (-r)
    | zero => rw [star_zero]; exact charSpan.zero_mem
    | add _ _ _ _ hf hg => rw [star_add]; exact charSpan.add_mem hf hg
    | smul z f _ hf => rw [star_smul]; exact charSpan.smul_mem (star z) hf

/-- Finite linear combinations of the rational characters are uniformly dense
in the continuous complex functions on the rational adele classes. -/
public theorem closure_span_rationalAdeleClassCharMap :
    closure (Submodule.span ℂ (Set.range rationalAdeleClassCharMap) : Set C(Cq, ℂ)) =
      Set.univ := by
  have hsep : charAlgebra.SeparatesPoints := by
    intro c d hcd
    obtain ⟨r, hr⟩ := rationalAdeleClassChar_separates hcd
    exact ⟨rationalAdeleClassCharMap r, ⟨_, char_mem_span r, rfl⟩, hr⟩
  change (charAlgebra.topologicalClosure : Set C(Cq, ℂ)) = Set.univ
  rw [ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep]
  rfl

private theorem exists_char_eq_neg_one {r : ℚ} (hr : r ≠ 0) :
    ∃ c : Cq, rationalAdeleClassChar r c = -1 := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let arch := (RingEquiv.piUnique InfinitePlace.Completion).trans e
  let a : A := (arch.symm (1 / 2 / (r : ℝ)), 0)
  have ha : rationalAdeleReal a = 1 / 2 / (r : ℝ) := by
    rw [rationalAdeleReal_apply]
    exact arch.apply_symm_apply _
  have hreal : rationalAdeleReal (a * ι r) = 1 / 2 := by
    rw [rationalAdeleReal_apply]
    change e (a.1 Rat.infinitePlace * (ι r).1 Rat.infinitePlace) = _
    rw [map_mul, ← rationalAdeleReal_apply, ← rationalAdeleReal_apply,
      ha, rationalAdeleReal_algebraMap, div_mul_cancel₀ _ (by exact_mod_cast hr)]
  have hfinite : (a * ι r).2 = 0 := zero_mul _
  refine ⟨π a, ?_⟩
  have hint (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
      (a * ι r).2 v ∈ v.adicCompletionIntegers ℚ := by
    rw [hfinite]
    exact zero_mem _
  rw [rationalAdeleClassChar_mk, rationalAdeleAddChar_eq_prod _ ∅ (fun v _ ↦ hint v),
    Finset.prod_empty, mul_one, hreal]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  ring

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

private theorem integral_char_eq_zero {r : ℚ} (hr : r ≠ 0) :
    ∫ c, rationalAdeleClassChar r c ∂rationalAdeleClassHaar = 0 := by
  obtain ⟨d, hd⟩ := exists_char_eq_neg_one hr
  have h := integral_add_left_eq_self (μ := rationalAdeleClassHaar)
    (rationalAdeleClassChar r : Cq → ℂ) d
  simp only [AddChar.map_add_eq_mul, hd, neg_one_mul, integral_neg] at h
  exact neg_eq_self.mp h

/-- The rational characters are orthonormal for quotient Haar probability. -/
public theorem integral_rationalAdeleClassChar_mul_conj (r s : ℚ) :
    (∫ c, rationalAdeleClassChar r c * conj (rationalAdeleClassChar s c)
      ∂rationalAdeleClassHaar) = if r = s then 1 else 0 := by
  have h (c : Cq) : rationalAdeleClassChar r c * conj (rationalAdeleClassChar s c) =
      rationalAdeleClassChar (r - s) c := by
    change (rationalAdeleClassCharMap r * star (rationalAdeleClassCharMap s)) c = _
    rw [← charMap_neg, ← charMap_add, sub_eq_add_neg]
    rfl
  simp only [h]
  by_cases hrs : r = s
  · subst s
    rw [sub_self, ite_eq_left rfl]
    change (∫ c, rationalAdeleClassCharMap 0 c ∂rationalAdeleClassHaar) = 1
    rw [charMap_zero]
    simp
  · rw [ite_eq_right hrs, integral_char_eq_zero (sub_ne_zero.mpr hrs)]

end Masullo
