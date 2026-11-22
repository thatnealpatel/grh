module

public import Theorems.IdeleFundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # The class-number factor in the idelic strip

Section A.3.3.1, PDF p. 561, uses the full fundamental domain of
(A.2.3.16), p. 550. Here we pass from the unit-window strip to the full
strip. A norm-one class lift translates the unit strip without changing
the log coordinate. The translated strips are Borel, and the section law
gives disjointness, so left invariance gives the class-number factor of
(A.3.2.1), p. 560. This does not identify any quotient Haar measure.
Source reading: Provisional, from pinned Markdown and numbered PDF text.
-/

open MeasureTheory NumberField Set
open scoped ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)
local notation "L" => Multiplicative ℝ

/-- The full idelic strip has `classNumber K` times the unit-window strip's mass,
for every continuous homomorphic log-norm section and Borel log set. -/
public theorem measure_ideleFundamentalDomain_strip_eq_classNumber_mul
    [MeasurableSpace I] [BorelSpace I] [MeasurableSpace I₁] [BorelSpace I₁]
    (μ : Measure I) [μ.IsMulLeftInvariant] (s : L →ₜ* I)
    (hs : ∀ x, ideleLogNorm (s x) = x) (v : InfinitePlace K) (r : P → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {J : Set L} (hJ : MeasurableSet J) :
    μ (ideleLogSplit s hs '' (J ×ˢ ideleFundamentalDomain v r)) =
      (classNumber K : ℝ≥0∞) * μ (ideleLogSplit s hs '' (J ×ˢ ideleUnitWindow v)) := by
  let e := ideleLogSplit s hs
  let W := e '' (J ×ˢ ideleUnitWindow v)
  let B (p : P) := (fun g : I₁ ↦ (r p)⁻¹ * g) ⁻¹' ideleUnitWindow v
  let F (p : P) := e '' (J ×ˢ B p)
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hW : MeasurableSet W :=
    he.measurableSet_image' (hJ.prod (measurableSet_ideleUnitWindow v))
  have hunion : e '' (J ×ˢ ideleFundamentalDomain v r) = ⋃ p, F p := by
    ext g
    simp only [F, B, ideleFundamentalDomain, mem_image, mem_prod, mem_iUnion]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨haj, p, hap⟩ := ha
      exact ⟨p, a, ⟨haj, hap⟩, rfl⟩
    · rintro ⟨p, a, ha, rfl⟩
      exact ⟨a, ⟨ha.1, p, ha.2⟩, rfl⟩
  have hdisj : Pairwise (fun p q ↦ Disjoint (F p) (F q)) := fun p q hpq ↦
    disjoint_image_of_injective e.injective
      ((pairwiseDisjoint_ideleFundamentalDomain_pieces v r hr hpq).set_prod_right J J)
  have hmeas (p : P) : MeasurableSet (F p) :=
    he.measurableSet_image' (hJ.prod (measurableSet_ideleFundamentalDomain_piece v r p))
  have htrans (p : P) : F p = (fun g : I ↦ (↑(r p) : I)⁻¹ * g) ⁻¹' W := by
    have hmul (a : L × I₁) : (↑(r p) : I)⁻¹ * e a = e (a.1, (r p)⁻¹ * a.2) := by
      simp only [e, ideleLogSplit_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      ac_rfl
    apply Set.ext
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    change (e a ∈ e '' (J ×ˢ B p)) ↔ (↑(r p) : I)⁻¹ * e a ∈ e '' (J ×ˢ ideleUnitWindow v)
    rw [hmul, e.injective.mem_set_image, e.injective.mem_set_image]
    rfl
  have hmass (p : P) : μ (F p) = μ W := by
    rw [htrans]
    exact (measurePreserving_mul_left μ (↑(r p) : I)⁻¹).measure_preimage hW.nullMeasurableSet
  change μ (e '' (J ×ˢ ideleFundamentalDomain v r)) = (classNumber K : ℝ≥0∞) * μ W
  rw [hunion, measure_iUnion hdisj hmeas]
  simp only [hmass, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]

end Masullo
