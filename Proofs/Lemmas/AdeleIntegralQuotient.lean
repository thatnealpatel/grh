module

public import Theorems.AdeleFundamentalDomain
public import Lemmas.FundamentalDomainQuotientMeasure
public import Mathlib.Topology.Algebra.Group.Quotient

import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Lemmas.FiniteCompletionCompact
import Mathlib.LinearAlgebra.Countable

/-! Borel descent on the topological additive adelic quotient. -/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical InnerProductSpace Masullo.AdeleStage

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A∞" => InfiniteAdeleRing K
local notation "A" => AdeleRing (𝓞 K) K
local notation "Δ" => AdeleRing.principalSubgroup (𝓞 K) K
local notation "Q" => A ⧸ Δ
local notation "π" => QuotientAddGroup.mk' Δ
local notation "b" => archimedeanIntegerBasis K
local notation "e" => archimedeanEuclideanToAdele K

namespace AdeleStage

public scoped instance : SecondCountableTopology A := by
  let : SecondCountableTopology A∞ := (e).symm.toHomeomorph.secondCountableTopology
  let (S : Finset V) : SecondCountableTopology (AdeleFiniteStage K S) := by
    change SecondCountableTopology (A∞ × (_ × _))
    infer_instance
  let (S : Finset V) : SecondCountableTopology (range (adeleFiniteStageEmbedding K (∅ ∪ S))) :=
    (isEmbedding_adeleFiniteStageEmbedding K (∅ ∪ S)).toHomeomorph.symm.secondCountableTopology
  exact secondCountableTopology_of_countable_cover
    (fun S ↦ (isOpenEmbedding_adeleFiniteStageEmbedding K (∅ ∪ S)).isOpen_range)
    (iUnion_range_adeleFiniteStageEmbedding K ∅)

public scoped instance : MeasurableSpace Q := borel _

public scoped instance : BorelSpace Q := ⟨rfl⟩

end AdeleStage

private theorem open_quotient : IsOpenQuotientMap (π : A → Q) :=
  QuotientAddGroup.isOpenQuotientMap_mk

public theorem measurable_adeleIntegralQuotient : Measurable (π : A → Q) :=
  (open_quotient K).continuous.measurable

private theorem injOn_quotient_cell : InjOn (π : A → Q) (adeleIntegralCell K) := by
  intro x hx y hy hxy
  obtain ⟨a, ha⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hxy
  have hy' : x - algebraMap K A a ∈ adeleIntegralCell K := by
    rwa [show algebraMap K A a = x - y from ha, sub_sub_cancel]
  have hx' : x - algebraMap K A 0 ∈ adeleIntegralCell K := by simpa using hx
  obtain ⟨c, _, hc⟩ := existsUnique_sub_mem_adeleIntegralCell K x
  have ha₀ := (hc a hy').trans (hc 0 hx').symm
  apply sub_eq_zero.mp
  simpa [ha₀] using ha.symm

private theorem nonempty_interior_cell : (interior (adeleIntegralCell K)).Nonempty := by
  let C := (b).equivFun ⁻¹' univ.pi (fun _ ↦ Ioo (0 : ℝ) 1)
  let B : Set A∞ := e '' C
  have hC : IsOpen C := (isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Ioo)).preimage
    (continuous_equivFun_basis b)
  have hB : IsOpen B := (e).toHomeomorph.isOpenMap _ hC
  have hsub : adeleIntegerRectangle K B ⊆ adeleIntegralCell K := by
    rintro x ⟨⟨y, hy, hyx⟩, hfinite⟩
    refine ⟨⟨y, fun i ↦ ?_, hyx⟩, hfinite⟩
    have hi : (b).equivFun y i ∈ Ioo (0 : ℝ) 1 := hy i (mem_univ _)
    exact ⟨hi.1.le, hi.2⟩
  have hO : IsOpen (adeleIntegerRectangle K B) := by
    rw [← image_adeleStageIntegerRectangle K B ∅, adeleStageIntegerRectangle]
    exact (isOpenEmbedding_adeleFiniteStageEmbedding K ∅).isOpenMap _
      (hB.prod ((isOpen_set_pi finite_univ (fun v _ ↦ Valued.isOpen_valuationSubring _)).prod isOpen_univ))
  let y := (b).equivFun.symm (fun _ ↦ (2 : ℝ)⁻¹)
  have hy : y ∈ C := by
    intro i _
    change (b).equivFun y i ∈ Ioo (0 : ℝ) 1
    rw [(b).equivFun.apply_symm_apply]
    exact ⟨by norm_num, by norm_num⟩
  exact ⟨(e y, 0), interior_maximal hsub hO
    ⟨mem_image_of_mem _ hy, fun _ ↦ zero_mem _⟩⟩

private theorem exists_open_injOn_quotient (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ InjOn (π : A → Q) U := by
  obtain ⟨y, hy⟩ := nonempty_interior_cell K
  let t : A := x - y
  refine ⟨(fun z : A ↦ t + z) '' interior (adeleIntegralCell K),
    isOpenMap_add_left t _ isOpen_interior, ⟨y, hy, sub_add_cancel _ _⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ heq
  have heq' : π z = π w := by
    simp only [map_add] at heq
    exact add_left_cancel heq
  exact congrArg (t + ·) (injOn_quotient_cell K (interior_subset hz) (interior_subset hw) heq')

public theorem discreteTopology_adelePrincipalSubgroup : DiscreteTopology Δ := by
  obtain ⟨U, hU, h₀, hinj⟩ := exists_open_injOn_quotient K (0 : A)
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  convert hU.preimage continuous_subtype_val using 1
  ext g
  constructor
  · intro hg
    simpa [mem_singleton_iff.mp hg] using h₀
  · intro hg
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    exact hinj hg h₀ ((QuotientAddGroup.eq_zero_iff _).mpr g.property |>.trans (map_zero _).symm)

public theorem isClosed_adelePrincipalSubgroup : IsClosed (Δ : Set A) := by
  let := discreteTopology_adelePrincipalSubgroup K
  exact AddSubgroup.isClosed_of_discreteTopology

/-- The closed Archimedean parallelepiped times the integral finite box
has compact image, and still meets all diagonal classes. -/
public theorem compactSpace_adeleIntegralQuotient : CompactSpace Q := by
  let B : Set A∞ := e '' (b).parallelepiped
  have hB : IsCompact B := (b).parallelepiped.isCompact.image (e).continuous
  let (v : V) : CompactSpace (v.adicCompletionIntegers K) :=
    compactSpace_finiteCompletionIntegers K v
  have hR : IsCompact (adeleIntegerRectangle K B) := by
    rw [← image_adeleStageIntegerRectangle K B ∅, adeleStageIntegerRectangle]
    apply IsCompact.image _ (isEmbedding_adeleFiniteStageEmbedding K ∅).continuous
    exact hB.prod ((isCompact_univ_pi fun v ↦ isCompact_iff_compactSpace.mpr
      (compactSpace_finiteCompletionIntegers K v.val)).prod isCompact_univ)
  have himage : (π : A → Q) '' adeleIntegerRectangle K B = univ := by
    apply eq_univ_of_forall
    intro c
    obtain ⟨a, rfl⟩ := (open_quotient K).surjective c
    obtain ⟨q, hq, _⟩ := existsUnique_sub_mem_adeleIntegralCell K a
    have hzero : π (algebraMap K A q) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨q, rfl⟩
    refine ⟨a - algebraMap K A q, ⟨image_mono (ZSpan.fundamentalDomain_subset_parallelepiped _)
      hq.1, hq.2⟩, by rw [map_sub, hzero, sub_zero]⟩
  exact ⟨himage ▸ hR.image (open_quotient K).continuous⟩

/-- Borel descent uses local injectivity on translates of an open subset of the cell. -/
public theorem measurable_of_comp_adeleIntegralQuotient {E : Type*} [MeasurableSpace E]
    {f : Q → E} (hf : Measurable (f ∘ π)) : Measurable f :=
  measurable_of_comp_openQuotientMap (open_quotient K) (exists_open_injOn_quotient K) hf

public theorem adeleIntegralQuotient_vadd (d : Δ) (a : A) : π (d +ᵥ a) = π a := by
  change π ((d : A) + a) = π a
  rw [map_add, show π (d : A) = 0 from (QuotientAddGroup.eq_zero_iff _).mpr d.property,
    zero_add]

/-- Index principal translations by the field itself, without multiplicity. -/
public def adelePrincipalIndex : K ≃ Δ :=
  Equiv.ofInjective (algebraMap K A) (AdeleRing.algebraMap_injective (𝓞 K) K)

public theorem countable_adelePrincipalSubgroup : Countable Δ := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  exact (adelePrincipalIndex K).surjective.countable

public theorem adelePrincipalIndex_tsum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : A → E) (a : A) : (∑' t : K, f (algebraMap K A t + a)) = ∑' d : Δ, f (d +ᵥ a) :=
  (adelePrincipalIndex K).tsum_eq (fun d : Δ ↦ f (d +ᵥ a))

/-- Pointwise Borel descent of the counting sum. For complex functions this
uses the totalized sum; the integral theorem supplies a.e. absolute summability. -/
public theorem exists_adeleCountingPeriodization {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] [T2Space E] [SecondCountableTopology E] [IsCompletelyPseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] {f : A → E} (hf : Measurable f) :
    ∃ F : Q → E, Measurable F ∧ ∀ a : A, F (π a) = ∑' t : K, f (algebraMap K A t + a) := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  let s : Q → A := Function.surjInv (open_quotient K).surjective
  let F (c : Q) := ∑' t : K, f (algebraMap K A t + s c)
  have hEq (a : A) : F (π a) = ∑' t : K, f (algebraMap K A t + a) := by
    have hs : π (s (π a)) = π a := Function.rightInverse_surjInv (open_quotient K).surjective (π a)
    obtain ⟨r, hr⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hs
    have ha : s (π a) = algebraMap K A r + a := sub_eq_iff_eq_add.mp hr.symm
    change (∑' t : K, f (algebraMap K A t + s (π a))) = _
    simp_rw [ha, ← add_assoc, ← map_add]
    exact (Equiv.addRight r).tsum_eq (fun t : K ↦ f (algebraMap K A t + a))
  refine ⟨F, measurable_of_comp_adeleIntegralQuotient K ?_, hEq⟩
  rw [show F ∘ π = _ from funext hEq]
  exact Measurable.tsum fun t ↦ hf.comp (measurable_const_add _)

end

end Masullo
