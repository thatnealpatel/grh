module

public import Theorems.IdeleLogSplit
public import Theorems.RationalIdeleLogSection
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Lemmas.RationalFiniteUnits
import Theorems.IdeleIdealClassStrict
import Mathlib.Data.Nat.PrimeFin
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The literal rational orbital section weight

In Masullo, p. 495, (11.3.2.2), both translated indicators are evaluated on
ideles. We use the canonical section in log coordinates and integrate their
product against Haar on the norm-one ideles, not on the quotient by principal
ideles. The first indicator alone confines the integration variable to at most
one point. Thus the literal weight gives a zero skew integral for every kernel.
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Masullo

namespace Masullo

local notation "I" => IdeleGroup (𝓞 ℚ) ℚ
local notation "N" => ideleNormOne (K := ℚ)
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

private theorem logNorm_section (t : Multiplicative ℝ) :
    ideleLogNorm (rationalIdeleLogSection t) = t := by
  apply Multiplicative.toAdd.injective
  rw [ideleLogNorm_apply, ideleNorm_logSection, Real.log_exp]

/-- In a fixed norm-one orbit, at most one translate lies on the section. -/
public theorem rationalOrbitalSectionFiber_subsingleton (ξ : ℚˣ) (x : I) :
    {g : N | principal ξ * g.val * x ∈ range rationalIdeleLogSection}.Subsingleton := by
  rintro g ⟨t, ht⟩ h ⟨u, hu⟩
  have norm_translate (k : N) : ideleLogNorm (principal ξ * k.val * x) =
      ideleLogNorm (principal ξ) * ideleLogNorm x := by
    have hk : ideleLogNorm k.val = 1 := by
      apply Multiplicative.toAdd.injective
      rw [ideleLogNorm_apply, (mem_ideleNormOne _).mp k.property, Real.log_one]
      rfl
    rw [map_mul, map_mul, hk, mul_one]
  have htu : t = u := by
    rw [← logNorm_section t, ← logNorm_section u, ht, hu, norm_translate, norm_translate]
  exact Subtype.ext (mul_left_cancel (mul_right_cancel (ht.symm.trans (htu ▸ hu))))

/-- The norm-one subgroup contains a continuous injective image of the compact,
infinite product of the finite integral unit groups, so it cannot be discrete. -/
public theorem not_discreteTopology_rationalIdeleNormOne :
    ¬ DiscreteTopology (ideleNormOne (K := ℚ)) := by
  classical
  intro hdisc
  let V := HeightOneSpectrum (𝓞 ℚ)
  let : Infinite V := Infinite.of_injective _
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  let (v : V) : Nontrivial (v.adicCompletionIntegers ℚ)ˣ := by
    let : CharZero (v.adicCompletion ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
    refine ⟨⟨-1, 1, fun h ↦ ?_⟩⟩
    apply Ring.neg_one_ne_one_of_char_ne_two (R := v.adicCompletion ℚ)
      (by rw [ringChar.eq_zero]; decide)
    simpa only [Units.coe_neg_one, Units.val_one, map_neg, map_one] using
      congrArg (fun u : (v.adicCompletionIntegers ℚ)ˣ ↦
        (v.adicCompletionIntegers ℚ).subtype u.val) h
  let : CompactSpace RationalFiniteUnits := compactSpace_rationalFiniteUnits
  -- In the empty stage all finite coordinates are integral units; fix the infinite part to one.
  let s (u : RationalFiniteUnits) : IdeleFiniteStage ℚ ∅ := (1, 1, fun v ↦ u v.val)
  have hs : Function.Injective s := by
    intro u w h
    funext v
    exact congrArg (fun x : IdeleFiniteStage ℚ ∅ ↦ x.2.2 ⟨v, Finset.notMem_empty v⟩) h
  have hcs : Continuous s :=
    continuous_const.prodMk (continuous_const.prodMk (continuous_pi fun v ↦ continuous_apply v.val))
  let j := ideleFiniteStageEmbedding ℚ ∅
  have hn (u : RationalFiniteUnits) : j (s u) ∈ ideleNormOne := by
    rw [mem_ideleNormOne, ideleNorm_eq_abs_rationalIdeleReal]
    · unfold rationalIdeleReal
      rw [ideleFiniteStageEmbedding_infinite]
      simp [s]
    · intro v
      rw [ideleFiniteStageEmbedding_finite_notMem ℚ ∅ (s u) v (Finset.notMem_empty v)]
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v).isUnit
  let f (u : RationalFiniteUnits) : ideleNormOne (K := ℚ) := ⟨j (s u), hn u⟩
  have hj := isOpenEmbedding_ideleFiniteStageEmbedding ℚ ∅
  have hf : Continuous f := (hj.continuous.comp hcs).subtype_mk hn
  have hi : Function.Injective f := fun _ _ h ↦ hs (hj.injective (congrArg Subtype.val h))
  exact (Set.infinite_range_of_injective hi) (isCompact_range hf).finite_of_discrete

/-- The identity is an accumulation point of the other norm-one rational ideles. -/
public theorem rationalIdeleNormOne_puncturedNhds_one_neBot : (𝓝[≠] (1 : N)).NeBot :=
  ⟨fun h ↦ not_discreteTopology_rationalIdeleNormOne
    (discreteTopology_of_isOpen_singleton_one ((isOpen_singleton_iff_punctured_nhds _).2 h))⟩

set_option linter.concreteInstances false

variable [MeasurableSpace N]

/-- The scalar weight of p. 495, (11.3.2.2), for the canonical rational section. -/
@[expose] public noncomputable def rationalOrbitalSectionWeight (μ : Measure N) (E : Set N)
    (xy : I × I) : ℝ :=
  ∑' ξ : ℚˣ, ∫ g in E,
    (range rationalIdeleLogSection).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
      (range rationalIdeleLogSection).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2) ∂μ

variable [BorelSpace N]

/-- Every upstairs norm-one Haar measure gives zero mass to points. -/
public theorem rationalNormOneHaar_nullSingletonClass (μ : Measure N) [μ.IsHaarMeasure] :
    NullSingletonClass μ := by
  have := rationalIdeleNormOne_puncturedNhds_one_neBot
  infer_instance

/-- In fact there are no measurable atoms, not just no point masses. -/
public theorem rationalNormOneHaar_noAtoms (μ : Measure N) [μ.IsHaarMeasure] : NoAtoms μ := by
  let := rationalNormOneHaar_nullSingletonClass μ
  let : SecondCountableTopology N :=
    (Topology.IsInducing.subtypeVal (t := (N : Set I))).secondCountableTopology
  constructor
  intro s hs
  obtain ⟨x, _, hx⟩ := exists_mem_forall_mem_nhdsWithin_pos_measure hs.measure_ne_zero
  obtain ⟨U, hxU, ho, hlt⟩ := ({x} : Set N).exists_isOpen_lt_of_lt (μ s)
    (by simpa only [measure_singleton] using hs.pos : μ {x} < μ s)
  exact (hs.measure_eq_zero_or_eq inter_subset_left).elim
    (hx (s ∩ U) (inter_mem_nhdsWithin s (ho.mem_nhds (hxU (mem_singleton x))))).ne'
    ((measure_mono inter_subset_right).trans_lt hlt).ne

/-- The literal section weight vanishes everywhere, with no measurability assumption on `E`. -/
public theorem rationalOrbitalSectionWeight_eq_zero (μ : Measure N) [μ.IsHaarMeasure] (E : Set N)
    (xy : I × I) : rationalOrbitalSectionWeight μ E xy = 0 := by
  let := rationalNormOneHaar_nullSingletonClass μ
  unfold rationalOrbitalSectionWeight
  refine (tsum_congr (g := fun _ ↦ (0 : ℝ)) fun ξ ↦ ?_).trans tsum_zero
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    ((rationalOrbitalSectionFiber_subsingleton ξ xy.1).measure_zero (μ.restrict E))] with g hg
  rw [indicator_of_notMem hg, zero_mul]
  rfl

/-- Any complex kernel (including any masks) gives zero on the weighted skew diagonal.
In log coordinates the outer measure may, in particular, be Haar on the log line. -/
public theorem rationalOrbitalSectionWeight_skewIntegral_eq_zero (μ : Measure N) [μ.IsHaarMeasure]
    (E : Set N) (ν : Measure (Multiplicative ℝ)) (K : I × I → ℂ) :
    (∑' ξ : ℚˣ, ∫ t, ∫ g in E,
      let xy := (rationalIdeleLogSection t, principal ξ * g.val * rationalIdeleLogSection t)
      (rationalOrbitalSectionWeight μ E xy : ℂ) * K xy ∂μ ∂ν) = 0 := by
  simp [rationalOrbitalSectionWeight_eq_zero]

end Masullo
