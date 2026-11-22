module

public import Theorems.AdeleRestrictedProductHaar
public import Theorems.FiniteAdeleTraceCharacter
public import Theorems.FiniteBoxFourier

import Lemmas.FiniteCompletionCompact
import Mathlib.MeasureTheory.Integral.Pi

/-! # The finite-stage integral of a translated finite-adele box

Masullo's (2.2.4.32), PDF p. 92, gives the tensor shape and conjugated
kernel. The finite test factors must be evaluated at the integration variable,
not at the frequency. The local measures are those of Definition A.3.1.2,
p. 556, and the positive finite trace phases are those of Example A.3.1.10,
p. 558. The conjugate of the corrected finite-adele character uses those
positive phases. Here the box and character are both restricted to the
actual stage before Fubini; the omitted factors are one by integrality and
Haar normalization. Source reading: Provisional, pinned Markdown and PDF layout.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ComplexConjugate Padic Pointwise

namespace Masullo

open scoped AdeleStage

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "A" => AdeleRing (𝓞 K) K
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "ν[" v "]" => finiteCompletionNormalizedHaar v
local notation "D[" a "," g "," v "]" => ((a v + ·) '' (Units.val g v • (O[v] : Set K[v])))

/-- The translated box in the actual finite adele ring. -/
@[expose] public def finiteAdeleBox (a : F) (g : Fˣ) : Set F :=
  {z | ∀ v : V, z v ∈ D[a,g,v]}

/-- The box indicator (taking the real values zero and one in `ℂ`) times
the conjugated finite-adele trace character at the diagonal frequency. -/
@[expose] public def finiteAdeleBoxFourierKernel (a : F) (g : Fˣ) (y : K) (z : F) : ℂ :=
  (finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) z *
    conj (numberFieldFiniteAdeleAddChar (z * algebraMap K F y))

/-- The conditions under which a stage captures a box and its diagonal
Fourier kernel, with a probability measure on the omitted coordinates. -/
public structure FiniteBoxStageConditions (a : F) (g : Fˣ) (y : K) (S : Finset V) : Prop where
  center : ∀ v ∉ S, a v ∈ O[v]
  scale : ∀ v ∉ S, g.val v ∈ O[v]
  inverse : ∀ v ∉ S, g.inv v ∈ O[v]
  frequency : ∀ v ∉ S, (algebraMap K F y) v ∈ O[v]
  mass : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1

/-- Include all four sets of nonintegral coordinates, the Haar exceptions,
and any initially prescribed places. -/
public theorem exists_finiteBoxStageConditions (a : F) (g : Fˣ) (y : K) (E : Finset V) :
    ∃ S : Finset V, E ⊆ S ∧ FiniteBoxStageConditions a g y S := by
  classical
  obtain ⟨M, hM⟩ := exists_finiteCompletionIntegerMass_exceptions K
  have hm : ∀ᶠ v : V in cofinite, finiteCompletionIntegerMass K v = 1 := by
    apply eventually_cofinite.mpr
    refine M.finite_toSet.subset fun v hv ↦ ?_
    exact (hM v).mpr hv
  have h : ∀ᶠ v : V in cofinite,
      a v ∈ O[v] ∧ g.val v ∈ O[v] ∧ g.inv v ∈ O[v] ∧
        (algebraMap K F y) v ∈ O[v] ∧ finiteCompletionIntegerMass K v = 1 :=
    a.cofinite_mem_adicCompletionIntegers.and (g.val.cofinite_mem_adicCompletionIntegers.and
      (g.inv.cofinite_mem_adicCompletionIntegers.and
        ((algebraMap K F y).cofinite_mem_adicCompletionIntegers.and hm)))
  let S := E ∪ (eventually_cofinite.mp h).toFinset
  have hS : ∀ v ∉ S, a v ∈ O[v] ∧ g.val v ∈ O[v] ∧ g.inv v ∈ O[v] ∧
      (algebraMap K F y) v ∈ O[v] ∧ finiteCompletionIntegerMass K v = 1 := by
    intro v hv
    by_contra hn
    exact hv (Finset.mem_union_right _ ((eventually_cofinite.mp h).mem_toFinset.mpr hn))
  exact ⟨S, Finset.subset_union_left, ⟨fun v hv ↦ (hS v hv).1, fun v hv ↦ (hS v hv).2.1,
    fun v hv ↦ (hS v hv).2.2.1, fun v hv ↦ (hS v hv).2.2.2.1,
    fun v hv ↦ (hS v hv).2.2.2.2⟩⟩

private theorem localBox_subset_integers (a : F) (g : Fˣ) (v : V)
    (ha : a v ∈ O[v]) (hg : g.val v ∈ O[v]) : D[a,g,v] ⊆ O[v] := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  exact (O[v]).toSubring.add_mem ha ((O[v]).toSubring.mul_mem hg ht)

private theorem localBox_eq_integers (a : F) (g : Fˣ) (v : V)
    (ha : a v ∈ O[v]) (hg : g.val v ∈ O[v]) (hi : g.inv v ∈ O[v]) :
    D[a,g,v] = (O[v] : Set K[v]) := by
  refine (localBox_subset_integers a g v ha hg).antisymm fun x hx ↦ ?_
  have h : g.val v * g.inv v = (1 : K[v]) := congrArg (fun z : F ↦ z v) g.val_inv
  refine ⟨x - a v, ⟨g.inv v * (x - a v),
    (O[v]).toSubring.mul_mem hi ((O[v]).toSubring.sub_mem hx ha), ?_⟩,
    by
      change a v + (x - a v) = x
      rw [add_comm, sub_add_cancel]⟩
  change g.val v * (g.inv v * (x - a v)) = _
  rw [← mul_assoc, h, one_mul]

/-- The full box cylinder is contained in the image of the stage. Inverse
integrality is needed for equality of the omitted boxes, not for containment. -/
public theorem finiteAdeleBox_preimage_snd_subset_stage (a : F) (g : Fˣ) (S : Finset V)
    (ha : ∀ v ∉ S, a v ∈ O[v]) (hg : ∀ v ∉ S, g.val v ∈ O[v]) :
    Prod.snd ⁻¹' finiteAdeleBox a g ⊆ range (adeleFiniteStageEmbedding K S) := by
  rw [range_adeleFiniteStageEmbedding]
  exact fun _ hz v hv ↦ localBox_subset_integers a g v (ha v hv) (hg v hv) (hz v)

private theorem isCompact_localBox (a : F) (g : Fˣ) (v : V) : IsCompact D[a,g,v] := by
  have hO : IsCompact (O[v] : Set K[v]) :=
    isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)
  exact (hO.image (continuous_const.mul continuous_id)).image (continuous_const.add continuous_id)

private def localPhase (y : K) (v : V) (t : K[v]) : ℂ :=
  finiteCompletionTraceAddChar v ((algebraMap K F y) v * t)

private theorem localPhase_eq_one_of_integral (y : K) (v : V) {t : K[v]}
    (hy : (algebraMap K F y) v ∈ O[v]) (ht : t ∈ O[v]) : localPhase y v t = 1 :=
  finiteCompletion_traceChar_eq_one_of_integral v ⟨_, (O[v]).toSubring.mul_mem hy ht⟩

private theorem continuous_localPhase (y : K) (v : V) : Continuous (localPhase y v) := by
  let _ := finiteCompletion_moduleFinite v
  change Continuous (fun t : K[v] ↦ padicStdAddChar (finiteCompletionBasePrime v)
    (Algebra.trace ℚ_[finiteCompletionBasePrime v] K[v] ((algebraMap K F y) v * t)))
  have hmul : Continuous (fun t : K[v] ↦ (algebraMap K F y) v * t) :=
    continuous_const.mul continuous_id
  exact (continuous_padicStdAddChar _).comp
    ((Algebra.trace ℚ_[finiteCompletionBasePrime v] K[v]).continuous_of_finiteDimensional.comp hmul)

private def localKernel (a : F) (g : Fˣ) (y : K) (v : V) : K[v] → ℂ :=
  D[a,g,v].indicator (localPhase y v)

private theorem integrable_localKernel (a : F) (g : Fˣ) (y : K) (v : V) :
    Integrable (localKernel a g y v) ν[v] := by
  rw [localKernel, integrable_indicator_iff (isCompact_localBox a g v).measurableSet]
  exact (continuous_localPhase y v).continuousOn.integrableOn_compact (isCompact_localBox a g v)

private theorem integral_localKernel (a : F) (g : Fˣ) (y : K) (v : V) :
    (∫ t, localKernel a g y v t ∂ν[v]) = finiteBoxLocalFourier a g y v := by
  rw [localKernel, integral_indicator (isCompact_localBox a g v).measurableSet]
  rfl

/-- Off the stage, the translated box is the integer ring, the local trace
phase is trivial there, and its normalized additive Haar mass is one. -/
public theorem finiteBoxLocalFourier_eq_one_off_stage (a : F) (g : Fˣ) (y : K)
    (S : Finset V) (hS : FiniteBoxStageConditions a g y S) (v : V) (hv : v ∉ S) :
    finiteBoxLocalFourier a g y v = 1 := by
  rw [← integral_localKernel, localKernel, localBox_eq_integers a g v (hS.center v hv)
    (hS.scale v hv) (hS.inverse v hv)]
  have hO : MeasurableSet (O[v] : Set K[v]) := (Valued.isOpen_valuationSubring _).measurableSet
  rw [integral_indicator hO,
    setIntegral_congr_fun hO (fun _ ht ↦ localPhase_eq_one_of_integral y v (hS.frequency v hv) ht),
    setIntegral_const, measureReal_def]
  change (finiteCompletionIntegerMass K v).toReal • (1 : ℂ) = 1
  simp [hS.mass v hv]

/-- The finite projection of the stage does not use its infinite coordinate. -/
public theorem adeleFiniteStageEmbedding_finite_eq_zero (S : Finset V)
    (x : AdeleFiniteStage K S) :
    (adeleFiniteStageEmbedding K S x).2 = (adeleFiniteStageEmbedding K S (0, x.2)).2 := by
  classical
  apply FiniteAdeleRing.ext K
  intro v
  by_cases hv : v ∈ S
  · rw [adeleFiniteStageEmbedding_finite_mem K S x v hv,
      adeleFiniteStageEmbedding_finite_mem K S (0, x.2) v hv]
  · rw [adeleFiniteStageEmbedding_finite_notMem K S x v hv,
      adeleFiniteStageEmbedding_finite_notMem K S (0, x.2) v hv]

private theorem stageKernel_eq_prod (a : F) (g : Fˣ) (y : K) (S : Finset V)
    (hS : FiniteBoxStageConditions a g y S) (x : AdeleFiniteStage K S) :
    finiteAdeleBoxFourierKernel a g y (adeleFiniteStageEmbedding K S x).2 =
      ∏ v : {v // v ∈ S}, localKernel a g y v.val (x.2.1 v) := by
  classical
  let z := (adeleFiniteStageEmbedding K S x).2
  have hbox : z ∈ finiteAdeleBox a g ↔ ∀ v : {v // v ∈ S}, x.2.1 v ∈ D[a,g,v.val] := by
    constructor
    · intro hz v
      rw [← adeleFiniteStageEmbedding_finite_mem K S x v.val v.property]
      exact hz v.val
    · intro hz v
      change (adeleFiniteStageEmbedding K S x).2 v ∈ D[a,g,v]
      by_cases hv : v ∈ S
      · rw [adeleFiniteStageEmbedding_finite_mem K S x v hv]
        exact hz ⟨v, hv⟩
      · rw [adeleFiniteStageEmbedding_finite_notMem K S x v hv,
          localBox_eq_integers a g v (hS.center v hv) (hS.scale v hv) (hS.inverse v hv)]
        exact (x.2.2 ⟨v, hv⟩).property
  have hz_freq : ∀ v ∉ S, (z * algebraMap K F y) v ∈ O[v] := by
    intro v hv
    change (adeleFiniteStageEmbedding K S x).2 v * (algebraMap K F y) v ∈ O[v]
    rw [adeleFiniteStageEmbedding_finite_notMem K S x v hv]
    exact (O[v]).toSubring.mul_mem (x.2.2 ⟨v, hv⟩).property (hS.frequency v hv)
  change finiteAdeleBoxFourierKernel a g y z = _
  by_cases hz : z ∈ finiteAdeleBox a g
  · rw [finiteAdeleBoxFourierKernel, indicator_of_mem hz, one_mul,
      conj_numberFieldFiniteAdeleAddChar_eq_prod _ S hz_freq, ← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro v _
    rw [localKernel, indicator_of_mem (hbox.mp hz v), localPhase]
    congr 1
    change (adeleFiniteStageEmbedding K S x).2 v.val * (algebraMap K F y) v.val = _
    rw [adeleFiniteStageEmbedding_finite_mem K S x v.val v.property, mul_comm]
  · obtain ⟨v, hv⟩ := not_forall.mp (mt hbox.mpr hz)
    rw [finiteAdeleBoxFourierKernel, indicator_of_notMem hz, zero_mul,
      Finset.prod_eq_zero (Finset.mem_univ v) (indicator_of_notMem hv _)]

-- The canonical finite part of the stage measure, with no Archimedean factor.
local notation "μf[" S "]" =>
  Measure.prod (Measure.pi (fun v : {v : V // v ∈ S} ↦ ν[Subtype.val v]))
    (Measure.infinitePi (adeleFiniteStageOutsideFactor K S))

/-- On the actual stage, the conjugated finite-adele Fourier integrand of the
translated box is integrable and has the expected finite local product.
The omitted factors evaluate to one, including when `y = 0` or `S = ∅`. -/
public theorem finiteAdeleBox_stage_fourier (a : F) (g : Fˣ) (y : K) (S : Finset V)
    (hS : FiniteBoxStageConditions a g y S) :
    Integrable (fun b ↦ finiteAdeleBoxFourierKernel a g y
      (adeleFiniteStageEmbedding K S (0, b)).2) μf[S] ∧
    (∫ b, finiteAdeleBoxFourierKernel a g y (adeleFiniteStageEmbedding K S (0, b)).2 ∂μf[S]) =
      ∏ᶠ v : V, finiteBoxLocalFourier a g y v := by
  classical
  let μ := Measure.pi (fun v : {v : V // v ∈ S} ↦ ν[v.val])
  let τ := Measure.infinitePi (adeleFiniteStageOutsideFactor K S)
  let : IsProbabilityMeasure τ := adeleFiniteStageOutside_isProbabilityMeasure K S hS.mass
  simp_rw [stageKernel_eq_prod a g y S hS]
  let f (x : (v : {v // v ∈ S}) → K[v.val]) := ∏ v, localKernel a g y v.val (x v)
  have hf : Integrable f μ := Integrable.fintype_prod_dep fun v ↦ integrable_localKernel a g y v.val
  refine ⟨hf.comp_fst τ, ?_⟩
  calc
    _ = ∫ x, f x ∂μ := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
        integral_fun_fst (μ := μ) (ν := τ) f
    _ = ∏ v : {v // v ∈ S}, finiteBoxLocalFourier a g y v.val := by
      dsimp only [f, μ]
      rw [integral_fintype_prod_eq_prod]
      simp only [integral_localKernel]
    _ = ∏ᶠ v : V, finiteBoxLocalFourier a g y v := by
      rw [Finset.prod_coe_sort, finprod_eq_prod_of_mulSupport_subset]
      intro v hv
      by_contra hn
      exact hv (finiteBoxLocalFourier_eq_one_off_stage a g y S hS v hn)

end

end Masullo
