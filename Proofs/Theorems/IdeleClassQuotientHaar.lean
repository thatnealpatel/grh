module

public import Lemmas.IdelePrincipalPeriodization
public import Theorems.IdeleLogHaar
public import Theorems.DiscriminantNormalizedIdeleHaar
import Lemmas.ArchimedeanAngularMass

/-! # Counting-normalized Haar on the actual norm-one idele classes

Masullo gives the pointwise principal partition in Proposition A.2.3.10(2),
(A.2.3.25)–(26), PDF p. 552, and cites the quotient integral formula
(D.1.2.1), p. 747. Definition A.3.2.1, pp. 559–560, prescribes the
volume; §A.3.3.1, p. 561, uses it in the strip formula. Remark A.5.2.7,
p. 571, gives the restriction-pushforward prescription. To compare with
the upstairs measure of (A.3.2.5), p. 560, we use the actual open quotient
and prove Borel descent by a finite cover by inverse charts. The resulting
counting Weil identities fix the scale; invariance alone would not.
The mass then comes from the independently calculated local-product strip
of log length one, not from an assumption of the prescribed quotient mass.
Source reading: Provisional, from Markdown and numbered PDF text.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open NumberField.InfinitePlace (nrRealPlaces nrComplexPlaces)
open NumberField.Units (regulator torsionOrder)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped ENNReal Masullo Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "d" => idelePrincipalNormOne (K := K)
local notation "Γ" => Subgroup.op (MonoidHom.range (idelePrincipalNormOne (K := K)))
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)

variable [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

private theorem measurable_quotient : Measurable q₁ :=
  (isOpenQuotientMap_ideleClassQuotientNormOne (K := K)).continuous.measurable

private instance : Countable Kˣ := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  exact Units.val_injective.countable

private instance : Countable Γ := (idelePrincipalIndex (K := K)).surjective.countable

/-- Push Haar restricted to the idelic domain down to the actual norm-one
classes. This does not restrict any ambient measure to a norm-one fibre. -/
@[expose] public noncomputable def ideleClassNormOneQuotientMeasure (ν : Measure I₁)
    (v : InfinitePlace K) (r : P → I₁) : Measure C₁ :=
  (ν.restrict (ideleFundamentalDomain v r)).map q₁

local notation "η" => ideleClassNormOneQuotientMeasure

variable (ν : Measure (ideleNormOne (K := K))) (v : InfinitePlace K)
  (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))

/-- The quotient mass is the measured mass of the idelic domain. -/
public theorem ideleClassNormOneQuotientMeasure_univ :
    η ν v r univ = ν (ideleFundamentalDomain v r) := by
  rw [ideleClassNormOneQuotientMeasure, Measure.map_apply measurable_quotient MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

variable (hr : ∀ p, ideleIdealClassNormOne (K := K) (r p) = p)

include hr

/-- The pushforward is Haar as soon as the upstairs domain has finite mass.
A nonempty open set has nonempty open saturated preimage, which cannot
be null on the domain: Its countably many principal translates cover it. -/
public theorem ideleClassNormOneQuotientMeasure_isHaarMeasure [ν.IsHaarMeasure]
    (hfin : ν (ideleFundamentalDomain v r) < ∞) : (η ν v r).IsHaarMeasure := by
  have hq := isOpenQuotientMap_ideleClassQuotientNormOne (K := K)
  have hD := isFundamentalDomain_ideleFundamentalDomain v r hr ν
  let : IsFiniteMeasure (η ν v r) := ⟨(ideleClassNormOneQuotientMeasure_univ ν v r).symm ▸ hfin⟩
  refine
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := invariant_map_restrict q₁ hD measurable_quotient hq.surjective
        ideleClassQuotientNormOne_smul
      open_pos := ?_ }
  intro A hA hne hzero
  rw [ideleClassNormOneQuotientMeasure, Measure.map_apply measurable_quotient hA.measurableSet,
    Measure.restrict_apply (hA.measurableSet.preimage measurable_quotient)] at hzero
  have hz := hD.measure_zero_of_invariant (q₁ ⁻¹' A) (fun a ↦ by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem, ideleClassQuotientNormOne_smul]) hzero
  exact (ne_of_gt ((hA.preimage hq.continuous).measure_pos ν (hne.preimage hq.surjective))) hz

/-- Nonnegative Borel Weil formula on the actual norm-one classes. The inner
integral is the sum over `Kˣ` with counting mass one per element. -/
public theorem lintegral_ideleClassNormOne_Weil [ν.IsMulLeftInvariant]
    {f : I₁ → ℝ≥0∞} (hf : Measurable f) :
    ∃ F : C₁ → ℝ≥0∞, Measurable F ∧
      (∀ x, F (q₁ x) = ∑' a : Kˣ, f (d a * x)) ∧
      (∫⁻ c, F c ∂(η ν v r)) = ∫⁻ x, f x ∂ν := by
  have hm : Measurable (fun x : I₁ ↦ ∑' a : Kˣ, f (d a * x)) :=
    Measurable.tsum (fun a ↦ hf.comp (measurable_const_mul _))
  obtain ⟨F, hF, hperiod⟩ := exists_measurable_ideleClassQuotientNormOne_lift hm
    (idelePrincipal_tsum_mul f)
  exact ⟨F, hF, hperiod, lintegral_periodization q₁
    (isFundamentalDomain_ideleFundamentalDomain v r hr ν) measurable_quotient hf hF
    (fun x ↦ (hperiod x).trans (idelePrincipalIndex_tsum f x))⟩

/-- Borel complex L¹ Weil formula on the actual norm-one classes. For almost
every class, the series is absolutely summable for every representative;
`tsum` gives a Borel function also on the exceptional classes. -/
public theorem integral_ideleClassNormOne_Weil [ν.IsMulLeftInvariant]
    {f : I₁ → ℂ} (hf : Measurable f) (hfi : Integrable f ν) :
    ∃ F : C₁ → ℂ, Measurable F ∧ Integrable F (η ν v r) ∧
      (∀ x, F (q₁ x) = ∑' a : Kˣ, f (d a * x)) ∧
      (∀ᵐ c ∂(η ν v r), ∀ x, q₁ x = c → Summable fun a : Kˣ ↦ ‖f (d a * x)‖) ∧
      (∫ c, F c ∂(η ν v r)) = ∫ x, f x ∂ν := by
  have hm : Measurable (fun x : I₁ ↦ ∑' a : Kˣ, f (d a * x)) :=
    Measurable.tsum (fun a ↦ hf.comp (measurable_const_mul _))
  obtain ⟨F, hF, hperiod⟩ := exists_measurable_ideleClassQuotientNormOne_lift hm
    (idelePrincipal_tsum_mul f)
  obtain ⟨hFi, hInt⟩ := integral_periodization q₁
    (isFundamentalDomain_ideleFundamentalDomain v r hr ν) measurable_quotient hf hfi hF
    (fun x ↦ (hperiod x).trans (idelePrincipalIndex_tsum f x))
  obtain ⟨B, hB, hBperiod, hBInt⟩ := lintegral_ideleClassNormOne_Weil ν v r hr hf.eNorm
  refine ⟨F, hF, hFi, hperiod, ?_, hInt⟩
  have hBfinite : ∀ᵐ c ∂(η ν v r), B c < ∞ :=
    ae_lt_top' hB.aemeasurable (hBInt.trans_ne hfi.2.ne)
  filter_upwards [hBfinite] with c hc x hx
  apply tsum_eNorm_ne_top_iff_summable_norm.mp
  rw [← hBperiod x, hx]
  exact hc.ne

variable [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletionIntegers K)ˣ]
  [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletionIntegers K)ˣ]

/-- The exact volume of (A.3.2.1) for the pushforward from the norm-one factor
in the canonical log split. The stage restriction is the local-product input
from (A.3.2.5), not a hypothesis about the quotient measure. -/
public theorem measure_ideleClassNormOne_univ_of_logSplit
    (μ : Measure I) [μ.IsMulLeftInvariant] [SFinite ν]
    (hν : μ.map (σ).symm = logVolume.prod ν)
    (S : Finset V) (hS : ∀ w ∉ S, multiplicity w.asIdeal (differentIdeal ℤ (𝓞 K)) = 0)
    (hstage : μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
        (fun w ↦ finiteCompletionMultiplicativeHaar w) S) :
    η ν v r univ = (classNumber K : ℝ≥0∞) *
      (ENNReal.ofReal (regulator K) *
        (((2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) /
          (torsionOrder K : ℝ≥0∞))) *
      ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
  rw [ideleClassNormOneQuotientMeasure_univ,
    measure_ideleFundamentalDomain_of_logSplit μ ν hν S hS hstage v r hr,
    measure_archimedeanAngular_univ]

/-- Existence with the upstream normalization discharged: The normalized
local restricted product determines the upstairs scale, Lebesgue log volume
determines the second factor, and counting on the principal group determines
the norm-one quotient scale. This does not yet transport the measure to the
full idele classes. -/
public theorem exists_discriminantNormalizedIdeleClassNormOneHaar :
    ∃ (μ : Measure I) (ν : Measure I₁), μ.IsHaarMeasure ∧
      (∀ S : Finset V, (∀ w ∉ S, multiplicity w.asIdeal (differentIdeal ℤ (𝓞 K)) = 0) →
        μ.comap (ideleFiniteStageEmbedding K S) =
          ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
            (fun w ↦ finiteCompletionMultiplicativeHaar w) S) ∧
      ν.IsHaarMeasure ∧ μ.map (σ).symm = logVolume.prod ν ∧ (η ν v r).IsHaarMeasure ∧
      η ν v r univ = (classNumber K : ℝ≥0∞) *
        (ENNReal.ofReal (regulator K) *
          (((2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) /
            (torsionOrder K : ℝ≥0∞))) *
        ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
  classical
  obtain ⟨μ, hμ, _, hstage, _⟩ := exists_discriminantNormalizedIdeleHaar (K := K)
  let : μ.IsHaarMeasure := hμ
  have hlocal := (hstage μ).mp rfl
  obtain ⟨ν₀, hν₀, hsplit⟩ := ideleLogSplit_haar (ideleLogSection W) (ideleLogNorm_section W) μ
  let : ν₀.IsHaarMeasure := hν₀
  let : SecondCountableTopology I₁ :=
    (Topology.IsInducing.subtypeVal (t := (I₁ : Set I))).secondCountableTopology
  let HD := finite_differentIdeal_multiplicity_support (K := K)
  let S := HD.toFinset
  have hS (w : V) (hw : w ∉ S) : multiplicity w.asIdeal (differentIdeal ℤ (𝓞 K)) = 0 := by
    by_contra hn
    exact hw (HD.mem_toFinset.mpr hn)
  have hmass := measure_ideleClassNormOne_univ_of_logSplit ν₀ v r hr μ hsplit S hS (hlocal S hS)
  have hfin : ν₀ (ideleFundamentalDomain v r) < ∞ := by
    rw [← ideleClassNormOneQuotientMeasure_univ ν₀ v r, hmass]
    apply lt_top_iff_ne_top.mpr
    have hden : (torsionOrder K : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Nat.card_pos (α := NumberField.Units.torsion K) |>.ne'
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ENNReal.ofReal_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top <| ENNReal.div_ne_top
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞))
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hden
  exact ⟨μ, ν₀, hμ, hlocal, hν₀, hsplit, ideleClassNormOneQuotientMeasure_isHaarMeasure ν₀ v r hr hfin,
    hmass⟩

end Masullo
