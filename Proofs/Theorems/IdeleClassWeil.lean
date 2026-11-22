module

public import Lemmas.IdeleFullPeriodization

/-! # Counting Weil integration on the full idele classes

Definition A.3.2.1, PDF pp. 559–560, fixes the full quotient scale by
counting on the principal group and `dt/t` in the norm coordinate.
The split of (A.2.2.12), p. 547, makes that coordinate Lebesgue in log.
For the discrete principal case of (D.1.2.1), p. 747, we transport the
actual Borel domain from Proposition A.2.3.10(2), p. 552, along this
split. The manuscript cites Weil integration; the proof here supplies
the restriction-pushforward equality of (D.1.2.5), p. 748, and measurable descent on the
full quotient, which are not consequences of the pointwise partition
alone. No measure is obtained by restricting to a norm fibre.

The last theorem gives the equal integrals in (3.2.2.11), p. 127,
on the Borel absolute-integrability domain. It does not prove the
Schwartz test-class bounds or identify analytic continuations.
Source reading: Provisional, from Markdown and numbered PDF text.
-/

open NumberField MeasureTheory Set
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped ENNReal Masullo Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "Γ" => Subgroup.op (IdeleGroup.principalSubgroup (𝓞 K) K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

private instance : Countable Kˣ := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  exact Units.val_injective.countable

private instance : Countable Γ := (ideleFullPrincipalIndex (K := K)).surjective.countable

private theorem tsum_invariant {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : I → E) (b : Kˣ) (x : I) : (∑' a : Kˣ, f (d a * (d b * x))) = ∑' a : Kˣ, f (d a * x) := by
  simp_rw [← mul_assoc, ← map_mul]
  exact (Equiv.mulRight b).tsum_eq (fun a : Kˣ ↦ f (d a * x))

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- Full-class measure in canonical log coordinates: Lebesgue in the log
variable and the counting quotient measure in the norm-one variable. -/
@[expose] public noncomputable def ideleClassQuotientMeasure (ν : Measure I₁)
    (v : InfinitePlace K) (r : P → I₁) : Measure C :=
  (logVolume.prod (ideleClassNormOneQuotientMeasure ν v r)).map τ

local notation "η" => ideleClassQuotientMeasure

variable (ν : Measure (ideleNormOne (K := K))) (v : InfinitePlace K)
  (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))

/-- The prescribed norm-one quotient volume determines the scale of the full
Haar measure by the log product with Lebesgue. -/
public theorem ideleClassQuotientMeasure_isHaarMeasure [ν.IsHaarMeasure]
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) (hfin : ν (ideleFundamentalDomain v r) < ∞) :
    (η ν v r).IsHaarMeasure := by
  let η₁ := ideleClassNormOneQuotientMeasure ν v r
  let : IsFiniteMeasure η₁ := ⟨(ideleClassNormOneQuotientMeasure_univ ν v r).symm ▸ hfin⟩
  let : η₁.IsHaarMeasure := ideleClassNormOneQuotientMeasure_isHaarMeasure ν v r hr hfin
  let : (logVolume.prod η₁).IsHaarMeasure := isHaarMeasure_logVolume_prod η₁
  exact (τ).isHaarMeasure_map _

variable [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]

/-- The two ways of constructing the full quotient measure agree: Log product
on the classes, or restriction to the full principal domain and pushforward. -/
public theorem ideleClassQuotientMeasure_eq_map_restrict [SFinite ν] (μ : Measure I)
    (hsplit : μ.map (σ).symm = logVolume.prod ν) :
    η ν v r = (μ.restrict (ideleFullFundamentalDomain v r)).map q := by
  let D := ideleFundamentalDomain v r
  have hs : Measurable σ := (σ).continuous.measurable
  have ht : Measurable τ := (τ).continuous.measurable
  have hq₁ : Measurable q₁ := isOpenQuotientMap_ideleClassQuotientNormOne.continuous.measurable
  have hsm : Measurable ((σ).symm : I → Multiplicative ℝ × I₁) :=
    (σ).symm.continuous.measurable
  let : SFinite logVolume := by
    have h := congrArg (Measure.map (Multiplicative.ofAdd : ℝ → Multiplicative ℝ))
      map_toAdd_logVolume
    rw [Measure.map_map measurable_ofAdd measurable_toAdd, show
      Multiplicative.ofAdd ∘ Multiplicative.toAdd = (id : Multiplicative ℝ → Multiplicative ℝ)
      from rfl, Measure.map_id] at h
    rw [h]
    infer_instance
  have hμ : (logVolume.prod ν).map σ = μ := by
    rw [← hsplit, Measure.map_map hs hsm]
    simp
  have hpre : σ ⁻¹' ideleFullFundamentalDomain v r = univ ×ˢ D :=
    (σ).injective.preimage_image _
  rw [← hμ, Measure.restrict_map hs (measurableSet_ideleFullFundamentalDomain v r), hpre,
    Measure.map_map measurable_ideleFullQuotient hs, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold ideleClassQuotientMeasure ideleClassNormOneQuotientMeasure
  have hprod : logVolume.prod ((ν.restrict D).map q₁) =
      (logVolume.prod (ν.restrict D)).map (Prod.map id q₁) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map logVolume (ν.restrict D) measurable_id hq₁
  rw [hprod, Measure.map_map ht (measurable_id.prodMap hq₁)]
  congr 1
  exact funext fun p ↦ (ideleFullQuotient_split p).symm

variable (hr : ∀ p, ideleIdealClassNormOne (K := K) (r p) = p)
  [SFinite ν] (μ : Measure (IdeleGroup (𝓞 K) K)) [μ.IsMulLeftInvariant]

variable (hsplit : μ.map (ideleLogSplit (ideleLogSection (w₀ : InfinitePlace K))
  (ideleLogNorm_section w₀)).symm = logVolume.prod ν)

include hr hsplit

/-- Full-class nonnegative Borel Weil formula, with counting mass one per
field unit. In particular, this applies to the absolute mass of any Borel test. -/
public theorem lintegral_ideleClass_Weil {f : I → ℝ≥0∞} (hf : Measurable f) :
    ∃ F : C → ℝ≥0∞, Measurable F ∧
      (∀ x, F (q x) = ∑' a : Kˣ, f (d a * x)) ∧
      (∫⁻ c, F c ∂(η ν v r)) = ∫⁻ x, f x ∂μ := by
  have hm : Measurable (fun x : I ↦ ∑' a : Kˣ, f (d a * x)) :=
    Measurable.tsum (fun a ↦ hf.comp (measurable_const_mul _))
  obtain ⟨F, hF, hperiod⟩ := exists_measurable_ideleFullQuotient_lift hm (tsum_invariant f)
  refine ⟨F, hF, hperiod, ?_⟩
  rw [ideleClassQuotientMeasure_eq_map_restrict ν v r μ hsplit]
  exact lintegral_periodization q (isFundamentalDomain_ideleFullFundamentalDomain μ v r hr)
    measurable_ideleFullQuotient hf hF (fun x ↦ (hperiod x).trans (ideleFullPrincipalIndex_tsum f x))

/-- Full-class complex Borel Weil formula. The principal sum is absolutely
summable for every representative of almost every class. -/
public theorem integral_ideleClass_Weil {f : I → ℂ} (hf : Measurable f) (hfi : Integrable f μ) :
    ∃ F : C → ℂ, Measurable F ∧ Integrable F (η ν v r) ∧
      (∀ x, F (q x) = ∑' a : Kˣ, f (d a * x)) ∧
      (∀ᵐ c ∂(η ν v r), ∀ x, q x = c → Summable fun a : Kˣ ↦ ‖f (d a * x)‖) ∧
      (∫ c, F c ∂(η ν v r)) = ∫ x, f x ∂μ := by
  have hm : Measurable (fun x : I ↦ ∑' a : Kˣ, f (d a * x)) :=
    Measurable.tsum (fun a ↦ hf.comp (measurable_const_mul _))
  obtain ⟨F, hF, hperiod⟩ := exists_measurable_ideleFullQuotient_lift hm (tsum_invariant f)
  obtain ⟨hFi, hInt⟩ := integral_periodization q
    (isFundamentalDomain_ideleFullFundamentalDomain μ v r hr) measurable_ideleFullQuotient hf hfi hF
    (fun x ↦ (hperiod x).trans (ideleFullPrincipalIndex_tsum f x))
  rw [← ideleClassQuotientMeasure_eq_map_restrict ν v r μ hsplit] at hFi hInt
  obtain ⟨B, hB, hBperiod, hBInt⟩ := lintegral_ideleClass_Weil ν v r hr μ hsplit hf.eNorm
  refine ⟨F, hF, hFi, hperiod, ?_, hInt⟩
  have hBfinite : ∀ᵐ c ∂(η ν v r), B c < ∞ :=
    ae_lt_top' hB.aemeasurable (hBInt.trans_ne hfi.2.ne)
  filter_upwards [hBfinite] with c hc x hx
  apply tsum_eNorm_ne_top_iff_summable_norm.mp
  rw [← hBperiod x, hx]
  exact hc.ne

/-- The absolutely integrable Mellin pairing in (3.2.2.11). The weight is
pulled back from the quotient, so it is constant on each principal orbit.
No convergence of the unweighted series is asserted on fibres where the
weight vanishes. -/
public theorem integral_ideleClass_Weil_weighted {f : I → ℂ} {c : C → ℂ}
    (hf : Measurable f) (hc : Measurable c) (hfi : Integrable (fun x ↦ f x * c (q x)) μ) :
    ∃ F : C → ℂ, Measurable F ∧ (∀ x, F (q x) = ∑' a : Kˣ, f (d a * x)) ∧
      Integrable (fun g ↦ F g * c g) (η ν v r) ∧
      (∀ᵐ g ∂(η ν v r), ∀ x, q x = g → Summable fun a : Kˣ ↦ ‖f (d a * x) * c g‖) ∧
      (∫ g, F g * c g ∂(η ν v r)) = ∫ x, f x * c (q x) ∂μ := by
  have hm : Measurable (fun x : I ↦ ∑' a : Kˣ, f (d a * x)) :=
    Measurable.tsum (fun a ↦ hf.comp (measurable_const_mul _))
  obtain ⟨F, hF, hperiod⟩ := exists_measurable_ideleFullQuotient_lift hm (tsum_invariant f)
  obtain ⟨B, _, hBi, hBperiod, hBabs, hBInt⟩ := integral_ideleClass_Weil ν v r hr μ hsplit
    (f := fun x ↦ f x * c (q x)) (hf.mul (hc.comp measurable_ideleFullQuotient)) hfi
  have hq (a : Kˣ) (x : I) : q (d a * x) = q x := by
    rw [map_mul, show q (d a) = 1 from (QuotientGroup.eq_one_iff (d a)).mpr ⟨a, rfl⟩]
    exact one_mul (q x)
  have hB (g : C) : B g = F g * c g := by
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective (q : I → C)) g
    change B (q x) = F (q x) * c (q x)
    rw [hBperiod, hperiod, ← tsum_mul_right]
    simp_rw [hq]
  have hBeq : B = fun g ↦ F g * c g := funext hB
  refine ⟨F, hF, hperiod, hBeq ▸ hBi, ?_, hBeq ▸ hBInt⟩
  filter_upwards [hBabs] with g hg x hx
  simpa only [hq, hx] using hg x hx

end Masullo
