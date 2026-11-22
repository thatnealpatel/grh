module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Lindelof

/-! Support for a countable fundamental-domain quotient. The invariance and
nonnegative integral arguments come from the checked `QuotientMeasureControl`
scratch controls; the actual quotient and its Borel descent are proved separately. -/

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace Masullo

section Descent

variable {G Q E : Type*} [TopologicalSpace G] [TopologicalSpace Q] [LindelofSpace Q]
    [MeasurableSpace G] [MeasurableSpace Q] [BorelSpace G] [BorelSpace Q] [MeasurableSpace E]
    {q : G → Q}

/-- Continuous inverse charts on a Lindelöf target detect Borel measurability. -/
public theorem measurable_of_comp_openQuotientMap (hq : IsOpenQuotientMap q)
    (hlocal : ∀ x, ∃ U : Set G, IsOpen U ∧ x ∈ U ∧ InjOn q U)
    {F : Q → E} (hF : Measurable (F ∘ q)) : Measurable F := by
  classical
  choose U hU hmem hinj using hlocal
  have hcover : (univ : Set Q) ⊆ ⋃ x, q '' U x := by
    intro y _
    obtain ⟨x, rfl⟩ := hq.surjective y
    exact mem_iUnion.mpr ⟨x, mem_image_of_mem q (hmem x)⟩
  obtain ⟨T, hTc, hT⟩ := isLindelof_univ.elim_countable_subcover _ (fun x ↦ hq.isOpenMap _ (hU x)) hcover
  intro A hA
  have hchart (x : G) : MeasurableSet ((F ⁻¹' A) ∩ (q '' U x)) := by
    let e := Equiv.Set.imageOfInjOn q (U x) (hinj x)
    let h := e.toHomeomorphOfContinuousOpen
      (hq.continuous.restrict (fun _ hx ↦ mem_image_of_mem q hx))
      (hq.isOpenMap.mapsToRestrict (hU x) (fun _ hx ↦ mem_image_of_mem q hx))
    have hs : Continuous (fun y : (q '' U x) ↦ (h.symm y : G)) :=
      continuous_subtype_val.comp h.symm.continuous
    have he (y : q '' U x) : q (h.symm y : G) = (y : Q) :=
      congrArg Subtype.val (h.apply_symm_apply y)
    have hm : Measurable (fun y : (q '' U x) ↦ F y) := by
      have heq : (F ∘ q) ∘ (fun y : (q '' U x) ↦ (h.symm y : G)) =
          (fun y : (q '' U x) ↦ F y) := funext fun y ↦ congrArg F (he y)
      exact heq ▸ hF.comp hs.measurable
    have hB := (hq.isOpenMap _ (hU x)).measurableSet.subtype_image (hm hA)
    convert hB using 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists]
    constructor
    · exact fun ⟨hy, hu⟩ ↦ ⟨y, hu, hy, rfl⟩
    · rintro ⟨_, hu, hy, rfl⟩
      exact ⟨hy, hu⟩
  have hEq : F ⁻¹' A = ⋃ x ∈ T, (F ⁻¹' A) ∩ (q '' U x) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hT (mem_univ y))
      exact mem_iUnion₂.mpr ⟨x, hx, hy, hxy⟩
    · intro hy
      obtain ⟨_, _, h, _⟩ := mem_iUnion₂.mp hy
      exact h
  rw [hEq]
  exact MeasurableSet.biUnion hTc fun x _ ↦ hchart x

end Descent

section Integration

variable {G Q Γ : Type*} [Group G] [Group Q] [Group Γ]
    [MeasurableSpace G] [MeasurableSpace Q] [MeasurableMul G] [MeasurableMul Q]
    [MulAction Γ G] [MeasurableConstSMul Γ G] [SMulCommClass G Γ G]
    {μ : Measure G} [μ.IsMulLeftInvariant] [SMulInvariantMeasure Γ G μ]
    {D : Set G}
    (q : G →* Q)

/-- The restriction pushforward is invariant under the quotient group. -/
public theorem invariant_map_restrict [Countable Γ] (hD : IsFundamentalDomain Γ D μ)
    (hq : Measurable q) (hsurj : Function.Surjective q)
    (horbit : ∀ (a : Γ) (x : G), q (a • x) = q x) :
    ((μ.restrict D).map q).IsMulLeftInvariant := by
  constructor
  intro c
  obtain ⟨g, rfl⟩ := hsurj c
  ext A hA
  have hm : Measurable (q g * ·) := measurable_const_mul _
  rw [Measure.map_apply hm hA, Measure.map_apply hq (hm hA), Measure.map_apply hq hA,
    Measure.restrict_apply (hq (hm hA)), Measure.restrict_apply (hq hA)]
  let B := q ⁻¹' A
  calc
    μ ((q ⁻¹' ((q g * ·) ⁻¹' A)) ∩ D) = μ ((fun x => g * x) ⁻¹' (B ∩ g • D)) := by
      congr 1
      ext x
      simp [B, Set.mem_smul_set_iff_inv_smul_mem, map_mul]
    _ = μ (B ∩ g • D) := measure_preimage_mul μ g _
    _ = μ (B ∩ D) := (hD.smul_of_comm g).measure_set_eq hD (hq hA) (fun a => by
      ext x
      simp [B, horbit])

omit [MeasurableMul G] [MeasurableMul Q] [SMulCommClass G Γ G] [μ.IsMulLeftInvariant] in
/-- Nonnegative Weil identity for a measurably descended periodization. -/
public theorem lintegral_periodization (hD : IsFundamentalDomain Γ D μ) (hq : Measurable q)
    [Countable Γ] {f : G → ℝ≥0∞} (hf : Measurable f)
    {F : Q → ℝ≥0∞} (hF : Measurable F) (hperiod : ∀ x, F (q x) = ∑' a : Γ, f (a • x)) :
    ∫⁻ c, F c ∂((μ.restrict D).map q) = ∫⁻ x, f x ∂μ := by
  rw [lintegral_map hF hq]
  simp_rw [hperiod]
  rw [lintegral_tsum (fun a : Γ => show AEMeasurable (fun x => f (a • x)) (μ.restrict D) from
    (hf.comp (measurable_const_smul a)).aemeasurable)]
  exact (hD.lintegral_eq_tsum'' f).symm

omit [MeasurableMul G] [MeasurableMul Q] [SMulCommClass G Γ G] [μ.IsMulLeftInvariant] in
/-- The complex Weil identity and integrability for a measurably descended
periodization of a Borel L¹ function. -/
public theorem integral_periodization (hD : IsFundamentalDomain Γ D μ) (hq : Measurable q)
    [Countable Γ] {f : G → ℂ} (hf : Measurable f) (hfi : Integrable f μ)
    {F : Q → ℂ} (hF : Measurable F) (hperiod : ∀ x, F (q x) = ∑' a : Γ, f (a • x)) :
    Integrable F ((μ.restrict D).map q) ∧
      (∫ c, F c ∂((μ.restrict D).map q)) = ∫ x, f x ∂μ := by
  have hm (a : Γ) : Measurable (fun x ↦ f (a • x)) := hf.comp (measurable_const_smul a)
  have htotal : (∑' a : Γ, ∫⁻ x, ‖f (a • x)‖ₑ ∂(μ.restrict D)) = ∫⁻ x, ‖f x‖ₑ ∂μ :=
    (hD.lintegral_eq_tsum'' (fun x ↦ ‖f x‖ₑ)).symm
  have hFi : Integrable F ((μ.restrict D).map q) := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    change (∫⁻ c, ‖F c‖ₑ ∂((μ.restrict D).map q)) < ∞
    rw [lintegral_map hF.eNorm hq]
    simp_rw [hperiod]
    calc
      (∫⁻ x, ‖∑' a : Γ, f (a • x)‖ₑ ∂(μ.restrict D))
          ≤ ∫⁻ x, ∑' a : Γ, ‖f (a • x)‖ₑ ∂(μ.restrict D) :=
        lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm
      _ = ∑' a : Γ, ∫⁻ x, ‖f (a • x)‖ₑ ∂(μ.restrict D) :=
        lintegral_tsum fun a ↦ (hm a).eNorm.aemeasurable
      _ < ∞ := htotal ▸ hfi.2
  refine ⟨hFi, ?_⟩
  rw [integral_map hq.aemeasurable hFi.1]
  simp_rw [hperiod]
  rw [integral_tsum (fun a ↦ (hm a).aestronglyMeasurable) (htotal.trans_ne hfi.2.ne)]
  exact (hD.integral_eq_tsum'' f hfi).symm

end Integration

end Masullo
