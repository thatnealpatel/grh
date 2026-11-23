module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order

/-! # Signed divisor limits in an open slab

Clearing two distinct points adds one order at each point, whether or not
it is a pole. Absolute summability over the numerator zeros then gives the
signed divisor limit for height truncations, with no boundary hypotheses.
-/

open Complex Filter Set
open scoped Topology

namespace Masullo

private theorem analyticOrderAt_ne_top_of_anchor {H : ℂ → ℂ} {a : ℂ}
    (hH : Differentiable ℂ H) (ha : H a ≠ 0) (z : ℂ) : analyticOrderAt H z ≠ ⊤ := by
  intro ht
  exact ha (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hH.analyticAt).mp ht) a)

private theorem meromorphicOrderAt_sub_const_eq (p z : ℂ) :
    meromorphicOrderAt (fun s : ℂ ↦ s - p) z = ((if z = p then (1 : ℤ) else 0) : WithTop ℤ) := by
  by_cases h : z = p
  · subst z
    simp
  · have han : AnalyticAt ℂ (fun s : ℂ ↦ s - p) z := by fun_prop
    rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h)]
    simp [h]

/-- The order of `L` is finite everywhere. On the punctured germ the clearing
identity subtracts exactly one from the numerator order at each clearing point,
without imposing a value or requiring a pole there. -/
public theorem meromorphicOrderAt_eq_sub_clearingOrders {L H : ℂ → ℂ} {a z₀ z₁ : ℂ}
    (hH : Differentiable ℂ H) (ha : H a ≠ 0) (_h₀₁ : z₀ ≠ z₁)
    (hclear : ∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) (z : ℂ) :
    meromorphicOrderAt L z =
      (((analyticOrderNatAt H z : ℤ) - (if z = z₀ then 1 else 0) -
        (if z = z₁ then 1 else 0) : ℤ) : WithTop ℤ) := by
  classical
  let q (s : ℂ) := (s - z₁) * (s - z₀)
  have hne (p : ℂ) : ∀ᶠ s in 𝓝[≠] z, s ≠ p := by
    by_cases h : z = p
    · subst p
      exact self_mem_nhdsWithin
    · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
  have heq : L =ᶠ[𝓝[≠] z] fun s ↦ H s / q s := by
    filter_upwards [hne z₁, hne z₀] with s hs₁ hs₀
    rw [hclear s hs₁ hs₀, mul_comm, mul_div_cancel_right₀ _
      (mul_ne_zero (sub_ne_zero.mpr hs₁) (sub_ne_zero.mpr hs₀))]
  have hq : meromorphicOrderAt q z =
      (((if z = z₁ then 1 else 0) + (if z = z₀ then 1 else 0) : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt ((· - z₁) * (· - z₀)) z = _
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
      meromorphicOrderAt_sub_const_eq, meromorphicOrderAt_sub_const_eq, WithTop.coe_add]
    split_ifs <;> norm_num
  rw [meromorphicOrderAt_congr heq]
  change meromorphicOrderAt (H / q) z = _
  have han := hH.analyticAt z
  rw [meromorphicOrderAt_div han.meromorphicAt (by dsimp [q]; fun_prop), hq,
    han.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_anchor hH ha z),
    ENat.map_natCast]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_eq_coe]
  ring

private theorem rectangleZeros_finite {H : ℂ → ℂ} {a : ℂ}
    (hH : Differentiable ℂ H) (ha : H a ≠ 0) (T : ℝ) :
    ((Icc (-1 : ℝ) 2 ×ℂ Icc (-T) T) ∩ H ⁻¹' {0}).Finite := by
  let Z : Set ℂ := H ⁻¹' {0}
  have hZ : Zᶜ ∈ Filter.codiscrete ℂ :=
    (show AnalyticOnNhd ℂ H univ from fun z _ ↦ hH.analyticAt z).preimage_zero_mem_codiscrete ha
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hZ
  exact ((isCompact_Icc.reProdIm isCompact_Icc).inter_right hclosed).finite
    (hdisc.mono inter_subset_right)

/-- Absolute summability of the tested entire numerator orders on the open slab
implies absolute summability and height exhaustion for the tested signed
meromorphic orders. The truncations retain precisely the nonzero signed orders
strictly below the height cut. No boundary nonvanishing is needed. -/
public theorem signedSlabDivisor_limit {L H Φ : ℂ → ℂ} {a z₀ z₁ : ℂ}
    (hH : Differentiable ℂ H) (ha : H a ≠ 0) (h₀₁ : z₀ ≠ z₁)
    (hclear : ∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s)
    (hsum : Summable (fun z : {z : ℂ // -1 < z.re ∧ z.re < 2 ∧ H z = 0} ↦
      ‖(analyticOrderNatAt H z.val : ℂ) * Φ z.val‖)) :
    ∃ S : ℝ → Finset {z : ℂ // -1 < z.re ∧ z.re < 2},
      (∀ T z, z ∈ S T ↔ (meromorphicOrderAt L z.val).untop₀ ≠ 0 ∧ |z.val.im| < T) ∧
      Summable (fun z : {z : ℂ // -1 < z.re ∧ z.re < 2} ↦
        ‖((meromorphicOrderAt L z.val).untop₀ : ℂ) * Φ z.val‖) ∧
      ∀ T : ℕ → ℝ, Tendsto T atTop atTop →
        Tendsto (fun n ↦ ∑ z ∈ S (T n), ((meromorphicOrderAt L z.val).untop₀ : ℂ) * Φ z.val)
          atTop (𝓝 (∑' z : {z : ℂ // -1 < z.re ∧ z.re < 2},
            ((meromorphicOrderAt L z.val).untop₀ : ℂ) * Φ z.val)) := by
  classical
  let A := {z : ℂ // -1 < z.re ∧ z.re < 2}
  let Z : Set A := {z | H z.val = 0}
  let g (z : A) := (analyticOrderNatAt H z.val : ℂ) * Φ z.val
  let c (z : A) := (meromorphicOrderAt L z.val).untop₀
  let f (z : A) := (c z : ℂ) * Φ z.val
  have hnat (z : A) (hz : H z.val ≠ 0) : analyticOrderNatAt H z.val = 0 := by
    simp [analyticOrderNatAt, (hH.analyticAt z.val).analyticOrderAt_eq_zero.mpr hz]
  have hc (z : A) (hz₀ : z.val ≠ z₀) (hz₁ : z.val ≠ z₁) :
      c z = (analyticOrderNatAt H z.val : ℤ) := by
    simp [c, meromorphicOrderAt_eq_sub_clearingOrders hH ha h₀₁ hclear, hz₀, hz₁]
  -- Extend the numerator weights by zero from the exact zero subtype.
  let e : Z ≃ {z : ℂ // -1 < z.re ∧ z.re < 2 ∧ H z = 0} :=
    ⟨fun z ↦ ⟨z.val.val, z.val.property.1, z.val.property.2, z.property⟩,
      fun z ↦ ⟨⟨z.val, z.property.1, z.property.2.1⟩, z.property.2.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hgZ : Summable ((fun z : A ↦ ‖g z‖) ∘ (Subtype.val : Z → A)) :=
    e.summable_iff.mpr hsum
  have hg : Summable (fun z : A ↦ ‖g z‖) := by
    refine (summable_subtype_iff_indicator.mp hgZ).congr fun z ↦ ?_
    by_cases hz : z ∈ Z
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      simp [g, hnat z hz]
  let P : Set ℂ := {z₀, z₁}
  have hP : P.Finite := (finite_singleton z₁).insert z₀
  have habs : Summable (fun z : A ↦ ‖f z‖) := by
    apply hg.congr_cofinite
    have hfin := hP.preimage (f := (Subtype.val : A → ℂ)) Subtype.val_injective.injOn
    filter_upwards [hfin.eventually_cofinite_notMem] with z hz
    change z.val ∉ P at hz
    have hn : z.val ≠ z₀ ∧ z.val ≠ z₁ := by simpa [P] using hz
    simp [g, f, hc z hn.1 hn.2]
  -- The nonzero signed orders occur only at numerator zeros or clearing points.
  let U (T : ℝ) : Set A := {z | c z ≠ 0 ∧ |z.val.im| < T}
  have hfin (T : ℝ) : (U T).Finite := by
    refine (((rectangleZeros_finite hH ha T).union hP).preimage
      (f := (Subtype.val : A → ℂ)) Subtype.val_injective.injOn).subset ?_
    intro z hz
    change c z ≠ 0 ∧ |z.val.im| < T at hz
    change z.val ∈ _ ∪ P
    by_cases hzp : z.val ∈ P
    · exact Or.inr hzp
    · have hn : z.val ≠ z₀ ∧ z.val ≠ z₁ := by simpa [P] using hzp
      have hzH : H z.val = 0 := by
        by_contra h
        exact hz.1 (by rw [hc z hn.1 hn.2, hnat z h, Nat.cast_zero])
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hz.2
      exact Or.inl ⟨mem_reProdIm.mpr ⟨⟨z.property.1.le, z.property.2.le⟩, ⟨hlo.le, hhi.le⟩⟩,
        hzH⟩
  let S (T : ℝ) := (hfin T).toFinset
  have hS (T : ℝ) (z : A) : z ∈ S T ↔ c z ≠ 0 ∧ |z.val.im| < T :=
    (hfin T).mem_toFinset
  refine ⟨S, hS, habs, fun T hT ↦ ?_⟩
  -- Exhaust the nonzero-order subtype; omitted zero-order indices contribute nothing.
  let p (z : A) := c z ≠ 0
  let R (n : ℕ) := (S (T n)).subtype p
  have hR : Tendsto R atTop atTop := by
    refine tendsto_atTop.mpr fun F ↦ ?_
    have h := (eventually_all_finset (l := atTop) (p := fun (z : Subtype p) (n : ℕ) ↦
      |z.val.val.im| < T n) F).mpr fun z _ ↦ hT.eventually_gt_atTop |z.val.val.im|
    filter_upwards [h] with n hn z hz
    exact Finset.mem_subtype.mpr ((hS (T n) z.val).mpr ⟨z.property, hn z hz⟩)
  have hp : Function.support f ⊆ {z | p z} := by
    intro z hz
    change c z ≠ 0
    intro he
    exact hz (by simp [f, he])
  have hs := (hasSum_subtype_iff_of_support_subset hp).mpr habs.of_norm.hasSum
  change Tendsto (fun F : Finset (Subtype p) ↦ ∑ z ∈ F, f z.val) atTop (𝓝 (∑' z, f z)) at hs
  have hRsum (n : ℕ) : (∑ z ∈ R n, f z.val) = ∑ z ∈ S (T n), f z :=
    Finset.sum_subtype_of_mem f (fun z hz ↦ ((hS (T n) z).mp hz).1)
  simpa only [Function.comp_def, hRsum] using hs.comp hR

end Masullo
