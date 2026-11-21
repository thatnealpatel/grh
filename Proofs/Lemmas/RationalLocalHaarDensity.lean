module

public import Lemmas.RationalLocalAdditiveModulus
public import Lemmas.RationalLocalNormShell
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Dilation invariance and unit calibration for the rational local density -/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set TopologicalSpace
open scoped Padic ENNReal

namespace Masullo.RationalLocalHaarDensity

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "O[" v "]" => adicCompletionIntegers ℚ v
local notation "G[" v "]" => (K[v])ˣ
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "P[" v "]" => ((p[v] : ℕ) : ℝ)
local notation "ν[" v "]" => rationalLocalFieldAddHaar v

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

private theorem mem_integers_iff (v : V) (x : K[v]) :
    x ∈ (O[v] : Set (K[v])) ↔ ‖x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, ← mem_adicCompletionIntegers]
  rfl

private theorem map_addHaar_mul (v : V) (a : G[v]) :
    (ν[v]).map (fun x : K[v] ↦ (a : K[v]) * x) = ENNReal.ofReal ‖(a : K[v])‖⁻¹ • ν[v] := by
  let h := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph
  let : SecondCountableTopology (K[v]) := h.secondCountableTopology
  let : LocallyCompactSpace (K[v]) := h.locallyCompactSpace_iff.mpr inferInstance
  let S : PositiveCompacts K[v] := {
    carrier := (O[v] : Set K[v])
    isCompact' := by
      have hS : h ⁻¹' Metric.closedBall 0 1 = (O[v] : Set K[v]) := by
        ext x
        change dist (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x) 0 ≤ 1 ↔ _
        rw [dist_zero_right, norm_rationalLocal_padicEquiv, mem_integers_iff]
      rw [← hS]
      exact h.isCompact_preimage.mpr (isCompact_closedBall _ _)
    interior_nonempty' := by
      have hO : IsOpen (O[v] : Set K[v]) := Valued.isOpen_valuationSubring (K[v])
      rw [hO.interior_eq]
      exact ⟨0, (O[v]).zero_mem⟩ }
  have hν : ν[v] = Measure.addHaarMeasure S := by
    have hmass : ν[v] S = 1 := rationalLocalFieldAddHaar_integers v
    rw [Measure.addHaarMeasure_unique ν[v] S, hmass, one_smul]
  let m := ContinuousAddEquiv.mulLeft a
  let μ := (ν[v]).map m
  have : μ.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map _ m
  have hm : μ S = ENNReal.ofReal ‖(a : K[v])‖⁻¹ := by
    change (ν[v]).map m.toHomeomorph (O[v] : Set (K[v])) = _
    rw [m.toHomeomorph.measurableEmbedding.map_apply]
    have he : m.toHomeomorph ⁻¹' (O[v] : Set (K[v])) = (fun x : K[v] ↦ (↑a⁻¹ : K[v]) * x) '' (O[v] : Set (K[v])) := by
      change m.toHomeomorph.toEquiv ⁻¹' _ = m.toHomeomorph.toEquiv.symm '' _
      exact (m.toHomeomorph.toEquiv.image_symm_eq_preimage _).symm
    rw [he, rationalLocalFieldAddHaar_dilate_integers v _ (Units.ne_zero a⁻¹),
      Units.val_inv_eq_inv_val, norm_inv]
  change μ = _
  rw [Measure.addHaarMeasure_unique μ S, hm, ← hν]

local notation "w[" v "]" => (fun x : K[v] ↦ ENNReal.ofReal ‖x‖⁻¹)

/-- The unnormalized inverse-norm density is invariant under nonzero dilation. -/
public theorem measure_preimage_mul (v : V) (a : G[v]) {s : Set (K[v])} (hs : MeasurableSet s) :
    ((ν[v]).withDensity (w[v])) ((fun x : K[v] ↦ (a : K[v]) * x) ⁻¹' s) =
      ((ν[v]).withDensity (w[v])) s := by
  let m := fun x : K[v] ↦ (a : K[v]) * x
  let c := ENNReal.ofReal ‖(a : K[v])‖⁻¹
  have hm : Measurable m := (continuous_const_mul _).measurable
  have hw : Measurable (w[v]) := continuous_norm.measurable.inv.ennreal_ofReal
  have he : ∀ x, w[v] (m x) = c * w[v] x := by
    intro x
    dsimp [m, c]
    rw [norm_mul, mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
  have h := setLIntegral_map hs hw hm (μ := ν[v])
  rw [map_addHaar_mul v a, Measure.restrict_smul, lintegral_smul_measure] at h
  simp_rw [he, lintegral_const_mul c hw] at h
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr (norm_pos_iff.mpr a.ne_zero))).ne'
  rw [withDensity_apply _ (hm hs), withDensity_apply _ hs]
  exact (ENNReal.mul_right_inj hc ENNReal.ofReal_ne_top).mp h.symm

private theorem range_unitValues (v : V) :
    (Units.val : G[v] → K[v]) '' range (rationalLocalUnitInclusion v) = {x | ‖x‖ = 1} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (RationalLocalNormShell.mem_unitRange_iff v u).mp hu
  · intro hx
    have hx' : ‖x‖ = 1 := hx
    have hn : x ≠ 0 := by intro h; subst x; simp at hx'
    exact ⟨Units.mk0 x hn, (RationalLocalNormShell.mem_unitRange_iff v _).mpr hx', rfl⟩

private theorem measure_norm_one (v : V) :
    ν[v] {x | ‖x‖ = 1} = ENNReal.ofReal (1 - P[v]⁻¹) := by
  let q : K[v] := (p[v] : ℕ)
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hq : ‖q‖ = P[v]⁻¹ := by
    rw [← norm_rationalLocal_padicEquiv v, show e q = ((p[v] : ℕ) : ℚ_[(p[v] : ℕ)]) from
      map_natCast e _, Padic.norm_p]
  have hp := RationalLocalNormShell.one_lt_prime v
  have hp₀ : 0 < P[v] := zero_lt_one.trans hp
  have hq₀ : 0 < ‖q‖ := hq ▸ inv_pos.mpr hp₀
  have hq' : q ≠ 0 := norm_pos_iff.mp hq₀
  have hball : (fun x : K[v] ↦ q * x) '' (O[v] : Set (K[v])) = {x | ‖x‖ ≤ P[v]⁻¹} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ‖q * y‖ ≤ _
      rw [norm_mul, ← hq]
      exact mul_le_of_le_one_right hq₀.le ((mem_integers_iff v y).mp hy)
    · intro hx
      refine ⟨q⁻¹ * x, (mem_integers_iff v _).mpr ?_, mul_inv_cancel_left₀ hq' _⟩
      rw [norm_mul, norm_inv, inv_mul_le_iff₀ hq₀, mul_one, hq]
      exact hx
  have hdiff : {x : K[v] | ‖x‖ = 1} = (O[v] : Set (K[v])) \ {x | ‖x‖ ≤ P[v]⁻¹} := by
    ext x
    change ‖x‖ = 1 ↔ x ∈ (O[v] : Set (K[v])) ∧ ¬ ‖x‖ ≤ P[v]⁻¹
    rw [mem_integers_iff]
    by_cases hx : x = 0
    · simp [hx, hp₀.le]
    have he := (map_ne_zero_iff e e.injective).mpr hx
    rw [← norm_rationalLocal_padicEquiv v x, Padic.norm_eq_zpow_neg_valuation he]
    rw [← zpow_zero P[v], ← zpow_neg_one, zpow_le_zpow_iff_right₀ hp,
      zpow_le_zpow_iff_right₀ hp, (zpow_right_injective₀ hp₀ hp.ne').eq_iff]
    omega
  have hsub : {x : K[v] | ‖x‖ ≤ P[v]⁻¹} ⊆ (O[v] : Set (K[v])) := fun x hx ↦
    (mem_integers_iff v x).mpr (le_trans hx (inv_le_one₀ hp₀ |>.mpr hp.le))
  have hmeas : MeasurableSet {x : K[v] | ‖x‖ ≤ P[v]⁻¹} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hmass := rationalLocalFieldAddHaar_dilate_integers v q hq'
  rw [hball, hq] at hmass
  rw [hdiff, measure_sdiff hsub hmeas.nullMeasurableSet (hmass ▸ ENNReal.ofReal_ne_top),
    rationalLocalFieldAddHaar_integers, hmass, ENNReal.ofReal_sub _ (inv_nonneg.mpr hp₀.le),
    ENNReal.ofReal_one]

variable (v : V) [MeasurableSpace (G[v])] [BorelSpace (G[v])]

local notation "j" => (Units.val : G[v] → K[v])

/-- The density `dν/‖x‖`, expressed on local units by pullback. -/
@[expose]
public noncomputable def onUnits : Measure (G[v]) := ((ν[v]).withDensity (w[v])).comap j

public theorem onUnits_unitMass :
    onUnits v (range (rationalLocalUnitInclusion v)) = ENNReal.ofReal (1 - P[v]⁻¹) := by
  let S := range (rationalLocalUnitInclusion v)
  have hs : MeasurableSet {x : K[v] | ‖x‖ = 1} :=
    (isClosed_eq continuous_norm continuous_const).measurableSet
  rw [onUnits, Units.isOpenEmbedding_val.measurableEmbedding.comap_apply _ S,
    range_unitValues, withDensity_apply _ hs, ← measure_norm_one v]
  rw [setLIntegral_congr_fun hs (g := fun _ ↦ 1) (fun x hx ↦ by
    change ‖x‖ = 1 at hx
    simp [hx]), lintegral_one, Measure.restrict_apply_univ]

public theorem onUnits_mulLeftInvariant : (onUnits v).IsMulLeftInvariant where
  map_mul_left_eq_self a := by
    ext s hs
    let m := fun x : G[v] ↦ a * x
    let l := fun x : K[v] ↦ (a : K[v]) * x
    have hm : Measurable m := (continuous_const_mul a).measurable
    let J : MeasurableEmbedding j := Units.isOpenEmbedding_val.measurableEmbedding
    have himage : j '' (m ⁻¹' s) = l ⁻¹' (j '' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨a * u, hu, rfl⟩
      · rintro ⟨u, hu, he⟩
        refine ⟨a⁻¹ * u, ?_, ?_⟩
        · simpa [m] using hu
        · change (u : K[v]) = (a : K[v]) * x at he
          rw [Units.val_mul, Units.val_inv_eq_inv_val, he, inv_mul_cancel_left₀ a.ne_zero]
    rw [Measure.map_apply hm hs, onUnits, J.comap_apply _ (m ⁻¹' s), J.comap_apply _ s,
      himage]
    exact measure_preimage_mul v a (J.measurableSet_image' hs)

omit [MeasurableSpace G[v]] [BorelSpace G[v]] in
public theorem range_val : range j = ({0} : Set (K[v]))ᶜ := by
  ext x
  exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩

end Masullo.RationalLocalHaarDensity
