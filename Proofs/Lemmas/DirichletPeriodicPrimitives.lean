module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Centered periodic primitives for Dirichlet characters

A nonprincipal character sum is periodic on `[1, ∞)`. Subtracting the mean
before each integration from `1` preserves periodicity and boundedness on that ray.
-/

open Finset Filter MeasureTheory Set
open scoped Interval

namespace Masullo

/-- The right-continuous partial sum of a Dirichlet character. -/
@[expose] public noncomputable def dirichletPartialSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, χ (k : ZMod q)

/-- The mean over the base period starting at `1`. -/
@[expose] public noncomputable def dirichletMean (q : ℕ) (A : ℝ → ℂ) : ℂ :=
  (q : ℂ)⁻¹ * ∫ t in (1 : ℝ)..(1 + q), A t

/-- The anchored primitive of the mean-zero part. -/
@[expose] public noncomputable def dirichletPrimitive (q : ℕ) (A : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..x, (A t - dirichletMean q A)

/-- Data for iterating centered integration on `[1, ∞)`. Periodicity is only
required on the ray, so the literal Dirichlet floor-sum can be used. -/
public structure PeriodicPrimitiveData (q : ℕ) (A : ℝ → ℂ) : Prop where
  periodic : ∀ x ≥ (1 : ℝ), A (x + (q : ℝ)) = A x
  measurable : Measurable A
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, ‖A x‖ ≤ B
  rightContinuous : ∀ x ≥ 1, ContinuousWithinAt A (Set.Ici x) x

@[simp] public theorem dirichletPrimitive_one (q : ℕ) (A : ℝ → ℂ) :
    dirichletPrimitive q A 1 = 0 := by
  simp [dirichletPrimitive]

private theorem bound_of_periodic {A : ℝ → ℂ} {p B : ℝ} (hp : 0 < p)
    (hper : ∀ x ≥ (1 : ℝ), A (x + p) = A x)
    (hB : ∀ x ∈ Icc 1 (1 + p), ‖A x‖ ≤ B) : ∀ x ≥ (1 : ℝ), ‖A x‖ ≤ B := by
  have hshift (y : ℝ) (hy : 1 ≤ y) (n : ℕ) : A (y + n * p) = A y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc,
        hper _ (hy.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hp.le))), ih]
  intro x hx
  let n := ⌊(x - 1) / p⌋₊
  have hn₁ : (n : ℝ) ≤ (x - 1) / p := Nat.floor_le (by positivity)
  have hn₂ : (x - 1) / p < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hy₁ : 1 ≤ x - n * p := by linarith [(le_div_iff₀ hp).mp hn₁]
  have hy₂ : x - n * p ≤ 1 + p := by
    linarith [(div_lt_iff₀ hp).mp hn₂, add_mul (n : ℝ) 1 p]
  have h := hshift _ hy₁ n
  rw [sub_add_cancel] at h
  exact h ▸ hB _ ⟨hy₁, hy₂⟩

private theorem dirichlet_sum_block {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (m : ℕ) :
    ∑ k ∈ Finset.Ico m (m + q), χ (k : ZMod q) = 0 := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun i ↦ (i.val : ZMod q)
      invFun := fun z ↦ ⟨z.val, z.val_lt⟩
      left_inv := fun i ↦ Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := ZMod.natCast_zmod_val }
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range]
  simp only [Nat.cast_add]
  exact (Equiv.sum_comp (e.trans (Equiv.addLeft (m : ZMod q))) χ).trans
    (χ.sum_eq_zero_of_ne_one hχ)

/-- The partial sums of a nonprincipal Dirichlet character provide the starting
function for centered integration. -/
public theorem dirichletPartialSum_data {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : PeriodicPrimitiveData q (dirichletPartialSum χ) := by
  have hIcc (n : ℕ) : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k
    simp
  have hper : ∀ x ≥ (1 : ℝ), dirichletPartialSum χ (x + (q : ℝ)) = dirichletPartialSum χ x := by
    intro x hx
    simp only [dirichletPartialSum, Nat.floor_add_natCast (zero_le_one.trans hx), hIcc]
    rw [add_right_comm ⌊x⌋₊ q 1,
      ← Finset.sum_Ico_consecutive _ (n := ⌊x⌋₊ + 1) (by omega) (by omega),
      dirichlet_sum_block χ hχ, add_zero]
  refine ⟨hper, ?_, ⟨(q : ℝ) + 1, by positivity, ?_⟩, ?_⟩
  · exact (measurable_of_countable fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)).comp
      Nat.measurable_floor
  · apply bound_of_periodic (Nat.cast_pos.mpr (NeZero.pos q)) hper
    intro x hx
    calc
      ‖dirichletPartialSum χ x‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ‖χ (k : ZMod q)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
      _ = (⌊x⌋₊ : ℝ) := by simp
      _ ≤ (q : ℝ) + 1 :=
        (Nat.floor_le (zero_le_one.trans hx.1)).trans (by simpa [add_comm] using hx.2)
  · intro x hx
    apply continuousWithinAt_const.congr_of_eventuallyEq _ rfl
    filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with y hy
    rw [dirichletPartialSum, Nat.floor_eq_on_Ico _ _
      ⟨(Nat.floor_le (zero_le_one.trans hx)).trans hy.1, hy.2⟩]
    rfl

private theorem intervalIntegrable_of_ray_bound {A : ℝ → ℂ} (hA : Measurable A)
    {B : ℝ} (hB : ∀ t ≥ (1 : ℝ), ‖A t‖ ≤ B) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable A volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ hA.aestronglyMeasurable B ?_
  · rw [uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht ↦ ?_)
    exact hB t ((le_min ha hb).trans ht.1.le)

/-- The bounds and measurability on the ray imply integrability between any two
endpoints in the ray. -/
public theorem PeriodicPrimitiveData.intervalIntegrable {q : ℕ} {A : ℝ → ℂ}
    (h : PeriodicPrimitiveData q A) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable A volume a b := by
  obtain ⟨B, _, hB⟩ := h.bounded
  exact intervalIntegrable_of_ray_bound h.measurable hB ha hb

private theorem measurable_integral_from_one {F : ℝ → ℂ} (hF : Measurable F) :
    Measurable (fun x : ℝ ↦ ∫ t in (1 : ℝ)..x, F t) := by
  have h₁ : Measurable (fun x : ℝ ↦ ∫ t in Ioc 1 x, F t) := by
    have hs : MeasurableSet {p : ℝ × ℝ | 1 < p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have hm : Measurable (fun x : ℝ ↦ ∫ t, (Ioc 1 x).indicator F t) :=
      (((hF.comp measurable_snd).indicator hs).stronglyMeasurable.integral_prod_right'
        (ν := volume)).measurable
    simpa only [integral_indicator measurableSet_Ioc] using hm
  have h₂ : Measurable (fun x : ℝ ↦ ∫ t in Ioc x 1, F t) := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 1} :=
      (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hm : Measurable (fun x : ℝ ↦ ∫ t, (Ioc x 1).indicator F t) :=
      (((hF.comp measurable_snd).indicator hs).stronglyMeasurable.integral_prod_right'
        (ν := volume)).measurable
    simpa only [integral_indicator measurableSet_Ioc] using hm
  exact h₁.sub h₂

/-- Integrating the centered function from `1` gives new periodic primitive data
with the same period. No integrability below `1` is assumed. -/
public theorem PeriodicPrimitiveData.primitive {q : ℕ} [NeZero q] {A : ℝ → ℂ}
    (h : PeriodicPrimitiveData q A) : PeriodicPrimitiveData q (dirichletPrimitive q A) := by
  let F := fun t ↦ A t - dirichletMean q A
  let p : ℝ := q
  have hp : 0 < p := Nat.cast_pos.mpr (NeZero.pos q)
  have h1p : (1 : ℝ) ≤ 1 + p := le_add_of_nonneg_right hp.le
  obtain ⟨B, hB₀, hB⟩ := h.bounded
  let M := B + ‖dirichletMean q A‖
  have hM : 0 ≤ M := add_nonneg hB₀ (norm_nonneg _)
  have hF : Measurable F := h.measurable.sub measurable_const
  have hFbound (t : ℝ) (ht : 1 ≤ t) : ‖F t‖ ≤ M :=
    (norm_sub_le _ _).trans (add_le_add (hB t ht) le_rfl)
  have hInt {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IntervalIntegrable F volume a b :=
    intervalIntegrable_of_ray_bound hF hFbound ha hb
  have hzero : (∫ t in (1 : ℝ)..(1 + p), F t) = 0 := by
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    dsimp only [F, p]
    rw [intervalIntegral.integral_sub (h.intervalIntegrable le_rfl h1p) intervalIntegrable_const,
      intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul, Complex.ofReal_natCast,
      dirichletMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul, sub_self]
  have hper (x : ℝ) (hx : 1 ≤ x) : dirichletPrimitive q A (x + p) = dirichletPrimitive q A x := by
    have hxp : 1 ≤ x + p := hx.trans (le_add_of_nonneg_right hp.le)
    calc
      _ = (∫ t in (1 : ℝ)..(1 + p), F t) + ∫ t in (1 + p)..(x + p), F t :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt le_rfl h1p) (hInt h1p hxp)).symm
      _ = ∫ t in (1 : ℝ)..x, F (t + p) := by
        rw [hzero, zero_add, intervalIntegral.integral_comp_add_right]
      _ = dirichletPrimitive q A x := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hx]
        intro t ht
        exact congrArg (fun z ↦ z - dirichletMean q A) (h.periodic t ht.1)
  refine ⟨hper, measurable_integral_from_one hF, ⟨M * p, mul_nonneg hM hp.le, ?_⟩, ?_⟩
  · apply bound_of_periodic hp hper
    intro x hx
    have hnorm : ‖dirichletPrimitive q A x‖ ≤ M * |x - 1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hx.1] at ht
      exact hFbound t ht.1.le
    exact hnorm.trans (mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]; linarith [hx.2]) hM)
  · intro x hx
    have hxx : x < x + 1 := by linarith
    have h1xx : (1 : ℝ) ≤ x + 1 := hx.trans hxx.le
    have hc := intervalIntegral.continuousOn_primitive_interval' (hInt le_rfl h1xx) left_mem_uIcc
    rw [uIcc_of_le h1xx] at hc
    exact (hc x ⟨hx, hxx.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hxx) (fun _ ht ↦ ⟨hx.trans ht.1, ht.2⟩))

end Masullo
