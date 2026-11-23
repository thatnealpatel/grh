module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Floor-grid columns in unweighted real L² -/

open Filter MeasureTheory Set
open scoped Topology

namespace Masullo

/-- The positive physical envelope, including all weights of the column. -/
@[expose] public noncomputable def floorGridEnvelope (a x : ℝ) : ℝ :=
  2 * Real.exp (-x / 2) * Real.exp (a * |x|) * (1 + x ^ 2)

/-- The fractional part at dyadic scale `j` in logarithmic coordinates. -/
@[expose] public noncomputable def floorGridPhase (j : ℕ) (x : ℝ) : ℝ :=
  Int.fract (Real.exp x / (2 : ℝ) ^ j)

private noncomputable def floorGridRep (a : ℝ) (j k : ℕ) (x : ℝ) : ℝ :=
  floorGridEnvelope a x * ((⌊(k : ℝ) * floorGridPhase j x⌋ : ℤ) : ℝ)

private theorem continuous_floorGridEnvelope (a : ℝ) : Continuous (floorGridEnvelope a) := by
  unfold floorGridEnvelope
  fun_prop

private theorem measurable_floorGridRep (a : ℝ) (j k : ℕ) : Measurable (floorGridRep a j k) := by
  have hphase : Measurable (floorGridPhase j) :=
    (Real.continuous_exp.measurable.div_const _).fract
  exact (continuous_floorGridEnvelope a).measurable.mul
    ((measurable_of_countable fun z : ℤ ↦ (z : ℝ)).comp (hphase.const_mul (k : ℝ)).floor)

private theorem floorGridRep_eq_zero {a x : ℝ} {j k : ℕ}
    (h : (k : ℝ) * Real.exp x < (2 : ℝ) ^ j) : floorGridRep a j k x = 0 := by
  have ht : 0 ≤ Real.exp x / (2 : ℝ) ^ j := by positivity
  have hfract : floorGridPhase j x ≤ Real.exp x / (2 : ℝ) ^ j := by
    unfold floorGridPhase Int.fract
    exact sub_le_self _ (by exact_mod_cast Int.floor_nonneg.mpr ht)
  have hlo : 0 ≤ (k : ℝ) * floorGridPhase j x :=
    mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)
  have hhi : (k : ℝ) * floorGridPhase j x < 1 := calc
    _ ≤ (k : ℝ) * (Real.exp x / (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hfract (Nat.cast_nonneg _)
    _ = ((k : ℝ) * Real.exp x) / (2 : ℝ) ^ j := (mul_div_assoc ..).symm
    _ < 1 := (div_lt_one (by positivity)).2 h
  have hf : ⌊(k : ℝ) * floorGridPhase j x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hlo, hhi⟩
  simp [floorGridRep, hf]

private theorem integrableOn_floorGridEnvelope_sq (a : ℝ) (ha : a < 1 / 2)
    {b : ℝ} (hb : b ≤ 0) :
    IntegrableOn (fun x ↦ floorGridEnvelope a x ^ 2) (Ici b) volume := by
  let d : ℝ := 1 - 2 * a
  have hd : 0 < d := by dsimp [d]; linarith
  have hmoment (n : ℕ) : IntegrableOn (fun x : ℝ ↦ x ^ n * Real.exp (-d * x)) (Ioi 0) volume := by
    have hn : (-1 : ℝ) < (n : ℝ) :=
      (show (-1 : ℝ) < 0 by norm_num).trans_le (Nat.cast_nonneg _)
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hn one_pos hd)
  have htail : IntegrableOn (fun x ↦ floorGridEnvelope a x ^ 2) (Ioi 0) volume := by
    have hpoly : IntegrableOn _ (Ioi (0 : ℝ)) volume :=
      ((hmoment 0).const_mul 4).add (((hmoment 2).const_mul 8).add ((hmoment 4).const_mul 4))
    refine hpoly.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    have hx' : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [Pi.add_apply, pow_zero, one_mul, floorGridEnvelope, abs_of_nonneg hx']
    have hexp : (Real.exp (-x / 2) * Real.exp (a * x)) ^ 2 = Real.exp (-d * x) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [d]
      ring
    rw [← hexp]
    ring
  have hcompact : IntegrableOn (fun x ↦ floorGridEnvelope a x ^ 2) (Icc b 0) volume :=
    ((continuous_floorGridEnvelope a).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  rw [← Icc_union_Ioi_eq_Ici hb]
  exact hcompact.union htail

-- The cutoff can be coarse, but must be uniform in `j` for each fixed `k`.
private noncomputable def floorGridMajorant (a : ℝ) (k : ℕ) : ℝ → ℝ :=
  (Ici (-(k : ℝ))).indicator (fun x ↦ ((k : ℝ) * floorGridEnvelope a x) ^ 2)

private theorem integrable_floorGridMajorant (a : ℝ) (ha : a < 1 / 2) (k : ℕ) :
    Integrable (floorGridMajorant a k) volume := by
  rw [floorGridMajorant, integrable_indicator_iff measurableSet_Ici]
  simpa only [IntegrableOn, mul_pow] using
    (integrableOn_floorGridEnvelope_sq a ha (neg_nonpos.mpr (Nat.cast_nonneg k))).const_mul
      ((k : ℝ) ^ 2)

private theorem norm_floorGridRep_sq_le (a : ℝ) (j k : ℕ) (x : ℝ) :
    ‖floorGridRep a j k x ^ 2‖ ≤ floorGridMajorant a k x := by
  rw [Real.norm_of_nonneg (sq_nonneg _), floorGridMajorant]
  by_cases hx : x ∈ Ici (-(k : ℝ))
  · rw [indicator_of_mem hx]
    have hlo : 0 ≤ (k : ℝ) * floorGridPhase j x :=
      mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)
    have hflo : 0 ≤ ((⌊(k : ℝ) * floorGridPhase j x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr hlo
    have hfhi : ((⌊(k : ℝ) * floorGridPhase j x⌋ : ℤ) : ℝ) ≤ k := calc
      _ ≤ (k : ℝ) * floorGridPhase j x := Int.floor_le _
      _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (Nat.cast_nonneg _)
      _ = k := mul_one _
    have hE : 0 ≤ floorGridEnvelope a x := by unfold floorGridEnvelope; positivity
    rw [floorGridRep, mul_comm (k : ℝ) (floorGridEnvelope a x)]
    exact pow_le_pow_left₀ (mul_nonneg hE hflo) (mul_le_mul_of_nonneg_left hfhi hE) 2
  · rw [indicator_of_notMem hx]
    have hx' : x < -(k : ℝ) := lt_of_not_ge hx
    have hk : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
    have h : (k : ℝ) * Real.exp x < (2 : ℝ) ^ j := calc
      _ ≤ Real.exp (k : ℝ) * Real.exp x := mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = Real.exp ((k : ℝ) + x) := (Real.exp_add ..).symm
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      _ ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    simp [floorGridRep_eq_zero (a := a) h]

private theorem memLp_floorGridRep (a : ℝ) (ha : a < 1 / 2) (j k : ℕ) :
    MemLp (floorGridRep a j k) 2 volume := by
  have hmeas := measurable_floorGridRep a j k
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    ((integrable_floorGridMajorant a ha k).mono' (hmeas.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (norm_floorGridRep_sq_le a j k)))

/-- The floor-grid column as a vector in unweighted real `L²(dx)`. -/
public noncomputable def floorGridColumn (a : ℝ) (ha : a < 1 / 2) (j k : ℕ) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_floorGridRep a ha j k).toLp (floorGridRep a j k)

/-- The column agrees almost everywhere with its explicit physical representative. -/
public theorem floorGridColumn_ae (a : ℝ) (ha : a < 1 / 2) (j k : ℕ) :
    (floorGridColumn a ha j k : ℝ → ℝ) =ᵐ[volume]
      fun x ↦ floorGridEnvelope a x * ((⌊(k : ℝ) * floorGridPhase j x⌋ : ℤ) : ℝ) :=
  (memLp_floorGridRep a ha j k).coeFn_toLp

/-- The norms of the `k = 2` columns tend to zero as the scale tends to infinity. -/
public theorem tendsto_floorGridColumn_two_norm (a : ℝ) (ha : a < 1 / 2) :
    Filter.Tendsto (fun j : ℕ ↦ ‖floorGridColumn a ha j 2‖) Filter.atTop (nhds 0) := by
  have hev (x : ℝ) : (fun j : ℕ ↦ floorGridRep a j 2 x ^ 2) =ᶠ[atTop] (fun _ ↦ 0) := by
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num))
      |>.eventually_gt_atTop ((2 : ℕ) * Real.exp x)] with j hj
    simp [floorGridRep_eq_zero (a := a) hj]
  have hmass : Tendsto (fun j : ℕ ↦ ∫ x, floorGridRep a j 2 x ^ 2) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (f := fun _ : ℝ ↦ (0 : ℝ))
        (floorGridMajorant a 2)
        (fun j ↦ ((measurable_floorGridRep a j 2).pow_const 2).aestronglyMeasurable)
        (integrable_floorGridMajorant a ha 2)
        (fun j ↦ ae_of_all _ (norm_floorGridRep_sq_le a j 2))
        (ae_of_all _ fun x ↦ tendsto_const_nhds.congr' (hev x).symm))
  have hnorm (j : ℕ) :
      ‖floorGridColumn a ha j 2‖ = Real.sqrt (∫ x, floorGridRep a j 2 x ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (floorGridColumn a ha j 2)),
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [floorGridColumn_ae a ha j 2] with x hx
    rw [Real.inner_apply, ← pow_two, hx]
    rfl
  simpa only [Function.comp_def, ← hnorm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hmass

end Masullo
