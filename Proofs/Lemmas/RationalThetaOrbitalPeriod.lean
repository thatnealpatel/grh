module

public import Theorems.RationalThetaCutBand

/-! # Vanishing of orbital periodization on genuine dilation differences -/

open scoped FourierTransform SchwartzMap

namespace Masullo

/-- A two-moment theta profile is absolutely summable on each log orbit. -/
public theorem summable_rationalTheta_log_translates {B L : ℝ} (hL : 0 < L)
    {b : 𝓢(ℝ, ℂ)} (hb : b ∈ rationalThetaBandInput B) (u : ℝ) :
    Summable (fun k : ℤ ↦ rationalTheta b (Real.exp (u + (k : ℝ) * L))) := by
  obtain ⟨C, hC, h⟩ := rationalTheta_uniform_log_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) 1
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-L)).le
    (by rw [← Real.exp_zero, Real.exp_lt_exp]; linarith : Real.exp (-L) < 1)
  have hs : Summable (fun k : ℤ ↦ Real.exp (-(|(k : ℝ)| * L))) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;>
      simpa [abs_of_nonneg, ← Real.exp_nat_mul, mul_neg] using hg
  apply Summable.of_norm_bounded (hs.mul_left (C * Real.exp |u|))
  intro k
  have habs : |(k : ℝ)| * L ≤ |u + (k : ℝ) * L| + |u| := by
    have h := abs_sub_le (u + (k : ℝ) * L) 0 u
    simpa [abs_mul, abs_of_pos hL] using h
  calc
    _ ≤ C * Real.exp (-|u + (k : ℝ) * L|) := by
      simpa using h b (Set.mem_singleton b) hb.2.1 hb.2.2.1 _
    _ ≤ C * Real.exp (|u| + -(|(k : ℝ)| * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
    _ = _ := by rw [Real.exp_add, mul_assoc]

/-- A theta dilation difference has actual period sum zero, not just a
vanishing totalized `tsum`. The period is the logarithm of the dilation. -/
public theorem rationalTheta_logPeriod_hasSum_zero_of_difference {B p : ℝ}
    (hp : 1 < p) {c d : 𝓢(ℝ, ℂ)} (hc : c ∈ rationalThetaBandInput B)
    (hd : ∀ t : ℝ, 0 < t → rationalTheta d t = rationalTheta c t - rationalTheta c (p * t))
    (u : ℝ) : HasSum (fun k : ℤ ↦ rationalTheta d (Real.exp (u + (k : ℝ) * Real.log p))) 0 := by
  let v (k : ℤ) := rationalTheta c (Real.exp (u + (k : ℝ) * Real.log p))
  have hv : Summable v := summable_rationalTheta_log_translates (Real.log_pos hp) hc u
  let e := Equiv.addLeft (1 : ℤ)
  have hs : HasSum (fun k : ℤ ↦ v (e k)) (∑' k : ℤ, v k) :=
    e.hasSum_iff.mpr hv.hasSum
  have h := hv.hasSum.sub hs
  rw [sub_self] at h
  convert h using 1
  funext k
  rw [hd _ (Real.exp_pos _)]
  congr 1
  dsimp [v, e]
  congr 1
  rw [← Real.exp_log (zero_lt_one.trans hp), ← Real.exp_add, Real.log_exp,
    Int.cast_add, Int.cast_one]
  congr 1
  ring

end Masullo
