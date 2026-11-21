module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The counterclockwise rectangular boundary integral and its Cauchy kernel. -/

open Complex Set MeasureTheory

namespace Masullo

/-- Integrate counterclockwise along the real-coordinate edges of a rectangle. -/
@[expose] public noncomputable def rectangleIntegral (a b c d : ℝ) (g : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, g (x + c * I)) - (∫ x : ℝ in a..b, g (x + d * I)) +
    I * (∫ y : ℝ in c..d, g (b + y * I)) - I * (∫ y : ℝ in c..d, g (a + y * I))

private theorem affine_log_edge (a b : ℝ) (s t q : ℂ)
    (hq : q ≠ 0) (hslit : ∀ x ∈ uIcc a b, q * (s * x + t) ∈ slitPlane) :
    s * (∫ x : ℝ in a..b, (s * x + t)⁻¹) =
      log (q * (s * b + t)) - log (q * (s * a + t)) := by
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ ↦ log (q * (s * y + t))) (s * (s * x + t)⁻¹) x := by
    have h := ((hasDerivAt_log (hslit x hx)).comp (x : ℂ)
      ((((hasDerivAt_id (x : ℂ)).const_mul s).add_const t).const_mul q)).comp_ofReal
    have hne := slitPlane_ne_zero (hslit x hx)
    convert h using 1
    simp [id] at *
    field_simp [hq, (mul_ne_zero_iff.mp hne).2]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt hd
  apply ContinuousOn.intervalIntegrable
  have hc : Continuous (fun x : ℝ ↦ s * x + t) := by fun_prop
  exact continuousOn_const.mul (hc.continuousOn.inv₀ fun x hx h ↦
    slitPlane_ne_zero (hslit x hx) (by simp [h]))

private theorem log_sub_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    log w - log (-w) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

private theorem log_neg_sub_log_of_im_neg {w : ℂ} (hw : w.im < 0) :
    log (-w) - log w = (Real.pi : ℂ) * I := by
  simpa using log_sub_log_neg_of_im_pos (show 0 < (-w).im by simpa using hw)

/-- A single Cauchy kernel has residue one at any strictly interior point. -/
public theorem rectangleIntegral_cauchyKernel {a b c d : ℝ} {z : ℂ}
    (haz : a < z.re) (hzb : z.re < b) (hcz : c < z.im) (hzd : z.im < d) :
    rectangleIntegral a b c d (fun w ↦ (w - z)⁻¹) = 2 * Real.pi * I := by
  have bottom := affine_log_edge a b 1 (c * I - z) 1 one_ne_zero (by
    intro x hx
    exact mem_slitPlane_iff.mpr (Or.inr (by simpa using (sub_ne_zero.mpr hcz.ne))))
  have top := affine_log_edge a b 1 (d * I - z) 1 one_ne_zero (by
    intro x hx
    exact mem_slitPlane_iff.mpr (Or.inr (by simpa using (sub_ne_zero.mpr hzd.ne'))))
  have right := affine_log_edge c d I (b - z) 1 one_ne_zero (by
    intro y hy
    exact mem_slitPlane_iff.mpr (Or.inl (by simpa using (sub_pos.mpr hzb))))
  have left := affine_log_edge c d I (a - z) (-1) (neg_ne_zero.mpr one_ne_zero) (by
    intro y hy
    exact mem_slitPlane_iff.mpr (Or.inl (by simpa using (sub_pos.mpr haz))))
  simp only [one_mul, ← add_sub_assoc] at bottom top
  have edge (v y : ℝ) : I * y + ((v : ℂ) - z) = v + y * I - z := by ring
  simp only [one_mul, neg_one_mul, edge] at left right
  unfold rectangleIntegral
  rw [bottom, top, right, left]
  have up := log_sub_log_neg_of_im_pos (w := a + d * I - z) (by simpa using sub_pos.mpr hzd)
  have down := log_neg_sub_log_of_im_neg (w := a + c * I - z) (by simpa using sub_neg.mpr hcz)
  linear_combination up + down

/-- The boundary calculation for a regular remainder and a finite sum of kernels. -/
public theorem rectangleIntegral_eq_sum_of_eqOn {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {Z : Finset ℂ} {g h : ℂ → ℂ} {k : ℂ → ℂ}
    (hZ : ∀ z ∈ Z, z ∈ Ioo a b ×ℂ Ioo c d)
    (hh : DifferentiableOn ℂ h (Icc a b ×ℂ Icc c d))
    (heq : EqOn g (fun w ↦ h w + ∑ z ∈ Z, k z * (w - z)⁻¹)
      ((Icc a b ×ℂ Icc c d) \ (Z : Set ℂ))) :
    rectangleIntegral a b c d g = (2 * Real.pi * I) * ∑ z ∈ Z, k z := by
  have edge {u v : ℝ} {p : ℝ → ℂ} (hp : Continuous p)
      (hmap : MapsTo p (uIcc u v) ((Icc a b ×ℂ Icc c d) \ (Z : Set ℂ))) :
      (∫ t : ℝ in u..v, g (p t)) = (∫ t : ℝ in u..v, h (p t)) +
        ∑ z ∈ Z, k z * (∫ t : ℝ in u..v, (p t - z)⁻¹) := by
    have hh' : IntervalIntegrable (fun t ↦ h (p t)) volume u v :=
      (hh.continuousOn.comp hp.continuousOn (fun t ht ↦ (hmap ht).1)).intervalIntegrable
    have hk (z : ℂ) (hz : z ∈ Z) : ContinuousOn (fun t ↦ k z * (p t - z)⁻¹) (uIcc u v) :=
      continuousOn_const.mul ((hp.sub continuous_const).continuousOn.inv₀
        fun t ht he ↦ (hmap ht).2 (sub_eq_zero.mp he ▸ hz))
    have hk' := fun z hz ↦ (hk z hz).intervalIntegrable (μ := volume)
    calc
      _ = ∫ t : ℝ in u..v, h (p t) + ∑ z ∈ Z, k z * (p t - z)⁻¹ :=
        intervalIntegral.integral_congr fun t ht ↦ heq (hmap ht)
      _ = _ := by
        rw [intervalIntegral.integral_add hh']
        · rw [intervalIntegral.integral_finsetSum hk']
          simp only [intervalIntegral.integral_const_mul]
        · exact (continuousOn_finsetSum _ hk).intervalIntegrable
  have horiz (v : ℝ) (hv : v = c ∨ v = d) :
      MapsTo (fun t : ℝ ↦ (t : ℂ) + v * I) (uIcc a b)
        ((Icc a b ×ℂ Icc c d) \ (Z : Set ℂ)) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hclosed : v ∈ Icc c d := hv.elim (fun e ↦ e.symm ▸ left_mem_Icc.mpr hcd)
      (fun e ↦ e.symm ▸ right_mem_Icc.mpr hcd)
    refine ⟨by simpa [mem_reProdIm] using And.intro hx hclosed, fun hz ↦ ?_⟩
    have hopp : v ∈ Ioo c d := by simpa using (mem_reProdIm.mp (hZ _ hz)).2
    rcases hv with rfl | rfl
    · exact (lt_irrefl _) hopp.1
    · exact (lt_irrefl _) hopp.2
  have vert (v : ℝ) (hv : v = a ∨ v = b) :
      MapsTo (fun t : ℝ ↦ (v : ℂ) + t * I) (uIcc c d)
        ((Icc a b ×ℂ Icc c d) \ (Z : Set ℂ)) := by
    intro y hy
    rw [uIcc_of_le hcd] at hy
    have hclosed : v ∈ Icc a b := hv.elim (fun e ↦ e.symm ▸ left_mem_Icc.mpr hab)
      (fun e ↦ e.symm ▸ right_mem_Icc.mpr hab)
    refine ⟨by simpa [mem_reProdIm] using And.intro hclosed hy, fun hz ↦ ?_⟩
    have hopp : v ∈ Ioo a b := by simpa using (mem_reProdIm.mp (hZ _ hz)).1
    rcases hv with rfl | rfl
    · exact (lt_irrefl _) hopp.1
    · exact (lt_irrefl _) hopp.2
  have hzero : rectangleIntegral a b c d h = 0 := by
    simpa [rectangleIntegral, uIcc_of_le hab, uIcc_of_le hcd, smul_eq_mul] using
      integral_boundary_rect_eq_zero_of_differentiableOn h ⟨a, c⟩ ⟨b, d⟩
        (by simpa [uIcc_of_le hab, uIcc_of_le hcd] using hh)
  calc
    _ = rectangleIntegral a b c d h +
        ∑ z ∈ Z, k z * rectangleIntegral a b c d (fun w ↦ (w - z)⁻¹) := by
      simp only [rectangleIntegral, edge (by fun_prop) (horiz c (Or.inl rfl)),
        edge (by fun_prop) (horiz d (Or.inr rfl)), edge (by fun_prop) (vert b (Or.inr rfl)),
        edge (by fun_prop) (vert a (Or.inl rfl)), mul_add, mul_sub, Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_left_comm I]
      abel
    _ = _ := by
      rw [hzero, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      obtain ⟨⟨ha, hb⟩, hc, hd⟩ := mem_reProdIm.mp (hZ z hz)
      rw [rectangleIntegral_cauchyKernel ha hb hc hd, mul_comm]

end Masullo
