module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Model price of the exterior of a fixed census rectangle

Source: `20ac2a9d:.godel/bob/uncut-census-window.md:11–18,39–43`, whose
model equations are unchanged at Lean base `4c47eae3`.

Scope: the exact pointwise bounds for the model correction `U` in enclosure
(1), and their finite nonnegative weighted sum against the single unused
`2 k_h` model mass. This does not compare `2 k_h` with the actual paired
kernel `p_b^h`, estimate approximation errors, or prove the all-zero enclosure.

Owning check session: `01a20c03-fe6f-73b3-a1bb-bf0df5b6ef1a`.
-/

open scoped BigOperators

namespace Masullo.CensusExteriorPrice

noncomputable section

/-- The model envelope `ℓ(x)`. -/
@[expose] public def ell (x : ℝ) : ℝ := (1 / 4 + x ^ 2)⁻¹

/-- The Cauchy kernel `k_h(x)`. -/
@[expose] public def kernel (h x : ℝ) : ℝ := h / (h ^ 2 + x ^ 2)

@[expose] public def S : ℝ := 2 * Real.sinh 1
@[expose] public def B₀ : ℝ := 2 - 2 / Real.exp 1
@[expose] public def M : ℝ := 2 / Real.exp 1 + 2 * Real.cosh 1

/-- The model correction, using the first branch at the switch `c = 1`. -/
@[expose] public def U (c x g v : ℝ) : ℝ :=
  ell x * (if c ≤ 1 then 2 * g - B₀ + 2 * g * Real.cosh c * v
    else -(S * Real.exp (1 - c)) * g * v)

/-- The price of one unit of unused model mass. -/
@[expose] public def price (h C K : ℝ) : ℝ := max (K / h) (2 * h * S * Real.exp (1 - C))

private theorem ell_denom_pos (x : ℝ) : 0 < 1 / 4 + x ^ 2 := by positivity

private theorem ell_nonneg (x : ℝ) : 0 ≤ ell x := (inv_pos.mpr (ell_denom_pos x)).le

private theorem kernel_denom_pos {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 < h ^ 2 + x ^ 2 := by positivity

private theorem kernel_nonneg {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 ≤ kernel h x :=
  div_nonneg hh.le (kernel_denom_pos hh x).le

private theorem S_nonneg : 0 ≤ S :=
  mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr zero_le_one)

private theorem cosh_one_sub_sinh_one : Real.cosh 1 - Real.sinh 1 = 1 / Real.exp 1 := by
  rw [Real.cosh_sub_sinh, Real.exp_neg, one_div]

private theorem S_le_M : S ≤ M := by
  rw [S, M, ← mul_one_div (2 : ℝ) (Real.exp 1)]
  linarith only [cosh_one_sub_sinh_one, (show 0 ≤ 1 / Real.exp 1 by positivity)]

private theorem shallow_bounds {c g v : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hg₀ : 0 ≤ g) (hg₁ : g ≤ 1) (hv : |v| ≤ 1) :
    -S ≤ 2 * g - B₀ + 2 * g * Real.cosh c * v ∧
      2 * g - B₀ + 2 * g * Real.cosh c * v ≤ M := by
  have hcosh₀ : 0 ≤ Real.cosh c := zero_le_one.trans (Real.one_le_cosh c)
  have hcosh₁ : Real.cosh c ≤ Real.cosh 1 :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hc₀, abs_one] using hc₁)
  have hvL : -Real.cosh c ≤ Real.cosh c * v := by
    simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left (abs_le.mp hv).1 hcosh₀
  have hvH : Real.cosh c * v ≤ Real.cosh c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mp hv).2 hcosh₀
  have hg₂ : 0 ≤ 2 * g := by positivity
  have hL : 2 * (1 - Real.cosh 1) ≤ 2 * g * (1 + Real.cosh c * v) := calc
    _ ≤ 2 * g * (1 - Real.cosh 1) :=
      mul_le_mul_of_nonpos_right (by linarith) (sub_nonpos.mpr (Real.one_le_cosh 1))
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hg₂
  have hH : 2 * g * (1 + Real.cosh c * v) ≤ 2 * (1 + Real.cosh 1) := calc
    _ ≤ 2 * g * (1 + Real.cosh 1) := mul_le_mul_of_nonneg_left (by linarith) hg₂
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  simp only [S, B₀, M, ← mul_one_div (2 : ℝ) (Real.exp 1)]
  constructor
  · linarith only [hL, cosh_one_sub_sinh_one]
  · linarith only [hH]

private theorem U_deep_bounds {c x g v t : ℝ} (hc : 1 < c) (ht : t ≤ c)
    (hg₀ : 0 ≤ g) (hg₁ : g ≤ 1) (hv : |v| ≤ 1) :
    -(S * Real.exp (1 - t)) * ell x ≤ U c x g v ∧
      U c x g v ≤ (S * Real.exp (1 - t)) * ell x := by
  have hgv : |g * v| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hg₀]
    exact (mul_le_mul_of_nonneg_left hv hg₀).trans (by simpa only [mul_one] using hg₁)
  have ha : 0 ≤ S * Real.exp (1 - c) := mul_nonneg S_nonneg (Real.exp_pos _).le
  have hfactor : |-(S * Real.exp (1 - c)) * g * v| ≤ S * Real.exp (1 - t) := by
    rw [mul_assoc, abs_mul, abs_neg, abs_of_nonneg ha]
    calc
      _ ≤ S * Real.exp (1 - c) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hgv ha
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left ht 1)) S_nonneg
  rw [U, ite_eq_right hc.not_ge, mul_comm (ell x)]
  exact ⟨mul_le_mul_of_nonneg_right (abs_le.mp hfactor).1 (ell_nonneg x),
    mul_le_mul_of_nonneg_right (abs_le.mp hfactor).2 (ell_nonneg x)⟩

private theorem U_bounds {c x g v : ℝ} (hc₀ : 0 ≤ c)
    (hg₀ : 0 ≤ g) (hg₁ : g ≤ 1) (hv : |v| ≤ 1) :
    -S * ell x ≤ U c x g v ∧ U c x g v ≤ M * ell x := by
  by_cases hc : c ≤ 1
  · rw [U, ite_eq_left hc, mul_comm (ell x)]
    have h := shallow_bounds hc₀ hc hg₀ hg₁ hv
    exact ⟨mul_le_mul_of_nonneg_right h.1 (ell_nonneg x),
      mul_le_mul_of_nonneg_right h.2 (ell_nonneg x)⟩
  · have hc' := lt_of_not_ge hc
    have h := U_deep_bounds (x := x) hc' hc'.le hg₀ hg₁ hv
    simp only [sub_self, Real.exp_zero, mul_one] at h
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right S_le_M (ell_nonneg x))⟩

private theorem ell_le_height_tail {h x : ℝ} (hh : 0 < h) (hx : h < |x|) :
    ell x ≤ (1 / h) * (2 * kernel h x) := by
  have hx₂ : h ^ 2 ≤ x ^ 2 := by
    simpa only [sq_abs] using ((sq_le_sq₀ hh.le (abs_nonneg x)).mpr hx.le)
  calc
    ell x = 1 / (1 / 4 + x ^ 2) := (one_div _).symm
    _ ≤ 2 / (h ^ 2 + x ^ 2) := by
      apply (div_le_div_iff₀ (ell_denom_pos x) (kernel_denom_pos hh x)).mpr
      linarith only [hx₂]
    _ = (1 / h) * (2 * kernel h x) := by
      unfold kernel
      field_simp [hh.ne', (kernel_denom_pos hh x).ne']

private theorem ell_le_global {h : ℝ} (hh : 1 ≤ h) (x : ℝ) :
    ell x ≤ (2 * h) * (2 * kernel h x) := by
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  have hh₂ : 1 ≤ h ^ 2 := one_le_pow₀ hh
  have hprod := mul_nonneg (show 0 ≤ 4 * h ^ 2 - 1 by linarith only [hh₂]) (sq_nonneg x)
  calc
    ell x = 1 / (1 / 4 + x ^ 2) := (one_div _).symm
    _ ≤ (4 * h ^ 2) / (h ^ 2 + x ^ 2) := by
      apply (div_le_div_iff₀ (ell_denom_pos x) (kernel_denom_pos hh₀ x)).mpr
      linarith only [hprod]
    _ = (2 * h) * (2 * kernel h x) := by unfold kernel; ring

private theorem transfer_price {u e k r A B L H : ℝ} (hk : 0 ≤ k) (he : e ≤ r * k)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : -A * e ≤ u ∧ u ≤ B * e)
    (hL : A * r ≤ L) (hH : B * r ≤ H) : -L * k ≤ u ∧ u ≤ H * k := by
  constructor
  · calc
      -L * k ≤ -(A * r) * k := mul_le_mul_of_nonneg_right (neg_le_neg hL) hk
      _ = -A * (r * k) := by ring
      _ ≤ -A * e := mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hA)
      _ ≤ u := hu.1
  · calc
      u ≤ B * e := hu.2
      _ ≤ B * (r * k) := mul_le_mul_of_nonneg_left he hB
      _ = (B * r) * k := (mul_assoc _ _ _).symm
      _ ≤ H * k := mul_le_mul_of_nonneg_right hH hk

/-- Outside the closed census rectangle, price the signed model correction
against `2 k_h(x)`, with different lower and upper constants. -/
public theorem exterior_price {h C c x g v : ℝ} (hh : 1 ≤ h) (hC : 1 < C)
    (hc : 0 ≤ c) (hg₀ : 0 ≤ g) (hg₁ : g ≤ 1) (hv : |v| ≤ 1)
    (hout : ¬ (|x| ≤ h ∧ c ≤ C)) :
    -price h C S * (2 * kernel h x) ≤ U c x g v ∧
      U c x g v ≤ price h C M * (2 * kernel h x) := by
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  have hk : 0 ≤ 2 * kernel h x := mul_nonneg (by norm_num) (kernel_nonneg hh₀ x)
  by_cases hx : |x| ≤ h
  · have hcC : C < c := lt_of_not_ge fun hc' ↦ hout ⟨hx, hc'⟩
    have hA : 0 ≤ S * Real.exp (1 - C) := mul_nonneg S_nonneg (Real.exp_pos _).le
    have hprice (K : ℝ) : (S * Real.exp (1 - C)) * (2 * h) ≤ price h C K := calc
      _ = 2 * h * S * Real.exp (1 - C) := by ring
      _ ≤ _ := le_max_right _ _
    exact transfer_price hk (ell_le_global hh x) hA hA
      (U_deep_bounds (hC.trans hcC) hcC.le hg₀ hg₁ hv) (hprice S) (hprice M)
  · have hprice (K : ℝ) : K * (1 / h) ≤ price h C K := by
      rw [mul_one_div]
      exact le_max_left _ _
    exact transfer_price hk (ell_le_height_tail hh₀ (lt_of_not_ge hx)) S_nonneg
      (S_nonneg.trans S_le_M) (U_bounds hc hg₀ hg₁ hv) (hprice S) (hprice M)

/-- Sum over the complement of the rectangle. Even if both exterior
conditions hold at an index, its weight enters the single unused mass just once. -/
public theorem sum_exterior_price {ι : Type*} (s : Finset ι) (x c g v ν : ι → ℝ)
    {h C : ℝ} (hh : 1 ≤ h) (hC : 1 < C)
    (hν : ∀ i ∈ s, 0 ≤ ν i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hg₀ : ∀ i ∈ s, 0 ≤ g i) (hg₁ : ∀ i ∈ s, g i ≤ 1) (hv : ∀ i ∈ s, |v i| ≤ 1) :
    let outside := s.filter (fun i ↦ ¬ (|x i| ≤ h ∧ c i ≤ C))
    let mass := ∑ i ∈ outside, ν i * (2 * kernel h (x i))
    let correction := ∑ i ∈ outside, ν i * U (c i) (x i) (g i) (v i);
    -price h C S * mass ≤ correction ∧ correction ≤ price h C M * mass := by
  intro outside mass correction
  have hpoint (i : ι) (hi : i ∈ outside) := by
    have ⟨his, hiout⟩ := Finset.mem_filter.mp hi
    exact exterior_price hh hC (hc i his) (hg₀ i his) (hg₁ i his) (hv i his) hiout
  dsimp only [mass, correction]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hwi := hν i (Finset.mem_filter.mp hi).1
    calc
      _ = ν i * (-price h C S * (2 * kernel h (x i))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpoint i hi).1 hwi
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hwi := hν i (Finset.mem_filter.mp hi).1
    calc
      _ ≤ ν i * (price h C M * (2 * kernel h (x i))) :=
        mul_le_mul_of_nonneg_left (hpoint i hi).2 hwi
      _ = _ := by ring

end

end Masullo.CensusExteriorPrice
