module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Finset.Powerset
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Centered shape integral for the separated signed kernel

Source: `0e672a90:.godel/bob/separated-signed-tuples.md`, lines 59–69, and the
arithmetic handoff at the end of `6fe747e1:.godel/bob/detection-radius.md`.
This is the integral identity on the already indexed atoms, not a tuple relabeling,
squarefreeness argument, or bound. The support radius is a parameter (in particular,
it can be `D ^ 2`). An existing gate on the indexed atoms is intersected with this
separation; the passage from the ordered rounded-slot test to such a gate is not
formalized here.

Owning check session: `01a208fa-736c-75e9-a336-a5cd6d3b0490`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace SeparatedShapeIntegral

/-- The even kernel, including its zero continuation outside the triangular window. -/
@[expose] public noncomputable def triangularCosine (z : ℝ) : ℝ :=
  max (1 - |z| / (2 * Real.pi)) 0 * Real.cos z

/-- Inclusive weighted mass at or below `z`, with each index contributing separately. -/
@[expose] public noncomputable def cumulativeWeight {ι : Type*} (atoms : Finset ι)
    (weight mass : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ atoms, if mass i ≤ z then weight i else 0

local notation "L" => (2 * Real.pi)

private theorem window_pos : 0 < L := mul_pos (by norm_num) Real.pi_pos

private noncomputable def shape (z : ℝ) : ℝ := (1 - z / L) * Real.cos z

private noncomputable def slope (z : ℝ) : ℝ :=
  -(1 / L) * Real.cos z - (1 - z / L) * Real.sin z

private theorem shape_at_top : shape L = 0 := by
  simp [shape]

private theorem triangularCosine_eq_shape {z : ℝ} (hz : 0 ≤ z) (hzL : z ≤ L) :
    triangularCosine z = shape z := by
  rw [triangularCosine, abs_of_nonneg hz, max_eq_left, shape]
  exact sub_nonneg.mpr ((div_le_iff₀ window_pos).mpr (by simpa using hzL))

private theorem triangularCosine_eq_zero {z : ℝ} (hz : L ≤ z) : triangularCosine z = 0 := by
  have hz0 := window_pos.le.trans hz
  rw [triangularCosine, abs_of_nonneg hz0, max_eq_right, zero_mul]
  exact sub_nonpos.mpr ((le_div_iff₀ window_pos).mpr (by simpa using hz))

private theorem hasDerivAt_shape (z : ℝ) : HasDerivAt shape (slope z) z := by
  unfold shape slope
  convert (((hasDerivAt_id z).div_const L).const_sub 1).mul (Real.hasDerivAt_cos z) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

private theorem continuous_slope : Continuous slope := by
  unfold slope
  fun_prop

private theorem deriv_triangularCosine {z : ℝ} (hz : 0 < z) (hzL : z < L) :
    deriv triangularCosine z = slope z := by
  have h : triangularCosine =ᶠ[𝓝 z] shape := by
    filter_upwards [Ioo_mem_nhds hz hzL] with x hx
    exact triangularCosine_eq_shape hx.1.le hx.2.le
  rw [h.deriv_eq, (hasDerivAt_shape z).deriv]

private theorem ae_ne_real (y : ℝ) : ∀ᵐ x : ℝ, x ≠ y := by
  rw [ae_iff]
  simpa only [not_not, ofPred_eq_eq_singleton] using (measure_singleton (μ := volume) y)

private theorem integral_shape : ∫ z in (0 : ℝ)..L, shape z = 0 := by
  let F (z : ℝ) := (1 - z / L) * Real.sin z - Real.cos z / L
  have hF (z : ℝ) : HasDerivAt F (shape z) z := by
    unfold F shape
    convert ((((hasDerivAt_id z).div_const L).const_sub 1).mul
      (Real.hasDerivAt_sin z)).sub ((Real.hasDerivAt_cos z).div_const L) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hc : Continuous shape := by unfold shape; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ ↦ hF z)
    (hc.intervalIntegrable _ _)]
  simp [F, Real.sin_two_pi, Real.cos_two_pi]

private theorem integral_linear_slope : ∫ z in (0 : ℝ)..L, (z / L) * slope z = 0 := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun z : ℝ ↦ z / L)
    (fun z _ ↦ (hasDerivAt_id z).div_const L) (fun z _ ↦ hasDerivAt_shape z)
    (continuous_const.intervalIntegrable _ _) (continuous_slope.intervalIntegrable _ _)]
  simp [shape_at_top, intervalIntegral.integral_const_mul, integral_shape]

private theorem intervalIntegrable_atom (m c : ℝ) :
    IntervalIntegrable (fun z ↦ if m ≤ z then slope z * c else 0) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le window_pos.le]
  exact ((continuous_slope.mul_const c).intervalIntegrable (μ := volume) 0 L).1.indicator
    (measurableSet_Ici (a := m))

private theorem integral_atom {m : ℝ} (hm : 0 ≤ m) (c : ℝ) :
    (∫ z in (0 : ℝ)..L, if m ≤ z then slope z * c else 0) =
      -(c * triangularCosine m) := by
  by_cases hmL : m ≤ L
  · calc
      _ = ∫ z in (0 : ℝ)..L, (Ioi m).indicator (fun z ↦ slope z * c) z := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_ne_real m] with z hz _
        simp only [Set.indicator, Set.mem_Ioi, le_iff_lt_or_eq, show ¬ m = z from Ne.symm hz,
          or_false]
      _ = ∫ z in m..L, slope z * c := by
        have h : Ioc 0 L ∩ Ioi m = Ioc m L := by
          apply Set.ext
          intro z
          exact ⟨fun hz ↦ ⟨hz.2, hz.1.2⟩, fun hz ↦ ⟨⟨hm.trans_lt hz.1, hz.2⟩, hz.1⟩⟩
        rw [intervalIntegral.integral_of_le window_pos.le, setIntegral_indicator measurableSet_Ioi,
          h, intervalIntegral.integral_of_le hmL]
      _ = _ := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ ↦ hasDerivAt_shape z)
            (continuous_slope.intervalIntegrable _ _),
          shape_at_top, triangularCosine_eq_shape hm hmL]
        ring
  · have hzero : (∫ z in (0 : ℝ)..L, if m ≤ z then slope z * c else 0) = 0 := by
      calc
        _ = ∫ z in (0 : ℝ)..L, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro z hz
          rw [uIcc_of_le window_pos.le] at hz
          exact ite_eq_right (not_le.mpr (hz.2.trans_lt (lt_of_not_ge hmL)))
        _ = 0 := intervalIntegral.integral_zero
    simp [hzero, triangularCosine_eq_zero (le_of_not_ge hmL)]

/-- The sum of the triangular cosine against finitely many signed atoms equals the
negative integral of its derivative against the centered inclusive count. No
cancellation or exclusion of endpoints (or of masses past the cutoff) is required.
Each atom integrates over the tail from its mass to the cutoff; integration by
parts and the zero mean of the kernel on the window remove the linear profile. -/
public theorem sum_triangularCosine_eq_centered_integral {ι : Type*} (atoms : Finset ι)
    (weight mass : ι → ℝ) (hmass : ∀ i ∈ atoms, 0 ≤ mass i) :
    let N := cumulativeWeight atoms weight mass
    ∑ i ∈ atoms, weight i * triangularCosine (mass i) =
      -(∫ z in (0 : ℝ)..(2 * Real.pi),
        deriv triangularCosine z * (N z - z / (2 * Real.pi) * N (2 * Real.pi))) := by
  dsimp only
  let N := cumulativeWeight atoms weight mass
  change _ = -(∫ z in (0 : ℝ)..L, deriv triangularCosine z * (N z - z / L * N L))
  have hN (z : ℝ) : slope z * N z =
      ∑ i ∈ atoms, if mass i ≤ z then slope z * weight i else 0 := by
    change slope z * cumulativeWeight atoms weight mass z = _
    rw [cumulativeWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : mass i ≤ z <;> simp [hi]
  have hintN : IntervalIntegrable (fun z ↦ slope z * N z) volume 0 L := by
    simp_rw [hN]
    convert (IntervalIntegrable.sum atoms fun i _ ↦ intervalIntegrable_atom (mass i) (weight i))
      using 1
    funext z
    rw [Finset.sum_apply]
  have hintL : IntervalIntegrable (fun z ↦ slope z * (z / L * N L)) volume 0 L :=
    (continuous_slope.mul ((continuous_id.div_const L).mul_const (N L))).intervalIntegrable _ _
  have hL : ∫ z in (0 : ℝ)..L, slope z * (z / L * N L) = 0 := by
    calc
      _ = ∫ z in (0 : ℝ)..L, (z / L * slope z) * N L := by
        apply intervalIntegral.integral_congr
        intro z _
        ring
      _ = 0 := by rw [intervalIntegral.integral_mul_const, integral_linear_slope, zero_mul]
  calc
    _ = -(∫ z in (0 : ℝ)..L, slope z * N z) := by
      simp_rw [hN]
      rw [intervalIntegral.integral_finsetSum
        (fun i _ ↦ intervalIntegrable_atom (mass i) (weight i))]
      rw [show (∑ i ∈ atoms, ∫ z in (0 : ℝ)..L, if mass i ≤ z then slope z * weight i else 0) =
          ∑ i ∈ atoms, -(weight i * triangularCosine (mass i)) from
        Finset.sum_congr rfl (fun i hi ↦ integral_atom (hmass i hi) (weight i))]
      rw [Finset.sum_neg_distrib, neg_neg]
    _ = -(∫ z in (0 : ℝ)..L, slope z * (N z - z / L * N L)) := by
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub hintN hintL, hL, sub_zero]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_ne_real L] with z hz hzI
      rw [uIoc_of_le window_pos.le] at hzI
      rw [deriv_triangularCosine hzI.1 (lt_of_le_of_ne hzI.2 hz)]

/-- Label the balanced atoms by `(I, B)` from the given set of eligible starts,
retaining pairwise support separation and intersecting it with the supplied original
gate. Taking `gate` constantly `true` gives the separated count without a further
rounded-slot test. -/
@[expose] public noncomputable def balancedAtoms (starts : Finset ℕ) (R : ℝ) (h : ℕ)
    (gate : Finset ℕ → Finset ℕ → Bool) : Finset (Σ _ : Finset ℕ, Finset ℕ) := by
  classical
  exact ((starts.powersetCard (2 * h)).filter
      (fun I ↦ ∀ p : ℕ, p ∈ I → ∀ q : ℕ, q ∈ I → p ≠ q → R < |(p : ℝ) - (q : ℝ)|)).sigma
    (fun I ↦ (I.powersetCard h).filter (fun B ↦ gate I B))

/-- The integer `P_I` from the shifted pairs in the support. -/
@[expose] public def supportProduct (d : ℕ) (I : Finset ℕ) : ℕ :=
  ∏ p ∈ I, p * (p + d)

/-- The integer `v_B`, choosing the shifted endpoint on `B` and the start elsewhere. -/
@[expose] public def balancedDivisor (d : ℕ) (I B : Finset ℕ) : ℕ :=
  (∏ p ∈ B, (p + d)) * ∏ p ∈ I \ B, p

/-- Weight of one balanced atom, including the multiplicity of the two orderings. -/
@[expose] public noncomputable def balancedWeight (h : ℕ) (w : ℕ → ℝ) (I : Finset ℕ) : ℝ :=
  (h.factorial : ℝ) ^ 2 * ∏ p ∈ I, w p

private theorem mass_le_iff_in_window {t P v : ℝ} (ht : 0 < t) (hP : 0 < P) (hv : 0 < v)
    (z : ℝ) :
    t * |Real.log (v ^ 2 / P)| ≤ z ↔
      √P * Real.exp (-(z / (2 * t))) ≤ v ∧ v ≤ √P * Real.exp (z / (2 * t)) := by
  have hs : Real.exp (Real.log P / 2) = √P := by
    rw [← Real.log_sqrt hP.le, Real.exp_log (Real.sqrt_pos.2 hP)]
  have hlo : √P * Real.exp (-(z / (2 * t))) ≤ v ↔
      Real.log P / 2 - z / (2 * t) ≤ Real.log v := by
    rw [← hs, ← Real.exp_add, ← Real.exp_log hv, Real.exp_le_exp, sub_eq_add_neg, Real.log_exp]
  have hhi : v ≤ √P * Real.exp (z / (2 * t)) ↔
      Real.log v ≤ Real.log P / 2 + z / (2 * t) := by
    rw [← hs, ← Real.exp_add, ← Real.exp_log hv, Real.exp_le_exp, Real.log_exp]
  rw [hlo, hhi, ← le_div_iff₀' ht, abs_le, Real.log_div (pow_ne_zero _ hv.ne') hP.ne',
    Real.log_pow, show z / (2 * t) = (z / t) / 2 by ring]
  constructor <;> intro hz <;> constructor <;> linarith only [hz.1, hz.2]

/-- The constrained divisor count summed over all admitted supports and balanced selections.
Both bounds are inclusive, and `w` may have either sign. -/
@[expose] public noncomputable def balancedDivisorCount (starts : Finset ℕ) (R : ℝ) (h d : ℕ)
    (gate : Finset ℕ → Finset ℕ → Bool) (w : ℕ → ℝ) (t z : ℝ) : ℝ :=
  ∑ a ∈ balancedAtoms starts R h gate,
    if √(supportProduct d a.1 : ℝ) * Real.exp (-(z / (2 * t))) ≤ (balancedDivisor d a.1 a.2 : ℝ) ∧
        (balancedDivisor d a.1 a.2 : ℝ) ≤ √(supportProduct d a.1 : ℝ) * Real.exp (z / (2 * t))
    then balancedWeight h w a.1 else 0

/-- The source's centered signed shape identity for balanced divisor atoms. The sum is
unrestricted in mass: the kernel itself vanishes past its cutoff. No absence of zero
atoms, squarefreeness, or zero total weight is needed for this integral step. -/
public theorem balancedDivisor_sum_eq_centered_integral (starts : Finset ℕ) (R : ℝ) (h d : ℕ)
    (gate : Finset ℕ → Finset ℕ → Bool) (w : ℕ → ℝ) {t : ℝ} (ht : 0 < t)
    (hstarts : ∀ p ∈ starts, 0 < p) :
    let N := balancedDivisorCount starts R h d gate w t
    (∑ a ∈ balancedAtoms starts R h gate,
      balancedWeight h w a.1 * triangularCosine
        (t * |Real.log ((balancedDivisor d a.1 a.2 : ℝ) ^ 2 / (supportProduct d a.1 : ℝ))|)) =
      -(∫ z in (0 : ℝ)..(2 * Real.pi),
        deriv triangularCosine z * (N z - z / (2 * Real.pi) * N (2 * Real.pi))) := by
  let A := balancedAtoms starts R h gate
  let weight : (Σ _ : Finset ℕ, Finset ℕ) → ℝ := fun a ↦ balancedWeight h w a.1
  let mass : (Σ _ : Finset ℕ, Finset ℕ) → ℝ := fun a ↦
    t * |Real.log ((balancedDivisor d a.1 a.2 : ℝ) ^ 2 / (supportProduct d a.1 : ℝ))|
  have hcount (z : ℝ) : cumulativeWeight A weight mass z =
      balancedDivisorCount starts R h d gate w t z := by
    unfold cumulativeWeight balancedDivisorCount
    apply Finset.sum_congr rfl
    intro a ha
    change a ∈ balancedAtoms starts R h gate at ha
    unfold balancedAtoms at ha
    have hmem := Finset.mem_sigma.mp ha
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hmem
    obtain ⟨⟨⟨hI, _⟩, _⟩, ⟨⟨hB, _⟩, _⟩⟩ := hmem
    have hp (p : ℕ) (hp : p ∈ a.1) : 0 < p := hstarts p (hI hp)
    have hshift (p : ℕ) (hp' : p ∈ a.1) : 0 < p + d := (hp p hp').trans_le (Nat.le_add_right ..)
    have hP : 0 < (supportProduct d a.1 : ℝ) := by
      exact_mod_cast (Finset.prod_pos (fun p hp' ↦ Nat.mul_pos (hp p hp') (hshift p hp')) :
        0 < supportProduct d a.1)
    have hv : 0 < (balancedDivisor d a.1 a.2 : ℝ) := by
      have hv' : 0 < balancedDivisor d a.1 a.2 :=
        Nat.mul_pos (Finset.prod_pos fun p hp' ↦ hshift p (hB hp'))
          (Finset.prod_pos fun p hp' ↦ hp p (Finset.mem_sdiff.mp hp').1)
      exact_mod_cast hv'
    change (if mass a ≤ z then weight a else 0) = _
    unfold mass weight
    simp only [mass_le_iff_in_window ht hP hv]
  have hi := sum_triangularCosine_eq_centered_integral A weight mass
    (fun _ _ ↦ mul_nonneg ht.le (abs_nonneg _))
  dsimp only at hi ⊢
  simpa only [hcount] using hi

end SeparatedShapeIntegral
