module

public import Lemmas.PositiveTupleCore
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- Reuse the proved permutation witness and the angular phase identities.
import all Lemmas.OrderedPrimeTupleDiagonal
import all Lemmas.PrimeTupleRedrawSpacing
import all Lemmas.SignedBlockIntervalMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compact majorants for a frozen prime-pair moment

Source: `db760d6f:.godel/bob/dyadic-prime-pair-moments.md:9–15`.
Consumer: `78091476:.godel/bob/balanced-height-reconstruction.md:48–62`,
where the short moment prices the omitted heights on each dyadic shell.
Owning check session: `01a209ce-61c0-7258-9ef8-09cad8ad12db`.

One positive shift, one finite set of genuine prime pairs, and fixed weights and
unit twists throughout the height integral. The exact mass counts ordered tuple
pairs, not permutation witnesses. This is a continuous integral in the strict
short-order spacing range; it does not address moving cutoffs, grids, or long
moments with surviving nonzero frequencies.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Masullo.PrimePairShellMoment

open SignedBlockIntervalMoment (phase phase_add phase_neg norm_phase continuous_phase
  sincKernel triangle integrable_sincKernel sincKernel_transform)

/-- The frozen polynomial at one shift, with one fixed complex twist per start. -/
@[expose] public noncomputable def primePairSum (S : Finset ℕ) (d : ℕ)
    (w : ℕ → ℝ) (χ : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ S, (w p : ℂ) * χ p *
    Complex.exp ((↑(u * Real.log ((↑(p + d) : ℝ) / p)) : ℂ) * Complex.I)

/-- The translated *unnormalized* compact-Fourier majorant. -/
@[expose] public noncomputable def shellKernel (T c u : ℝ) : ℝ :=
  Real.sinc ((u - c) / (2 * T)) ^ 2

private theorem shellKernel_eq_scale {T : ℝ} (hT : 0 < T) (c u : ℝ) :
    shellKernel T c u = (2 * Real.pi * T) * sincKernel (80 * T) (u - c) := by
  have harg : 80 * (u - c) / (2 * (80 * T)) = (u - c) / (2 * T) := by
    field_simp [hT.ne']
  have hscale : (2 * Real.pi * T) * (80 / (2 * Real.pi * (80 * T))) = 1 := by
    field_simp [Real.pi_ne_zero, hT.ne']
  rw [shellKernel, sincKernel, harg, ← mul_assoc, hscale, one_mul]

private theorem integrable_shellKernel {T : ℝ} (hT : 0 < T) (c : ℝ) :
    Integrable (shellKernel T c) := by
  rw [funext (shellKernel_eq_scale hT c)]
  exact ((integrable_sincKernel (show 0 < 80 * T by positivity)).comp_sub_right c).const_mul _

private theorem integrable_shellKernel_phase {T : ℝ} (hT : 0 < T) (c x : ℝ) :
    Integrable (fun u ↦ (shellKernel T c u : ℂ) * phase (u * x)) :=
  ((integrable_shellKernel hT c).ofReal (𝕜 := ℂ)).mul_bdd
    (continuous_phase.comp (continuous_id.mul_const _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ (norm_phase (u * x)).le)

private theorem shellKernel_transform {T : ℝ} (hT : 0 < T) (c x : ℝ) :
    (∫ u, (shellKernel T c u : ℂ) * phase (u * x)) =
      (↑(2 * Real.pi * T) : ℂ) * phase (c * x) * (↑(max (1 - T * |x|) 0) : ℂ) := by
  let f (u : ℝ) := (shellKernel T c u : ℂ) * phase (u * x)
  change (∫ u, f u) = _
  rw [← integral_add_right_eq_self f c]
  have hstep (v : ℝ) : f (v + c) =
      ((↑(2 * Real.pi * T) : ℂ) * phase (c * x)) *
        ((sincKernel (80 * T) v : ℂ) * phase (v * x)) := by
    simp only [f, shellKernel_eq_scale hT, add_sub_cancel_right, Complex.ofReal_mul, add_mul,
      phase_add]
    ring
  simp_rw [hstep]
  rw [integral_const_mul, sincKernel_transform (show 0 < 80 * T by positivity), triangle]
  have ha : 80 / (80 * T) = T⁻¹ := by field_simp [hT.ne']
  rw [ha, div_inv_eq_mul, mul_comm |x| T]

private abbrev tuples (S : Finset ℕ) (m : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m ↦ S)

private noncomputable def tupleFreq {m : ℕ} (d : ℕ) (a : Fin m → ℕ) : ℝ :=
  ∑ i, Real.log ((↑(a i + d) : ℝ) / a i)

private def tupleWeight {m : ℕ} (w : ℕ → ℝ) (a : Fin m → ℕ) : ℝ :=
  ∏ i, w (a i)

private def tupleCoeff {m : ℕ} (w : ℕ → ℝ) (χ : ℕ → ℂ) (a : Fin m → ℕ) : ℂ :=
  ∏ i, (w (a i) : ℂ) * χ (a i)

private theorem pow_primePairSum_eq {S : Finset ℕ} {d m : ℕ}
    (w : ℕ → ℝ) (χ : ℕ → ℂ) (u : ℝ) :
    primePairSum S d w χ u ^ m =
      ∑ a ∈ tuples S m, tupleCoeff w χ a * phase (u * tupleFreq d a) := by
  rw [← Fin.prod_const m (primePairSum S d w χ u)]
  unfold primePairSum
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [tupleCoeff, tupleFreq, phase, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum, Finset.prod_mul_distrib]

private theorem moment_expansion (S : Finset ℕ) (d m : ℕ) (w : ℕ → ℝ) (χ : ℕ → ℂ) (u : ℝ) :
    (↑(‖primePairSum S d w χ u‖ ^ (2 * m)) : ℂ) =
      ∑ ab ∈ (tuples S m ×ˢ tuples S m),
        (tupleCoeff w χ ab.1 * conj (tupleCoeff w χ ab.2)) *
          phase (u * (tupleFreq d ab.1 - tupleFreq d ab.2)) := by
  rw [Nat.mul_comm 2 m, pow_mul, ← norm_pow, Complex.ofReal_pow, ← Complex.mul_conj',
    pow_primePairSum_eq, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, ← phase_neg, mul_sub, sub_eq_add_neg, phase_add]
  ring

private theorem coeff_mul_conj_of_eq {S : Finset ℕ} {d m : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) {a b : Fin m → ℕ}
    (ha : a ∈ tuples S m) (hb : b ∈ tuples S m) (heq : tupleFreq d a = tupleFreq d b)
    (w : ℕ → ℝ) (χ : ℕ → ℂ) (hχ : ∀ p ∈ S, ‖χ p‖ = 1) :
    tupleCoeff w χ a * conj (tupleCoeff w χ b) = ↑(tupleWeight w a * tupleWeight w b) := by
  have ha' := Fintype.mem_piFinset.mp ha
  have hb' := Fintype.mem_piFinset.mp hb
  obtain ⟨σ, hσ⟩ := OrderedPrimeTupleDiagonal.exists_perm_of_frequency_eq hd hprime ha' hb' heq
  let twist (v : Fin m → ℕ) : ℂ := ∏ i, χ (v i)
  have hreindex : twist b = twist a := by
    rw [hσ]
    exact Equiv.prod_comp σ (fun i ↦ χ (a i))
  have hunit : ‖twist a‖ = 1 := by
    dsimp only [twist]
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ ↦ hχ _ (ha' i)
  have hcancel : twist a * conj (twist a) = 1 := by
    rw [Complex.mul_conj', hunit]
    simp
  have hfactor (v : Fin m → ℕ) : tupleCoeff w χ v = (tupleWeight w v : ℂ) * twist v := by
    simp only [tupleCoeff, tupleWeight, twist, Finset.prod_mul_distrib, Complex.ofReal_prod]
  simp only [hfactor, map_mul, Complex.conj_ofReal, hreindex, Complex.ofReal_mul]
  calc
    _ = (↑(tupleWeight w a) * ↑(tupleWeight w b)) * (twist a * conj (twist a)) := by ring
    _ = _ := by rw [hcancel, mul_one]

private theorem bandwidth_lt_of_ne {S : Finset ℕ} {d m : ℕ} {X T : ℝ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X) (hT : 0 < T)
    (hshort : X ^ (2 * m) < T) {a b : Fin m → ℕ}
    (ha : a ∈ tuples S m) (hb : b ∈ tuples S m) (hne : tupleFreq d a ≠ tupleFreq d b) :
    1 < T * |tupleFreq d a - tupleFreq d b| := by
  open PrimeTupleRedrawSpacing in
  have hbounded {v : Fin m → ℕ} (hv : v ∈ tuples S m) : BoundedStarts X d v := by
    intro i
    have hi := Fintype.mem_piFinset.mp hv i
    exact ⟨(hprime _ hi).1.pos, hcap _ hi⟩
  open PrimeTupleRedrawSpacing in
  have hfreq (v : Fin m → ℕ) : frequency d (fun _ ↦ true) v = tupleFreq d v := by
    simp only [frequency, signedLabel, ite_true, tupleFreq]
  open PrimeTupleRedrawSpacing in
  have hsep := spacing_of_ne (k := m) hd (fun _ ↦ true) (hbounded hb) (hbounded ha)
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)) (by simpa only [hfreq] using hne)
  have hexp : 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) := by norm_cast
  rw [hfreq, hfreq, hexp, zpow_neg, zpow_natCast, ← one_div] at hsep
  exact (div_lt_iff₀' hT).mp
    ((one_div_lt_one_div_of_lt (pow_pos (zero_lt_one.trans hX) _) hshort).trans_le hsep)

/-- In the strict spacing range, the translated sinc-square integral is exactly
`2πT` times the ordered zero-frequency mass, for every center and fixed unit twist.
Real weights need not have a sign. -/
public theorem integral_shellKernel_mul_moment_eq {S : Finset ℕ} {d m : ℕ} {X T : ℝ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X) (hT : 0 < T)
    (hshort : X ^ (2 * m) < T) (w : ℕ → ℝ) (χ : ℕ → ℂ)
    (hχ : ∀ p ∈ S, ‖χ p‖ = 1) (c : ℝ) :
    (∫ u, shellKernel T c u * ‖primePairSum S d w χ u‖ ^ (2 * m)) =
      (2 * Real.pi * T) * PositiveTupleCore.zeroMass (Fintype.piFinset (fun _ : Fin m ↦ S))
        (fun a ↦ ∑ i, Real.log ((↑(a i + d) : ℝ) / a i)) (fun a ↦ ∏ i, w (a i)) := by
  classical
  let B := tuples S m ×ˢ tuples S m
  let ν (ab : (Fin m → ℕ) × (Fin m → ℕ)) := tupleFreq d ab.1 - tupleFreq d ab.2
  let C (ab : (Fin m → ℕ) × (Fin m → ℕ)) :=
    tupleCoeff w χ ab.1 * conj (tupleCoeff w χ ab.2)
  let M (ab : (Fin m → ℕ) × (Fin m → ℕ)) (u : ℝ) :=
    C ab * ((shellKernel T c u : ℂ) * phase (u * ν ab))
  have hM (ab : (Fin m → ℕ) × (Fin m → ℕ)) : Integrable (M ab) :=
    (integrable_shellKernel_phase hT c (ν ab)).const_mul _
  apply Complex.ofReal_injective
  calc
    _ = ∫ u, (↑(shellKernel T c u * ‖primePairSum S d w χ u‖ ^ (2 * m)) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = ∫ u, ∑ ab ∈ B, M ab u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Complex.ofReal_mul, moment_expansion, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ab _ ↦ by dsimp only [M, C, ν]; ring
    _ = ∑ ab ∈ B, ∫ u, M ab u := integral_finsetSum _ fun ab _ ↦ hM ab
    _ = ∑ ab ∈ B, (↑(2 * Real.pi * T) : ℂ) *
        (if tupleFreq d ab.1 = tupleFreq d ab.2 then
           (↑(tupleWeight w ab.1 * tupleWeight w ab.2) : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro ab hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      change (∫ u, C ab * ((shellKernel T c u : ℂ) * phase (u * ν ab))) = _
      rw [integral_const_mul, shellKernel_transform hT]
      by_cases heq : tupleFreq d ab.1 = tupleFreq d ab.2
      · have hz : ν ab = 0 := sub_eq_zero.mpr heq
        simp only [C, coeff_mul_conj_of_eq hd hprime ha hb heq w χ hχ, hz, mul_zero, abs_zero,
          sub_zero, max_eq_left zero_le_one, Complex.ofReal_one, phase, Complex.ofReal_zero,
          zero_mul, Complex.exp_zero, mul_one, ite_eq_left heq]
        exact mul_comm _ _
      · have hcut : max (1 - T * |ν ab|) 0 = 0 :=
          max_eq_right (sub_nonpos.mpr (bandwidth_lt_of_ne hd hprime hcap hX hT hshort ha hb heq).le)
        simp [hcut, heq]
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [PositiveTupleCore.zeroMass, Finset.sum_filter, Complex.ofReal_mul,
        Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero, B, tupleFreq,
        tupleWeight]

private theorem quarter_le_sinc_sq {x : ℝ} (hx : |x| ≤ 1 / 4) :
    1 / 4 ≤ Real.sinc x ^ 2 := by
  suffices h : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 4 → 1 / 2 ≤ Real.sinc y by
    have hy := h |x| (abs_nonneg _) hx
    have heq : Real.sinc |x| = Real.sinc x := by
      rcases le_total 0 x with hx' | hx'
      · rw [abs_of_nonneg hx']
      · rw [abs_of_nonpos hx', Real.sinc_neg]
    rw [heq] at hy
    calc
      _ = (1 / 2 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hy 2
  intro y hy hy'
  rcases hy.eq_or_lt with rfl | hy
  · norm_num
  rw [Real.sinc_of_ne_zero hy.ne', le_div_iff₀ hy]
  have hcube : y ^ 3 ≤ (1 / 4 : ℝ) ^ 2 * y := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le hy' 2) hy.le
  linarith [Real.sin_gt_sub_cube hy]

private theorem integrable_shellKernel_mul_moment {T : ℝ} (hT : 0 < T)
    (S : Finset ℕ) (d m : ℕ) (w : ℕ → ℝ) (χ : ℕ → ℂ) (c : ℝ) :
    Integrable (fun u ↦ shellKernel T c u * ‖primePairSum S d w χ u‖ ^ (2 * m)) := by
  have hc : Continuous (primePairSum S d w χ) := by
    unfold primePairSum
    fun_prop
  apply (integrable_shellKernel hT c).mul_bdd (c := (∑ p ∈ S, ‖(w p : ℂ) * χ p‖) ^ (2 * m))
    (hc.norm.pow (2 * m)).aestronglyMeasurable
  filter_upwards with u
  change ‖‖primePairSum S d w χ u‖ ^ (2 * m)‖ ≤ _
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    _ ≤ ∑ p ∈ S, ‖(w p : ℂ) * χ p * phase (u * Real.log ((↑(p + d) : ℝ) / p))‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_phase, mul_one]

/-- The unweighted shell integral, using the translates centered at `±3T/2`.
The factorial bounds the diagonal without counting repeated permutation witnesses. -/
public theorem setIntegral_shell_moment_le {S : Finset ℕ} {d m : ℕ} {X T : ℝ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X) (hT : 0 < T)
    (hshort : X ^ (2 * m) < T) (w : ℕ → ℝ) (χ : ℕ → ℂ) (hχ : ∀ p ∈ S, ‖χ p‖ = 1) :
    (∫ u in {u : ℝ | T ≤ |u| ∧ |u| ≤ 2 * T}, ‖primePairSum S d w χ u‖ ^ (2 * m)) ≤
      16 * Real.pi * T * (m.factorial : ℝ) * (∑ p ∈ S, w p ^ 2) ^ m := by
  let c := 3 * T / 2
  let E := {u : ℝ | T ≤ |u| ∧ |u| ≤ 2 * T}
  let f (u : ℝ) := ‖primePairSum S d w χ u‖ ^ (2 * m)
  let G (b u : ℝ) := shellKernel T b u * f u
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hG (b : ℝ) : Integrable (G b) := integrable_shellKernel_mul_moment hT S d m w χ b
  have hnonneg (u : ℝ) : 0 ≤ f u := pow_nonneg (norm_nonneg _) _
  have hkernel (b u : ℝ) : 0 ≤ shellKernel T b u := sq_nonneg _
  have hmajor (u : ℝ) (hu : u ∈ E) : 1 / 4 ≤ shellKernel T c u + shellKernel T (-c) u := by
    change T ≤ |u| ∧ |u| ≤ 2 * T at hu
    have hnear (x : ℝ) (hl : -T / 2 ≤ x) (hr : x ≤ T / 2) : |x / (2 * T)| ≤ 1 / 4 := by
      apply abs_le.mpr
      constructor
      · exact (le_div_iff₀ (by positivity : 0 < 2 * T)).mpr (by linarith)
      · exact (div_le_iff₀ (by positivity : 0 < 2 * T)).mpr (by linarith)
    rcases le_total 0 u with hu' | hu'
    · rw [abs_of_nonneg hu'] at hu
      have h := quarter_le_sinc_sq (hnear (u - c) (by dsimp [c]; linarith [hu.1])
        (by dsimp [c]; linarith [hu.2]))
      exact h.trans (le_add_of_nonneg_right (hkernel (-c) u))
    · rw [abs_of_nonpos hu'] at hu
      have h := quarter_le_sinc_sq (hnear (u - (-c)) (by dsimp [c]; linarith [hu.2])
        (by dsimp [c]; linarith [hu.1]))
      exact h.trans (le_add_of_nonneg_left (hkernel c u))
  change (∫ u in E, f u) ≤ _
  calc
    _ = ∫ u, E.indicator f u := (integral_indicator hE).symm
    _ ≤ ∫ u, 4 * (G c u + G (-c) u) := by
      have hf : 0 ≤ᵐ[volume] E.indicator f := Filter.Eventually.of_forall
        (Set.indicator_nonneg fun u _ ↦ hnonneg u)
      apply integral_mono_of_nonneg hf (((hG c).add (hG (-c))).const_mul 4)
      filter_upwards with u
      by_cases hu : u ∈ E
      · rw [Set.indicator_of_mem hu]
        have h := mul_le_mul_of_nonneg_right (hmajor u hu) (hnonneg u)
        change f u ≤ 4 * (shellKernel T c u * f u + shellKernel T (-c) u * f u)
        rw [add_mul] at h
        linarith only [h]
      · rw [Set.indicator_of_notMem hu]
        dsimp only [G]
        exact mul_nonneg (by norm_num) (add_nonneg
          (mul_nonneg (hkernel _ _) (hnonneg _)) (mul_nonneg (hkernel _ _) (hnonneg _)))
    _ = 4 * ((∫ u, G c u) + ∫ u, G (-c) u) := by
      rw [integral_const_mul, integral_add (hG c) (hG (-c))]
    _ ≤ _ := by
      dsimp only [G, f]
      rw [integral_shellKernel_mul_moment_eq hd hprime hcap hX hT hshort w χ hχ,
        integral_shellKernel_mul_moment_eq hd hprime hcap hX hT hshort w χ hχ]
      have h := mul_le_mul_of_nonneg_left (OrderedPrimeTupleDiagonal.zeroMass_le hd hprime m w)
        (show 0 ≤ 2 * Real.pi * T by positivity)
      calc
        _ ≤ 4 * (_ + _) := mul_le_mul_of_nonneg_left (add_le_add h h) (by norm_num)
        _ = _ := by ring

end Masullo.PrimePairShellMoment
