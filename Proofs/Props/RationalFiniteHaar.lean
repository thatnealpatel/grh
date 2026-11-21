module

public import Lemmas.RationalLocalNormShell
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp

/-! # The paired finite Haar shells over the rationals

Masullo defines the unit subtraction in (B.4.4.14), pp. 622–623,
and uses uniformizer translates in (B.4.4.22), p. 625. We calculate
these terms for radial log profiles in the actual rational completion.
The normalization in (B.4.4.21) is `log p` times unit-mass Haar.
This is the subtracted Haar side, not the additive Fourier comparison.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "K" v:max => adicCompletion ℚ v
local notation "G" v => (K v)ˣ
local notation "P[" v "]" => ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)

/-- The finite local kernel before subtracting the unit-group value. -/
@[expose]
public noncomputable def rationalLocalRadialKernel (v : V) (F : ℝ → ℂ) (x : G v) : ℂ :=
  F (Real.log ‖(x : K v)‖) * (‖(x : K v)‖ ^ (1 / 2 : ℝ) : ℝ) / (‖1 - (x : K v)‖ : ℝ)

/-- The kernel of Masullo's subtracted Haar principal value (B.4.4.14).
For a radial profile the subtraction on the unit group is identically zero. -/
@[expose]
public noncomputable def rationalLocalRadialSubtracted (v : V) (F : ℝ → ℂ) (x : G v) : ℂ :=
  if ‖(x : K v)‖ = 1 then 0 else rationalLocalRadialKernel v F x

/-- The subtraction cancels on the entire unit shell, including at the identity. -/
public theorem rationalLocalRadialSubtracted_eq_zero_on_units (v : V) (F : ℝ → ℂ) :
    EqOn (rationalLocalRadialSubtracted v F) 0 (rationalLocalNormShell v 0) := by
  intro x hx
  change ‖(x : K v)‖ = ((P[v] : ℝ)⁻¹) ^ (0 : ℤ) at hx
  rw [zpow_zero] at hx
  simp [rationalLocalRadialSubtracted, hx]

private theorem radial_weight {r : ℝ} (hr : 0 < r) :
    r ^ (1 / 2 : ℝ) / max 1 r = Real.exp (-|Real.log r| / 2) := by
  rw [Real.rpow_def_of_pos hr]
  by_cases h : r ≤ 1
  · rw [max_eq_left h, div_one, abs_of_nonpos (Real.log_nonpos hr.le h), neg_neg]
    congr 1
    ring
  · have h' : 1 < r := lt_of_not_ge h
    rw [max_eq_right h'.le, abs_of_nonneg (Real.log_nonneg h'.le)]
    calc
      _ = Real.exp (Real.log r * (1 / 2)) / Real.exp (Real.log r) := by rw [Real.exp_log hr]
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring

private theorem radial_on_shell (v : V) (F : ℝ → ℂ) {k : ℤ} (hk : k ≠ 0) :
    EqOn (rationalLocalRadialKernel v F)
      (fun _ ↦ F (-(k : ℝ) * Real.log (P[v] : ℝ)) *
        (Real.exp (-|-(k : ℝ) * Real.log (P[v] : ℝ)| / 2) : ℝ)) (rationalLocalNormShell v k) := by
  intro x hx
  have hx' := RationalLocalNormShell.norm_ne_one hk hx
  simp only [rationalLocalRadialKernel, RationalLocalNormShell.norm_sub_one v x hx']
  rw [mul_div_assoc, ← Complex.ofReal_div, radial_weight (norm_pos_iff.mpr x.ne_zero),
    RationalLocalNormShell.log_norm hx]

private theorem radial_integral_shell (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (F : ℝ → ℂ) {k : ℤ} (hk : k ≠ 0) :
    let μ := rationalLocalMultiplicativeHaar v
    let S := rationalLocalNormShell v k
    IntegrableOn (rationalLocalRadialKernel v F) S μ ∧
    (∫ x in S, rationalLocalRadialKernel v F x ∂μ) =
      F (-(k : ℝ) * Real.log (P[v] : ℝ)) *
        (Real.exp (-|-(k : ℝ) * Real.log (P[v] : ℝ)| / 2) : ℝ) := by
  intro μ S
  have hs : MeasurableSet S := RationalLocalNormShell.measurableSet v k
  have hm : μ S = 1 := RationalLocalNormShell.measure v k
  have heq := radial_on_shell v F hk
  refine ⟨(integrableOn_const (by rw [hm]; exact ENNReal.one_ne_top)).congr_fun heq.symm hs, ?_⟩
  rw [setIntegral_congr_fun hs heq, setIntegral_const, measureReal_def, hm,
    ENNReal.toReal_one, one_smul]

/-- Each pair of opposite nonzero shells gives the two reflected prime-power
samples, with the *same* half weight on both. This evaluates one pair in
(B.4.4.22) and includes the normalization in (B.4.4.21).
The source supplies the uniformizer sum; `RationalLocalNormShell.eq_translate`
and `.measure` check its domains and masses, and the ultrametric identity
checks the denominator on each shell before taking the integral. -/
public theorem rationalLocalRadialHaar_shellPair
    (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (F : ℝ → ℂ) {m : ℕ} (hm : 0 < m) :
    let S := rationalLocalNormShell v
    let μ := rationalLocalMultiplicativeHaar v
    let l := Real.log (P[v] : ℝ)
    let a := (m : ℝ) * l
    let B := rationalLocalRadialKernel v F
    IntegrableOn B (S (m : ℤ)) μ ∧ IntegrableOn B (S (-(m : ℤ))) μ ∧
      (l : ℂ) * ((∫ x in S (m : ℤ), B x ∂μ) + (∫ x in S (-(m : ℤ)), B x ∂μ)) =
        (l : ℂ) * (Real.exp (-a / 2) : ℝ) * (F (-a) + F a) := by
  intro S μ l a B
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨hp, hpe⟩ := radial_integral_shell v F hm'
  obtain ⟨hn, hne⟩ := radial_integral_shell v F (neg_ne_zero.mpr hm')
  refine ⟨hp, hn, ?_⟩
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg m)
    (Real.log_pos (RationalLocalNormShell.one_lt_prime v)).le
  have hp' : -((m : ℤ) : ℝ) * Real.log (P[v] : ℝ) = -a := by
    push_cast
    exact neg_mul _ _
  have hn' : -((-(m : ℤ) : ℤ) : ℝ) * Real.log (P[v] : ℝ) = a := by
    push_cast
    simp [a, l]
  rw [hp', abs_neg, abs_of_nonneg ha] at hpe
  rw [hn', abs_of_nonneg ha] at hne
  change (l : ℂ) * ((∫ x in rationalLocalNormShell v (m : ℤ), rationalLocalRadialKernel v F x ∂μ) +
    (∫ x in rationalLocalNormShell v (-(m : ℤ)), rationalLocalRadialKernel v F x ∂μ)) = _
  rw [hpe, hne]
  ring

/-- The rational radial case of the subtracted Haar side of (B.4.4.21)–(22).
The `m` in the sum indexes the pair of shells of valuation `±(m+1)`.
The unit term is removed by subtraction, not by a limit of an unsubtracted
integral. Compact log support makes the individual shell integrals vanish
outside a finite valuation interval. -/
public theorem rationalLocalRadialHaar_eq_shellSum
    (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]
    {F : ℝ → ℂ} (hF : HasCompactSupport F) :
    let μ := rationalLocalMultiplicativeHaar v
    let B := rationalLocalRadialSubtracted v F
    let l := Real.log (P[v] : ℝ)
    let C := fun m : ℕ ↦
      let a := ((m + 1 : ℕ) : ℝ) * l
      (l : ℂ) * (Real.exp (-a / 2) : ℝ) * (F (-a) + F a)
    Integrable B μ ∧ (∃ M : ℕ, ∀ m ≥ M, C m = 0) ∧
      (l : ℂ) * (∫ x, B x ∂μ) = ∑' m : ℕ, C m := by
  intro μ B l C
  let S := rationalLocalNormShell v
  have hl : 0 < l := Real.log_pos (RationalLocalNormShell.one_lt_prime v)
  have hcover : (⋃ k : ℤ, S k) = univ := RationalLocalNormShell.iUnion_eq_univ v
  have hS (k : ℤ) : MeasurableSet (S k) := RationalLocalNormShell.measurableSet v k
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hF.isBounded
  obtain ⟨M, hM⟩ := exists_nat_ge (R / l)
  have hM' : R ≤ (M : ℝ) * l := (div_le_iff₀ hl).mp hM
  have hF₀ {x : ℝ} (hx : R < |x|) : F x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx.not_ge (by simpa [Real.dist_eq] using hR h))
  have hnonunit {k : ℤ} (hk : k ≠ 0) : EqOn B (rationalLocalRadialKernel v F) (S k) := by
    intro x hx
    exact ite_eq_right (RationalLocalNormShell.norm_ne_one hk hx)
  have hBi (k : ℤ) : IntegrableOn B (S k) μ := by
    rcases eq_or_ne k 0 with rfl | hk
    · exact integrableOn_zero.congr_fun (rationalLocalRadialSubtracted_eq_zero_on_units v F).symm (hS 0)
    · exact (radial_integral_shell v F hk).1.congr_fun (hnonunit hk).symm (hS k)
  -- Apply compact support before summing: No cancellation of opposite shells is needed.
  let T : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hout (k : ℤ) (hk : k ∉ T) : EqOn B 0 (S k) := by
    have hki : (M : ℤ) < |k| := by
      simpa only [T, Finset.mem_Icc, ← abs_le, not_le] using hk
    have hkr : (M : ℝ) < |(k : ℝ)| := by exact_mod_cast hki
    intro x hx
    have hlog := RationalLocalNormShell.log_norm hx
    have hxR : R < |Real.log ‖(x : K v)‖| := by
      rw [hlog, abs_mul, abs_neg, abs_of_pos hl]
      exact hM'.trans_lt (mul_lt_mul_of_pos_right hkr hl)
    simp [B, rationalLocalRadialSubtracted, rationalLocalRadialKernel, hF₀ hxR]
  have hBall : Integrable B μ := by
    have hsum : Summable (fun k : ℤ ↦ ∫ x in S k, ‖B x‖ ∂μ) := by
      refine summable_of_ne_finset_zero (s := T) (fun k hk ↦ ?_)
      rw [setIntegral_congr_fun (hS k) (g := fun _ ↦ 0)
        (fun x hx ↦ by simp [hout k hk hx]), integral_zero]
    simpa only [hcover, integrableOn_univ] using
      integrableOn_iUnion_of_summable_integral_norm hBi hsum
  refine ⟨hBall, ⟨M, fun m hm ↦ ?_⟩, ?_⟩
  · have hlt : (M : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hm
    have hpos : R < ((m + 1 : ℕ) : ℝ) * l := hM'.trans_lt (mul_lt_mul_of_pos_right hlt hl)
    have hnonneg : 0 ≤ ((m + 1 : ℕ) : ℝ) * l := mul_nonneg (Nat.cast_nonneg _) hl.le
    have hp := hF₀ (by rwa [abs_of_nonneg hnonneg])
    have hn := hF₀ (by rwa [abs_neg, abs_of_nonneg hnonneg])
    dsimp only [C]
    rw [hp, hn, add_zero, mul_zero]
  · let I (k : ℤ) := ∫ x in S k, B x ∂μ
    have hwhole : HasSum I (∫ x, B x ∂μ) := by
      simpa only [hcover, Measure.restrict_univ] using
        hasSum_integral_iUnion hS (RationalLocalNormShell.pairwiseDisjoint v)
          (hBall.integrableOn (s := ⋃ k : ℤ, S k))
    have h₀ : I 0 = 0 := by
      change (∫ x in S 0, B x ∂μ) = 0
      rw [setIntegral_congr_fun (hS 0) (rationalLocalRadialSubtracted_eq_zero_on_units v F)]
      exact integral_zero _ _
    have hplus := hwhole.summable.comp_injective (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
    have hminus := hwhole.summable.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1))
      (fun _ _ h ↦ Nat.cast_injective (add_right_cancel (neg_injective h)))
    have hshift := hplus.tsum_eq_zero_add
    simp only [Function.comp_apply, Nat.cast_zero, h₀, zero_add] at hshift
    rw [← hwhole.tsum_eq, tsum_of_nat_of_neg_add_one hplus hminus, hshift, ← Summable.tsum_add,
      ← tsum_mul_left]
    · refine tsum_congr (fun m ↦ ?_)
      have hm : ((m + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
      simp only [I, Nat.cast_add, Nat.cast_one] at hm ⊢
      rw [setIntegral_congr_fun (hS _) (hnonunit hm),
        setIntegral_congr_fun (hS _) (hnonunit (neg_ne_zero.mpr hm))]
      simpa only [C, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
        (rationalLocalRadialHaar_shellPair v F (Nat.succ_pos m)).2.2
    · exact hplus.comp_injective Nat.succ_injective
    · exact hminus

private theorem reflected_sample (F : ℝ → ℂ) {n : ℝ} (hn : 0 < n) :
    let g := fun x : ℝ ↦ Complex.exp (-(x : ℂ) / 2) * F x
    g (Real.log n) + g (-Real.log n) / (n : ℂ) =
      (Real.exp (-Real.log n / 2) : ℝ) * (F (-Real.log n) + F (Real.log n)) := by
  dsimp only
  have hn₀ : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hlog : Complex.exp (Real.log n : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hn]
  have href : Complex.exp (-((-Real.log n : ℝ) : ℂ) / 2) =
      Complex.exp (-(Real.log n : ℂ) / 2) * (n : ℂ) := by
    rw [← hlog, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  rw [href, Complex.ofReal_exp]
  push_cast
  field_simp
  ring

/-- At each rational place, the full subtracted Haar value is the sum of
its prime-power samples from (B.4.2.10)–(11), p. 615, with the same half
twist as at the real place. The two samples have a plus sign, and the
reflected sample is divided by the prime power before undoing the twist.
There is no claim here about the additive Fourier definition of the
primed integral in (B.4.4.21). -/
public theorem rationalLocalRadialHaar_eq_primeSamples
    (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]
    {F : ℝ → ℂ} (hF : HasCompactSupport F) :
    let μ := rationalLocalMultiplicativeHaar v
    let g := fun x : ℝ ↦ Complex.exp (-(x : ℂ) / 2) * F x
    let l := Real.log (P[v] : ℝ)
    let C := fun m : ℕ ↦
      let n := (P[v] : ℝ) ^ (m + 1)
      (l : ℂ) * (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    Integrable (rationalLocalRadialSubtracted v F) μ ∧ (∃ M : ℕ, ∀ m ≥ M, C m = 0) ∧
      (l : ℂ) * (∫ x, rationalLocalRadialSubtracted v F x ∂μ) = ∑' m : ℕ, C m := by
  intro μ g l C
  have hC (m : ℕ) : C m =
      (l : ℂ) * (Real.exp (-(((m + 1 : ℕ) : ℝ) * l) / 2) : ℝ) *
        (F (-(((m + 1 : ℕ) : ℝ) * l)) + F (((m + 1 : ℕ) : ℝ) * l)) := by
    dsimp only [C]
    rw [reflected_sample F (pow_pos (RationalLocalNormShell.prime_pos v) _),
      Real.log_pow, mul_assoc]
  obtain ⟨hi, ⟨M, hM⟩, heq⟩ := rationalLocalRadialHaar_eq_shellSum v hF
  exact ⟨hi, ⟨M, fun m hm ↦ (hC m).trans (hM m hm)⟩, heq.trans (tsum_congr fun m ↦ (hC m).symm)⟩

end Masullo
