module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite gray-band Weil charge of a reflected pair

Source: `1d56883c42befcdc4375f63d983f30dc76e2aba3:.godel/bob/weil-phase-bands.md`,
lines 11–45; the consumer deducts this price once at lines 47–53.

Scope: the exact phase from the two finite halves of the test with its complex
multiplier, and the signed charge of one same-ordinate reflected pair. The
amplitude comparison is a premise; no asymptotic amplitude estimate, completed
Poisson budget, or twist estimate is asserted here.

Scope baseline: `b3723e8a43baefe5b5795e39005ed92872c52b99`.
Owning check session: `01a20b48-5cad-74c3-865b-b625005166b3`.
-/

open scoped ComplexConjugate

namespace WeilGrayPair

/-- The exact inverse amplitude `P` for depth `c` and weighted transform `Z`. -/
@[expose] public noncomputable def phaseAmplitude (c : ℝ) (Z : ℂ) : ℂ :=
  ((Real.exp (c / 2) : ℂ) * Z - (Real.exp (-c / 2) : ℂ) * conj Z) /
    ((Real.exp c - Real.exp (-c) : ℝ) : ℂ)

private theorem exp_half_sq (c : ℝ) : Real.exp (c / 2) ^ 2 = Real.exp c := by
  rw [pow_two, ← Real.exp_add, add_halves]

/-- Inverting the phase amplitude recovers the unapproximated weighted transform. -/
public theorem eq_exp_phaseAmplitude_add_conj {c : ℝ} (hc : 0 < c) (Z : ℂ) :
    Z = (Real.exp (c / 2) : ℂ) * phaseAmplitude c Z +
      (Real.exp (-c / 2) : ℂ) * conj (phaseAmplitude c Z) := by
  have hden : ((Real.exp c - Real.exp (-c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith : -c < c))))
  simp only [phaseAmplitude, map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply (eq_div_iff hden).mpr
  calc
    _ = Z * ((Real.exp (c / 2) : ℂ) ^ 2 - (Real.exp (-c / 2) : ℂ) ^ 2) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, exp_half_sq,
        exp_half_sq]
    _ = _ := by ring

/-- A zero amplitude contributes zero, independently of any phase convention at zero. -/
public theorem phaseAmplitude_eq_zero_iff {c : ℝ} (hc : 0 < c) (Z : ℂ) :
    phaseAmplitude c Z = 0 ↔ Z = 0 := by
  constructor
  · intro hP
    simpa [hP] using eq_exp_phaseAmplitude_add_conj hc Z
  · rintro rfl
    simp [phaseAmplitude]

private theorem re_sq_mix (u v : ℝ) (P : ℂ) :
    (((u : ℂ) * P + (v : ℂ) * conj P) ^ 2).re =
      (u ^ 2 + v ^ 2) * (P ^ 2).re + 2 * (u * v) * ‖P‖ ^ 2 := by
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero,
    Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  ring

private theorem re_sq_arg (P : ℂ) : (P ^ 2).re = ‖P‖ ^ 2 * Real.cos (2 * Complex.arg P) := by
  rw [pow_two, Complex.mul_re, ← Complex.norm_mul_cos_arg P,
    ← Complex.norm_mul_sin_arg P, Real.cos_two_mul]
  linear_combination (- (‖P‖ ^ 2)) * Real.cos_sq_add_sin_sq (Complex.arg P)

/-- The exact real-part identity (1), with `θ = 2 arg P`. It also holds at `P = 0`. -/
public theorem re_sq_eq_phase {c : ℝ} (hc : 0 < c) (Z : ℂ) :
    (Z ^ 2).re = 2 * ‖phaseAmplitude c Z‖ ^ 2 *
      (1 + Real.cosh c * Real.cos (2 * Complex.arg (phaseAmplitude c Z))) := by
  have huv : Real.exp (c / 2) * Real.exp (-c / 2) = 1 := by
    rw [← Real.exp_add, show c / 2 + -c / 2 = 0 by ring, Real.exp_zero]
  conv_lhs => rw [eq_exp_phaseAmplitude_add_conj hc Z]
  rw [re_sq_mix, exp_half_sq, exp_half_sq, huv, re_sq_arg, Real.cosh_eq]
  ring

/-- The shifted zero `s = β + ix`. -/
@[expose] public def shiftedZero (β x : ℝ) : ℂ := ⟨β, x⟩

/-- The argument of the multiplier, `z = x - i(β - 1/2)`. -/
@[expose] public noncomputable def shiftedArgument (β x : ℝ) : ℂ := ⟨x, -(β - 1 / 2)⟩

/-- The finite inward endpoint integral, with its value at zero. -/
@[expose] public noncomputable def endpointIntegral (L : ℝ) (v : ℂ) : ℂ :=
  if v = 0 then (L : ℂ) else (1 - Complex.exp (-(L : ℂ) * v)) / v

/-- The two finite halves of `B(z)`, at `L = D/2` and `c = (β - 1/2)D`. -/
@[expose] public noncomputable def testTransform (D β x : ℝ) : ℂ :=
  let L := D / 2
  let c := (β - 1 / 2) * D
  let w := (x : ℂ) * (L : ℂ) * Complex.I
  (Real.exp (c / 2) : ℂ) * Complex.exp w * endpointIntegral L (shiftedZero β x) +
    (Real.exp (-c / 2) : ℂ) * Complex.exp (-w) * endpointIntegral L (1 - shiftedZero β x)

/-- The analytic square root `r` of the complex multiplier `gε`. -/
@[expose] public noncomputable def multiplierRoot (ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((1 - Complex.cosh ((ε : ℂ) * z)) / 2)

/-- `Z = r(z) B(z)`. The multiplier is not replaced by its modulus. -/
@[expose] public noncomputable def weightedTest (ε D β x : ℝ) : ℂ :=
  multiplierRoot ε (shiftedArgument β x) * testTransform D β x

/-- Squaring `Z` recovers the original complex quantity `gε(z) B(z)^2`. -/
public theorem weightedTest_sq (ε D β x : ℝ) :
    weightedTest ε D β x ^ 2 =
      Complex.exp (1 - Complex.cosh ((ε : ℂ) * shiftedArgument β x)) * testTransform D β x ^ 2 := by
  rw [weightedTest, mul_pow, multiplierRoot, pow_two, ← Complex.exp_add, add_halves]

private theorem endpointIntegral_conj (L : ℝ) (v : ℂ) :
    conj (endpointIntegral L v) = endpointIntegral L (conj v) := by
  by_cases hv : v = 0
  · simp [endpointIntegral, hv]
  · have hcv : conj v ≠ 0 := by simpa using hv
    simp [endpointIntegral, hv, hcv, ← Complex.exp_conj]

private theorem shiftedZero_reflect (β x : ℝ) :
    shiftedZero (1 - β) x = conj (1 - shiftedZero β x) := by
  apply Complex.ext <;> simp [shiftedZero]

private theorem one_sub_shiftedZero_reflect (β x : ℝ) :
    1 - shiftedZero (1 - β) x = conj (shiftedZero β x) := by
  rw [shiftedZero_reflect, map_sub, map_one, sub_sub_cancel]

private theorem shiftedArgument_reflect (β x : ℝ) :
    shiftedArgument (1 - β) x = conj (shiftedArgument β x) := by
  apply Complex.ext
  · rfl
  · simp only [shiftedArgument, Complex.conj_im]
    ring

private theorem testTransform_reflect (D β x : ℝ) :
    testTransform D (1 - β) x = conj (testTransform D β x) := by
  have hc : (1 - β - 1 / 2) * D = -((β - 1 / 2) * D) := by ring
  unfold testTransform
  dsimp only
  rw [hc, neg_neg, one_sub_shiftedZero_reflect, shiftedZero_reflect]
  simp only [map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, map_neg,
    mul_neg, endpointIntegral_conj, neg_neg]
  exact add_comm _ _

/-- Reflection across the line conjugates `Z`, keeping the same offset `x`. -/
public theorem weightedTest_reflect (ε D β x : ℝ) :
    weightedTest ε D (1 - β) x = conj (weightedTest ε D β x) := by
  simp [weightedTest, shiftedArgument_reflect, testTransform_reflect, multiplierRoot,
    ← Complex.exp_conj, ← Complex.cosh_conj, Complex.conj_ofNat]

/-- The original two summands, with `2R` in each denominator, count as one
right-member charge with denominator `R`. -/
public theorem reflected_charge_eq (ε D β x R : ℝ) :
    -(weightedTest ε D β x ^ 2).re / (2 * R) +
        -(weightedTest ε D (1 - β) x ^ 2).re / (2 * R) =
      -(weightedTest ε D β x ^ 2).re / R := by
  rw [weightedTest_reflect, ← map_pow, Complex.conj_re, ← add_div, ← two_mul,
    mul_div_mul_left _ _ two_ne_zero]

/-- Gray includes band equality; the zero branch does not use `arg`. -/
@[expose] public def IsGray (K c : ℝ) (P : ℂ) : Prop :=
  P = 0 ∨ |Real.cosh c * Real.cos (2 * Complex.arg P)| ≤ K

/-- The real Poisson kernel `k(d)` at offset `x`. -/
@[expose] public noncomputable def kernel (d x : ℝ) : ℝ := d / (d ^ 2 + x ^ 2)

/-- The two kernels at `σ = 1 + 1/D`, with one at each member of the pair. -/
@[expose] public noncomputable def pairKernel (D β x : ℝ) : ℝ :=
  kernel (1 - β + 1 / D) x + kernel (β + 1 / D) x

/-- The exact finite replacement for the kernel comparison in (43). -/
public theorem reciprocal_le_pairKernel {D β : ℝ} (hD : 0 < D) (hβ₀ : 1 / 2 < β)
    (hβ₁ : β < 1) (x : ℝ) :
    1 / (β ^ 2 + x ^ 2) ≤ (1 + 2 / D) * pairKernel D β x := by
  let h := 1 / D
  let d₁ := 1 - β + h
  let d₂ := β + h
  let f := 1 + 2 * h
  have hh : 0 < h := one_div_pos.mpr hD
  have hβ : 0 < β := by linarith
  have hd₁ : 0 < d₁ := by dsimp [d₁]; linarith
  have hd₂ : 0 < d₂ := by dsimp [d₂]; positivity
  have hf : 1 ≤ f := by dsimp [f]; linarith
  have hf₀ : 0 ≤ f := zero_le_one.trans hf
  have hd₁₂ : d₁ ≤ d₂ := by dsimp [d₁, d₂]; linarith
  have hden : d₁ ^ 2 + x ^ 2 ≤ d₂ ^ 2 + x ^ 2 :=
    add_le_add (pow_le_pow_left₀ hd₁.le hd₁₂ 2) le_rfl
  have hpair : f / (d₂ ^ 2 + x ^ 2) ≤ pairKernel D β x := by
    change f / (d₂ ^ 2 + x ^ 2) ≤ d₁ / (d₁ ^ 2 + x ^ 2) + d₂ / (d₂ ^ 2 + x ^ 2)
    rw [show f = d₁ + d₂ by dsimp [f, d₁, d₂]; ring, add_div]
    exact add_le_add (div_le_div_of_nonneg_left hd₁.le (by positivity) hden) le_rfl
  have hd₂f : d₂ ≤ β * f := by
    dsimp [d₂, f]
    nlinarith only [mul_nonneg (show 0 ≤ 2 * β - 1 by linarith) hh.le]
  have hden' : d₂ ^ 2 + x ^ 2 ≤ f ^ 2 * (β ^ 2 + x ^ 2) := by
    have hd := pow_le_pow_left₀ hd₂.le hd₂f 2
    have hx := le_mul_of_one_le_left (sq_nonneg x)
      (show 1 ≤ f ^ 2 by simpa using pow_le_pow_left₀ zero_le_one hf 2)
    rw [mul_pow] at hd
    nlinarith only [hd, hx]
  rw [show (1 + 2 / D) = f by dsimp [f, h]; ring]
  calc
    _ ≤ f * (f / (d₂ ^ 2 + x ^ 2)) := by
      rw [← mul_div_assoc, ← pow_two]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden')
    _ ≤ _ := mul_le_mul_of_nonneg_left hpair hf₀

private theorem neg_re_sq_le_of_gray {K c : ℝ} (hc : 0 < c) (Z : ℂ)
    (hgray : IsGray K c (phaseAmplitude c Z)) :
    -(Z ^ 2).re ≤ 2 * (K - 1) * ‖phaseAmplitude c Z‖ ^ 2 := by
  rcases hgray with hP | hphase
  · have hZ := (phaseAmplitude_eq_zero_iff hc Z).mp hP
    rw [hP, hZ]
    simp
  · rw [re_sq_eq_phase hc Z]
    have hcos := (abs_le.mp hphase).1
    have ht := mul_le_mul_of_nonneg_left hcos
      (show 0 ≤ 2 * ‖phaseAmplitude c Z‖ ^ 2 by positivity)
    nlinarith only [ht]

/-- The conditional finite signed price of a single gray pair. The hypothesis
`hamp` is about the exact amplitude, not the charge or a limiting amplitude.
The kernel sum corresponds to both zeros, and the charge is counted once. -/
public theorem grayWeilPairCharge_le {D R β K A : ℝ} (hD : 0 < D) (hR : 0 < R)
    (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) (hK : 1 ≤ K) (hA : 0 ≤ A) (ε x : ℝ)
    (hgray : IsGray K ((β - 1 / 2) * D)
      (phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)))
    (hamp : ‖phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)‖ ^ 2 ≤
      A / ‖shiftedZero β x‖ ^ 2) :
    -(weightedTest ε D β x ^ 2).re / R ≤
      2 * (K - 1) * A * (1 + 2 / D) / R * pairKernel D β x := by
  let c := (β - 1 / 2) * D
  let Z := weightedTest ε D β x
  have hc : 0 < c := mul_pos (sub_pos.mpr hβ₀) hD
  have hs : ‖shiftedZero β x‖ ^ 2 = β ^ 2 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change β * β + x * x = β ^ 2 + x ^ 2
    ring
  have hcoeff : 0 ≤ 2 * (K - 1) := mul_nonneg (by norm_num) (sub_nonneg.mpr hK)
  have hcomp := reciprocal_le_pairKernel hD hβ₀ hβ₁ x
  rw [hs] at hamp
  change -(Z ^ 2).re / R ≤ _
  apply div_le_iff₀ hR |>.mpr
  calc
    -(Z ^ 2).re ≤ 2 * (K - 1) * ‖phaseAmplitude c Z‖ ^ 2 := neg_re_sq_le_of_gray hc Z hgray
    _ ≤ 2 * (K - 1) * (A / (β ^ 2 + x ^ 2)) := mul_le_mul_of_nonneg_left hamp hcoeff
    _ = (2 * (K - 1) * A) * (1 / (β ^ 2 + x ^ 2)) := by ring
    _ ≤ (2 * (K - 1) * A) * ((1 + 2 / D) * pairKernel D β x) :=
      mul_le_mul_of_nonneg_left hcomp (mul_nonneg hcoeff hA)
    _ = _ := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hR.ne']
      ring

end WeilGrayPair
