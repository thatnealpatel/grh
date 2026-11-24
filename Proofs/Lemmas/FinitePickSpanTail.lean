module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Weighted tails on a finite exponential span

Source: `22912fa2:.godel/adhoc/pick-block-weil-window.md`, §2, lines 51–60.
Consumers: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §4, and
`85842a8f:.godel/alice/prime-conductor-window.md`, lines 64–70.
Owning check session: `01a20e58-ec66-7c2b-94b4-741e4461cd8a`.

Scope: the squared `L²` weight and tail bounds for the entire complex span of
half-line exponentials at distinct positive real nodes. The two real Gram
forms for the real and imaginary parts retain all cross terms. A finite
all-pass step moves one node at a time to the negative half-line; no prime
estimates enter the proof.
-/

open MeasureTheory Set
open Real (exp)

namespace Masullo

private noncomputable def realSpan (S : Finset ℝ) (r c : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ S, c i * exp (-r i * x)

private noncomputable def gram (S : Finset ℝ) (r c : ℝ → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, c i * c j / (r i + r j)

private theorem realSpan_sq_expand (S : Finset ℝ) (r c : ℝ → ℝ) (x : ℝ) :
    realSpan S r c x ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, (c i * c j) * exp (-(r i + r j) * x) := by
  rw [realSpan, pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  calc
    _ = (c i * c j) * (exp (-r i * x) * exp (-r j * x)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show -r i * x + -r j * x = -(r i + r j) * x by ring]

private theorem integrableOn_gramTerm {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℝ) {i j : ℝ} (hi : i ∈ S) (hj : j ∈ S) :
    IntegrableOn (fun x ↦ (c i * c j) * exp (-(r i + r j) * x)) (Ici (0 : ℝ)) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 <|
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (add_pos (hr i hi) (hr j hj))) 0).const_mul _

private theorem integrableOn_realSpan_sq {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℝ) :
    IntegrableOn (fun x ↦ realSpan S r c x ^ 2) (Ici (0 : ℝ)) := by
  simp_rw [realSpan_sq_expand]
  exact integrable_finsetSum S fun i hi ↦
    integrable_finsetSum S fun j hj ↦ integrableOn_gramTerm hr c hi hj

private theorem integral_realSpan_sq {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℝ) :
    (∫ x in Ici (0 : ℝ), realSpan S r c x ^ 2) = gram S r c := by
  simp_rw [realSpan_sq_expand]
  rw [integral_finsetSum S (fun i hi ↦
    integrable_finsetSum S fun j hj ↦ integrableOn_gramTerm hr c hi hj)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum S (fun j hj ↦ integrableOn_gramTerm hr c hi hj)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos (add_pos (hr i hi) (hr j hj))) 0]
  rw [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg]
  ring

private theorem gram_nonneg {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℝ) : 0 ≤ gram S r c := by
  rw [← integral_realSpan_sq hr]
  exact integral_nonneg fun _ ↦ sq_nonneg _

private theorem realSpan_sub (S : Finset ℝ) (r c : ℝ → ℝ) (η x : ℝ) :
    realSpan S (fun i ↦ r i - η) c x = exp (η * x) * realSpan S r c x := by
  simp only [realSpan, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show -(r i - η) * x = η * x + -r i * x by ring, Real.exp_add]
  ring

private theorem gram_congr (S : Finset ℝ) (r : ℝ → ℝ) {c d : ℝ → ℝ}
    (h : ∀ i ∈ S, c i = d i) : gram S r c = gram S r d := by
  exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by
    rw [h i hi, h j hj]

private theorem gram_insert_zero {S : Finset ℝ} {m : ℝ} (hm : m ∉ S) (r : ℝ → ℝ)
    {c : ℝ → ℝ} (hc : c m = 0) : gram (insert m S) r c = gram S r c := by
  classical
  simp only [gram, Finset.sum_insert hm, hc, zero_mul, mul_zero, zero_div,
    Finset.sum_const_zero, zero_add]

/-- Expansion of the shifted derivative energy on one half-line. Its mixed
term divides out the Cauchy denominator and is a square of the boundary value. -/
private theorem gram_scale_add {S : Finset ℝ} {r : ℝ → ℝ} (hr : ∀ i ∈ S, 0 < r i)
    (a : ℝ → ℝ) (k s : ℝ) :
    gram S r (fun i ↦ (k * r i + s) * a i) =
      k ^ 2 * gram S r (fun i ↦ r i * a i) + s ^ 2 * gram S r a +
        k * s * (∑ i ∈ S, a i) ^ 2 := by
  rw [pow_two (∑ i ∈ S, a i), Finset.sum_mul_sum]
  simp only [gram, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  field_simp [ne_of_gt (add_pos (hr i hi) (hr j hj))]
  ring

private theorem gram_add_le {T : Finset ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hT : ∀ i ∈ T, 0 < i) (d : ℝ → ℝ) :
    gram T (fun i ↦ i + η) d ≤ gram T id d := by
  have hT' : ∀ i ∈ T, 0 < i + η := fun i hi ↦ add_pos_of_pos_of_nonneg (hT i hi) hη
  rw [← integral_realSpan_sq hT', ← integral_realSpan_sq (r := id) hT]
  refine setIntegral_mono_on (integrableOn_realSpan_sq hT' d)
    (integrableOn_realSpan_sq hT d) measurableSet_Ici fun x hx ↦ ?_
  rw [show (fun i : ℝ ↦ i + η) = (fun i ↦ id i - (-η)) by simp [sub_neg_eq_add],
    realSpan_sub, mul_pow]
  have he : exp (-η * x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη) hx)
  have he' : exp (-η * x) ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (Real.exp_pos _).le zero_le_one).2 he
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he' (sq_nonneg (realSpan T id d x))

/-- Sum of the squared energies of the two half-lines. On the negative one
we use the coordinate `x ↦ -x`, so the rate there is shifted by `+δ`. -/
private noncomputable def mixedGram (S T : Finset ℝ) (δ : ℝ) (a b : ℝ → ℝ) : ℝ :=
  gram S (fun i ↦ i - δ) a + gram T (fun i ↦ i + δ) b

private theorem mixedGram_nonneg {S T : Finset ℝ} {δ : ℝ}
    (hs : ∀ i ∈ S, 0 < i - δ) (ht : ∀ i ∈ T, 0 < i + δ) (a b : ℝ → ℝ) :
    0 ≤ mixedGram S T δ a b := add_nonneg (gram_nonneg hs a) (gram_nonneg ht b)

/-- With matching boundary values, the mixed terms on the two half-lines
cancel. The two all-pass outputs correspond to `s = m` and `s = -m`. -/
private theorem mixedGram_shift {S T : Finset ℝ} {δ : ℝ}
    (hs : ∀ i ∈ S, 0 < i - δ) (ht : ∀ i ∈ T, 0 < i + δ)
    {a b : ℝ → ℝ} (hab : (∑ i ∈ S, a i) = ∑ i ∈ T, b i) (s : ℝ) :
    mixedGram S T δ (fun i ↦ (i + s) * a i) (fun i ↦ (s - i) * b i) =
      mixedGram S T δ (fun i ↦ (i - δ) * a i) (fun i ↦ (i + δ) * b i) +
        (s + δ) ^ 2 * mixedGram S T δ a b := by
  have hpos : (fun i : ℝ ↦ (i + s) * a i) =
      (fun i ↦ (1 * (i - δ) + (s + δ)) * a i) := by ext i; ring
  have hneg : (fun i : ℝ ↦ (s - i) * b i) =
      (fun i ↦ ((-1) * (i + δ) + (s + δ)) * b i) := by ext i; ring
  unfold mixedGram
  rw [hpos, hneg, gram_scale_add hs, gram_scale_add ht, hab]
  ring

private theorem mixedGram_allPass {S T : Finset ℝ} {η m : ℝ} (hη : 0 ≤ η) (hm : η < m)
    (hs : ∀ i ∈ S, η < i) (ht : ∀ i ∈ T, η < i)
    {a b : ℝ → ℝ} (hab : (∑ i ∈ S, a i) = ∑ i ∈ T, b i) :
    (mixedGram S T η (fun i ↦ (i + m) * a i) (fun i ↦ (m - i) * b i) ≤
      ((m + η) / (m - η)) ^ 2 *
        mixedGram S T η (fun i ↦ (i + -m) * a i) (fun i ↦ (-m - i) * b i)) ∧
    (mixedGram S T 0 (fun i ↦ (i + m) * a i) (fun i ↦ (m - i) * b i) =
      mixedGram S T 0 (fun i ↦ (i + -m) * a i) (fun i ↦ (-m - i) * b i)) := by
  have hs' : ∀ i ∈ S, 0 < i - η := fun i hi ↦ sub_pos.mpr (hs i hi)
  have ht' : ∀ i ∈ T, 0 < i + η := fun i hi ↦
    add_pos_of_pos_of_nonneg (hη.trans_lt (ht i hi)) hη
  have hm' : 0 < m - η := sub_pos.mpr hm
  have hfac : 1 ≤ (m + η) / (m - η) := (le_div_iff₀ hm').2 (by linarith)
  have hfac' : 1 ≤ ((m + η) / (m - η)) ^ 2 := by
    simpa only [one_pow] using (sq_le_sq₀ zero_le_one (zero_le_one.trans hfac)).2 hfac
  constructor
  · rw [mixedGram_shift hs' ht' hab, mixedGram_shift hs' ht' hab]
    let A := mixedGram S T η (fun i ↦ (i - η) * a i) (fun i ↦ (i + η) * b i)
    let B := mixedGram S T η a b
    change A + (m + η) ^ 2 * B ≤ ((m + η) / (m - η)) ^ 2 * (A + (-m + η) ^ 2 * B)
    have hA : 0 ≤ A := mixedGram_nonneg hs' ht' _ _
    calc
      _ ≤ ((m + η) / (m - η)) ^ 2 * A + (m + η) ^ 2 * B := by
        have h := mul_le_mul_of_nonneg_right hfac' hA
        exact add_le_add (by simpa only [one_mul] using h) le_rfl
      _ = _ := by field_simp [ne_of_gt hm']; ring
  · have hs₀ : ∀ i ∈ S, 0 < i - 0 := fun i hi ↦ by simpa using hη.trans_lt (hs i hi)
    have ht₀ : ∀ i ∈ T, 0 < i + 0 := fun i hi ↦ by simpa using hη.trans_lt (ht i hi)
    rw [mixedGram_shift hs₀ ht₀ hab, mixedGram_shift hs₀ ht₀ hab]
    simp

/-- Move the right-hand nodes one at a time to the left. Each all-pass step
costs one factor at `η` and preserves the energy at `0`. -/
private theorem mixedGram_weight {η : ℝ} (hη : 0 ≤ η) (S T : Finset ℝ) (c d : ℝ → ℝ)
    (hd : Disjoint S T) (hs : ∀ i ∈ S, η < i) (ht : ∀ i ∈ T, η < i) :
    mixedGram S T η c d ≤ (∏ i ∈ S, (i + η) / (i - η)) ^ 2 * mixedGram S T 0 c d := by
  classical
  induction S using Finset.induction_on generalizing T c d with
  | empty =>
    simpa only [mixedGram, gram, Finset.sum_empty, Finset.prod_empty, one_pow, one_mul,
      zero_add, add_zero, id_eq] using gram_add_le hη (fun i hi ↦ hη.trans_lt (ht i hi)) d
  | @insert m S hmS ih =>
    obtain ⟨hmT, hdST⟩ := Finset.disjoint_insert_left.1 hd
    have hm : η < m := hs m (Finset.mem_insert_self _ _)
    have hs' : ∀ i ∈ S, η < i := fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)
    have ht' : ∀ i ∈ insert m T, η < i := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hm
      · exact ht i hi
    have hne (i : ℝ) (hi : i ∈ T) : i ≠ m := by
      rintro rfl
      exact hmT hi
    -- The input multiplier is nonzero on the right and on the old left nodes.
    -- The free coefficient at the new left node matches the boundary values.
    let a (i : ℝ) := c i / (i + m)
    let b (i : ℝ) := if i = m then (∑ j ∈ insert m S, a j) - ∑ j ∈ T, d j / (m - j)
      else d i / (m - i)
    have hab : (∑ i ∈ insert m S, a i) = ∑ i ∈ insert m T, b i := by
      have hb : (∑ i ∈ T, b i) = ∑ i ∈ T, d i / (m - i) :=
        Finset.sum_congr rfl fun i hi ↦ by simp [b, hne i hi]
      rw [Finset.sum_insert hmT, hb]
      simp [b]
    let c₀ (i : ℝ) := (i + m) * a i
    let d₀ (i : ℝ) := (m - i) * b i
    let c₁ (i : ℝ) := (i + -m) * a i
    let d₁ (i : ℝ) := (-m - i) * b i
    have hc₀ (i : ℝ) (hi : i ∈ insert m S) : c i = c₀ i :=
      (mul_div_cancel₀ _ (ne_of_gt (add_pos (hη.trans_lt (hs i hi)) (hη.trans_lt hm)))).symm
    have hd₀ (i : ℝ) (hi : i ∈ T) : d i = d₀ i := by
      simp [d₀, b, hne i hi, mul_div_cancel₀ _ (sub_ne_zero.mpr (hne i hi).symm)]
    have hstart (δ : ℝ) :
        mixedGram (insert m S) T δ c d = mixedGram (insert m S) (insert m T) δ c₀ d₀ := by
      unfold mixedGram
      rw [gram_insert_zero hmT _ (show d₀ m = 0 by simp [d₀]),
        gram_congr (insert m S) _ hc₀, gram_congr T _ hd₀]
    have hfinish (δ : ℝ) :
        mixedGram (insert m S) (insert m T) δ c₁ d₁ = mixedGram S (insert m T) δ c₁ d₁ := by
      unfold mixedGram
      rw [gram_insert_zero hmS _ (show c₁ m = 0 by simp [c₁])]
    obtain ⟨hstep, hzero⟩ := mixedGram_allPass hη hm hs ht' hab
    change mixedGram (insert m S) (insert m T) η c₀ d₀ ≤
      ((m + η) / (m - η)) ^ 2 * mixedGram (insert m S) (insert m T) η c₁ d₁ at hstep
    change mixedGram (insert m S) (insert m T) 0 c₀ d₀ =
      mixedGram (insert m S) (insert m T) 0 c₁ d₁ at hzero
    rw [← hstart η, hfinish η] at hstep
    rw [← hstart 0, hfinish 0] at hzero
    have hind := ih (insert m T) c₁ d₁ (Finset.disjoint_insert_right.2 ⟨hmS, hdST⟩) hs' ht'
    calc
      _ ≤ ((m + η) / (m - η)) ^ 2 * mixedGram S (insert m T) η c₁ d₁ := hstep
      _ ≤ ((m + η) / (m - η)) ^ 2 *
          ((∏ i ∈ S, (i + η) / (i - η)) ^ 2 * mixedGram S (insert m T) 0 c₁ d₁) :=
        mul_le_mul_of_nonneg_left hind (sq_nonneg _)
      _ = _ := by rw [← hzero, Finset.prod_insert hmS, mul_pow, mul_assoc]

private theorem gram_weight {η : ℝ} (hη : 0 ≤ η) {S : Finset ℝ} (hs : ∀ i ∈ S, η < i)
    (c : ℝ → ℝ) :
    gram S (fun i ↦ i - η) c ≤ (∏ i ∈ S, (i + η) / (i - η)) ^ 2 * gram S id c := by
  simpa only [mixedGram, gram, Finset.sum_empty, add_zero, sub_zero, id_eq] using
    mixedGram_weight hη S ∅ c 0 (Finset.disjoint_empty_right S) hs (by simp)

private noncomputable def complexSpan (S : Finset ℝ) (r : ℝ → ℝ) (c : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ S, c i * (exp (-r i * x) : ℂ)

private theorem complexSpan_sq (S : Finset ℝ) (r : ℝ → ℝ) (c : ℝ → ℂ) (x : ℝ) :
    ‖complexSpan S r c x‖ ^ 2 =
      realSpan S r (fun i ↦ (c i).re) x ^ 2 + realSpan S r (fun i ↦ (c i).im) x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [complexSpan, realSpan, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add, pow_two]

private theorem complexSpan_sub (S : Finset ℝ) (r : ℝ → ℝ) (c : ℝ → ℂ) (η x : ℝ) :
    complexSpan S (fun i ↦ r i - η) c x = (exp (η * x) : ℂ) * complexSpan S r c x := by
  simp only [complexSpan, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show -(r i - η) * x = η * x + -r i * x by ring, Real.exp_add, Complex.ofReal_mul]
  ring

private theorem integrableOn_complexSpan_sq {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℂ) :
    IntegrableOn (fun x ↦ ‖complexSpan S r c x‖ ^ 2) (Ici (0 : ℝ)) := by
  simp_rw [complexSpan_sq]
  exact (integrableOn_realSpan_sq hr _).add (integrableOn_realSpan_sq hr _)

private theorem integral_complexSpan_sq {S : Finset ℝ} {r : ℝ → ℝ}
    (hr : ∀ i ∈ S, 0 < r i) (c : ℝ → ℂ) :
    (∫ x in Ici (0 : ℝ), ‖complexSpan S r c x‖ ^ 2) =
      gram S r (fun i ↦ (c i).re) + gram S r (fun i ↦ (c i).im) := by
  simp_rw [complexSpan_sq]
  rw [integral_add (integrableOn_realSpan_sq hr _) (integrableOn_realSpan_sq hr _),
    integral_realSpan_sq hr, integral_realSpan_sq hr]

/-- The finite exponential sum, extended by zero to the negative half-line. -/
@[expose] public noncomputable def finitePickSpan (S : Finset ℝ) (c : ℝ → ℂ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (fun x ↦ ∑ i ∈ S, c i * (exp (-i * x) : ℂ))

private theorem weight_sq_eq_indicator (S : Finset ℝ) (c : ℝ → ℂ) (η : ℝ) :
    (fun x ↦ ‖(exp (η * x) : ℂ) * finitePickSpan S c x‖ ^ 2) =
      (Ici (0 : ℝ)).indicator (fun x ↦ ‖complexSpan S (fun i ↦ i - η) c x‖ ^ 2) := by
  funext x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx, complexSpan_sub S (fun i ↦ i)]
    simp [finitePickSpan, complexSpan, hx]
  · simp [finitePickSpan, hx]

private theorem norm_sq_eq_indicator (S : Finset ℝ) (c : ℝ → ℂ) :
    (fun x ↦ ‖finitePickSpan S c x‖ ^ 2) =
      (Ici (0 : ℝ)).indicator (fun x ↦ ‖complexSpan S id c x‖ ^ 2) := by
  change _ = (Ici (0 : ℝ)).indicator (fun x ↦ ‖complexSpan S (fun i ↦ i) c x‖ ^ 2)
  simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul, sub_zero] using
    weight_sq_eq_indicator S c 0

/-- The exponentially weighted squared norm is integrable when the weight
exponent is strictly below every node. The unweighted case uses `η = 0`. -/
public theorem integrable_finitePickSpan_weight_sq (S : Finset ℝ) (c : ℝ → ℂ) {η : ℝ}
    (hS : ∀ m ∈ S, η < m) :
    Integrable (fun x ↦ ‖(exp (η * x) : ℂ) * finitePickSpan S c x‖ ^ 2) := by
  rw [weight_sq_eq_indicator]
  exact (integrableOn_complexSpan_sq (fun m hm ↦ sub_pos.mpr (hS m hm)) c).integrable_indicator
    measurableSet_Ici

private theorem cut_norm_sq (s : Set ℝ) (h : ℝ → ℂ) :
    (fun x ↦ ‖s.indicator h x‖ ^ 2) = s.indicator (fun x ↦ ‖h x‖ ^ 2) := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The squared norm of the zero-extended positive-node span is integrable. -/
public theorem integrable_finitePickSpan_sq (S : Finset ℝ) (c : ℝ → ℂ)
    (hS : ∀ m ∈ S, 0 < m) : Integrable (fun x ↦ ‖finitePickSpan S c x‖ ^ 2) := by
  simpa using integrable_finitePickSpan_weight_sq S c (η := 0) hS

/-- Every cut of the positive-node span has integrable squared norm. -/
public theorem integrable_finitePickSpan_tail_sq (S : Finset ℝ) (c : ℝ → ℂ) (t : ℝ)
    (hS : ∀ m ∈ S, 0 < m) :
    Integrable (fun x ↦ ‖(Ici t).indicator (finitePickSpan S c) x‖ ^ 2) := by
  rw [cut_norm_sq]
  exact (integrable_finitePickSpan_sq S c hS).indicator measurableSet_Ici

/-- The squared whole-span exponential-weight bound, with the product over
the distinct real nodes (including the empty product). -/
public theorem finitePickSpan_weight_sq_le (S : Finset ℝ) (c : ℝ → ℂ) {η : ℝ}
    (hη : 0 < η) (hS : ∀ m ∈ S, η < m) :
    (∫ x, ‖(exp (η * x) : ℂ) * finitePickSpan S c x‖ ^ 2) ≤
      (∏ m ∈ S, (m + η) / (m - η)) ^ 2 * (∫ x, ‖finitePickSpan S c x‖ ^ 2) := by
  rw [weight_sq_eq_indicator, norm_sq_eq_indicator,
    integral_indicator measurableSet_Ici, integral_indicator measurableSet_Ici,
    integral_complexSpan_sq (fun m hm ↦ sub_pos.mpr (hS m hm)),
    integral_complexSpan_sq (r := id) (fun m hm ↦ hη.trans (hS m hm)), mul_add]
  exact add_le_add (gram_weight hη.le hS _) (gram_weight hη.le hS _)

/-- The squared tail bound on `[t,∞)`, taking the better of monotonicity and
exponential weighting. -/
public theorem finitePickSpan_tail_sq_le (S : Finset ℝ) (c : ℝ → ℂ) {η t : ℝ}
    (hη : 0 < η) (hS : ∀ m ∈ S, η < m) (ht : 0 ≤ t) :
    (∫ x, ‖(Ici t).indicator (finitePickSpan S c) x‖ ^ 2) ≤
      (min 1 (exp (-η * t) * ∏ m ∈ S, (m + η) / (m - η))) ^ 2 *
        (∫ x, ‖finitePickSpan S c x‖ ^ 2) := by
  rw [cut_norm_sq, integral_indicator measurableSet_Ici]
  let f (x : ℝ) := ‖finitePickSpan S c x‖ ^ 2
  let g (x : ℝ) := ‖(exp (η * x) : ℂ) * finitePickSpan S c x‖ ^ 2
  let P := ∏ m ∈ S, (m + η) / (m - η)
  change (∫ x in Ici t, f x) ≤ (min 1 (exp (-η * t) * P)) ^ 2 * ∫ x, f x
  have hf : Integrable f := integrable_finitePickSpan_sq S c fun m hm ↦ hη.trans (hS m hm)
  have hg : Integrable g := integrable_finitePickSpan_weight_sq S c hS
  by_cases h : 1 ≤ exp (-η * t) * P
  · rw [min_eq_left h, one_pow, one_mul]
    calc
      _ ≤ ∫ x in Ici (0 : ℝ), f x :=
        integral_mono_measure (Measure.restrict_mono (Ici_subset_Ici.2 ht) le_rfl)
          (ae_of_all _ fun _ ↦ sq_nonneg _) hf.integrableOn
      _ ≤ _ := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun _ ↦ sq_nonneg _) hf
  · rw [min_eq_right (le_of_not_ge h)]
    have hcut : (∫ x in Ici t, f x) ≤ exp (-η * t) ^ 2 * (∫ x in Ici t, g x) := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hf.integrableOn (hg.integrableOn.const_mul _)
        measurableSet_Ici fun x hx ↦ ?_
      have he : 1 ≤ exp (-η * t) * exp (η * x) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hx)])
      have he₂ : 1 ≤ (exp (-η * t) * exp (η * x)) ^ 2 := by
        simpa only [one_pow] using (sq_le_sq₀ zero_le_one (zero_le_one.trans he)).2 he
      calc
        f x ≤ (exp (-η * t) * exp (η * x)) ^ 2 * f x := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right he₂ (sq_nonneg _)
        _ = exp (-η * t) ^ 2 * g x := by
          simp only [f, g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), mul_pow, mul_assoc]
    calc
      _ ≤ exp (-η * t) ^ 2 * (∫ x in Ici t, g x) := hcut
      _ ≤ exp (-η * t) ^ 2 * (∫ x, g x) :=
        mul_le_mul_of_nonneg_left
          (integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ ↦ sq_nonneg _) hg)
          (sq_nonneg _)
      _ ≤ exp (-η * t) ^ 2 * (P ^ 2 * (∫ x, f x)) :=
        mul_le_mul_of_nonneg_left (finitePickSpan_weight_sq_le S c hη hS) (sq_nonneg _)
      _ = _ := by rw [mul_pow, mul_assoc]

end Masullo
