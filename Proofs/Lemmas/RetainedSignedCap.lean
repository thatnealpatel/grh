module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed cap transfer for a retained prime shift

Source: `dcc11ec5bbd653cbb1068ea454799744de33fb73`,
`.godel/bob/retained-shell-overshoot.md:5–21`.
Consumer: `dcc11ec:.godel/bob/signed-gap-cube-screen.md`, “Use and cost”.
Owning check session: `01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.

On a finite frozen pool, an ordered collision estimate at radius `(log X)^2`
controls the whole near strip, including the diagonal. Deleting the sparse
integer gaps then gives a pointwise comparison with the *signed* dense sum, at
arbitrary real heights. A cosine chord bound then transfers a cap from the
untranslated cell nodes, with explicit error. Neither transfer is an arithmetic
upper bound on the node values or an estimate for smaller-excursion integrals.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo.RetainedSignedCap

/-- The admissible frozen pool for one positive shift. -/
public structure IsPrimePool (S : Finset ℕ) (X : ℝ) (d : ℕ) : Prop where
  one_lt : 1 < X
  shift_pos : 0 < d
  shift_le : (d : ℝ) ≤ 5 * Real.log X
  band : ∀ p ∈ S, p.Prime ∧ (p + d).Prime ∧
    (p : ℝ) ∈ Set.Icc (Real.exp (-8) * X) X ∧
    ((p + d : ℕ) : ℝ) ∈ Set.Icc (Real.exp (-8) * X) X

/-- The frozen logarithmic prime-pair weight. -/
@[expose] public noncomputable def weight (X : ℝ) (d p : ℕ) : ℝ :=
  X⁻¹ * Real.log (X / p) * Real.log p * Real.log ((p + d : ℕ) : ℝ)

/-- The exact, unrounded frequency of the edge from `p` to `p+d`. -/
@[expose] public noncomputable def frequency (d p : ℕ) : ℝ :=
  Real.log (1 + (d : ℝ) / p)

/-- The original frozen polynomial, with no twist or choice of height origin. -/
@[expose] public noncomputable def Z (S : Finset ℕ) (X : ℝ) (d : ℕ) (u : ℝ) : ℂ :=
  ∑ p ∈ S, (weight X d p : ℂ) * Complex.exp ((↑(u * frequency d p) : ℂ) * Complex.I)

/-- The near strip counts *ordered* pairs with the diagonal and boundary included. -/
@[expose] public noncomputable def nearPairs (S : Finset ℕ) (r : ℝ) : Finset (ℕ × ℕ) :=
  open Classical in
  (S ×ˢ S).filter fun pq ↦ |(pq.2 : ℝ) - pq.1| ≤ r

/-- The weighted ordered collision mass at radius `r`. -/
@[expose] public noncomputable def collisionMass (S : Finset ℕ) (w : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ pq ∈ nearPairs S r, w pq.1 * w pq.2

/-- The half of the far strip with the lower start first. -/
@[expose] public noncomputable def farPairs (S : Finset ℕ) (R : ℝ) : Finset (ℕ × ℕ) :=
  open Classical in
  (S ×ˢ S).filter fun pq ↦ R < (pq.2 : ℝ) - pq.1

/-- The positive integer gap of a lower-first far pair. -/
@[expose] public def gap (pq : ℕ × ℕ) : ℕ := pq.2 - pq.1

/-- The number of lower starts in one far integer gap. A lower start determines
its upper start uniquely in that gap. -/
@[expose] public noncomputable def gapCount (S : Finset ℕ) (R : ℝ) (g : ℕ) : ℕ :=
  ((farPairs S R).filter fun pq ↦ gap pq = g).card

/-- Retain exactly the far groups with strictly more than `M` lower starts. -/
@[expose] public noncomputable def densePairs (S : Finset ℕ) (R M : ℝ) : Finset (ℕ × ℕ) :=
  open Classical in
  (farPairs S R).filter fun pq ↦ M < (gapCount S R (gap pq) : ℝ)

/-- The signed dense real sum, with the factor of two for the opposite order. -/
@[expose] public noncomputable def Q (S : Finset ℕ) (X : ℝ) (d n : ℕ) (u : ℝ) : ℝ :=
  2 * ∑ pq ∈ densePairs S (n * (Real.log X)^2) (X / (n * (Real.log X)^4)),
    weight X d pq.1 * weight X d pq.2 * Real.cos (u * (frequency d pq.1 - frequency d pq.2))

private theorem mem_near {S : Finset ℕ} {r : ℝ} {pq : ℕ × ℕ} :
    pq ∈ nearPairs S r ↔ pq.1 ∈ S ∧ pq.2 ∈ S ∧ |(pq.2 : ℝ) - pq.1| ≤ r := by
  simp [nearPairs, and_assoc]

private theorem mem_far {S : Finset ℕ} {R : ℝ} {pq : ℕ × ℕ} :
    pq ∈ farPairs S R ↔ pq.1 ∈ S ∧ pq.2 ∈ S ∧ R < (pq.2 : ℝ) - pq.1 := by
  simp [farPairs, and_assoc]

private theorem cell_close {r : ℝ} (hr : 0 < r) {n p q : ℕ}
    (h : |(q : ℝ) - p| ≤ n * r) :
    |⌊(p : ℝ) / r⌋ - ⌊(q : ℝ) / r⌋| ≤ (n : ℤ) + 1 := by
  have hPQ := (abs_le.mp h).1
  have hQP := (abs_le.mp h).2
  have hdiv₁ : (p : ℝ) / r - (q : ℝ) / r ≤ n := by
    rw [← sub_div, div_le_iff₀ hr]
    linarith only [hPQ]
  have hdiv₂ : (q : ℝ) / r - (p : ℝ) / r ≤ n := by
    rwa [← sub_div, div_le_iff₀ hr]
  have h₁ := Int.floor_le ((p : ℝ) / r)
  have h₂ := Int.floor_le ((q : ℝ) / r)
  have h₃ := Int.lt_floor_add_one ((p : ℝ) / r)
  have h₄ := Int.lt_floor_add_one ((q : ℝ) / r)
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact_mod_cast (show -((n : ℝ) + 1) ≤ (⌊(p : ℝ) / r⌋ : ℝ) - ⌊(q : ℝ) / r⌋ by
      linarith only [hdiv₂, h₂, h₃])
  · exact_mod_cast (show (⌊(p : ℝ) / r⌋ : ℝ) - ⌊(q : ℝ) / r⌋ ≤ (n : ℝ) + 1 by
      linarith only [hdiv₁, h₁, h₄])

private theorem same_cell_close {r : ℝ} (hr : 0 < r) {p q : ℕ}
    (h : ⌊(p : ℝ) / r⌋ = ⌊(q : ℝ) / r⌋) : |(q : ℝ) - p| ≤ r := by
  have h₁ := Int.floor_le ((p : ℝ) / r)
  have h₂ := Int.floor_le ((q : ℝ) / r)
  have h₃ := Int.lt_floor_add_one ((p : ℝ) / r)
  have h₄ := Int.lt_floor_add_one ((q : ℝ) / r)
  rw [h] at h₁ h₃
  have ha : (q : ℝ) / r - (p : ℝ) / r ≤ 1 := by linarith only [h₁, h₄]
  have hb : (p : ℝ) / r - (q : ℝ) / r ≤ 1 := by linarith only [h₂, h₃]
  rw [← sub_div, div_le_iff₀ hr, one_mul] at ha hb
  exact abs_le.mpr ⟨by linarith only [hb], ha⟩

private theorem sum_by_cell (S : Finset ℕ) (c : ℕ → ℤ) (w : ℕ → ℝ) (v : ℤ → ℝ) :
    ∑ p ∈ S, w p * v (c p) =
      ∑ i ∈ S.image c, (∑ p ∈ S.filter (fun p ↦ c p = i), w p) * v i := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := S.image c)
    (fun p hp ↦ Finset.mem_image_of_mem c hp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2]

private theorem sum_cell_pair (S : Finset ℕ) (c : ℕ → ℤ) (w : ℕ → ℝ) (F : ℤ → ℤ → ℝ) :
    ∑ pq ∈ S ×ˢ S, w pq.1 * w pq.2 * F (c pq.1) (c pq.2) =
      ∑ i ∈ S.image c, ∑ j ∈ S.image c,
        (∑ p ∈ S.filter (fun p ↦ c p = i), w p) *
        (∑ q ∈ S.filter (fun q ↦ c q = j), w q) * F i j := by
  let b (i : ℤ) := ∑ p ∈ S.filter (fun p ↦ c p = i), w p
  rw [Finset.sum_product]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [sum_by_cell S c w (F _)]
  exact sum_by_cell S c w (fun i ↦ ∑ j ∈ S.image c, b j * F i j)

private theorem cell_band_le (J : Finset ℤ) (b : ℤ → ℝ) (m : ℕ) :
    (∑ i ∈ J, ∑ j ∈ J, b i * b j * (if |i - j| ≤ (m : ℤ) then 1 else 0)) ≤
      (2 * (m : ℝ) + 1) * ∑ i ∈ J, b i ^ 2 := by
  let a (i j : ℤ) : ℝ := if |i - j| ≤ (m : ℤ) then 1 else 0
  change (∑ i ∈ J, ∑ j ∈ J, b i * b j * a i j) ≤ _
  have ha (i j : ℤ) : 0 ≤ a i j := by unfold a; split <;> norm_num
  have hs (i j : ℤ) : a i j = a j i := by simp [a, abs_sub_comm]
  have hrow (i : ℤ) : ∑ j ∈ J, a i j ≤ 2 * (m : ℝ) + 1 := by
    have hsub : J.filter (fun j ↦ |i - j| ≤ (m : ℤ)) ⊆
        Finset.Icc (i - (m : ℤ)) (i + (m : ℤ)) := by
      intro j hj
      have h := abs_le.mp (Finset.mem_filter.mp hj).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hcard : (Finset.Icc (i - (m : ℤ)) (i + (m : ℤ))).card = 2 * m + 1 := by
      rw [Int.card_Icc]
      omega
    have h := Finset.card_le_card hsub
    rw [hcard] at h
    calc
      _ = ((J.filter fun j ↦ |i - j| ≤ (m : ℤ)).card : ℝ) := by
        simp [a]
      _ ≤ _ := by exact_mod_cast h
  have hrows : (∑ i ∈ J, ∑ j ∈ J, b i ^ 2 * a i j) ≤
      (2 * (m : ℝ) + 1) * ∑ i ∈ J, b i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by
      rw [← Finset.mul_sum, mul_comm (2 * (m : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
  have hswap : ∑ i ∈ J, ∑ j ∈ J, b j ^ 2 * a i j =
      ∑ i ∈ J, ∑ j ∈ J, b i ^ 2 * a i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hs j i]
  have hbound : 2 * (∑ i ∈ J, ∑ j ∈ J, b i * b j * a i j) ≤
      ∑ i ∈ J, ∑ j ∈ J, (b i ^ 2 + b j ^ 2) * a i j := by
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (b i - b j)]) (ha i j)
  simp only [add_mul, Finset.sum_add_distrib, hswap] at hbound
  linarith only [hbound, hrows]

private theorem near_mass_le (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    collisionMass S w (n * r) ≤ (2 * (n : ℝ) + 3) * collisionMass S w r := by
  classical
  let c (p : ℕ) : ℤ := ⌊(p : ℝ) / r⌋
  let J := S.image c
  let b (i : ℤ) := ∑ p ∈ S.filter (fun p ↦ c p = i), w p
  let F (i j : ℤ) : ℝ := if |i - j| ≤ (n : ℤ) + 1 then 1 else 0
  let E (i j : ℤ) : ℝ := if i = j then 1 else 0
  have hnear : collisionMass S w (n * r) ≤ ∑ i ∈ J, ∑ j ∈ J, b i * b j * F i j := by
    rw [← sum_cell_pair S c w F, collisionMass, nearPairs, Finset.sum_filter]
    refine Finset.sum_le_sum fun pq hpq ↦ ?_
    have hp := Finset.mem_product.mp hpq
    split_ifs with h
    · simp [F, c, cell_close hr h]
    · unfold F
      split <;> simp [mul_nonneg (hw _ hp.1) (hw _ hp.2)]
  have hdiag : ∑ i ∈ J, b i ^ 2 ≤ collisionMass S w r := by
    have h := sum_cell_pair S c w E
    change _ = (∑ i ∈ J, ∑ j ∈ J, b i * b j * E i j) at h
    simp only [E, mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at h
    have hrow (i : ℤ) (hi : i ∈ J) : J.filter (fun j ↦ i = j) = {i} := by
      ext j
      constructor
      · exact fun hj ↦ Finset.mem_singleton.mpr ((Finset.mem_filter.mp hj).2).symm
      · intro hj
        obtain rfl := Finset.mem_singleton.mp hj
        exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    calc
      _ = ∑ i ∈ J, ∑ j ∈ J.filter (fun j ↦ i = j), b i * b j := by
        exact Finset.sum_congr rfl fun i hi ↦ by rw [hrow i hi, Finset.sum_singleton, pow_two]
      _ = ∑ pq ∈ S ×ˢ S, (if c pq.1 = c pq.2 then w pq.1 * w pq.2 else 0) := by
        rw [← Finset.sum_filter]
        exact h.symm
      _ ≤ _ := by
        rw [collisionMass, nearPairs, Finset.sum_filter]
        refine Finset.sum_le_sum fun pq hpq ↦ ?_
        have hp := Finset.mem_product.mp hpq
        by_cases he : c pq.1 = c pq.2
        · simp [he, same_cell_close hr he]
        · simp only [he, ite_false]
          split <;> simp [mul_nonneg (hw _ hp.1) (hw _ hp.2)]
  have hband := cell_band_le J b (n + 1)
  push_cast at hband
  calc
    _ ≤ _ := hnear
    _ ≤ (2 * (n : ℝ) + 3) * ∑ i ∈ J, b i ^ 2 := by
      dsimp only [F]
      norm_num at hband ⊢
      convert hband using 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (by positivity)

private noncomputable def signedTerm (w ω : ℕ → ℝ) (u : ℝ) (pq : ℕ × ℕ) : ℝ :=
  w pq.1 * w pq.2 * Real.cos (u * (ω pq.1 - ω pq.2))

private theorem abs_signedTerm_le (w ω : ℕ → ℝ) (u : ℝ) (pq : ℕ × ℕ)
    (hp : 0 ≤ w pq.1) (hq : 0 ≤ w pq.2) :
    |signedTerm w ω u pq| ≤ w pq.1 * w pq.2 := by
  rw [signedTerm, abs_mul, abs_of_nonneg (mul_nonneg hp hq)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg hp hq)

private theorem signedTerm_swap (w ω : ℕ → ℝ) (u : ℝ) (pq : ℕ × ℕ) :
    signedTerm w ω u pq.swap = signedTerm w ω u pq := by
  simp only [signedTerm, Prod.fst_swap, Prod.snd_swap, mul_comm (w pq.2) (w pq.1)]
  rw [show u * (ω pq.2 - ω pq.1) = -(u * (ω pq.1 - ω pq.2)) by ring, Real.cos_neg]

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

private theorem phase_sub (x y : ℝ) : phase x * conj (phase y) = phase (x - y) := by
  rw [phase, phase, ← Complex.exp_conj, ← Complex.exp_add, phase]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring_nf

private theorem norm_Z_sq_eq (S : Finset ℕ) (X : ℝ) (d : ℕ) (u : ℝ) :
    ‖Z S X d u‖ ^ 2 =
      ∑ pq ∈ S ×ˢ S, signedTerm (weight X d) (frequency d) u pq := by
  let w := weight X d
  let ω := frequency d
  let f (p : ℕ) : ℂ := (w p : ℂ) * phase (u * ω p)
  change ‖∑ p ∈ S, f p‖ ^ 2 = _
  have hz : (↑(‖∑ p ∈ S, f p‖ ^ 2) : ℂ) =
      ∑ pq ∈ S ×ˢ S, ((w pq.1 * w pq.2 : ℝ) : ℂ) * phase (u * (ω pq.1 - ω pq.2)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [f, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [mul_mul_mul_comm, phase_sub, ← mul_sub]
  have h := congrArg Complex.reAddGroupHom hz
  rw [map_sum] at h
  change ‖∑ p ∈ S, f p‖ ^ 2 =
    ∑ pq ∈ S ×ˢ S, (((w pq.1 * w pq.2 : ℝ) : ℂ) * phase (u * (ω pq.1 - ω pq.2))).re at h
  rw [h]
  exact Finset.sum_congr rfl fun pq _ ↦ by
    simp only [signedTerm, phase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, w, ω]

private theorem ordered_split (S : Finset ℕ) (w ω : ℕ → ℝ) (u : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ pq ∈ S ×ˢ S, signedTerm w ω u pq =
      (∑ pq ∈ nearPairs S R, signedTerm w ω u pq) +
        2 * ∑ pq ∈ farPairs S R, signedTerm w ω u pq := by
  classical
  let B : Finset (ℕ × ℕ) := (S ×ˢ S).filter fun pq ↦ R < (pq.1 : ℝ) - pq.2
  have hB (pq : ℕ × ℕ) : pq ∈ B ↔ pq.swap ∈ farPairs S R := by
    simp only [B, Finset.mem_filter, Finset.mem_product, mem_far, Prod.fst_swap, Prod.snd_swap]
    tauto
  have hdis : Disjoint (farPairs S R) B := by
    refine Finset.disjoint_left.mpr fun pq ha hb ↦ ?_
    have h₁ := (mem_far.mp ha).2.2
    have h₂ := (mem_far.mp ((hB pq).mp hb)).2.2
    simp only [Prod.fst_swap, Prod.snd_swap] at h₂
    linarith only [hR, h₁, h₂]
  have hcover : ((S ×ˢ S).filter fun pq : ℕ × ℕ ↦ ¬ |(pq.2 : ℝ) - pq.1| ≤ R) =
      farPairs S R ∪ B := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, mem_far, B]
    rw [abs_le]
    constructor
    · rintro ⟨⟨hp, hq⟩, h⟩
      by_cases hf : R < (pq.2 : ℝ) - pq.1
      · exact Or.inl ⟨hp, hq, hf⟩
      · exact Or.inr ⟨⟨hp, hq⟩, by
          have : ¬ -R ≤ (pq.2 : ℝ) - pq.1 := fun h' ↦ h ⟨h', le_of_not_gt hf⟩
          linarith only [lt_of_not_ge this]⟩
    · rintro (⟨hp, hq, hf⟩ | ⟨⟨hp, hq⟩, hb⟩)
      · exact ⟨⟨hp, hq⟩, fun h ↦ (not_lt_of_ge h.2) hf⟩
      · exact ⟨⟨hp, hq⟩, fun h ↦ by linarith only [h.1, hb]⟩
  have hreverse : ∑ pq ∈ B, signedTerm w ω u pq =
      ∑ pq ∈ farPairs S R, signedTerm w ω u pq := by
    refine Finset.sum_bij (fun pq _ ↦ pq.swap) (fun pq hpq ↦ (hB pq).mp hpq) ?_ ?_ ?_
    · intro p _ q _ h
      simpa only [Prod.swap_swap] using congrArg Prod.swap h
    · intro p hp
      exact ⟨p.swap, (hB p.swap).mpr (by simpa only [Prod.swap_swap]), Prod.swap_swap p⟩
    · exact fun pq _ ↦ (signedTerm_swap w ω u pq).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (S ×ˢ S)
    (fun pq : ℕ × ℕ ↦ |(pq.2 : ℝ) - pq.1| ≤ R) (signedTerm w ω u)
  change (∑ pq ∈ nearPairs S R, signedTerm w ω u pq) + _ = _ at hsplit
  rw [hcover, Finset.sum_union hdis, hreverse, ← two_mul] at hsplit
  exact hsplit.symm

private theorem sparse_card_le (S : Finset ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    (((farPairs S R).filter fun pq ↦ (gapCount S R (gap pq) : ℝ) ≤ M).card : ℝ) ≤ X * M := by
  classical
  let P := (farPairs S R).filter fun pq ↦ (gapCount S R (gap pq) : ℝ) ≤ M
  let G := Finset.Icc 1 ⌊X⌋₊
  change (P.card : ℝ) ≤ _
  have hmaps (pq : ℕ × ℕ) (hpq : pq ∈ P) : gap pq ∈ G := by
    obtain ⟨_, hq, hgap⟩ := mem_far.mp (Finset.mem_filter.mp hpq).1
    have hpq' : pq.1 < pq.2 := by exact_mod_cast (sub_pos.mp (hR.trans_lt hgap))
    refine Finset.mem_Icc.mpr ⟨by unfold gap; omega, Nat.le_floor ?_⟩
    exact (by exact_mod_cast (Nat.sub_le pq.2 pq.1) : (gap pq : ℝ) ≤ pq.2).trans (hS _ hq)
  have hc (g : ℕ) : ((P.filter fun pq ↦ gap pq = g).card : ℝ) ≤ M := by
    by_cases hg : (gapCount S R g : ℝ) ≤ M
    · have hsub : P.filter (fun pq ↦ gap pq = g) ⊆
          (farPairs S R).filter (fun pq ↦ gap pq = g) := by
        intro pq hpq
        obtain ⟨hp, hg'⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, hg'⟩
      have hcard : ((P.filter fun pq ↦ gap pq = g).card : ℝ) ≤ gapCount S R g := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans hg
    · have hzero : P.filter (fun pq ↦ gap pq = g) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro pq hpq
        obtain ⟨hp, hg'⟩ := Finset.mem_filter.mp hpq
        exact hg (by simpa only [← hg'] using (Finset.mem_filter.mp hp).2)
      simpa only [hzero, Finset.card_empty, Nat.cast_zero] using hM
  have hcG : (G.card : ℝ) ≤ X := by
    have : G.card = ⌊X⌋₊ := by simp [G, Nat.card_Icc]
    rw [this]
    exact Nat.floor_le hX
  calc
    _ = ∑ g ∈ G, ((P.filter fun pq ↦ gap pq = g).card : ℝ) := by
      simpa using (Finset.sum_fiberwise_of_maps_to hmaps (fun _ ↦ (1 : ℝ))).symm
    _ ≤ ∑ g ∈ G, M := Finset.sum_le_sum fun g _ ↦ hc g
    _ = (G.card : ℝ) * M := by simp
    _ ≤ X * M := mul_le_mul_of_nonneg_right hcG hM

/-- The pool weights are nonnegative and bounded by the dense-gap scale. -/
public theorem weight_bounds {S : Finset ℕ} {X : ℝ} {d : ℕ} (h : IsPrimePool S X d)
    {p : ℕ} (hp : p ∈ S) : 0 ≤ weight X d p ∧ weight X d p ≤ 8 * (Real.log X)^2 / X := by
  obtain ⟨hpp, hpdp, ⟨hlo, hhi⟩, ⟨_, hdhi⟩⟩ := h.band p hp
  have hX : 0 < X := zero_lt_one.trans h.one_lt
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hpd₁ : (1 : ℝ) ≤ ((p + d : ℕ) : ℝ) := by exact_mod_cast hpdp.one_lt.le
  have hp₀ := zero_lt_one.trans_le hp₁
  have hpd₀ := zero_lt_one.trans_le hpd₁
  have hl : 0 ≤ Real.log (X / p) := Real.log_nonneg ((le_div_iff₀ hp₀).2 (by simpa using hhi))
  have hlp := Real.log_nonneg hp₁
  have hlpd := Real.log_nonneg hpd₁
  have hratio : X / (p : ℝ) ≤ Real.exp 8 := by
    apply (div_le_iff₀ hp₀).2
    have hm := mul_le_mul_of_nonneg_left hlo (Real.exp_pos 8).le
    rwa [← mul_assoc, ← Real.exp_add, show (8 : ℝ) + -8 = 0 by norm_num, Real.exp_zero,
      one_mul] at hm
  have hl8 := (Real.log_le_log (div_pos hX hp₀) hratio).trans_eq (Real.log_exp 8)
  have hlD := Real.log_le_log hp₀ hhi
  have hldD := Real.log_le_log hpd₀ hdhi
  have hD := (Real.log_pos h.one_lt).le
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hX.le) hl) hlp) hlpd, ?_⟩
  calc
    weight X d p ≤ X⁻¹ * 8 * Real.log X * Real.log X := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hl8 (inv_nonneg.mpr hX.le))
        hlD hlp (by positivity)) hldD hlpd (by positivity)
    _ = _ := by ring

/-- The frequency in `Q` on an integer gap is the logarithm of the exact
rational defect, not a rounded or asymptotic phase. -/
public theorem frequency_sub_eq_gap (d p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) :
    frequency d p - frequency d q =
      Real.log (1 + (d : ℝ) * (gap (p, q) : ℝ) / ((p : ℝ) * ((q + d : ℕ) : ℝ))) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  unfold frequency gap
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  rw [Nat.cast_sub hpq, Nat.cast_add]
  field_simp
  ring

/-- At every real height, deletion of the *ordered* near strip (diagonal
included) and of the sparse far integer gaps costs the stated additive error.
The only collision-mass hypothesis is retention at radius `(log X)^2`. -/
public theorem norm_Z_sq_sub_Q_le {S : Finset ℕ} {X K : ℝ} {d n : ℕ}
    (h : IsPrimePool S X d) (hn : 1 ≤ n)
    (hret : (n : ℝ)^2 * collisionMass S (weight X d) ((Real.log X)^2) ≤ K) (u : ℝ) :
    |‖Z S X d u‖ ^ 2 - Q S X d n u| ≤ (2 * (n : ℝ) + 3) * K / (n : ℝ)^2 + 128 / n := by
  classical
  let D := Real.log X
  let R : ℝ := n * D^2
  let M : ℝ := X / (n * D^4)
  let W : ℝ := 8 * D^2 / X
  let w := weight X d
  let f := signedTerm w (frequency d) u
  let P := (farPairs S R).filter fun pq ↦ (gapCount S R (gap pq) : ℝ) ≤ M
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn : 0 < n)
  have hX : 0 < X := zero_lt_one.trans h.one_lt
  have hD : 0 < D := Real.log_pos h.one_lt
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hnw (p : ℕ) (hp : p ∈ S) : 0 ≤ w p := (weight_bounds h hp).1
  have hbw (p : ℕ) (hp : p ∈ S) : w p ≤ W := (weight_bounds h hp).2
  have hnear : |∑ pq ∈ nearPairs S R, f pq| ≤ (2 * (n : ℝ) + 3) * K / (n : ℝ)^2 := by
    have hret' : collisionMass S w (D^2) ≤ K / (n : ℝ)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hn')).2 (by simpa only [mul_comm] using hret)
    calc
      _ ≤ ∑ pq ∈ nearPairs S R, |f pq| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ collisionMass S w R := Finset.sum_le_sum fun pq hpq ↦ by
        obtain ⟨hp, hq, _⟩ := mem_near.mp hpq
        exact abs_signedTerm_le w _ u pq (hnw _ hp) (hnw _ hq)
      _ ≤ (2 * (n : ℝ) + 3) * collisionMass S w (D^2) :=
        near_mass_le S w hnw (sq_pos_of_pos hD) n
      _ ≤ _ := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hret' (by positivity)
  have hspace : |∑ pq ∈ P, f pq| ≤ X * M * W^2 := by
    have hc : (P.card : ℝ) ≤ X * M := sparse_card_le S X hX.le
      (fun p hp ↦ (h.band p hp).2.2.1.2) hR hM
    calc
      _ ≤ ∑ pq ∈ P, |f pq| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ P, W^2 := Finset.sum_le_sum fun pq hpq ↦ by
        obtain ⟨hp, hq, _⟩ := mem_far.mp (Finset.mem_filter.mp hpq).1
        exact (abs_signedTerm_le w _ u pq (hnw _ hp) (hnw _ hq)).trans
          (by rw [pow_two]; exact mul_le_mul (hbw _ hp) (hbw _ hq) (hnw _ hq) hW)
      _ = (P.card : ℝ) * W^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hsplit : ∑ pq ∈ farPairs S R, f pq =
      (∑ pq ∈ densePairs S R M, f pq) + ∑ pq ∈ P, f pq := by
    have hf := Finset.sum_filter_add_sum_filter_not (farPairs S R)
      (fun pq ↦ M < (gapCount S R (gap pq) : ℝ)) f
    simpa only [not_lt, densePairs, P] using hf.symm
  have hdiff : ‖Z S X d u‖ ^ 2 - Q S X d n u =
      (∑ pq ∈ nearPairs S R, f pq) + 2 * ∑ pq ∈ P, f pq := by
    rw [norm_Z_sq_eq, ordered_split S w (frequency d) u hR]
    change (∑ pq ∈ nearPairs S R, f pq) + 2 * (∑ pq ∈ farPairs S R, f pq) -
      2 * (∑ pq ∈ densePairs S R M, f pq) = _
    rw [hsplit]
    ring
  have hcost : 2 * (X * M * W^2) = 128 / (n : ℝ) := by
    dsimp only [M, W]
    field_simp
    ring
  rw [hdiff]
  calc
    _ ≤ |∑ pq ∈ nearPairs S R, f pq| + 2 * |∑ pq ∈ P, f pq| := by
      simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using
        abs_add_le (∑ pq ∈ nearPairs S R, f pq) (2 * ∑ pq ∈ P, f pq)
    _ ≤ (2 * (n : ℝ) + 3) * K / (n : ℝ)^2 + 2 * (X * M * W^2) :=
      add_le_add hnear (mul_le_mul_of_nonneg_left hspace (by norm_num))
    _ = _ := by rw [hcost]

private theorem convex_cos_add_sq : ConvexOn ℝ Set.univ (fun x : ℝ ↦ Real.cos x + x^2 / 2) := by
  let f := fun x : ℝ ↦ Real.cos x + x^2 / 2
  let g := fun x : ℝ ↦ -Real.sin x + x
  have hf (x : ℝ) : HasDerivAt f (g x) x := by
    have hp : HasDerivAt (fun y : ℝ ↦ y^2 / 2) x x := by
      simpa using (((hasDerivAt_id x).pow 2).div_const (2 : ℝ))
    exact (Real.hasDerivAt_cos x).add hp
  have hg (x : ℝ) : HasDerivAt g (1 - Real.cos x) x := by
    rw [show 1 - Real.cos x = -Real.cos x + 1 by ring]
    exact (Real.hasDerivAt_sin x).neg.add (hasDerivAt_id x)
  have hderiv : deriv f = g := funext fun x ↦ (hf x).deriv
  apply convexOn_of_deriv2_nonneg (convex_univ) (fun x _ ↦ (hf x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (hf x).differentiableAt.differentiableWithinAt)
  · rw [hderiv]
    exact fun x _ ↦ (hg x).differentiableAt.differentiableWithinAt
  · intro x _
    change 0 ≤ deriv (deriv f) x
    rw [hderiv, (hg x).deriv]
    exact sub_nonneg.mpr (Real.cos_le_one x)

private theorem cos_chord (a b ω s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    Real.cos ((s * a + t * b) * ω) ≤
      s * Real.cos (a * ω) + t * Real.cos (b * ω) + ω^2 * (b - a)^2 / 8 := by
  have h := convex_cos_add_sq.2 (x := a * ω) (y := b * ω) (Set.mem_univ _) (Set.mem_univ _) hs ht hst
  simp only [smul_eq_mul] at h
  rw [show s * (a * ω) + t * (b * ω) = (s * a + t * b) * ω by ring] at h
  have hquad : s * ((a * ω)^2 / 2) + t * ((b * ω)^2 / 2) - ((s * a + t * b) * ω)^2 / 2 =
      s * t * (ω^2 * (b - a)^2 / 2) := by
    rw [show s = 1 - t by linarith only [hst]]
    ring
  have hst' : s * t ≤ 1 / 4 := by
    rw [show s = 1 - t by linarith only [hst]]
    nlinarith only [sq_nonneg (t - 1 / 2)]
  have hquad' := mul_le_mul_of_nonneg_right hst' (show 0 ≤ ω^2 * (b - a)^2 / 2 by positivity)
  linarith only [h, hquad, hquad']

private theorem frequency_bounds {S : Finset ℕ} {X : ℝ} {d : ℕ} (h : IsPrimePool S X d)
    {p : ℕ} (hp : p ∈ S) :
    0 ≤ frequency d p ∧ frequency d p ≤ (5 * Real.exp 8) / (X / Real.log X) := by
  have hX : 0 < X := zero_lt_one.trans h.one_lt
  have hD := Real.log_pos h.one_lt
  obtain ⟨hprime, _, ⟨hlo, _⟩, _⟩ := h.band p hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hbase : (1 : ℝ) ≤ 1 + (d : ℝ) / p :=
    le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hp₀.le)
  refine ⟨Real.log_nonneg hbase, ?_⟩
  calc
    frequency d p ≤ (d : ℝ) / p := by
      unfold frequency
      linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hbase)]
    _ ≤ (5 * Real.log X) / p := div_le_div_of_nonneg_right h.shift_le hp₀.le
    _ ≤ (5 * Real.log X) / (Real.exp (-8) * X) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (Real.exp_pos _) hX) hlo
    _ = _ := by
      rw [Real.exp_neg]
      field_simp

/-- On any cell of length at most `(X / log X) / √n`, the signed dense sum
lies under the larger of its two genuine node values plus the curvature error.
There is no constraint on the origin of the cell. -/
public theorem Q_le_max_nodes {S : Finset ℕ} {X : ℝ} {d n : ℕ}
    (h : IsPrimePool S X d) (hn : 1 ≤ n) {a b u : ℝ} (hu : u ∈ Set.Icc a b)
    (hlen : b - a ≤ (X / Real.log X) / Real.sqrt (n : ℝ)) :
    Q S X d n u ≤ max (Q S X d n a) (Q S X d n b) +
      (10 * Real.exp 8)^2 * (∑ p ∈ S, weight X d p)^2 / (8 * (n : ℝ)) := by
  classical
  let L := X / Real.log X
  let C := 5 * Real.exp 8
  let w := weight X d
  let A := ∑ p ∈ S, w p
  let e := C^2 / (8 * (n : ℝ))
  let P := densePairs S (n * (Real.log X)^2) (X / (n * (Real.log X)^4))
  let f (v : ℝ) := signedTerm w (frequency d) v
  have hL : 0 < L := div_pos (zero_lt_one.trans h.one_lt) (Real.log_pos h.one_lt)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn : 0 < n)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hnonneg (pq : ℕ × ℕ) (hpq : pq ∈ S ×ˢ S) : 0 ≤ w pq.1 * w pq.2 := by
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    exact mul_nonneg (weight_bounds h hp).1 (weight_bounds h hq).1
  have hP : P ⊆ S ×ˢ S := by
    intro pq hpq
    have hp := (Finset.mem_filter.mp hpq).1
    exact (Finset.mem_filter.mp hp).1
  have hA : ∑ pq ∈ P, w pq.1 * w pq.2 ≤ A^2 := by
    calc
      _ ≤ ∑ pq ∈ S ×ˢ S, w pq.1 * w pq.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hP fun pq hpq _ ↦ hnonneg pq hpq
      _ = _ := by
        change (∑ pq ∈ S ×ˢ S, w pq.1 * w pq.2) = (∑ p ∈ S, w p)^2
        rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  obtain ⟨s, t, hs, ht, hst, hcomb⟩ :
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ s * a + t * b = u := by
    have hab : a ≤ b := hu.1.trans hu.2
    rcases hab.eq_or_lt with hab | hab
    · have hau : a = u := le_antisymm hu.1 (hu.2.trans_eq hab.symm)
      exact ⟨1, 0, zero_le_one, le_rfl, by ring, by simpa using hau⟩
    · let t := (u - a) / (b - a)
      have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hab.le)
      have ht1 : t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hab)).2 (by linarith only [hu.2])
      refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht, by ring, ?_⟩
      dsimp [t]
      field_simp
      ring
  have hlen' : (b - a)^2 ≤ L^2 / (n : ℝ) := by
    calc
      _ ≤ (L / Real.sqrt (n : ℝ))^2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr (hu.1.trans hu.2)) hlen 2
      _ = _ := by rw [div_pow, Real.sq_sqrt hn'.le]
  have hterm (pq : ℕ × ℕ) (hpq : pq ∈ P) :
      f u pq ≤ s * f a pq + t * f b pq + e * (w pq.1 * w pq.2) := by
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp (hP hpq)
    let ω := frequency d pq.1 - frequency d pq.2
    have hp' := frequency_bounds h hp
    have hq' := frequency_bounds h hq
    have hω : |ω| ≤ C / L := abs_le.mpr ⟨by dsimp [ω, C, L]; linarith only [hp'.1, hq'.2],
      by dsimp [ω, C, L]; linarith only [hp'.2, hq'.1]⟩
    have hω' : ω^2 ≤ (C / L)^2 := by
      rw [← sq_abs ω]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    have hangle : ω^2 * (b - a)^2 / 8 ≤ e := by
      calc
        _ ≤ (C / L)^2 * (L^2 / (n : ℝ)) / 8 :=
          div_le_div_of_nonneg_right (mul_le_mul hω' hlen' (sq_nonneg _) (sq_nonneg _)) (by norm_num)
        _ = _ := by dsimp only [e]; field_simp
    have hcos := (cos_chord a b ω s t hs ht hst).trans (add_le_add le_rfl hangle)
    rw [hcomb] at hcos
    have hmul := mul_le_mul_of_nonneg_left hcos (hnonneg pq (hP hpq))
    change w pq.1 * w pq.2 * Real.cos (u * ω) ≤
      s * (w pq.1 * w pq.2 * Real.cos (a * ω)) + t * (w pq.1 * w pq.2 * Real.cos (b * ω)) +
        e * (w pq.1 * w pq.2)
    linarith only [hmul]
  have hQ : Q S X d n u ≤ s * Q S X d n a + t * Q S X d n b + 2 * (e * A^2) := by
    change 2 * (∑ pq ∈ P, f u pq) ≤ s * (2 * ∑ pq ∈ P, f a pq) +
      t * (2 * ∑ pq ∈ P, f b pq) + 2 * (e * A^2)
    have hsum := Finset.sum_le_sum hterm
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    linarith only [hsum, mul_le_mul_of_nonneg_left hA he]
  have hmax : s * Q S X d n a + t * Q S X d n b ≤ max (Q S X d n a) (Q S X d n b) := by
    calc
      _ ≤ s * max (Q S X d n a) (Q S X d n b) + t * max (Q S X d n a) (Q S X d n b) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hs)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
      _ = _ := by rw [← add_mul, hst, one_mul]
  calc
    _ ≤ _ := hQ
    _ ≤ max (Q S X d n a) (Q S X d n b) + 2 * (e * A^2) := add_le_add hmax le_rfl
    _ ≤ _ := by
      have hq : 0 ≤ e * A^2 := mul_nonneg he (sq_nonneg _)
      have heq : (10 * Real.exp 8)^2 * A^2 / (8 * (n : ℝ)) = 4 * (e * A^2) := by
        dsimp only [C, e]
        ring
      change _ ≤ max (Q S X d n a) (Q S X d n b) + (10 * Real.exp 8)^2 * A^2 / (8 * (n : ℝ))
      rw [heq]
      linarith only [hq]

/-- A threshold test on the two signed dense node values gives a cap on the
original norm square throughout the cell, with both explicit additive losses. -/
public theorem norm_Z_sq_le_of_Q_nodes {S : Finset ℕ} {X K cap : ℝ} {d n : ℕ}
    (h : IsPrimePool S X d) (hn : 1 ≤ n)
    (hret : (n : ℝ)^2 * collisionMass S (weight X d) ((Real.log X)^2) ≤ K)
    {a b u : ℝ} (hu : u ∈ Set.Icc a b)
    (hlen : b - a ≤ (X / Real.log X) / Real.sqrt (n : ℝ))
    (ha : Q S X d n a ≤ cap) (hb : Q S X d n b ≤ cap) :
    ‖Z S X d u‖ ^ 2 ≤ cap + (10 * Real.exp 8)^2 * (∑ p ∈ S, weight X d p)^2 / (8 * (n : ℝ)) +
      ((2 * (n : ℝ) + 3) * K / (n : ℝ)^2 + 128 / n) := by
  have hQ := Q_le_max_nodes h hn hu hlen
  have hdel := (abs_le.mp (norm_Z_sq_sub_Q_le h hn hret u)).2
  linarith only [hdel, hQ, max_le ha hb]

end Masullo.RetainedSignedCap
