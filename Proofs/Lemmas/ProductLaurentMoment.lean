module

public import Lemmas.LaurentCircleMoment
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite product Laurent moment

Source: `3d2886df:.godel/bob/signed-gap-cube-screen.md:56–64`, selection at `1de21475`.
Owning check session: `01a20c3b-0de7-75d0-b4f0-194be0854305`.

This formalizes the independent-phase moment bound, with a charge only on nonzero
coordinates of each distinct Laurent key, and its bounded-support corollary.
Both signs in a coordinate use the same normalized Haar circle phase.
There is no transfer to a continuous shell or a mesh.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace Masullo.ProductLaurentMoment

open LaurentCircleMoment (uniformCircle integral_norm_laurent_pow_le)

/-- The entries `0`, `1`, and `2` encode Laurent exponents `0`, `+1`, and `-1`. -/
@[expose] public def phaseFactor (s : Fin 3) (z : Circle) : ℂ :=
  if s = 0 then 1 else if s = 1 then (z : ℂ) else conj (z : ℂ)

/-- The character of the product of circles specified by a ternary Laurent key. -/
@[expose] public def monomial {ι : Type*} [Fintype ι] (v : ι → Fin 3) (z : ι → Circle) : ℂ :=
  ∏ i, phaseFactor (v i) (z i)

/-- The number of coordinates with exponent different from zero. -/
@[expose] public def supportSize {ι : Type*} [Fintype ι] (v : ι → Fin 3) : ℕ :=
  (Finset.univ.filter fun i ↦ v i ≠ 0).card

private theorem continuous_monomial {ι : Type*} [Fintype ι] (v : ι → Fin 3) :
    Continuous (monomial v) := by
  apply continuous_finsetProd
  intro i _
  have hi : Continuous (fun z : ι → Circle ↦ (z i : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  by_cases h₀ : v i = 0
  · simpa [phaseFactor, h₀] using (continuous_const : Continuous (fun _ : ι → Circle ↦ (1 : ℂ)))
  by_cases h₁ : v i = 1
  · simpa [phaseFactor, h₀, h₁] using hi
  have hj : Continuous (fun z : ι → Circle ↦ conj (z i : ℂ)) := Complex.continuous_conj.comp hi
  simpa [phaseFactor, h₀, h₁] using hj

private theorem charge_ge_one {m : ℕ} (hm : 0 < m) : (1 : ℝ) ≤ 4 * (m : ℝ) - 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

section Integrals

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

private theorem moment_add_le {m : ℕ} (hm : 0 < m)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfm : (∫ x, f x ^ m ∂μ) ≤ A ^ m) (hgm : (∫ x, g x ^ m ∂μ) ≤ B ^ m) :
    (∫ x, (f x + g x) ^ m ∂μ) ≤ (A + B) ^ m := by
  have hm₀ : m ≠ 0 := Nat.ne_of_gt hm
  have hm₁ : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hm
  have hnorm {u : X → ℝ} (hu : Continuous u) (hu₀ : ∀ x, 0 ≤ u x) :
      eLpNorm u (m : ℝ≥0∞) μ = ENNReal.ofReal ((∫ x, u x ^ m ∂μ) ^ (m : ℝ)⁻¹) := by
    have huLp : MemLp u (m : ℝ≥0∞) μ :=
      hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [huLp.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hm₀) (ENNReal.natCast_ne_top m)]
    simp [Real.norm_eq_abs, abs_of_nonneg (hu₀ _), Real.rpow_natCast]
  have moment_nonneg (u : X → ℝ) (hu₀ : ∀ x, 0 ≤ u x) :
      0 ≤ ∫ x, u x ^ m ∂μ := integral_nonneg fun x ↦ pow_nonneg (hu₀ x) _
  have norm_le {u : X → ℝ} (hu : Continuous u) (hu₀ : ∀ x, 0 ≤ u x)
      {C : ℝ} (hC : 0 ≤ C) (h : (∫ x, u x ^ m ∂μ) ≤ C ^ m) :
      eLpNorm u (m : ℝ≥0∞) μ ≤ ENNReal.ofReal C := by
    rw [hnorm hu hu₀, ENNReal.ofReal_le_ofReal_iff hC, ← Real.pow_rpow_inv_natCast hC hm₀]
    exact Real.rpow_le_rpow (moment_nonneg u hu₀) h (by positivity)
  have hfg₀ : ∀ x, 0 ≤ (f + g) x := fun x ↦ add_nonneg (hf₀ x) (hg₀ x)
  have hLp := (eLpNorm_add_le (μ := μ) (f := f) (g := g) hm₁).trans
    (add_le_add (norm_le hf hf₀ hA hfm) (norm_le hg hg₀ hB hgm))
  rw [← ENNReal.ofReal_add hA hB, hnorm (hf.add hg) hfg₀,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg hA hB)] at hLp
  exact (Real.rpow_inv_natCast_pow (moment_nonneg (f + g) hfg₀) hm₀) ▸
    pow_le_pow_left₀ (Real.rpow_nonneg (moment_nonneg (f + g) hfg₀) _) hLp m

private theorem integral_three_branches_le {m : ℕ} (hm : 0 < m)
    {a b c : X → ℂ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ham : (∫ x, ‖a x‖ ^ (2 * m) ∂μ) ≤ A ^ m)
    (hbm : (∫ x, ‖b x‖ ^ (2 * m) ∂μ) ≤ B ^ m)
    (hcm : (∫ x, ‖c x‖ ^ (2 * m) ∂μ) ≤ C ^ m) :
    (∫ p : Circle × X, ‖a p.2 + b p.2 * (p.1 : ℂ) + c p.2 * conj (p.1 : ℂ)‖ ^ (2 * m)
      ∂uniformCircle.prod μ) ≤ (A + (4 * (m : ℝ) - 2) * (B + C)) ^ m := by
  let K := 4 * (m : ℝ) - 2
  have hK : 0 ≤ K := zero_le_one.trans (charge_ge_one hm)
  have hz : Continuous (fun p : Circle × X ↦ (p.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hh : Continuous (fun p : Circle × X ↦
      ‖a p.2 + b p.2 * (p.1 : ℂ) + c p.2 * conj (p.1 : ℂ)‖ ^ (2 * m)) :=
    (((ha.comp continuous_snd).add ((hb.comp continuous_snd).mul hz)).add
      ((hc.comp continuous_snd).mul (Complex.continuous_conj.comp hz))).norm.pow _
  have hInt := hh.integrable_of_hasCompactSupport (μ := uniformCircle.prod μ)
    (HasCompactSupport.of_compactSpace _)
  rw [integral_prod_symm _ hInt]
  have habc : Continuous (fun x ↦ ‖a x‖ ^ 2 + K * (‖b x‖ ^ 2 + ‖c x‖ ^ 2)) :=
    (ha.norm.pow _).add (continuous_const.mul ((hb.norm.pow _).add (hc.norm.pow _)))
  calc
    _ ≤ ∫ x, (‖a x‖ ^ 2 + K * (‖b x‖ ^ 2 + ‖c x‖ ^ 2)) ^ m ∂μ :=
      integral_mono hInt.integral_prod_right
        ((habc.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (fun x ↦ integral_norm_laurent_pow_le (a x) (b x) (c x) hm)
    _ ≤ (A + K * (B + C)) ^ m := by
      have hbc := moment_add_le hm (f := fun x ↦ ‖b x‖ ^ 2) (g := fun x ↦ ‖c x‖ ^ 2)
        (hb.norm.pow 2) (hc.norm.pow 2)
        (fun x ↦ sq_nonneg ‖b x‖) (fun x ↦ sq_nonneg ‖c x‖) hB hC
        (by simpa only [pow_mul] using hbm) (by simpa only [pow_mul] using hcm)
      have hKbc : (∫ x, (K * (‖b x‖ ^ 2 + ‖c x‖ ^ 2)) ^ m ∂μ) ≤ (K * (B + C)) ^ m := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hbc (pow_nonneg hK _)
      exact moment_add_le hm (f := fun x ↦ ‖a x‖ ^ 2)
        (g := fun x ↦ K * (‖b x‖ ^ 2 + ‖c x‖ ^ 2)) (ha.norm.pow 2)
        (continuous_const.mul ((hb.norm.pow 2).add (hc.norm.pow 2)))
        (fun x ↦ sq_nonneg ‖a x‖) (fun x ↦ mul_nonneg hK (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        hA (mul_nonneg hK (add_nonneg hB hC)) (by simpa only [pow_mul] using ham) hKbc

end Integrals

private noncomputable def polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → Fin 3) → ℂ) (z : ι → Circle) : ℂ :=
  ∑ v, c v * monomial v z

private noncomputable def energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℝ) (c : (ι → Fin 3) → ℂ) : ℝ :=
  ∑ v, K ^ supportSize v * ‖c v‖ ^ 2

private theorem continuous_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → Fin 3) → ℂ) :
    Continuous (polynomial c) := by
  unfold polynomial
  exact continuous_finsetSum _ fun v _ ↦ continuous_const.mul (continuous_monomial v)

private theorem energy_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℝ} (hK : 0 ≤ K)
    (c : (ι → Fin 3) → ℂ) : 0 ≤ energy K c := by
  unfold energy
  exact Finset.sum_nonneg fun v _ ↦ mul_nonneg (pow_nonneg hK _) (sq_nonneg ‖c v‖)

private theorem integral_pi_cons {n : ℕ} (f : (Fin (n + 1) → Circle) → ℝ) :
    (∫ z, f z ∂Measure.pi (fun _ ↦ uniformCircle)) =
      ∫ p : Circle × (Fin n → Circle), f (Fin.cons p.1 p.2)
        ∂uniformCircle.prod (Measure.pi (fun _ ↦ uniformCircle)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Circle) 0
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ uniformCircle) 0).symm e
  rw [← he.integral_comp e.symm.measurableEmbedding f]
  apply integral_congr_ae
  filter_upwards with p
  change f ((MeasurableEquiv.piFinSuccAbove _ 0).symm p) = f (Fin.cons p.1 p.2)
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, Fin.insertNth_zero']

/-- A key is uniquely its first exponent together with its tail key. -/
private theorem sum_keys_cons {n : ℕ} {G : Type*} [AddCommMonoid G]
    (f : (Fin (n + 1) → Fin 3) → G) :
    (∑ v, f v) = ∑ s : Fin 3, ∑ v : Fin n → Fin 3, f (Fin.cons s v) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin 3)) f,
    Fintype.sum_prod_type]
  rfl

private theorem monomial_cons {n : ℕ} (s : Fin 3) (v : Fin n → Fin 3)
    (z : Circle) (w : Fin n → Circle) :
    monomial (Fin.cons s v) (Fin.cons z w) = phaseFactor s z * monomial v w := by
  simp [monomial, Fin.prod_univ_succ]

private theorem supportSize_cons {n : ℕ} (s : Fin 3) (v : Fin n → Fin 3) :
    supportSize (Fin.cons s v) = (if s = 0 then 0 else 1) + supportSize v := by
  simp [supportSize, Finset.card_filter, Fin.sum_univ_succ]

private theorem polynomial_cons {n : ℕ} (c : (Fin (n + 1) → Fin 3) → ℂ)
    (z : Circle) (w : Fin n → Circle) :
    polynomial c (Fin.cons z w) =
      polynomial (fun v ↦ c (Fin.cons 0 v)) w +
        polynomial (fun v ↦ c (Fin.cons 1 v)) w * (z : ℂ) +
        polynomial (fun v ↦ c (Fin.cons 2 v)) w * conj (z : ℂ) := by
  have h (s : Fin 3) :
      (∑ v : Fin n → Fin 3, c (Fin.cons s v) * monomial (Fin.cons s v) (Fin.cons z w)) =
        polynomial (fun v ↦ c (Fin.cons s v)) w * phaseFactor s z := by
    rw [polynomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    rw [monomial_cons]
    ring
  calc
    polynomial c (Fin.cons z w) =
        ∑ s : Fin 3, ∑ v : Fin n → Fin 3, c (Fin.cons s v) * monomial (Fin.cons s v) (Fin.cons z w) :=
      sum_keys_cons (fun v ↦ c v * monomial v (Fin.cons z w))
    _ = _ := by simp [h, Fin.sum_univ_three, phaseFactor]

private theorem energy_cons {n : ℕ} (K : ℝ) (c : (Fin (n + 1) → Fin 3) → ℂ) :
    energy K c = energy K (fun v ↦ c (Fin.cons 0 v)) +
      K * (energy K (fun v ↦ c (Fin.cons 1 v)) + energy K (fun v ↦ c (Fin.cons 2 v))) := by
  have h (s : Fin 3) :
      (∑ v : Fin n → Fin 3, K ^ supportSize (Fin.cons s v) * ‖c (Fin.cons s v)‖ ^ 2) =
        (if s = 0 then 1 else K) * energy K (fun v ↦ c (Fin.cons s v)) := by
    rw [energy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [supportSize_cons, pow_add, mul_assoc]
    split_ifs <;> simp
  calc
    energy K c = ∑ s : Fin 3, ∑ v : Fin n → Fin 3,
        K ^ supportSize (Fin.cons s v) * ‖c (Fin.cons s v)‖ ^ 2 :=
      sum_keys_cons (fun v ↦ K ^ supportSize v * ‖c v‖ ^ 2)
    _ = _ := by simp [h, Fin.sum_univ_three, mul_add, add_assoc]

private theorem integral_pow_le_fin {m : ℕ} (hm : 0 < m) (n : ℕ)
    (c : (Fin n → Fin 3) → ℂ) :
    (∫ z, ‖polynomial c z‖ ^ (2 * m) ∂Measure.pi (fun _ ↦ uniformCircle)) ≤
      (energy (4 * (m : ℝ) - 2) c) ^ m := by
  induction n with
  | zero =>
    have hp (z : Fin 0 → Circle) : polynomial c z = c default := by
      simp [polynomial, monomial]
      exact congrArg c (Subsingleton.elim _ _)
    have he : energy (4 * (m : ℝ) - 2) c = ‖c default‖ ^ 2 := by
      simp [energy, supportSize]
      exact congrArg (fun v ↦ ‖c v‖) (Subsingleton.elim _ _)
    simp [hp, he, pow_mul]
  | succ n ih =>
    let a (s : Fin 3) (v : Fin n → Fin 3) := c (Fin.cons s v)
    let K := 4 * (m : ℝ) - 2
    have hK : 0 ≤ K := zero_le_one.trans (charge_ge_one hm)
    rw [integral_pi_cons, energy_cons]
    simp only [polynomial_cons]
    exact integral_three_branches_le hm
      (continuous_polynomial (a 0)) (continuous_polynomial (a 1)) (continuous_polynomial (a 2))
      (energy_nonneg hK (a 0)) (energy_nonneg hK (a 1)) (energy_nonneg hK (a 2))
      (ih (a 0)) (ih (a 1)) (ih (a 2))

private theorem integral_pow_le_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (c : (ι → Fin 3) → ℂ) :
    (∫ z, ‖polynomial c z‖ ^ (2 * m) ∂Measure.pi (fun _ ↦ uniformCircle)) ≤
      (energy (4 * (m : ℝ) - 2) c) ^ m := by
  let e := (Fintype.equivFin ι).symm
  let eZ := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ Circle) e
  let eV := Equiv.piCongrLeft (fun _ : ι ↦ Fin 3) e
  have hZ (z : Fin (Fintype.card ι) → Circle) (i : Fin (Fintype.card ι)) : (eZ z) (e i) = z i :=
    congrFun (eZ.symm_apply_apply z) i
  have hV (v : Fin (Fintype.card ι) → Fin 3) (i : Fin (Fintype.card ι)) : (eV v) (e i) = v i :=
    congrFun (eV.symm_apply_apply v) i
  have hM (v : Fin (Fintype.card ι) → Fin 3) (z : Fin (Fintype.card ι) → Circle) :
      monomial (eV v) (eZ z) = monomial v z := by
    unfold monomial
    rw [← e.prod_comp (fun i ↦ phaseFactor ((eV v) i) ((eZ z) i))]
    simp only [hV, hZ]
  have hS (v : Fin (Fintype.card ι) → Fin 3) : supportSize (eV v) = supportSize v := by
    simp only [supportSize, Finset.card_filter]
    rw [← e.sum_comp (fun i ↦ if (eV v) i ≠ 0 then 1 else 0)]
    simp only [hV]
  have hp (z : Fin (Fintype.card ι) → Circle) : polynomial c (eZ z) = polynomial (c ∘ eV) z := by
    unfold polynomial
    rw [← eV.sum_comp (fun v ↦ c v * monomial v (eZ z))]
    simp only [hM, Function.comp_apply]
  have he (K : ℝ) : energy K c = energy K (c ∘ eV) := by
    unfold energy
    rw [← eV.sum_comp (fun v ↦ K ^ supportSize v * ‖c v‖ ^ 2)]
    simp only [hS, Function.comp_apply]
  have hμ : MeasurePreserving eZ (Measure.pi fun _ ↦ uniformCircle) (Measure.pi fun _ ↦ uniformCircle) :=
    measurePreserving_piCongrLeft (fun _ : ι ↦ uniformCircle) e
  rw [← hμ.integral_comp eZ.measurableEmbedding (fun z ↦ ‖polynomial c z‖ ^ (2 * m)), he]
  simp_rw [hp]
  exact integral_pow_le_fin hm _ (c ∘ eV)

/-- For a finite set of distinct ternary Laurent keys, the `2m`-th moment over
independent uniform circle phases is bounded by the `m`-th power of the
weighted sum of squared coefficient norms. Zero coefficients are allowed. -/
public theorem integral_norm_laurent_sum_pow_le {ι : Type*} [Fintype ι] {m : ℕ} (hm : 0 < m)
    (S : Finset (ι → Fin 3)) (c : (ι → Fin 3) → ℂ) :
    (∫ z : ι → Circle, ‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)
      ∂Measure.pi (fun _ : ι ↦ uniformCircle)) ≤
      (∑ v ∈ S, (4 * (m : ℝ) - 2) ^ supportSize v * ‖c v‖ ^ 2) ^ m := by
  classical
  let d : (ι → Fin 3) → ℂ := fun v ↦ if v ∈ S then c v else 0
  have hp (z : ι → Circle) : polynomial d z = ∑ v ∈ S, c v * monomial v z := by
    simp only [polynomial, d, ite_mul, zero_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  have he (K : ℝ) : energy K d = ∑ v ∈ S, K ^ supportSize v * ‖c v‖ ^ 2 := by
    unfold energy
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · exact Finset.sum_congr rfl fun v hv ↦ by simp [d, hv]
    · intro v _ hv
      simp [d, hv]
  simpa only [hp, he] using integral_pow_le_full hm d

/-- If every nonzero coefficient has support size at most `R`, the charge
`(4m - 2)^R` can be taken outside the sum. -/
public theorem integral_norm_laurent_sum_pow_le_of_support_le {ι : Type*} [Fintype ι]
    {m : ℕ} (hm : 0 < m) (S : Finset (ι → Fin 3)) (c : (ι → Fin 3) → ℂ) {R : ℕ}
    (hR : ∀ v ∈ S, c v ≠ 0 → supportSize v ≤ R) :
    (∫ z : ι → Circle, ‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)
      ∂Measure.pi (fun _ : ι ↦ uniformCircle)) ≤
      ((4 * (m : ℝ) - 2) ^ R * ∑ v ∈ S, ‖c v‖ ^ 2) ^ m := by
  let K := 4 * (m : ℝ) - 2
  have hK : 1 ≤ K := charge_ge_one hm
  refine (integral_norm_laurent_sum_pow_le hm S c).trans (pow_le_pow_left₀ ?_ ?_ m)
  · exact Finset.sum_nonneg fun v _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) (sq_nonneg _)
  · change (∑ v ∈ S, K ^ supportSize v * ‖c v‖ ^ 2) ≤ K ^ R * ∑ v ∈ S, ‖c v‖ ^ 2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    by_cases hc : c v = 0
    · simp [hc]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (hR v hv hc)) (sq_nonneg _)

end Masullo.ProductLaurentMoment
