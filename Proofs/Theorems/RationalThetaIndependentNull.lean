module

public import Theorems.RationalThetaMellinContinuation
public import Lemmas.RationalThetaWeightedLog
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Independent null vectors for rational theta zero sampling

On the norm interval `(1, 2)` compactly supported even inputs with no support
at `|x| ≥ 2` contribute only the lattice terms at `±1`. Disjoint positive-side
bumps therefore give independent theta images, while the two moments force
all critical-strip zeta-zero Mellin samples to vanish.
-/

open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

/-- Above norm one, a Schwartz input vanishing at `|x| ≥ 2` contributes only
its values at `u` and `-u` to the nonzero-integer theta sum. -/
public theorem rationalTheta_eq_add_neg_of_one_lt (b : 𝓢(ℝ, ℂ))
    (hb : ∀ x : ℝ, 2 ≤ |x| → b x = 0) {u : ℝ} (hu : 1 < u) :
    rationalTheta b u = b u + b (-u) := by
  classical
  let p : {n : ℤ // n ≠ 0} := ⟨1, by decide⟩
  let m : {n : ℤ // n ≠ 0} := ⟨-1, by decide⟩
  have hpm : p ≠ m := by decide
  unfold rationalTheta
  rw [tsum_eq_sum (s := {p, m}), Finset.sum_pair hpm]
  · simp [p, m]
  · intro n hn
    have hp : (n : ℤ) ≠ 1 := by
      intro h
      have he : n = p := Subtype.ext h
      exact hn (by simp [he])
    have hm : (n : ℤ) ≠ -1 := by
      intro h
      have he : n = m := Subtype.ext h
      exact hn (by simp [he])
    have hn₀ := n.property
    have hfar : (n : ℤ) ≤ -2 ∨ 2 ≤ (n : ℤ) := by omega
    have habs : (2 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
      rcases hfar with h | h
      · have h' : ((n : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h
        exact (by linarith : (2 : ℝ) ≤ -((n : ℤ) : ℝ)).trans (neg_le_abs _)
      · exact (by exact_mod_cast h : (2 : ℝ) ≤ ((n : ℤ) : ℝ)).trans (le_abs_self _)
    apply hb
    rw [abs_mul, abs_of_pos (zero_lt_one.trans hu)]
    exact habs.trans (le_mul_of_one_le_left (abs_nonneg _) hu.le)

-- A smooth unit-mass bump with a prescribed support ball.
private theorem exists_unitMass_bump (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ f : 𝓢(ℝ, ℂ), Function.support (f : ℝ → ℂ) = Metric.ball c r ∧
      HasCompactSupport (f : ℝ → ℂ) ∧ (∫ x : ℝ, f x) = 1 := by
  let β : ContDiffBump c := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let F (x : ℝ) : ℂ := β.normed volume x
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp β.contDiff_normed
  have hFc : HasCompactSupport F := β.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  refine ⟨hFc.toSchwartzMap hF, ?_, hFc, ?_⟩
  · rw [← β.support_normed_eq (μ := volume)]
    ext x
    exact Complex.ofReal_ne_zero
  · exact (integral_ofReal (f := β.normed volume)).trans
      ((congrArg Complex.ofReal β.integral_normed).trans Complex.ofReal_one)

-- Subtract two unit-mass bumps. The first centre is an explicit nonzero evaluation point.
private theorem exists_zeroMass_bump {a b : ℝ} (hab : a < b) :
    ∃ (p : 𝓢(ℝ, ℂ)) (u : ℝ), u ∈ Ioo a b ∧ p u ≠ 0 ∧
      (∀ x ∉ Ioo a b, p x = 0) ∧ HasCompactSupport (p : ℝ → ℂ) ∧
      (∫ x : ℝ, p x) = 0 := by
  let u := a + (b - a) / 4
  let v := b - (b - a) / 4
  let r := (b - a) / 8
  have hr : 0 < r := by dsimp [r]; linarith
  obtain ⟨f, hfs, hfc, hfi⟩ := exists_unitMass_bump u hr
  obtain ⟨g, hgs, hgc, hgi⟩ := exists_unitMass_bump v hr
  refine ⟨f - g, u, ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩, ?_, ?_, hfc.sub hgc, ?_⟩
  · have hfu : u ∈ Function.support (f : ℝ → ℂ) := hfs.symm ▸ Metric.mem_ball_self hr
    have hgu : u ∉ Function.support (g : ℝ → ℂ) := by
      rw [hgs, Metric.mem_ball, Real.dist_eq]
      intro h
      have := (abs_lt.mp h).1
      dsimp [u, v, r] at this
      linarith
    change f u - g u ≠ 0
    rw [Function.notMem_support.mp hgu, sub_zero]
    exact hfu
  · intro x hx
    have hsubset (c : ℝ) (ha : a ≤ c - r) (hb : c + r ≤ b) :
        Metric.ball c r ⊆ Ioo a b := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hf : x ∉ Function.support (f : ℝ → ℂ) := by
      rw [hfs]
      exact fun h ↦ hx (hsubset u (by dsimp [u, r]; linarith) (by dsimp [u, r]; linarith) h)
    have hg : x ∉ Function.support (g : ℝ → ℂ) := by
      rw [hgs]
      exact fun h ↦ hx (hsubset v (by dsimp [v, r]; linarith) (by dsimp [v, r]; linarith) h)
    change f x - g x = 0
    rw [Function.notMem_support.mp hf, Function.notMem_support.mp hg, sub_self]
  · change (∫ x : ℝ, f x - g x) = 0
    rw [integral_sub f.integrable g.integrable, hfi, hgi, sub_self]

private theorem exists_even_twoMoment_bump {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (q : RationalThetaInput) (u : ℝ), u ∈ Ioo a b ∧ q.val u ≠ 0 ∧
      Function.Even (q.val : ℝ → ℂ) ∧ HasCompactSupport (q.val : ℝ → ℂ) ∧
      ∀ x : ℝ, |x| ∉ Ioo a b → q.val x = 0 := by
  obtain ⟨p, u, hu, hpu, hp, hpC, hpM⟩ := exists_zeroMass_bump hab
  let g (x : ℝ) : ℂ := p x + p (-x)
  have hnegC : HasCompactSupport (fun x : ℝ ↦ p (-x)) :=
    hpC.comp_homeomorph (Homeomorph.neg ℝ)
  have hC : HasCompactSupport g := hpC.add hnegC
  let q := hC.toSchwartzMap ((p.smooth ⊤).add ((p.smooth ⊤).comp contDiff_neg))
  have hq (x : ℝ) : q x = g x := rfl
  have hEven : Function.Even (q : ℝ → ℂ) := by
    intro x
    simp only [hq, g, neg_neg, add_comm]
  have hpos (x : ℝ) (hx : 0 ≤ x) : q x = p x := by
    have hnx : -x ∉ Ioo a b := fun h ↦ (not_lt_of_ge (by linarith : -x ≤ a)) h.1
    change p x + p (-x) = p x
    rw [hp _ hnx, add_zero]
  have hq0 : q 0 = 0 := by
    rw [hpos 0 le_rfl, hp _ (fun h ↦ (not_lt_of_ge ha) h.1)]
  have hqF : (𝓕 q) 0 = 0 := by
    rw [congrFun (SchwartzMap.fourier_coe q) 0, Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_smul, hq, g]
    have hi : Integrable (fun x : ℝ ↦ p (-x)) :=
      (p.continuous.comp continuous_neg).integrable_of_hasCompactSupport hnegC
    rw [integral_add p.integrable hi, integral_neg_eq_self, hpM, add_zero]
  refine ⟨⟨q, hq0, hqF⟩, u, hu, ?_, hEven, hC, ?_⟩
  · rwa [hpos u (ha.trans hu.1.le)]
  · intro x hx
    have hxq : q |x| = q x := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, hEven x]
    rw [← hxq, hpos |x| (abs_nonneg x), hp _ hx]

-- A diagonal matrix of point evaluations detects every finite linear relation.
private theorem linearIndependent_of_diagonal_eval {X : Type*} (f : ℕ → X → ℂ) (u : ℕ → X)
    (hne : ∀ i, f i (u i) ≠ 0) (hoff : ∀ i j, j ≠ i → f j (u i) = 0) :
    LinearIndependent ℂ f := by
  classical
  refine linearIndependent_iff'.mpr fun s c h i hi ↦ ?_
  have he := congrFun h (u i)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at he
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [hoff i j hji, smul_zero])
    (fun hni ↦ (hni hi).elim), smul_eq_mul] at he
  exact (mul_eq_zero.mp he).resolve_right (hne i)

/-- There are infinitely many complex-linearly independent actual rational theta
images of even, compactly supported two-moment Schwartz inputs. Independence
holds already on the positive norm line (in logarithmic coordinates), and
the absolutely convergent Mellin samples vanish at all open-critical-strip
zeta zeros. -/
public theorem exists_rationalTheta_linearlyIndependent_mellin_null :
    ∃ b : ℕ → RationalThetaInput,
      (∀ n, Function.Even ((b n).val : ℝ → ℂ) ∧ HasCompactSupport ((b n).val : ℝ → ℂ)) ∧
      LinearIndependent ℂ (fun n ↦ rationalTheta (b n).val) ∧
      LinearIndependent ℂ (fun n x ↦ rationalTheta (b n).val (Real.exp x)) ∧
      ∀ (n : ℕ) (z : ℂ), 0 < z.re → z.re < 1 → riemannZeta z = 0 →
        Integrable (fun x : ℝ ↦ rationalTheta (b n).val (Real.exp x) * Complex.exp (z * x)) ∧
        (∫ x : ℝ, rationalTheta (b n).val (Real.exp x) * Complex.exp (z * x)) = 0 := by
  classical
  -- The intervals between successive dyadic endpoints are disjoint and lie in `(1, 2)`.
  let e (n : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ n
  have he : StrictAnti e := fun _ _ h ↦
    add_lt_add_right (pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) h) 1
  have he₁ (n : ℕ) : 1 < e n := by dsimp [e]; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  have he₂ (n : ℕ) : e n ≤ 2 := (he.antitone (Nat.zero_le n)).trans (by norm_num [e])
  choose b u hu hbu hEven hCompact hs using fun n : ℕ ↦
    exists_even_twoMoment_bump (zero_lt_one.trans (he₁ (n + 1))).le (he (Nat.lt_succ_self n))
  have hθ (i : ℕ) {t : ℝ} (ht : 1 < t) : rationalTheta (b i).val t = 2 * (b i).val t := by
    rw [rationalTheta_eq_add_neg_of_one_lt _ (fun x hx ↦ hs i x (fun h ↦
      (not_lt_of_ge ((he₂ i).trans hx)) h.2)) ht, hEven i t, two_mul]
  have hu₁ (i : ℕ) : 1 < u i := (he₁ (i + 1)).trans (hu i).1
  have hd (i : ℕ) : rationalTheta (b i).val (u i) ≠ 0 := by
    rw [hθ i (hu₁ i)]
    exact mul_ne_zero (by norm_num) (hbu i)
  have ho (i j : ℕ) (hji : j ≠ i) : rationalTheta (b j).val (u i) = 0 := by
    rw [hθ j (hu₁ i), hs j _ ?_, mul_zero]
    rw [abs_of_pos (zero_lt_one.trans (hu₁ i))]
    intro h
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · exact (not_lt_of_ge ((he.antitone (Nat.succ_le_of_lt hlt)).trans' (hu i).2.le)) h.1
    · exact (not_lt_of_ge ((he.antitone (Nat.succ_le_of_lt hgt)).trans (hu i).1.le)) h.2
  refine ⟨b, fun n ↦ ⟨hEven n, hCompact n⟩, linearIndependent_of_diagonal_eval _ u hd ho, ?_, ?_⟩
  · have hexp (i : ℕ) : Real.exp (Real.log (u i)) = u i :=
      Real.exp_log (zero_lt_one.trans (hu₁ i))
    apply linearIndependent_of_diagonal_eval _ (fun i ↦ Real.log (u i))
    · simpa only [hexp] using hd
    · simpa only [hexp] using ho
  · intro n z hpos hlt hz
    exact ⟨(hasDerivAt_rationalTheta_mellin _ (b n).property.1 (b n).property.2 z).1,
      rationalTheta_mellin_eq_zero_of_zeta_zero _ (b n).property.1 (b n).property.2 hpos hlt hz⟩

end Masullo
