module

public import Lemmas.DetectorCoefficientRatios
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Closed-disk and coefficient bounds for the detector

Source: `0e672a90:.godel/bob/separated-signed-tuples.md:15–27`, equation (2).
Consumer: `8fd18679:Proofs/Lemmas/DetectorCoefficientRatios.lean`,
`finite_ratio_bounds` (`hhigher`), for the detector in
`6fe747e1:.godel/bob/detection-radius.md:19–29`.
Owning check session: `01a209a4-4028-76c1-a295-487f5bedcbac`.

For the actual independence polynomial on finite natural starts, the degree
counts distinct starts at distance at most the cutoff. With real activities
bounded by the original weights, the disk argument uses the full mass
`∑ p ∈ starts, w p`, not a probability normalization or a degree-weighted mass.
The Cauchy estimate is transferred to the real formal quotient defining `b`.
The detector's separate quadratic improvement is unchanged.
-/

open scoped BigOperators

namespace DetectorCoefficientDisk

open SeparationQuadraticCost (independentSets independencePolynomial startDistance)

private noncomputable def far (s : Finset ℕ) (R : ℝ) (p : ℕ) : Finset ℕ := by
  classical
  exact s.filter fun q ↦ R < startDistance p q

private theorem mem_far {s : Finset ℕ} {R : ℝ} {p q : ℕ} :
    q ∈ far s R p ↔ q ∈ s ∧ R < startDistance p q := by
  classical
  exact Finset.mem_filter

private theorem notMem_far_self {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R) (p : ℕ) :
    p ∉ far s R p := by
  simp [mem_far, startDistance, not_lt.mpr hR]

private theorem far_subset_erase {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R) (p : ℕ) :
    far s R p ⊆ s.erase p := by
  intro q hq
  exact Finset.mem_erase.mpr ⟨fun h ↦ notMem_far_self hR p (h ▸ hq), (mem_far.mp hq).1⟩

private theorem mem_independent {s I : Finset ℕ} {R : ℝ} :
    I ∈ independentSets s R ↔ I ⊆ s ∧
      ∀ p ∈ I, ∀ q ∈ I, p ≠ q → R < startDistance p q := by
  classical
  simp [independentSets]

-- Inserting the marked vertex bijects the independent sets in the two sums.
private theorem sum_with_vertex {M : Type*} [AddCommMonoid M] {s : Finset ℕ} {R : ℝ}
    (hR : 0 ≤ R) {p : ℕ} (hp : p ∈ s) (g : Finset ℕ → M) :
    ∑ I ∈ (independentSets s R).filter (fun I ↦ p ∈ I), g I =
      ∑ J ∈ independentSets (far s R p) R, g (insert p J) := by
  classical
  symm
  refine Finset.sum_nbij' (insert p) (fun I ↦ I.erase p) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro J hJ
    obtain ⟨hs, hsep⟩ := mem_independent.mp hJ
    have hfar (q : ℕ) (hq : q ∈ J) := mem_far.mp (hs hq)
    refine Finset.mem_filter.mpr ⟨mem_independent.mpr ⟨?_, ?_⟩, Finset.mem_insert_self ..⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact (hfar q hq).1
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hae | haJ
      · subst a
        exact (hfar b ((Finset.mem_insert.mp hb).resolve_left hab.symm)).2
      · rcases Finset.mem_insert.mp hb with hbe | hbJ
        · subst b
          simpa only [startDistance, abs_sub_comm (a : ℝ)] using (hfar a haJ).2
        · exact hsep a haJ b hbJ hab
  · intro I hI
    obtain ⟨hI, hpI⟩ := Finset.mem_filter.mp hI
    obtain ⟨hs, hsep⟩ := mem_independent.mp hI
    refine mem_independent.mpr ⟨?_, fun a ha b hb ↦ hsep a (Finset.mem_of_mem_erase ha) b
      (Finset.mem_of_mem_erase hb)⟩
    intro q hq
    obtain ⟨hne, hqI⟩ := Finset.mem_erase.mp hq
    exact mem_far.mpr ⟨hs hqI, hsep p hpI q hqI hne.symm⟩
  · intro J hJ
    exact Finset.erase_insert (fun hpJ ↦ notMem_far_self hR p ((mem_independent.mp hJ).1 hpJ))
  · intro I hI
    exact Finset.insert_erase ((Finset.mem_filter.mp hI).2)

open Polynomial in
private theorem deletion {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R) (x : ℕ → ℝ)
    {p : ℕ} (hp : p ∈ s) :
    independencePolynomial s R x = independencePolynomial (s.erase p) R x +
      monomial 1 (x p) * independencePolynomial (far s R p) R x := by
  classical
  unfold independencePolynomial
  let g (I : Finset ℕ) := monomial I.card (∏ q ∈ I, x q)
  change ∑ I ∈ independentSets s R, g I = _
  rw [← Finset.sum_filter_add_sum_filter_not (independentSets s R) (fun I ↦ p ∈ I) g,
    sum_with_vertex hR hp, add_comm, Finset.mul_sum]
  congr 1
  · congr 1
    ext I
    simp only [Finset.mem_filter, mem_independent]
    constructor
    · rintro ⟨⟨hs, hsep⟩, hn⟩
      exact ⟨fun q hq ↦ Finset.mem_erase.mpr ⟨fun h ↦ hn (h ▸ hq), hs hq⟩, hsep⟩
    · rintro ⟨hs, hsep⟩
      exact ⟨⟨fun q hq ↦ Finset.mem_of_mem_erase (hs hq), hsep⟩,
        fun h ↦ (Finset.mem_erase.mp (hs h)).1 rfl⟩
  · refine Finset.sum_congr rfl fun J hJ ↦ ?_
    have hn : p ∉ J := fun h ↦ notMem_far_self hR p ((mem_independent.mp hJ).1 h)
    simp [g, Finset.card_insert_of_notMem hn, Finset.prod_insert hn, monomial_mul_monomial,
      Nat.add_comm]

open Polynomial in
private theorem marked_derivative (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (x : ℕ → ℝ) :
    (independencePolynomial s R x).derivative =
      ∑ p ∈ s, C (x p) * independencePolynomial (far s R p) R x := by
  classical
  let g (I : Finset ℕ) := monomial (I.card - 1) (∏ q ∈ I, x q)
  calc
    _ = ∑ I ∈ independentSets s R, ∑ _p ∈ I, g I := by
      rw [independencePolynomial, derivative_sum]
      refine Finset.sum_congr rfl fun I _ ↦ ?_
      dsimp only [g]
      rw [derivative_monomial, Finset.sum_const, ← map_nsmul, nsmul_eq_mul, mul_comm]
    _ = ∑ I ∈ independentSets s R, ∑ p ∈ s, if p ∈ I then g I else 0 := by
      refine Finset.sum_congr rfl fun I hI ↦ ?_
      rw [← Finset.sum_filter]
      congr 1
      ext p
      exact ⟨fun hp ↦ Finset.mem_filter.mpr ⟨(mem_independent.mp hI).1 hp, hp⟩,
        fun hp ↦ (Finset.mem_filter.mp hp).2⟩
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_filter]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [sum_with_vertex hR hp, independencePolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun J hJ ↦ ?_
      have hn : p ∉ J := fun h ↦ notMem_far_self hR p ((mem_independent.mp hJ).1 h)
      simp [g, Finset.card_insert_of_notMem hn, Finset.prod_insert hn, C_mul_monomial]

private theorem pow_mul_sdiff_le {a : ℝ} (ha : 0 ≤ a) (f : Finset ℕ → ℝ)
    (s d : Finset ℕ) (hd : d ⊆ s)
    (hstep : ∀ t ⊆ s, ∀ p ∈ t, a * f (t.erase p) ≤ f t) :
    a ^ d.card * f (s \ d) ≤ f s := by
  classical
  induction d using Finset.induction_on with
  | empty => simp
  | insert p d hp ih =>
    have hpe : p ∈ s \ d := Finset.mem_sdiff.mpr ⟨hd (by simp), hp⟩
    have he : s \ insert p d = (s \ d).erase p := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    rw [he, Finset.card_insert_of_notMem hp, pow_succ, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hstep _ Finset.sdiff_subset p hpe) (pow_nonneg ha _)).trans
      (ih (fun q hq ↦ hd (Finset.mem_insert_of_mem hq)))

private theorem polynomial_empty (R : ℝ) (x : ℕ → ℝ) :
    independencePolynomial ∅ R x = 1 := by
  classical
  have h : independentSets ∅ R = {∅} := by
    ext I
    simp only [mem_independent, Finset.mem_singleton, Finset.subset_empty]
    constructor
    · exact And.left
    · rintro rfl
      simp
  simp [independencePolynomial, h]

/-- Closed-disk nonvanishing and the log-derivative estimate in Bob's proof of (2).
The degree bound is on the actual graph of distinct close starts. -/
public theorem nonvanishing_and_logDerivative_bound
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (x w : ℕ → ℝ) (Δ : ℕ) {wStar B : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hx : ∀ p ∈ starts, |x p| ≤ w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hB : 0 < B) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / B) :
    let P := (independencePolynomial starts R x).map Complex.ofRealHom
    P.eval z ≠ 0 ∧ ‖P.derivative.eval z / P.eval z‖ ≤ 4 * ∑ p ∈ starts, w p := by
  classical
  let E (s : Finset ℕ) := (independencePolynomial s R x).eval₂ Complex.ofRealHom z
  simp only [Polynomial.eval_map, Polynomial.derivative_map]
  change E starts ≠ 0 ∧
    ‖((independencePolynomial starts R x).derivative.eval₂ Complex.ofRealHom z) / E starts‖ ≤ _
  by_cases hne : starts.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp [E, polynomial_empty]
  obtain ⟨p, hp⟩ := hne
  have hw₀ (p : ℕ) (hp : p ∈ starts) : 0 ≤ w p := (abs_nonneg _).trans (hx p hp)
  have hstar : 0 ≤ wStar := (hw₀ p hp).trans (hw p hp)
  let t := 2 * ‖z‖ * wStar
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsmall : ((Δ : ℝ) + 1) * t ≤ 1 / 4 := by
    have hzB := (le_div_iff₀ hB).mp hz
    have h := mul_le_mul_of_nonneg_left hscale (norm_nonneg z)
    dsimp [t]
    nlinarith only [hzB, h]
  have ht' : t ≤ 1 / 4 := by
    nlinarith only [hsmall, mul_nonneg (Nat.cast_nonneg (α := ℝ) Δ) ht]
  have ha : 0 < 1 - t := by linarith
  have half_le (d : ℕ) (hd : d ≤ Δ) : 1 / 2 ≤ (1 - t) ^ d := by
    have hd' : (d : ℝ) ≤ (Δ : ℝ) + 1 := by exact_mod_cast (hd.trans (Nat.le_succ Δ))
    have hm := mul_le_mul_of_nonneg_right hd' ht
    have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1 - t by linarith) d
    linarith only [hm, hb, hsmall, show 1 - t - 1 = -t by ring]
  -- Induct on the induced subgraph. The one-step lower bound telescopes over
  -- the neighbors of a vertex, using exclusively strictly smaller subgraphs.
  have bounds (s : Finset ℕ) (hs : s ⊆ starts) : E s ≠ 0 ∧
      ∀ p ∈ s, (1 - t) * ‖E (s.erase p)‖ ≤ ‖E s‖ ∧
        ‖E (far s R p)‖ ≤ 2 * ‖E (s.erase p)‖ := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      have step (p : ℕ) (hp : p ∈ s) :
          (1 - t) * ‖E (s.erase p)‖ ≤ ‖E s‖ ∧
            ‖E (far s R p)‖ ≤ 2 * ‖E (s.erase p)‖ := by
        let d := (s.erase p).filter (fun q ↦ startDistance p q ≤ R)
        have hd : d ⊆ s.erase p := Finset.filter_subset _ _
        have hsub : s.erase p ⊆ starts.erase p := by
          intro q hq
          obtain ⟨hne, hqs⟩ := Finset.mem_erase.mp hq
          exact Finset.mem_erase.mpr ⟨hne, hs hqs⟩
        have hcard : d.card ≤ Δ := (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans
          (hdeg p (hs hp))
        have he : s.erase p \ d = far s R p := by
          ext q
          simp only [d, Finset.mem_sdiff, Finset.mem_filter, mem_far]
          have hf := far_subset_erase (s := s) hR p
          constructor
          · rintro ⟨hq, hn⟩
            exact ⟨Finset.mem_of_mem_erase hq, lt_of_not_ge (fun h ↦ hn ⟨hq, h⟩)⟩
          · intro hq
            exact ⟨hf (mem_far.mpr hq), fun h ↦ (not_le_of_gt hq.2) h.2⟩
        have htel := pow_mul_sdiff_le ha.le (fun u ↦ ‖E u‖) (s.erase p) d hd
          (fun u hu q hq ↦ ((ih u (lt_of_le_of_lt hu (Finset.erase_ssubset hp))
            (hu.trans ((Finset.erase_subset p s).trans hs))).2 q hq).1)
        rw [he] at htel
        have hfar : ‖E (far s R p)‖ ≤ 2 * ‖E (s.erase p)‖ := by
          have hh := mul_le_mul_of_nonneg_right (half_le _ hcard) (norm_nonneg (E (far s R p)))
          linarith only [hh, htel]
        have hdelta : E s - E (s.erase p) = z * (x p : ℂ) * E (far s R p) := by
          dsimp [E]
          rw [deletion hR x hp]
          simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_monomial, mul_comm z]
        have hnorm : ‖E s - E (s.erase p)‖ ≤ t * ‖E (s.erase p)‖ := by
          rw [hdelta, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            _ ≤ ‖z‖ * wStar * (2 * ‖E (s.erase p)‖) := by
              gcongr
              exact (hx p (hs hp)).trans (hw p (hs hp))
            _ = _ := by dsimp [t]; ring
        refine ⟨?_, hfar⟩
        have htri := norm_sub_norm_le (E (s.erase p)) (E s)
        rw [norm_sub_rev] at htri
        linarith only [htri, hnorm]
      refine ⟨?_, step⟩
      by_cases he : s.Nonempty
      · obtain ⟨p, hp⟩ := he
        have hn := (ih (s.erase p) (Finset.erase_ssubset hp) ((Finset.erase_subset p s).trans hs)).1
        exact norm_pos_iff.mp ((mul_pos ha (norm_pos_iff.mpr hn)).trans_le (step p hp).1)
      · rw [Finset.not_nonempty_iff_eq_empty.mp he]
        simp [E, polynomial_empty]
  obtain ⟨hn, hs⟩ := bounds starts (fun _ h ↦ h)
  refine ⟨hn, ?_⟩
  rw [marked_derivative starts hR x, Polynomial.eval₂_finsetSum, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).2
  calc
    _ ≤ ∑ p ∈ starts, w p * (4 * ‖E starts‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, norm_mul]
      change ‖(x p : ℂ)‖ * ‖E (far starts R p)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hh := (hs p hp).1
      have hh' : (1 / 2) * ‖E (starts.erase p)‖ ≤ ‖E starts‖ :=
        (mul_le_mul_of_nonneg_right (by linarith : 1 / 2 ≤ 1 - t) (norm_nonneg _)).trans hh
      have hh'' : ‖E (far starts R p)‖ ≤ 4 * ‖E starts‖ := by
        linarith only [(hs p hp).2, hh']
      exact mul_le_mul (hx p hp) hh'' (norm_nonneg _) (hw₀ p hp)
    _ = _ := by rw [← Finset.sum_mul]; ring

-- Coefficients of the analytic germ in the ordinary (not exponential) convention.
private noncomputable def taylor (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ iteratedDeriv n f 0 / (n.factorial : ℂ)

private theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (f * g) = taylor f * taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k ↦ iteratedDeriv i f 0 / (i.factorial : ℂ) *
        (iteratedDeriv k g 0 / (k.factorial : ℂ))), Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hi₀ : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hni : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  field_simp
  linear_combination (iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) * hfac

private theorem taylor_poly (p : Polynomial ℂ) : taylor p.eval = (p : PowerSeries ℂ) := by
  have hd (n : ℕ) (q : Polynomial ℂ) :
      iteratedDeriv n q.eval = ((⇑Polynomial.derivative)^[n] q).eval := by
    induction n generalizing q with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ', Function.iterate_succ_apply, ← ih q.derivative]
      exact congrArg (iteratedDeriv n) (funext fun z ↦ (q.hasDerivAt z).deriv)
  ext n
  rw [taylor, PowerSeries.coeff_mk, Polynomial.coeff_coe, hd]
  change ((⇑Polynomial.derivative)^[n] p).eval 0 / (n.factorial : ℂ) = p.coeff n
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [nsmul_eq_mul, Nat.descFactorial_self, Nat.factorial_ne_zero]

private theorem norm_taylor_coeff_le {f : ℂ → ℂ} {B M : ℝ} (hB : 0 < B)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / B)))
    (hb : ∀ z : ℂ, ‖z‖ ≤ 1 / B → ‖f z‖ ≤ M) (n : ℕ) :
    ‖PowerSeries.coeff n (taylor f)‖ ≤ M * B ^ n := by
  let r : NNReal := ⟨1 / B, by positivity⟩
  have hr : 0 < r := by exact one_div_pos.mpr hB
  have hs := (hd.hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have he := hs.eq_formalMultilinearSeries hs.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) he
  rw [FormalMultilinearSeries.coeff_ofScalars] at hc
  rw [taylor, PowerSeries.coeff_mk, ← hc]
  change ‖cauchyPowerSeries f 0 (1 / B) n (fun _ ↦ 1)‖ ≤ _
  rw [cauchyPowerSeries_apply]
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z : ℂ ↦ (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z) (c := 0)
    (C := B ^ n * B * M) (show 0 ≤ 1 / B by positivity) (by
      intro z hz
      have hz' : ‖z‖ = 1 / B := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_inv, hz', one_div, inv_inv]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb z hz'.le) (by positivity))
  refine h.trans_eq ?_
  field_simp

-- Multiplying by the polynomial identifies the analytic germ with the real
-- formal quotient after coefficientwise complexification.
private theorem taylor_quotient (p : Polynomial ℝ) {r : ℝ} (hr : 0 < r)
    (hn : ∀ z : ℂ, ‖z‖ ≤ r → (p.map Complex.ofRealHom).eval z ≠ 0) :
    let q := p.map Complex.ofRealHom
    taylor (fun z ↦ q.derivative.eval z / q.eval z) =
      PowerSeries.map Complex.ofRealHom (PowerSeries.derivative (p : PowerSeries ℝ) *
        (p : PowerSeries ℝ)⁻¹) := by
  let q := p.map Complex.ofRealHom
  let f (z : ℂ) := q.derivative.eval z / q.eval z
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 r) :=
    q.derivative.differentiable.differentiableOn.div q.differentiable.differentiableOn
      (fun z hz ↦ hn z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz))
  have hq : AnalyticAt ℂ q.eval 0 := q.differentiable.analyticAt _
  have hf : AnalyticAt ℂ f 0 := hd.analyticAt (Metric.closedBall_mem_nhds _ hr)
  have he : f * q.eval =ᶠ[nhds 0] q.derivative.eval := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with z hz
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact div_mul_cancel₀ _ (hn z hz')
  have hprod : taylor f * (q : PowerSeries ℂ) = (q.derivative : PowerSeries ℂ) := by
    rw [← taylor_poly q, ← taylor_mul hf hq, ← taylor_poly]
    ext n
    simp only [taylor, PowerSeries.coeff_mk, he.iteratedDeriv_eq n]
  have hq₀ : PowerSeries.constantCoeff (q : PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
    exact hn 0 (by simpa using hr.le)
  have hp₀ : PowerSeries.constantCoeff (p : PowerSeries ℝ) ≠ 0 := by
    intro hp₀
    apply hq₀
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map]
    change Complex.ofRealHom (PowerSeries.constantCoeff (p : PowerSeries ℝ)) = 0
    rw [hp₀, map_zero]
  have hreal : (PowerSeries.derivative (p : PowerSeries ℝ) * (p : PowerSeries ℝ)⁻¹) *
      (p : PowerSeries ℝ) = (p.derivative : PowerSeries ℝ) := by
    rw [mul_assoc, mul_comm ((p : PowerSeries ℝ)⁻¹), PowerSeries.mul_inv_cancel _ hp₀,
      mul_one, PowerSeries.derivative_coe]
  let F := PowerSeries.map Complex.ofRealHom
    (PowerSeries.derivative (p : PowerSeries ℝ) * (p : PowerSeries ℝ)⁻¹)
  have hmap : F * (q : PowerSeries ℂ) = (q.derivative : PowerSeries ℂ) := by
    simpa only [F, q, map_mul, Polynomial.derivative_map, Polynomial.polynomial_map_coe] using
      congrArg (PowerSeries.map Complex.ofRealHom) hreal
  change taylor f = F
  have h := congrArg (fun g : PowerSeries ℂ ↦ g * (q : PowerSeries ℂ)⁻¹) (hprod.trans hmap.symm)
  simpa only [mul_assoc, PowerSeries.mul_inv_cancel _ hq₀, mul_one] using h

/-- Equation (2) for the detector's actual coefficient `b`, the degree-`j - 1`
coefficient of the formal logarithmic derivative. In particular, this supplies
`hhigher` in `DetectorCoefficientRatios.finite_ratio_bounds` at any order. -/
public theorem abs_b_le
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (x w : ℕ → ℝ) (Δ : ℕ) {wStar B : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hx : ∀ p ∈ starts, |x p| ≤ w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hB : 0 < B) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B) (j : ℕ) (hj : 1 ≤ j) :
    |DetectorCoefficientRatios.b starts R x j| ≤ 4 * (∑ p ∈ starts, w p) * B ^ (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  let p := independencePolynomial starts R x
  let q := p.map Complex.ofRealHom
  let f (z : ℂ) := q.derivative.eval z / q.eval z
  have hb z hz := nonvanishing_and_logDerivative_bound starts hR x w Δ hdeg hx hw hB hscale z hz
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / B)) :=
    q.derivative.differentiable.differentiableOn.div q.differentiable.differentiableOn
      (fun z hz ↦ (hb z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)).1)
  have hc := norm_taylor_coeff_le hB hd (fun z hz ↦ (hb z hz).2) k
  have ht := taylor_quotient p (one_div_pos.mpr hB) (fun z hz ↦ (hb z hz).1)
  rw [ht, PowerSeries.coeff_map] at hc
  change ‖(DetectorCoefficientRatios.b starts R x (k + 1) : ℂ)‖ ≤ _ at hc
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.succ_sub_one] using hc

end DetectorCoefficientDisk
