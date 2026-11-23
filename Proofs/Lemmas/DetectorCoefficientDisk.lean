module

public import Lemmas.DetectorCoefficientRatios
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Closed-disk and coefficient bounds for the detector

Sources: `0e672a90:.godel/bob/separated-signed-tuples.md:15–27`, equation (2),
and `78091476:.godel/bob/balanced-height-reconstruction.md:25–42`.
Consumers: the balanced reconstruction's cubic logarithmic tail at lines 34–40,
and `DetectorCoefficientRatios.finite_ratio_bounds` (`hhigher`) for the real
detector in `6fe747e1:.godel/bob/detection-radius.md:19–29`.
Owning check sessions: `01a209ce-61c0-7258-9ef8-09cad8ad12db` (complex extension),
`01a209a4-4028-76c1-a295-487f5bedcbac` (real detector).

The degree counts distinct starts at distance at most the cutoff. The deletion
argument uses the full mass `∑ p ∈ starts, w p`, not a probability normalization
or degree-weighted mass. On the ray with complex activities `y`, degree `j`
in the auxiliary variable is homogeneous degree `j` in the activities: each
monomial has one activity per selected start. We estimate the formal log of
this polynomial (constant term zero), by Cauchy's bound on its analytic
logarithmic derivative. We also preserve the real detector's API. No saddle
construction or estimate of its remainder integral is asserted here.
-/

open scoped BigOperators

namespace DetectorCoefficientDisk

open SeparationQuadraticCost (independentSets independencePolynomial startDistance)

/-- The actual distance-conflict independence polynomial on the ray `z ↦ z y`. -/
@[expose] public noncomputable def complexIndependencePolynomial
    (starts : Finset ℕ) (R : ℝ) (y : ℕ → ℂ) : Polynomial ℂ :=
  ∑ I ∈ independentSets starts R, Polynomial.monomial I.card (∏ p ∈ I, y p)

private theorem complexIndependencePolynomial_ofReal (starts : Finset ℕ) (R : ℝ)
    (x : ℕ → ℝ) :
    complexIndependencePolynomial starts R (fun p ↦ (x p : ℂ)) =
      (independencePolynomial starts R x).map Complex.ofRealHom := by
  simp only [complexIndependencePolynomial, independencePolynomial, Polynomial.map_sum,
    Polynomial.map_monomial, map_prod]
  rfl

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
private theorem deletion {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R) (x : ℕ → ℂ)
    {p : ℕ} (hp : p ∈ s) :
    complexIndependencePolynomial s R x = complexIndependencePolynomial (s.erase p) R x +
      monomial 1 (x p) * complexIndependencePolynomial (far s R p) R x := by
  classical
  unfold complexIndependencePolynomial
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
private theorem marked_derivative (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (x : ℕ → ℂ) :
    (complexIndependencePolynomial s R x).derivative =
      ∑ p ∈ s, C (x p) * complexIndependencePolynomial (far s R p) R x := by
  classical
  let g (I : Finset ℕ) := monomial (I.card - 1) (∏ q ∈ I, x q)
  calc
    _ = ∑ I ∈ independentSets s R, ∑ _p ∈ I, g I := by
      rw [complexIndependencePolynomial, derivative_sum]
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
      rw [sum_with_vertex hR hp, complexIndependencePolynomial, Finset.mul_sum]
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

private theorem polynomial_empty (R : ℝ) (x : ℕ → ℂ) :
    complexIndependencePolynomial ∅ R x = 1 := by
  classical
  have h : independentSets ∅ R = {∅} := by
    ext I
    simp only [mem_independent, Finset.mem_singleton, Finset.subset_empty]
    constructor
    · exact And.left
    · rintro rfl
      simp
  simp [complexIndependencePolynomial, h]

private theorem complex_disk
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (x : ℕ → ℂ) (w : ℕ → ℝ) (Δ : ℕ) {wStar B : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hx : ∀ p ∈ starts, ‖x p‖ ≤ w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hB : 0 < B) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / B) :
    let P := complexIndependencePolynomial starts R x
    P.eval z ≠ 0 ∧ ‖P.derivative.eval z / P.eval z‖ ≤ 4 * ∑ p ∈ starts, w p := by
  classical
  let E (s : Finset ℕ) := (complexIndependencePolynomial s R x).eval z
  change E starts ≠ 0 ∧
    ‖(complexIndependencePolynomial starts R x).derivative.eval z / E starts‖ ≤ _
  by_cases hne : starts.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp [E, polynomial_empty]
  obtain ⟨p, hp⟩ := hne
  have hw₀ (p : ℕ) (hp : p ∈ starts) : 0 ≤ w p := (norm_nonneg _).trans (hx p hp)
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
        have hdelta : E s - E (s.erase p) = z * x p * E (far s R p) := by
          dsimp [E]
          rw [deletion hR x hp]
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_monomial, mul_comm z]
        have hnorm : ‖E s - E (s.erase p)‖ ≤ t * ‖E (s.erase p)‖ := by
          rw [hdelta, norm_mul, norm_mul]
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
  rw [marked_derivative starts hR x, Polynomial.eval_finsetSum, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).2
  calc
    _ ≤ ∑ p ∈ starts, w p * (4 * ‖E starts‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_C, norm_mul]
      change ‖x p‖ * ‖E (far starts R p)‖ ≤ _
      have hh := (hs p hp).1
      have hh' : (1 / 2) * ‖E (starts.erase p)‖ ≤ ‖E starts‖ :=
        (mul_le_mul_of_nonneg_right (by linarith : 1 / 2 ≤ 1 - t) (norm_nonneg _)).trans hh
      have hh'' : ‖E (far starts R p)‖ ≤ 4 * ‖E starts‖ := by
        linarith only [(hs p hp).2, hh']
      exact mul_le_mul (hx p hp) hh'' (norm_nonneg _) (hw₀ p hp)
    _ = _ := by rw [← Finset.sum_mul]; ring

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
  simpa only [complexIndependencePolynomial_ofReal] using
    complex_disk starts hR (fun p ↦ (x p : ℂ)) w Δ hdeg
      (fun p hp ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx p hp)
      hw hB hscale z hz

/-- Closed-disk nonvanishing and control of `P′/P` for the scaled complex activities.
The full unnormalized mass appears in the bound. -/
public theorem complex_nonvanishing_and_logDerivative_bound
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) (w : ℕ → ℝ) (Δ : ℕ)
    {wStar B₀ L : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hy : ∀ p ∈ starts, ‖y p‖ ≤ L * w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hL : 0 < L) (hB₀ : 0 < B₀) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B₀)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / (L * B₀)) :
    let P := complexIndependencePolynomial starts R y
    P.eval z ≠ 0 ∧ ‖P.derivative.eval z / P.eval z‖ ≤ 4 * (∑ p ∈ starts, w p) * L := by
  have hs : 8 * ((Δ : ℝ) + 1) * (L * wStar) ≤ L * B₀ := by
    calc
      _ = L * (8 * ((Δ : ℝ) + 1) * wStar) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hL.le
  have h := complex_disk starts hR y (fun p ↦ L * w p) Δ hdeg hy
    (fun p hp ↦ mul_le_mul_of_nonneg_left (hw p hp) hL.le) (mul_pos hL hB₀) hs z hz
  rw [← Finset.mul_sum] at h
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

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

-- Multiplication by the polynomial identifies the analytic germ with the formal quotient.
private theorem taylor_quotient (p : Polynomial ℂ) {r : ℝ} (hr : 0 < r)
    (hn : ∀ z : ℂ, ‖z‖ ≤ r → p.eval z ≠ 0) :
    taylor (fun z ↦ p.derivative.eval z / p.eval z) =
      PowerSeries.derivative (p : PowerSeries ℂ) * (p : PowerSeries ℂ)⁻¹ := by
  let f (z : ℂ) := p.derivative.eval z / p.eval z
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 r) :=
    p.derivative.differentiable.differentiableOn.div p.differentiable.differentiableOn
      (fun z hz ↦ hn z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz))
  have hp : AnalyticAt ℂ p.eval 0 := p.differentiable.analyticAt _
  have hf : AnalyticAt ℂ f 0 := hd.analyticAt (Metric.closedBall_mem_nhds _ hr)
  have he : f * p.eval =ᶠ[nhds 0] p.derivative.eval := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with z hz
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact div_mul_cancel₀ _ (hn z hz')
  have hprod : taylor f * (p : PowerSeries ℂ) = (p.derivative : PowerSeries ℂ) := by
    rw [← taylor_poly p, ← taylor_mul hf hp, ← taylor_poly]
    ext n
    simp only [taylor, PowerSeries.coeff_mk, he.iteratedDeriv_eq n]
  have hp₀ : PowerSeries.constantCoeff (p : PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
    exact hn 0 (by simpa using hr.le)
  have h := congrArg (fun g : PowerSeries ℂ ↦ g * (p : PowerSeries ℂ)⁻¹) hprod
  simpa only [mul_assoc, PowerSeries.mul_inv_cancel _ hp₀, mul_one, PowerSeries.derivative_coe]
    using h

private theorem norm_logDerivativeCoeff_le (p : Polynomial ℂ) {B M : ℝ} (hB : 0 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ 1 / B →
      p.eval z ≠ 0 ∧ ‖p.derivative.eval z / p.eval z‖ ≤ M) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.derivative (p : PowerSeries ℂ) *
      (p : PowerSeries ℂ)⁻¹)‖ ≤ M * B ^ k := by
  let f (z : ℂ) := p.derivative.eval z / p.eval z
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / B)) :=
    p.derivative.differentiable.differentiableOn.div p.differentiable.differentiableOn
      (fun z hz ↦ (hb z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)).1)
  have hc := norm_taylor_coeff_le hB hd (fun z hz ↦ (hb z hz).2) k
  rwa [taylor_quotient p (one_div_pos.mpr hB) (fun z hz ↦ (hb z hz).1)] at hc

private theorem complex_constantCoeff (starts : Finset ℕ) (R : ℝ) (y : ℕ → ℂ) :
    PowerSeries.constantCoeff (complexIndependencePolynomial starts R y : PowerSeries ℂ) = 1 := by
  classical
  rw [Polynomial.constantCoeff_coe, complexIndependencePolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem ∅ (by simp [mem_independent])]
  · simp
  · intro I _ hI
    have hc : I.card ≠ 0 := by simpa using hI
    simp [Polynomial.coeff_monomial, hc]

-- Differentiate the substituted log(1+X), then use (log(1+X))' · (1+X) = 1.
open PowerSeries in
private theorem derivative_logOf_eq (P : PowerSeries ℂ) (hP : constantCoeff P = 1) :
    derivative (logOf P) = derivative P * P⁻¹ := by
  have hs : HasSubst (P - 1) := HasSubst.of_constantCoeff_zero' (by simp [hP])
  have h := congrArg (fun f : PowerSeries ℂ ↦ f.subst (P - 1))
    (derivative_log_mul_one_add_X (A := ℂ))
  rw [subst_mul hs, subst_add hs, subst_X hs] at h
  simp only [← coe_substAlgHom hs, map_one, add_sub_cancel] at h
  have hP₀ : constantCoeff P ≠ 0 := by rw [hP]; exact one_ne_zero
  have hi := congrArg (fun f : PowerSeries ℂ ↦ f * P⁻¹) h
  simp only [mul_assoc, PowerSeries.mul_inv_cancel _ hP₀, mul_one, one_mul] at hi
  rw [logOf_eq, derivative_subst hs, map_sub, Derivation.map_one_eq_zero, sub_zero, mul_comm]
  rw [← coe_substAlgHom hs, hi]

/-- The degree-`j` coefficient of the normalized formal log of the actual complex
independence polynomial. This is the homogeneous degree-`j` term along the ray
of activities `y`; the Cauchy estimate on `P′/P` bounds `j` times this coefficient. -/
public theorem norm_logCoeff_le
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) (w : ℕ → ℝ) (Δ : ℕ)
    {wStar B₀ L : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hy : ∀ p ∈ starts, ‖y p‖ ≤ L * w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hL : 0 < L) (hB₀ : 0 < B₀) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B₀)
    (j : ℕ) (hj : 1 ≤ j) :
    let P := complexIndependencePolynomial starts R y
    ‖PowerSeries.coeff j (PowerSeries.logOf (P : PowerSeries ℂ))‖ ≤
      4 * (∑ p ∈ starts, w p) * L * (L * B₀) ^ (j - 1) / j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  let p := complexIndependencePolynomial starts R y
  have hb := complex_nonvanishing_and_logDerivative_bound starts hR y w Δ hdeg hy hw hL hB₀ hscale
  have hc := norm_logDerivativeCoeff_le p (mul_pos hL hB₀) hb k
  rw [← derivative_logOf_eq _ (complex_constantCoeff starts R y), PowerSeries.coeff_derivative,
    norm_mul, ← Nat.cast_succ, Complex.norm_natCast] at hc
  exact (le_div_iff₀ (by positivity)).2 hc

-- Complexification preserves the real quotient: both solve F * P = P′.
private theorem map_logDerivative (p : Polynomial ℝ)
    (hp₀ : PowerSeries.constantCoeff (p : PowerSeries ℝ) ≠ 0) :
    let q := p.map Complex.ofRealHom
    PowerSeries.map Complex.ofRealHom
        (PowerSeries.derivative (p : PowerSeries ℝ) * (p : PowerSeries ℝ)⁻¹) =
      PowerSeries.derivative (q : PowerSeries ℂ) * (q : PowerSeries ℂ)⁻¹ := by
  let q := p.map Complex.ofRealHom
  have hq₀ : PowerSeries.constantCoeff (q : PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map]
    exact Complex.ofReal_ne_zero.mpr (by simpa only [Polynomial.constantCoeff_coe] using hp₀)
  have hreal : (PowerSeries.derivative (p : PowerSeries ℝ) * (p : PowerSeries ℝ)⁻¹) *
      (p : PowerSeries ℝ) = (p.derivative : PowerSeries ℝ) := by
    rw [mul_assoc, mul_comm ((p : PowerSeries ℝ)⁻¹), PowerSeries.mul_inv_cancel _ hp₀,
      mul_one, PowerSeries.derivative_coe]
  let F := PowerSeries.map Complex.ofRealHom
    (PowerSeries.derivative (p : PowerSeries ℝ) * (p : PowerSeries ℝ)⁻¹)
  have hmap : F * (q : PowerSeries ℂ) = (q.derivative : PowerSeries ℂ) := by
    simpa only [F, q, map_mul, Polynomial.derivative_map, Polynomial.polynomial_map_coe] using
      congrArg (PowerSeries.map Complex.ofRealHom) hreal
  have h := congrArg (fun g : PowerSeries ℂ ↦ g * (q : PowerSeries ℂ)⁻¹) hmap
  simpa only [F, q, mul_assoc, PowerSeries.mul_inv_cancel _ hq₀, mul_one,
    PowerSeries.derivative_coe] using h

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
  have hp₀ : PowerSeries.constantCoeff (p : PowerSeries ℝ) ≠ 0 := by
    have h := complex_constantCoeff starts R (fun p ↦ (x p : ℂ))
    rw [complexIndependencePolynomial_ofReal, Polynomial.constantCoeff_coe, Polynomial.coeff_map] at h
    rw [Polynomial.constantCoeff_coe]
    intro hz
    simp [p, hz] at h
  have hb := nonvanishing_and_logDerivative_bound starts hR x w Δ hdeg hx hw hB hscale
  have hc := norm_logDerivativeCoeff_le q hB hb k
  have hm := map_logDerivative p hp₀
  change PowerSeries.map Complex.ofRealHom (DetectorCoefficientRatios.logDerivative starts R x) = _ at hm
  rw [← hm, PowerSeries.coeff_map] at hc
  change ‖(DetectorCoefficientRatios.b starts R x (k + 1) : ℂ)‖ ≤ _ at hc
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.succ_sub_one] using hc

end DetectorCoefficientDisk
