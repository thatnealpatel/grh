module

public import Lemmas.SignedSuccessorPrice
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Local grid bound for the signed successor score

Source: `ac8b771857b16d36dcc380c4ca3990f33a4f5e1d:.godel/bob/finite-successor-cap.md`,
lines 24–32 and 36–40, and `.godel/bob/check-finite-successor-cap.py` at the same revision,
lines 25–59 and 66–80 (`tab`, `err`, `cap`).

Scope: the interpolation allowance for a single angular cell (in particular at
width `π/96`). The bound uses the maximum of the four full corner scores. It does
not certify the rounded table, a numerical intercept, or a cutoff cap.

Owning check session: `01a20b8b-65a1-7430-ae92-47e2bde881a8`.
-/

namespace Masullo.SignedSuccessorGrid

open Masullo.SignedSuccessorPrice (U deficit phase)

noncomputable section

/-- The signed successor score at a pair of angles, with independent prices. -/
@[expose] public def score (c A B T u v : ℝ) : ℝ :=
  c * (U u v - 1) + A * deficit u + B * deficit v - T * Real.cos (2 * (u + v))

private def mix (r p q : ℝ) : ℝ := (1 - r) * p + r * q

private theorem mix_mono {r p q P Q : ℝ} (hr : r ∈ Set.Icc 0 1)
    (hp : p ≤ P) (hq : q ≤ Q) : mix r p q ≤ mix r P Q :=
  add_le_add (mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hr.2))
    (mul_le_mul_of_nonneg_left hq hr.1)

private theorem mix_self (r p : ℝ) : mix r p p = p := by unfold mix; ring

private theorem mix_add (r p q E : ℝ) : mix r (p + E) (q + E) = mix r p q + E := by
  unfold mix
  ring

/-- Quadratic convexification gives an upper chord allowance from a lower bound
on the second derivative. The allowance includes both endpoints. -/
private theorem chord_le {f f' f'' : ℝ → ℝ} {K a h r : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hcurv : ∀ x, -K ≤ f'' x)
    (hr : r ∈ Set.Icc 0 1) :
    f (a + r * h) ≤ mix r (f a) (f (a + h)) + h ^ 2 * K / 8 := by
  let g (x : ℝ) := f x + K / 2 * x ^ 2
  have hg (x : ℝ) : HasDerivAt g (f' x + K * x) x := by
    exact ((hf x).add (((hasDerivAt_id x).pow 2).const_mul (K / 2))).congr_deriv (by
      norm_num
      ring)
  have hg' (x : ℝ) : HasDerivAt (fun y ↦ f' y + K * y) (f'' x + K) x := by
    change HasDerivAt (f' + fun y ↦ K * y) (f'' x + K) x
    simpa only [id_eq, mul_one] using (hf' x).add ((hasDerivAt_id x).const_mul K)
  have hdg : deriv g = fun x ↦ f' x + K * x := funext fun x ↦ (hg x).deriv
  have hconv : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_deriv2_nonneg' convex_univ
    · exact fun x _ ↦ (hg x).differentiableAt.differentiableWithinAt
    · rw [hdg]
      exact fun x _ ↦ (hg' x).differentiableAt.differentiableWithinAt
    · intro x _
      change 0 ≤ deriv (deriv g) x
      rw [hdg, (hg' x).deriv]
      linarith only [hcurv x]
  have hc := hconv.2 (Set.mem_univ a) (Set.mem_univ (a + h))
    (sub_nonneg.mpr hr.2) hr.1 (by ring : 1 - r + r = 1)
  simp only [smul_eq_mul, show (1 - r) * a + r * (a + h) = a + r * h by ring, g] at hc
  -- The quadratic contributes `K * h ^ 2 * r * (1 - r) / 2`, at most `K * h ^ 2 / 8`.
  have hs : 0 ≤ K * (r - 1 / 2) ^ 2 * h ^ 2 := by positivity
  unfold mix
  nlinarith only [hc, hs]

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem phase_deriv (ε x : ℝ) :
    HasDerivAt (fun y ↦ phase (ε * y)) (phase (ε * x) * ((ε : ℂ) * Complex.I)) x := by
  simpa only [phase, id_eq, mul_one] using
    ((((hasDerivAt_id x).const_mul ε).ofReal_comp).mul_const Complex.I).cexp

/-- Freeze the other angle. The rotating term of the vector has coefficient of
norm `3/10`; the two cosine frequencies are `1/2` and `2`. A fixed norm-at-most-one
real functional on the vector gives a smooth scalar score with these same bounds. -/
private theorem slice_chord (c A T k m ε : ℝ) (p z : ℂ) (L : ℂ →L[ℝ] ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hT : 0 ≤ T) (hL : ‖L‖ ≤ 1) (hε : |ε| = 1)
    (hp : ‖p‖ = 3 / 10) {a h r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    let f (x : ℝ) := c * (L (p * phase (ε * x) + z) - 1) + A * deficit x + m -
      T * Real.cos (2 * (x + k))
    f (a + r * h) ≤ mix r (f a) (f (a + h)) + h ^ 2 * (3 / 10 * c + A / 4 + 4 * T) / 8 := by
  let d : ℂ := (ε : ℂ) * Complex.I
  have hd : ‖d‖ = 1 := by
    change ‖(ε : ℂ) * Complex.I‖ = 1
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hε, Complex.norm_I, mul_one]
  let V (x : ℝ) := p * phase (ε * x) + z
  let V₁ (x : ℝ) := p * (phase (ε * x) * d)
  let V₂ (x : ℝ) := p * (phase (ε * x) * d * d)
  have hV (x : ℝ) : HasDerivAt V (V₁ x) x :=
    ((phase_deriv ε x).const_mul p).add_const z
  have hV₁ (x : ℝ) : HasDerivAt V₁ (V₂ x) x :=
    ((phase_deriv ε x).mul_const d).const_mul p
  have hhalf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (2 : ℝ)⁻¹
  have htwice (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 2 * (y + k)) 2 x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).add_const k).const_mul 2
  let f₁ (x : ℝ) := c * L (V₁ x) + A * (Real.sin (x / 2) * (1 / 2)) +
    T * (2 * Real.sin (2 * (x + k)))
  let f₂ (x : ℝ) := c * L (V₂ x) + A * (Real.cos (x / 2) / 4) +
    T * (4 * Real.cos (2 * (x + k)))
  intro f
  refine chord_le (f := f) (f' := f₁) (f'' := f₂) (by positivity) ?_ ?_ ?_ hr
  · intro x
    have hP := L.hasFDerivAt.comp_hasDerivAt x (hV x)
    have hD := ((hhalf x).cos.const_sub 1).const_mul A
    have hC := (htwice x).cos.const_mul T
    exact ((((hP.sub_const 1).const_mul c).add hD).add_const m |>.sub hC).congr_deriv (by
      dsimp [f₁]
      ring)
  · intro x
    have hP := L.hasFDerivAt.comp_hasDerivAt x (hV₁ x)
    have hD := (((hhalf x).sin).mul_const (1 / 2)).const_mul A
    have hC := (((htwice x).sin).const_mul 2).const_mul T
    exact (((hP.const_mul c).add hD).add hC).congr_deriv (by dsimp [f₂]; ring)
  · intro x
    have hv : ‖V₂ x‖ = 3 / 10 := by simp [V₂, norm_phase, hp, hd]
    have hP : |L (V₂ x)| ≤ 3 / 10 := by
      rw [← Real.norm_eq_abs]
      exact (L.le_opNorm _).trans (by rw [hv]; nlinarith only [hL])
    have hD := mul_le_mul_of_nonneg_left (abs_le.mp (Real.abs_cos_le_one (x / 2))).1 hA
    have hC := mul_le_mul_of_nonneg_left (abs_le.mp (Real.abs_cos_le_one (2 * (x + k)))).1 hT
    have hV₂ := mul_le_mul_of_nonneg_left (abs_le.mp hP).1 hc
    dsimp [f₂]
    linarith only [hD, hC, hV₂]

private def flank (s : Bool) : ℂ := if s then 3 / 10 else -(3 / 10)

private def branch (s t : Bool) (u v : ℝ) : ℂ :=
  flank s * phase (-u) + (4 / 10 : ℂ) + flank t * phase v

private theorem norm_flank (s : Bool) : ‖flank s‖ = 3 / 10 := by
  cases s <;> norm_num [flank, norm_div]

private theorem max_branch_norm (u v : ℝ) : U u v =
    max (max ‖branch true true u v‖ ‖branch true false u v‖)
      (max ‖branch false true u v‖ ‖branch false false u v‖) := by
  simp [U, branch, flank, sub_eq_add_neg]

private theorem norm_branch_le (s t : Bool) (u v : ℝ) : ‖branch s t u v‖ ≤ U u v := by
  rw [max_branch_norm]
  cases s <;> cases t
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)

private theorem exists_branch (u v : ℝ) : ∃ s t, ‖branch s t u v‖ = U u v := by
  have choice (x y : ℝ) : max x y = x ∨ max x y = y :=
    (le_total x y).elim (fun h ↦ Or.inr (max_eq_right h)) (fun h ↦ Or.inl (max_eq_left h))
  rw [max_branch_norm]
  rcases choice (max ‖branch true true u v‖ ‖branch true false u v‖)
      (max ‖branch false true u v‖ ‖branch false false u v‖) with h | h <;> rw [h]
  · rcases choice ‖branch true true u v‖ ‖branch true false u v‖ with h | h <;> rw [h]
    · exact ⟨true, true, rfl⟩
    · exact ⟨true, false, rfl⟩
  · rcases choice ‖branch false true u v‖ ‖branch false false u v‖ with h | h <;> rw [h]
    · exact ⟨false, true, rfl⟩
    · exact ⟨false, false, rfl⟩

private theorem exists_support (z : ℂ) : ∃ L : ℂ →L[ℝ] ℝ, ‖L‖ ≤ 1 ∧ L z = ‖z‖ := by
  by_cases hz : ‖z‖ = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  · obtain ⟨L, hL, heq⟩ := exists_dual_vector ℝ z hz
    exact ⟨L, hL.le, heq⟩

private theorem exists_cell_weight {a h u : ℝ} (hh : 0 < h) (hu : u ∈ Set.Icc a (a + h)) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, u = a + r * h := by
  refine ⟨(u - a) / h,
    ⟨div_nonneg (sub_nonneg.mpr hu.1) hh.le, (div_le_iff₀ hh).mpr ?_⟩, ?_⟩
  · linarith only [hu.2]
  · rw [div_mul_cancel₀ _ hh.ne']
    ring

/-- On a square angular cell, the full signed score is bounded by the largest
full corner score plus the checker's interpolation allowance. The score need not
be smooth: we support an attaining signed vector by a fixed real linear functional
and interpolate its smooth score, which is dominated by the full score at each corner. -/
public theorem score_le_corner_max_add_error {c A B T a b h u v : ℝ}
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) (hh : 0 < h)
    (hu : u ∈ Set.Icc a (a + h)) (hv : v ∈ Set.Icc b (b + h)) :
    score c A B T u v ≤
      max (max (score c A B T a b) (score c A B T a (b + h)))
        (max (score c A B T (a + h) b) (score c A B T (a + h) (b + h))) +
        h ^ 2 * (3 * c / 5 + (A + B) / 4 + 8 * T) / 8 := by
  obtain ⟨r, hr, hru⟩ := exists_cell_weight hh hu
  obtain ⟨q, hq, hqv⟩ := exists_cell_weight hh hv
  obtain ⟨s, t, hst⟩ := exists_branch u v
  obtain ⟨L, hL, hLz⟩ := exists_support (branch s t u v)
  let F (x y : ℝ) := c * (L (branch s t x y) - 1) + A * deficit x + B * deficit y -
    T * Real.cos (2 * (x + y))
  have hEq : F u v = score c A B T u v := by simp only [F, score, hLz, hst]
  have hF (x y : ℝ) : F x y ≤ score c A B T x y := by
    have hz : L (branch s t x y) ≤ ‖branch s t x y‖ := calc
      _ ≤ ‖L (branch s t x y)‖ := le_abs_self _
      _ ≤ ‖L‖ * ‖branch s t x y‖ := L.le_opNorm _
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hL (norm_nonneg (branch s t x y))
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right (hz.trans (norm_branch_le s t x y)) 1) hc
    dsimp [F, score]
    linarith only [hp]
  let E₁ := h ^ 2 * (3 / 10 * c + A / 4 + 4 * T) / 8
  let E₂ := h ^ 2 * (3 / 10 * c + B / 4 + 4 * T) / 8
  have hX : F u v ≤ mix r (F a v) (F (a + h) v) + E₁ := by
    rw [hru]
    simpa only [F, branch, add_assoc, neg_one_mul, E₁] using
      slice_chord c A T v (B * deficit v) (-1) (flank s) (4 / 10 + flank t * phase v) L
        hc hA hT hL (by simp) (norm_flank s) (a := a) (h := h) hr
  have hY (x : ℝ) : F x v ≤ mix q (F x b) (F x (b + h)) + E₂ := by
    have he (y : ℝ) : F x y = c * (L (flank t * phase (1 * y) +
        (flank s * phase (-x) + 4 / 10)) - 1) + B * deficit y + A * deficit x -
        T * Real.cos (2 * (y + x)) := by
      simp only [F, branch, one_mul, add_comm y x, add_comm (flank t * phase y), add_right_comm]
    simp only [hqv, he]
    exact slice_chord c B T x (A * deficit x) 1 (flank t) (flank s * phase (-x) + 4 / 10) L
      hc hB hT hL abs_one (norm_flank t) hq
  let M := max (max (score c A B T a b) (score c A B T a (b + h)))
    (max (score c A B T (a + h) b) (score c A B T (a + h) (b + h)))
  have hCorners : mix r (mix q (F a b) (F a (b + h)))
      (mix q (F (a + h) b) (F (a + h) (b + h))) ≤ M := by
    rw [← mix_self r M]
    apply mix_mono hr <;> rw [← mix_self q M] <;> apply mix_mono hq
    · exact (hF _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hF _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hF _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hF _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  calc
    score c A B T u v = F u v := hEq.symm
    _ ≤ mix r (F a v) (F (a + h) v) + E₁ := hX
    _ ≤ mix r (mix q (F a b) (F a (b + h)) + E₂)
        (mix q (F (a + h) b) (F (a + h) (b + h)) + E₂) + E₁ :=
      add_le_add (mix_mono hr (hY a) (hY (a + h))) le_rfl
    _ ≤ M + E₂ + E₁ := by
      rw [mix_add]
      exact add_le_add (add_le_add hCorners le_rfl) le_rfl
    _ = M + h ^ 2 * (3 * c / 5 + (A + B) / 4 + 8 * T) / 8 := by
      dsimp only [E₁, E₂]
      ring

end

end Masullo.SignedSuccessorGrid
