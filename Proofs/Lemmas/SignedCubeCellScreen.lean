module

public import Lemmas.SignedCubeFrequencyBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite whole-cell screen for the signed gap cube

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:22–66`, especially
"Use and cost" (line 66). Owning check session: `01a20d85-3fca-796b-bf11-8791e07c4ba8`.

For the original normalized surviving product sum, the lower endpoint of
nonzero gap-pair amplitudes controls the oscillation, while the upper endpoint
supplies the shell moment bound. Closed cells respect both endpoints, including
those of a shorter last cell. The explicit width condition is sufficient for
the midpoint rule, and the finite measure estimate applies with `m = k` when
its moment and frequency-cutoff hypotheses hold. The cleared-cell result is
only an upper bound on `Re S`: no implication from a large dense-gap arithmetic
sum, asymptotic shell estimate, or evaluation count is proved here.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Masullo.SignedCubeCellScreen

open SignedBlockIntervalMoment (phase)
open SignedCubeShell TriangularCubeCoefficients TriangularCubeDeletion

variable {G H k : ℕ}

/-- The uniform angular frequency budget on the lower prime band. -/
@[expose] public noncomputable def frequencyBound (d : ℤ) (H k : ℕ) (X : ℝ) : ℝ :=
  2 * (d : ℝ) * (k.factorial : ℝ) * (H : ℝ) ^ k * (Real.exp 8 / X) ^ (k + 1)

private theorem frequencyBound_nonneg {d : ℤ} {X : ℝ} (hd : 0 ≤ d) (hX : 0 < X) :
    0 ≤ frequencyBound d H k X := by
  unfold frequencyBound
  positivity

private theorem cubeWeight_bounds {a : Fin G → ℤ → ℝ}
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1) (x : Label G H k) :
    0 ≤ cubeWeight a x ∧ cubeWeight a x ≤ 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (ha _ _).1),
    Finset.prod_le_one₀ (fun _ _ => (ha _ _).1) (fun _ _ => (ha _ _).2)⟩

/-- The surviving product amplitudes have mass at most one with the original
ordered-draw denominator; this is also the mass of the coalesced coefficients. -/
public theorem sum_survivingCube_mass_le_one (d : ℤ) (a : Fin G → ℤ → ℝ)
    (hG : 0 < G) (hH : 0 < H) (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1) :
    (∑ x ∈ survivors (H := H) (k := k) d, cubeWeight a x) / normalizer G H k ≤ 1 := by
  rw [← sum_coefficient_eq]
  exact sum_coefficient_le_one hG hH d (cubeWeight a) (fun x => (cubeWeight_bounds ha x).2)

private theorem lower_band_of_cubeWeight_ne_zero {d : ℤ} {X : ℝ} {a : Fin G → ℤ → ℝ}
    (hd : 0 ≤ d) (haL : ∀ g p, a g p ≠ 0 → Real.exp (-8) * X ≤ (p : ℝ))
    {x : Label G H k} (hx : cubeWeight a x ≠ 0) (v : VertexLabel k) :
    Real.exp (-8) * X ≤ (labelVertex d x v : ℝ) := by
  obtain ⟨s, e, b⟩ := v
  have hs := Finset.prod_ne_zero_iff.mp hx s (Finset.mem_univ s)
  refine (haL _ _ hs).trans (Int.cast_le.mpr ?_)
  cases e <;> cases b <;> simp [labelVertex, vertex] <;> omega

private theorem norm_phase_sub_le (ω u v : ℝ) :
    ‖phase (u * ω) - phase (v * ω)‖ ≤ |ω| * |u - v| := by
  have hderiv (z : ℝ) :
      HasDerivAt (fun y : ℝ => phase (y * ω)) (phase (z * ω) * ((ω : ℂ) * Complex.I)) z := by
    simpa only [phase, one_mul, id_eq] using!
      ((((hasDerivAt_id z).mul_const ω).ofReal_comp).mul_const Complex.I).cexp
  have hnorm (z : ℝ) : ‖phase (z * ω) * ((ω : ℂ) * Complex.I)‖ ≤ |ω| := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs] using
    (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hderiv z).hasDerivWithinAt) (fun z _ => hnorm z) (mem_univ v) (mem_univ u)

/-- The actual normalized surviving product sum is Lipschitz with constant
`frequencyBound d H k X`. Only nonzero gap-pair amplitudes need the lower band. -/
public theorem norm_survivingCube_sub_le (d : ℤ) (a : Fin G → ℤ → ℝ)
    {X : ℝ} (hG : 0 < G) (hH : 0 < H) (hd : 0 ≤ d) (hX : 0 < X)
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1)
    (haL : ∀ g p, a g p ≠ 0 → Real.exp (-8) * X ≤ (p : ℝ)) (u v : ℝ) :
    ‖survivingSum d (cubeWeight (H := H) (k := k) a) u -
      survivingSum d (cubeWeight (H := H) (k := k) a) v‖ ≤ frequencyBound d H k X * |u - v| := by
  have hN : 0 ≤ normalizer G H k := by
    unfold normalizer
    positivity
  unfold survivingSum
  rw [← sub_div, ← Finset.sum_sub_distrib, norm_div, Complex.norm_real, Real.norm_of_nonneg hN]
  calc
    _ ≤ (∑ x ∈ survivors d, cubeWeight a x * (frequencyBound d H k X * |u - v|)) /
        normalizer G H k := by
      refine div_le_div_of_nonneg_right ((norm_sum_le ..).trans ?_) hN
      apply Finset.sum_le_sum
      intro x _
      have hx := (cubeWeight_bounds ha x).1
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]
      by_cases hw : cubeWeight a x = 0
      · simp [hw]
      have hω : |cubeFrequency d x| ≤ frequencyBound d H k X :=
        abs_cubeFrequency_le_exp_band x hd hX (lower_band_of_cubeWeight_ne_zero hd haL hw)
      exact mul_le_mul_of_nonneg_left ((norm_phase_sub_le _ _ _).trans
        (mul_le_mul_of_nonneg_right hω (abs_nonneg _))) hx
    _ = ((∑ x ∈ survivors d, cubeWeight a x) / normalizer G H k) *
        (frequencyBound d H k X * |u - v|) := by
      rw [← Finset.sum_mul, div_mul_eq_mul_div]
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (sum_survivingCube_mass_le_one (k := k) d a hG hH ha)
        (mul_nonneg (frequencyBound_nonneg hd hX) (abs_nonneg _))

/-- A closed cell, possibly of zero width. -/
public structure Cell where
  left : ℝ
  right : ℝ
  left_le_right : left ≤ right

@[expose] public def Cell.interval (c : Cell) : Set ℝ := Icc c.left c.right

@[expose] public noncomputable def Cell.midpoint (c : Cell) : ℝ := (c.left + c.right) / 2

@[expose] public noncomputable def Cell.width (c : Cell) : ℝ := c.right - c.left

/-- The radius bound holds at the endpoints as well as the interior. -/
public theorem Cell.abs_sub_midpoint_le_half_width (c : Cell) {u : ℝ} (hu : u ∈ c.interval) :
    |u - c.midpoint| ≤ c.width / 2 := by
  have ⟨hl, hr⟩ := hu
  rw [abs_le, Cell.midpoint, Cell.width]
  constructor <;> linarith

/-- With midpoint error `δ/16` and frequency budget times width at most `δ/4`,
a cleared cell stays below `3δ/4` in real part and a flagged cell stays in the
inclusive `δ/4` norm superlevel set. Equality at the estimate threshold clears. -/
public theorem cell_midpoint_screen (d : ℤ) (a : Fin G → ℤ → ℝ) {X δ : ℝ}
    (hG : 0 < G) (hH : 0 < H) (hd : 0 ≤ d) (hX : 0 < X) (hδ : 0 < δ)
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1)
    (haL : ∀ g p, a g p ≠ 0 → Real.exp (-8) * X ≤ (p : ℝ))
    (c : Cell) (q : ℝ)
    (hwidth : frequencyBound d H k X * c.width ≤ δ / 4)
    (herror : |(survivingSum d (cubeWeight (H := H) (k := k) a) c.midpoint).re - q| ≤ δ / 16)
    {u : ℝ} (hu : u ∈ c.interval) :
    (q ≤ δ / 2 → (survivingSum d (cubeWeight (H := H) (k := k) a) u).re < 3 * δ / 4) ∧
    (δ / 2 < q → δ / 4 ≤ ‖survivingSum d (cubeWeight (H := H) (k := k) a) u‖) := by
  let S := survivingSum d (cubeWeight (H := H) (k := k) a)
  have hosc : ‖S u - S c.midpoint‖ ≤ δ / 8 := by
    calc
      _ ≤ frequencyBound d H k X * |u - c.midpoint| :=
        norm_survivingCube_sub_le d a hG hH hd hX ha haL u c.midpoint
      _ ≤ frequencyBound d H k X * (c.width / 2) :=
        mul_le_mul_of_nonneg_left (c.abs_sub_midpoint_le_half_width hu) (frequencyBound_nonneg hd hX)
      _ = (frequencyBound d H k X * c.width) / 2 := by rw [mul_div_assoc]
      _ ≤ δ / 8 := by linarith
  have hre : |(S u).re - (S c.midpoint).re| ≤ δ / 8 := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hosc
  have hnear : |(S u).re - q| ≤ 3 * δ / 16 := by
    calc
      _ ≤ |(S u).re - (S c.midpoint).re| + |(S c.midpoint).re - q| := abs_sub_le _ _ _
      _ ≤ δ / 8 + δ / 16 := add_le_add hre herror
      _ = _ := by ring
  have hnear' := abs_le.mp hnear
  constructor
  · intro hq
    change (S u).re < 3 * δ / 4
    linarith [hnear'.2]
  · intro hq
    have hu' : δ / 4 ≤ (S u).re := by linarith [hnear'.1]
    exact hu'.trans (Complex.re_le_norm _)

/-- The union of precisely the cells whose estimates exceed `δ/2`. -/
@[expose] public def flaggedCellUnion {ι : Type*} (cells : Finset ι) (cell : ι → Cell)
    (q : ι → ℝ) (δ : ℝ) : Set ℝ :=
  {u | ∃ i ∈ cells, δ / 2 < q i ∧ u ∈ (cell i).interval}

/-- The finite whole-cell screen and flagged-union volume bound on the genuine
shell. No disjointness is needed for this union bound, so shared cell endpoints
are allowed. The conclusion about cleared cells concerns only the analytic sum. -/
public theorem flaggedCellUnion_screen {ι : Type*} (d : ℤ) (a : Fin G → ℤ → ℝ)
    {X t δ : ℝ} {m : ℕ} (hG : 0 < G) (hH : 0 < H) (hd : 0 ≤ d) (hX : 1 ≤ X)
    (hm : 1 ≤ m) (ht : X ^ (m * (4 * 2 ^ k)) < t) (hδ : 0 < δ)
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1)
    (haL : ∀ g p, a g p ≠ 0 → Real.exp (-8) * X ≤ (p : ℝ))
    (haX : ∀ g p, a g p ≠ 0 → ((p + (g.val : ℤ) + 1 + d : ℤ) : ℝ) ≤ X)
    (cells : Finset ι) (cell : ι → Cell) (q : ι → ℝ)
    (hinside : ∀ i ∈ cells, (cell i).interval ⊆ Icc t (5 * t / 4))
    (hwidth : ∀ i ∈ cells, frequencyBound d H k X * (cell i).width ≤ δ / 4)
    (herror : ∀ i ∈ cells,
      |(survivingSum d (cubeWeight (H := H) (k := k) a) (cell i).midpoint).re - q i| ≤ δ / 16) :
    (∀ i ∈ cells, q i ≤ δ / 2 → ∀ u ∈ (cell i).interval,
        (survivingSum d (cubeWeight (H := H) (k := k) a) u).re < 3 * δ / 4) ∧
    flaggedCellUnion cells cell q δ ⊆ {u : ℝ | u ∈ Icc t (5 * t / 4) ∧
        δ / 4 ≤ ‖survivingSum d (cubeWeight (H := H) (k := k) a) u‖} ∧
    volume (flaggedCellUnion cells cell q δ) ≤
      ENNReal.ofReal (8 * Real.pi * t * (((4 * (m : ℝ) - 2) ^ (4 * 2 ^ k) *
        (4 * 2 ^ k : ℝ) ^ (k + 2)) /
        (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k * (δ / 4) ^ 2)) ^ m) := by
  have hcell (i : ι) (hi : i ∈ cells) {u : ℝ} (hu : u ∈ (cell i).interval) :=
    cell_midpoint_screen d a hG hH hd (zero_lt_one.trans_le hX) hδ ha haL (cell i) (q i)
      (hwidth i hi) (herror i hi) hu
  have hsub : flaggedCellUnion cells cell q δ ⊆ {u : ℝ | u ∈ Icc t (5 * t / 4) ∧
        δ / 4 ≤ ‖survivingSum d (cubeWeight (H := H) (k := k) a) u‖} := by
    intro u hu
    obtain ⟨i, hi, hq, hui⟩ := hu
    exact ⟨hinside i hi hui, (hcell i hi hui).2 hq⟩
  exact ⟨fun i hi hq _ hu => (hcell i hi hu).1 hq, hsub,
    (measure_mono hsub).trans
      (volume_survivingCube_le d a hG hH hd hX hm ht (by positivity) ha haX)⟩

end Masullo.SignedCubeCellScreen
