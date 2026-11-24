module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Bernstein certificates for the released split atom price

Sources at `d62a81b9e592`: `.godel/bob/check-tail-deletion-33.py:19–35`
(power coefficients, Bernstein controls, and midpoint rows), and
`.godel/bob/check-released-slabs-33.py:72–111` (split coefficients and signed tilts).
Consumer: `d62a81b9e592:.godel/bob/full-release-deletion-33.md:61–71`,
where the two separate atom prices bound the tilted half-slab scores.
Owning check session: `01a20e21-be35-7bb8-b792-768105414492`.

Scope: exact symbolic prices for `m * u - a * X - b * T(X)` on all of `[0,1]`,
where `X = 2 * u² - 1` and `T(X) = 4 * X³ - 3 * X`. The certificate is a finite
binary midpoint subdivision whose seven controls on each leaf are at most the
specified upper price. The two-law result uses each half's own probability law
on the full closed atom interval. There is no numerical price, termination claim
for the search, or claim about feasibility of the released constraints.
-/

@[expose] public section

namespace Masullo.SplitAtomBernstein

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The available moment functions on the atom interval. -/
inductive Moment where
  | u
  | x
  | t

/-- The second and third fields are `X` and `T(X)`, respectively. -/
def Moment.eval : Moment → ℝ → ℝ
  | .u, z => z
  | .x, z => 2 * z ^ 2 - 1
  | .t, z => 4 * (2 * z ^ 2 - 1) ^ 3 - 3 * (2 * z ^ 2 - 1)

/-- The mass and signed-price coefficients of a half-slab. -/
structure Score where
  mass : ℝ
  a : ℝ
  b : ℝ

def Score.eval (s : Score) (u : ℝ) : ℝ :=
  s.mass * Moment.u.eval u - s.a * Moment.x.eval u - s.b * Moment.t.eval u

/-- Add `k` times the selected moment to the score. -/
def Score.tilt (s : Score) (y : Moment) (k : ℝ) : Score :=
  match y with
  | .u => { s with mass := s.mass + k }
  | .x => { s with a := s.a - k }
  | .t => { s with b := s.b - k }

theorem Score.eval_tilt (s : Score) (y : Moment) (k u : ℝ) :
    (s.tilt y k).eval u = s.eval u + k * y.eval u := by
  cases y <;> simp [tilt, eval, Moment.eval] <;> ring

abbrev Controls := Fin 7 → ℝ

/-- Power coefficients in ascending order, after applying the desired tilt to `s`. -/
def Score.powerCoeffs (s : Score) : Fin 7 → ℝ :=
  ![s.a + s.b, s.mass, -2 * s.a - 18 * s.b, 0, 48 * s.b, 0, -32 * s.b]

def powerEval (q : Fin 7 → ℝ) (u : ℝ) : ℝ := ∑ j, q j * u ^ j.val

theorem Score.powerEval_coeffs (s : Score) (u : ℝ) :
    powerEval s.powerCoeffs u = s.eval u := by
  norm_num [powerEval, powerCoeffs, eval, Moment.eval, Fin.sum_univ_succ]
  ring

/-- The degree-six power-to-Bernstein conversion. The terms with `i < j`
vanish because `i.choose j = 0`. -/
def powerToBernstein (q : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  ∑ j : Fin 7, q j * (i.val.choose j.val : ℝ) / (Nat.choose 6 j.val : ℝ)

def bernsteinWeight (i : Fin 7) (u : ℝ) : ℝ :=
  (Nat.choose 6 i.val : ℝ) * u ^ i.val * (1 - u) ^ (6 - i.val)

def bernsteinEval (c : Controls) (u : ℝ) : ℝ := ∑ i, c i * bernsteinWeight i u

theorem bernsteinEval_powerToBernstein (q : Fin 7 → ℝ) (u : ℝ) :
    bernsteinEval (powerToBernstein q) u = powerEval q u := by
  norm_num [bernsteinEval, bernsteinWeight, powerToBernstein, powerEval,
    Fin.sum_univ_succ, Nat.choose]
  ring

def Score.controls (s : Score) : Controls := powerToBernstein s.powerCoeffs

theorem Score.bernsteinEval_controls (s : Score) (u : ℝ) :
    bernsteinEval s.controls u = s.eval u := by
  rw [controls, bernsteinEval_powerToBernstein, powerEval_coeffs]

private theorem bernsteinWeight_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (i : Fin 7) :
    0 ≤ bernsteinWeight i u := by
  have h0 := hu.1
  have h1 := sub_nonneg.mpr hu.2
  unfold bernsteinWeight
  positivity

private theorem sum_bernsteinWeight (u : ℝ) : ∑ i, bernsteinWeight i u = 1 := by
  norm_num [bernsteinWeight, Fin.sum_univ_succ, Nat.choose]
  ring

/-- The seven Bernstein controls bound the polynomial on the full closed cell. -/
theorem bernsteinEval_le {c : Controls} {h u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, c i ≤ h) : bernsteinEval c u ≤ h := by
  calc
    bernsteinEval c u ≤ ∑ i, h * bernsteinWeight i u :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hc i) (bernsteinWeight_nonneg hu i)
    _ = h := by rw [← Finset.mul_sum, sum_bernsteinWeight, mul_one]

/-- One de Casteljau row, taking arithmetic means of consecutive controls. -/
def midpointRow {n : ℕ} (c : Fin (n + 2) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (c i.castSucc + c i.succ) / 2

/-- First entries of the successive midpoint rows, starting with the original row. -/
def leftControls : {n : ℕ} → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, c => c
  | n + 1, c => Fin.cases (c 0) (leftControls (midpointRow (n := n) c))

/-- Last entries of the successive midpoint rows, in reverse row order. -/
def rightControls : {n : ℕ} → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, c => c
  | n + 1, c => Fin.lastCases (c (Fin.last (n + 1))) (rightControls (midpointRow (n := n) c))

/-- The left child's parameter `u` represents `u / 2` in the parent. -/
theorem bernsteinEval_leftControls (c : Controls) (u : ℝ) :
    bernsteinEval (leftControls c) u = bernsteinEval c (u / 2) := by
  norm_num [bernsteinEval, bernsteinWeight, Fin.sum_univ_succ, Nat.choose,
    leftControls, midpointRow]
  ring

/-- The right child's parameter `u` represents `(1 + u) / 2` in the parent. -/
theorem bernsteinEval_rightControls (c : Controls) (u : ℝ) :
    bernsteinEval (rightControls c) u = bernsteinEval c ((1 + u) / 2) := by
  simp only [bernsteinEval, Fin.sum_univ_castSucc, Fin.sum_univ_zero, rightControls,
    Fin.lastCases_castSucc, Fin.lastCases_last]
  norm_num [bernsteinWeight, midpointRow, Nat.choose, Fin.last, Fin.castSucc, Fin.castLE,
    Fin.succ, Nat.succ_eq_add_one]
  ring

/-- A finite complete midpoint subdivision. Each split has both children, which
may have different depths. -/
inductive Subdivision where
  | leaf
  | split (left right : Subdivision)

/-- Test all seven controls at every leaf, deriving child rows from the parent. -/
def Subdivision.Passes : Subdivision → Controls → ℝ → Prop
  | .leaf, c, h => ∀ i, c i ≤ h
  | .split left right, c, h =>
    left.Passes (leftControls c) h ∧ right.Passes (rightControls c) h

/-- Leaf tests cover the entire parent interval, including both endpoints and
all shared midpoints. -/
theorem Subdivision.eval_le (d : Subdivision) {c : Controls} {h : ℝ} (hd : d.Passes c h)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : bernsteinEval c u ≤ h := by
  induction d generalizing c u with
  | leaf => exact bernsteinEval_le hu hd
  | split left right ihL ihR =>
    obtain ⟨hl, hr⟩ := hd
    rcases le_or_gt u (1 / 2) with hm | hm
    · have hv : 2 * u ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith only [hu.1], by linarith only [hm]⟩
      have hL := ihL hl hv
      rwa [bernsteinEval_leftControls, show 2 * u / 2 = u by ring] at hL
    · have hv : 2 * u - 1 ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith only [hm], by linarith only [hu.2]⟩
      have hR := ihR hr hv
      rwa [bernsteinEval_rightControls, show (1 + (2 * u - 1)) / 2 = u by ring] at hR

/-- A finite certificate for the tilted polynomial, with no restriction on which
atoms in `[0,1]` are admissible. -/
theorem tilted_atom_le (s : Score) (y : Moment) (k h : ℝ) (d : Subdivision)
    (hd : d.Passes (s.tilt y k).controls h) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    s.eval u + k * y.eval u ≤ h := by
  simpa only [Score.bernsteinEval_controls, Score.eval_tilt] using d.eval_le hd hu

/-- The full closed atom interval, with its subtype Borel measurable space. -/
abbrev Atom := Icc (0 : ℝ) 1

def Moment.mean (y : Moment) (ν : Measure Atom) : ℝ := ∫ u : Atom, y.eval u ∂ν

def Score.mean (s : Score) (ν : Measure Atom) : ℝ := ∫ u : Atom, s.eval u ∂ν

private theorem Moment.continuous_eval (y : Moment) : Continuous y.eval := by
  cases y with
  | u => exact continuous_id
  | x =>
    change Continuous (fun z : ℝ ↦ 2 * z ^ 2 - 1)
    fun_prop
  | t =>
    change Continuous (fun z : ℝ ↦ 4 * (2 * z ^ 2 - 1) ^ 3 - 3 * (2 * z ^ 2 - 1))
    fun_prop

private theorem Score.continuous_eval (s : Score) : Continuous s.eval :=
  (((Moment.u.continuous_eval.const_mul s.mass).sub
    (Moment.x.continuous_eval.const_mul s.a)).sub (Moment.t.continuous_eval.const_mul s.b))

private theorem integrable_atom {ν : Measure Atom} [IsFiniteMeasure ν]
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun u : Atom ↦ f u) ν :=
  integrableOn_univ.mp <|
    (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact isCompact_univ

/-- Under one half's law, the mean score is `m * U - a * A - b * B`. -/
theorem Score.mean_eq (s : Score) (ν : Measure Atom) [IsFiniteMeasure ν] :
    s.mean ν = s.mass * Moment.u.mean ν - s.a * Moment.x.mean ν - s.b * Moment.t.mean ν := by
  have hu := (integrable_atom (ν := ν) Moment.u.continuous_eval).const_mul s.mass
  have hx := (integrable_atom (ν := ν) Moment.x.continuous_eval).const_mul s.a
  have ht := (integrable_atom (ν := ν) Moment.t.continuous_eval).const_mul s.b
  have hux : Integrable (fun u : Atom ↦ s.mass * Moment.u.eval u - s.a * Moment.x.eval u) ν :=
    hu.sub hx
  unfold mean eval Moment.mean
  rw [integral_sub hux ht, integral_sub hu hx]
  simp only [integral_const_mul]

private theorem tilted_mean_le (s : Score) (y : Moment) (k h : ℝ) (d : Subdivision)
    (hd : d.Passes (s.tilt y k).controls h) (ν : Measure Atom) [IsProbabilityMeasure ν] :
    s.mean ν + k * y.mean ν ≤ h := by
  have hs := integrable_atom (ν := ν) s.continuous_eval
  have hy := (integrable_atom (ν := ν) y.continuous_eval).const_mul k
  have hmean := integral_mono (f := fun u : Atom ↦ s.eval u + k * y.eval u)
    (hs.add hy) (integrable_const h) (fun u ↦ tilted_atom_le s y k h d hd u.property)
  rw [integral_add hs hy, integral_const_mul, integral_const, probReal_univ, one_smul] at hmean
  exact hmean

/-- The left and right halves use opposite tilts and their own probability laws.
No common maximizing atom or joint law is required. -/
theorem split_mean_le (sL sR : Score) (y : Moment) (k hL hR : ℝ)
    (dL dR : Subdivision) (hdL : dL.Passes (sL.tilt y k).controls hL)
    (hdR : dR.Passes (sR.tilt y (-k)).controls hR)
    (νL νR : Measure Atom) [IsProbabilityMeasure νL] [IsProbabilityMeasure νR] :
    sL.mean νL + sR.mean νR ≤ hL + hR + k * (y.mean νR - y.mean νL) := by
  have hleft := tilted_mean_le sL y k hL dL hdL νL
  have hright := tilted_mean_le sR y (-k) hR dR hdR νR
  calc
    sL.mean νL + sR.mean νR =
        (sL.mean νL + k * y.mean νL) + (sR.mean νR + (-k) * y.mean νR) +
          k * (y.mean νR - y.mean νL) := by ring
    _ ≤ _ := add_le_add_left (add_le_add hleft hright) _

end

end Masullo.SplitAtomBernstein
