module

public import Lemmas.SplitAtomBernstein
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Real.Sqrt
import Lemmas.MeasurableBernsteinCell
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The shared primitive cell price for a real knot

Source: `1f5664a6:.godel/bob/two-knots-deletion-33.md:13–31` and
`1f5664a6:.godel/bob/check-two-knots-33.py:80–101` (the shared-control calculation,
unchanged at discovery pin `50cd94de` and implementation base `8b1b2fc2`).
Owning check session: `01a20e58-ec66-7c2b-94b4-741e4461cd8a`.

Scope: one closed smooth branch cell in a finite slab. Both half-scores use the
same primitive vector for each of the three controls. Add the two atom prices
before taking the maximum over controls; the derivative bound is on the joint
score. The two laws may be any probability measures on the closed atom interval.
No numerical curvature or slab replay is included.
-/

@[expose] public section

namespace Masullo.SharedKnotCell

open Set MeasureTheory SplitAtomBernstein

noncomputable section

/-- The two signed primitives followed by the mass primitive. -/
abbrev Primitive := ℝ × ℝ × ℝ

/-- The coefficient vector `start - stop` paired against `(-X, -T(X), u)`. -/
def halfScore (start stop : Primitive) : Score :=
  ⟨start.2.2 - stop.2.2, start.1 - stop.1, start.2.1 - stop.2.1⟩

/-- The source's joint score at a real split with two fixed atoms. -/
def splitAtomScore (p : ℝ → Primitive) (l r s u v : ℝ) : ℝ :=
  (halfScore (p l) (p s)).eval u + (halfScore (p s) (p r)).eval v

/-- The score with the left and right atom replaced by their respective laws. -/
def splitLawScore (p : ℝ → Primitive) (l r s : ℝ) (νL νR : Measure Atom) : ℝ :=
  (halfScore (p l) (p s)).mean νL + (halfScore (p s) (p r)).mean νR

/-- The primitive-vector controls at the left, middle and right of the quadratic
Bernstein representation. The middle control is not the midpoint value. -/
def control (p : ℝ → Primitive) (a b : ℝ) (i : Fin 3) : Primitive :=
  ![p a, (2 : ℝ) • p ((a + b) / 2) - (1 / 2 : ℝ) • (p a + p b), p b] i

/-- The largest joint upper price, not the sum of separately maximized prices. -/
def jointPrice (priceL priceR : Fin 3 → ℝ) : ℝ :=
  max (priceL 0 + priceR 0) (max (priceL 1 + priceR 1) (priceL 2 + priceR 2))

private theorem le_jointPrice (priceL priceR : Fin 3 → ℝ) (i : Fin 3) :
    priceL i + priceR i ≤ jointPrice priceL priceR := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem middle_control_eval (p : ℝ → Primitive) (l r a b u v : ℝ) :
    (halfScore (p l) (control p a b 1)).eval u +
        (halfScore (control p a b 1) (p r)).eval v =
      2 * splitAtomScore p l r ((a + b) / 2) u v -
        (splitAtomScore p l r a u v + splitAtomScore p l r b u v) / 2 := by
  simp [control, splitAtomScore, halfScore, Score.eval, smul_eq_mul]
  ring

-- In centered coordinates `d = h/2`, `y = |s - mid|`, the absolute nodal
-- product is `y * (d² - y²)`. Its sharp cap follows by factoring the deficit.
private theorem abs_nodal_le {a b s : ℝ} (hs : s ∈ Icc a b) :
    |(s - a) * (s - (a + b) / 2) * (s - b)| ≤ (b - a) ^ 3 / (12 * Real.sqrt 3) := by
  let d := (b - a) / 2
  let y := |s - (a + b) / 2|
  let q := Real.sqrt 3
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr (hs.1.trans hs.2)) (by norm_num)
  have hy : 0 ≤ y := abs_nonneg _
  have hq : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq2 : q ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnode : |(s - a) * (s - (a + b) / 2) * (s - b)| = y * (d ^ 2 - y ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.1),
      abs_of_nonpos (sub_nonpos.mpr hs.2), show y ^ 2 = (s - (a + b) / 2) ^ 2 from sq_abs _]
    change (s - a) * y * -(s - b) = _
    dsimp only [d]
    ring
  have hfactor : 0 ≤ (q * y - d) ^ 2 * (q * y + 2 * d) := by positivity
  have hpoly : (q * y - d) ^ 2 * (q * y + 2 * d) =
      2 * d ^ 3 - 3 * q * (y * (d ^ 2 - y ^ 2)) := by
    calc
      _ = q ^ 2 * (q * y ^ 3) - 3 * d ^ 2 * q * y + 2 * d ^ 3 := by ring
      _ = _ := by rw [hq2]; ring
  rw [hpoly] at hfactor
  rw [hnode]
  change _ ≤ (b - a) ^ 3 / (12 * q)
  apply (le_div_iff₀ (by positivity)).2
  dsimp only [d] at hfactor ⊢
  linarith only [hfactor]

private theorem splitAtomScore_le (p : ℝ → Primitive) {l r a b s R : ℝ}
    (hs : s ∈ Icc a b) (priceL priceR : Fin 3 → ℝ) (u v : Atom)
    (hSmooth : ContDiffOn ℝ 3 (fun z ↦ splitAtomScore p l r z u v) (Icc a b))
    (hThird : ∀ z ∈ Ioo a b, |iteratedDeriv 3 (fun y ↦ splitAtomScore p l r y u v) z| ≤ R)
    (hL : ∀ i, (halfScore (p l) (control p a b i)).eval u ≤ priceL i)
    (hR : ∀ i, (halfScore (control p a b i) (p r)).eval v ≤ priceR i) :
    splitAtomScore p l r s u v ≤ jointPrice priceL priceR + R * (b - a) ^ 3 / (72 * Real.sqrt 3) := by
  have hcontrol (i : Fin 3) :
      (halfScore (p l) (control p a b i)).eval u +
        (halfScore (control p a b i) (p r)).eval v ≤ jointPrice priceL priceR :=
    (add_le_add (hL i) (hR i)).trans (le_jointPrice priceL priceR i)
  have ha : splitAtomScore p l r a u v ≤ jointPrice priceL priceR := hcontrol 0
  rcases (hs.1.trans hs.2).lt_or_eq with hab | hab
  · have hb : splitAtomScore p l r b u v ≤ jointPrice priceL priceR := hcontrol 2
    have hm := hcontrol 1
    rw [middle_control_eval] at hm
    have hinterp := MeasurableBernsteinCell.le_cap_add_nodal_error hab hSmooth hThird ha hm hb hs
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (hThird _ hmid)
    refine hinterp.trans (add_le_add_right ?_ _)
    calc
      _ ≤ (R / 6) * ((b - a) ^ 3 / (12 * Real.sqrt 3)) :=
        mul_le_mul_of_nonneg_left (abs_nodal_le hs) (by positivity)
      _ = _ := by ring
  · have hsa : s = a := (hs.2.trans hab.symm.le).antisymm hs.1
    simpa [hsa, hab] using ha

private theorem mean_le {q : Score} {ν : Measure Atom} [IsProbabilityMeasure ν] {B : ℝ}
    (h : ∀ u : Atom, q.eval u ≤ B) : q.mean ν ≤ B := by
  have hc : Continuous q.eval := by
    unfold Score.eval Moment.eval
    fun_prop
  have hi : Integrable (fun u : Atom ↦ q.eval u) ν :=
    integrableOn_univ.mp <|
      (hc.comp continuous_subtype_val).continuousOn.integrableOn_compact isCompact_univ
  simpa only [Score.mean, integral_const, probReal_univ, one_smul] using
    integral_mono hi (integrable_const B) h

/-- For every split in the closed cell inside the slab, the score of two arbitrary
probability laws is at most the largest of the three joint control prices plus
`R * (b - a)^3 / (72 * √3)`. The third derivative is taken for fixed atoms in the
open branch interior. A singleton cell is included, with zero remainder. -/
theorem splitLawScore_le (p : ℝ → Primitive) {l r a b s R : ℝ}
    (hs : l ≤ a ∧ s ∈ Icc a b ∧ b ≤ r) (priceL priceR : Fin 3 → ℝ)
    (hSmooth : ∀ u v : Atom, ContDiffOn ℝ 3 (fun z ↦ splitAtomScore p l r z u v) (Icc a b))
    (hThird : ∀ u v : Atom, ∀ z ∈ Ioo a b,
      |iteratedDeriv 3 (fun y ↦ splitAtomScore p l r y u v) z| ≤ R)
    (hL : ∀ (i : Fin 3) (u : Atom), (halfScore (p l) (control p a b i)).eval u ≤ priceL i)
    (hR : ∀ (i : Fin 3) (v : Atom), (halfScore (control p a b i) (p r)).eval v ≤ priceR i)
    (νL νR : Measure Atom) [IsProbabilityMeasure νL] [IsProbabilityMeasure νR] :
    splitLawScore p l r s νL νR ≤ jointPrice priceL priceR + R * (b - a) ^ 3 / (72 * Real.sqrt 3) := by
  let sl := halfScore (p l) (p s)
  let sr := halfScore (p s) (p r)
  let B := jointPrice priceL priceR + R * (b - a) ^ 3 / (72 * Real.sqrt 3)
  have hatom (u v : Atom) : sl.eval u + sr.eval v ≤ B :=
    splitAtomScore_le p hs.2.1 priceL priceR u v (hSmooth u v) (hThird u v)
      (fun i ↦ hL i u) (fun i ↦ hR i v)
  have hleft (v : Atom) : sl.mean νL ≤ B - sr.eval v :=
    mean_le fun u ↦ le_sub_iff_add_le.mpr (hatom u v)
  have hright : sr.mean νR ≤ B - sl.mean νL :=
    mean_le fun v ↦ by linarith only [hleft v]
  change sl.mean νL + sr.mean νR ≤ B
  linarith only [hright]

end

end Masullo.SharedKnotCell
