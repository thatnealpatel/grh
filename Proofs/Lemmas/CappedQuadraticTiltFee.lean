module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capped quadratic tilt fee

Source: `31754ce259eb:.godel/bob/eight-knot-local-q-33.md:37–64,166–186`,
with `s = Q(V)` and `L` the raw score `𝓛`.
Consumer: `df36e0b4e122:.godel/bob/check-eight-knots-local-q-33.py:50–61,144–160`.
Owning check session: `01a21064-e15a-7bed-9349-0a50688b4367`.

For `D = B_left - B_right`, the added tilt `-βD` shifts the left coefficient by
`+β` and the right coefficient by `-β` in the consumer's negative coefficient
convention. The bounds below take the slack and, for the quadratic branch, the
pairing inequality as hypotheses. They do not verify a numerical certificate
or require the center to be a feasible law.
-/

public section

namespace Masullo.CappedQuadraticTiltFee

/-- The drop cap alone pays for the tilt when positivity of `a` is not certified. -/
theorem le_tilted_add_cap {M L σ s D β : ℝ}
    (hslack : M - 8 / 9 ≤ L - σ * s) (hs : 0 ≤ s) (hσ : 0 < σ)
    (hD : D ≤ 2) (hβ : 0 ≤ β) :
    M - 8 / 9 ≤ (L - β * D) + 2 * β := by
  have htilt := mul_le_mul_of_nonneg_left hD hβ
  have hloss := mul_nonneg hσ.le hs
  linarith only [hslack, htilt, hloss]

/-- With a positive pairing coefficient, the smaller of the cap and quadratic fee suffices.
The drop `D` can have either sign. -/
theorem le_tilted_add_min_fee {M L σ s D β C err den a : ℝ}
    (hslack : M - 8 / 9 ≤ L - σ * s) (hs : 0 ≤ s) (hσ : 0 < σ)
    (hD : D ≤ 2) (hβ : 0 ≤ β) (_hC : 0 ≤ C) (_herr : 0 ≤ err)
    (hden : 0 ≤ den) (ha : 0 < a) (hpair : a * D ≤ err + C * Real.sqrt (s * den)) :
    M - 8 / 9 ≤ (L - β * D) + min (2 * β) (β * err / a + (β * C / a) ^ 2 * den / (4 * σ)) := by
  have hscaled : β * D ≤ β * err / a + (β * C / a) * Real.sqrt (s * den) := by
    calc
      β * D = (β / a) * (a * D) := by field_simp
      _ ≤ (β / a) * (err + C * Real.sqrt (s * den)) :=
        mul_le_mul_of_nonneg_left hpair (div_nonneg hβ ha.le)
      _ = _ := by ring
  have hquad : (β * C / a) * Real.sqrt (s * den) - σ * s ≤
      (β * C / a) ^ 2 * den / (4 * σ) := by
    rw [Real.sqrt_mul hs]
    apply (le_div_iff₀ (show 0 < 4 * σ by positivity)).2
    nlinarith only [sq_nonneg (2 * σ * Real.sqrt s - (β * C / a) * Real.sqrt den),
      congrArg (fun x : ℝ => 4 * σ ^ 2 * x) (Real.sq_sqrt hs),
      congrArg (fun x : ℝ => (β * C / a) ^ 2 * x) (Real.sq_sqrt hden)]
  rw [add_min]
  refine le_min (le_tilted_add_cap hslack hs hσ hD hβ) ?_
  linarith only [hslack, hscaled, hquad]

end Masullo.CappedQuadraticTiltFee
