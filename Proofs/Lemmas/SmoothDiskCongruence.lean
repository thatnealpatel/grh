module

public import Lemmas.SmoothBranchEvaluation
import Mathlib.Algebra.Polynomial.Div

/-!
# Two-root congruence on a smooth p-adic residue disk

Source: `db84b3c3:.godel/alice/jet-reference-disks.md:35–76`,
with the earlier `db84b3c3:.godel/alice/jet-axis-lcm.md:28–42`.
Owning check session: `01a20f51-211d-73b8-9726-8aa026238fa2`.

Scope: the local implication from free-coordinate depth to ordinate depth for two
roots in one residue disk. The center need not be a root or a row. No determinant
or global divisibility claim is made.
-/

open Polynomial SmoothBranchEvaluation

namespace SmoothDiskCongruence

variable {p : ℕ} [Fact p.Prime]

private theorem reduction_eq_iff {e : ℕ} {u v : ℤ_[p]} :
    PadicInt.toZModPow e u = PadicInt.toZModPow e v ↔ (p : ℤ_[p]) ^ e ∣ u - v := by
  rw [← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

/-- When the ordinate derivative is a unit at the disk center, two roots congruent
in the abscissa modulo `p ^ e` are also congruent in the ordinate modulo `p ^ e`. -/
public theorem dvd_ordinate_diff_of_dvd_abscissa_diff (F : ℤ_[p][X][X])
    {a b x y x₀ y₀ : ℤ_[p]} (hunit : IsUnit (evalAt F.derivative a b))
    (hx : (p : ℤ_[p]) ∣ x - a) (hy : PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 b)
    (hroot : evalAt F x y = 0)
    (hx₀ : (p : ℤ_[p]) ∣ x₀ - a) (hy₀ : PadicInt.toZModPow 1 y₀ = PadicInt.toZModPow 1 b)
    (hroot₀ : evalAt F x₀ y₀ = 0) (e : ℕ) (h : (p : ℤ_[p]) ^ e ∣ x - x₀) :
    (p : ℤ_[p]) ^ e ∣ y - y₀ := by
  obtain ⟨P, hP⟩ := exists_ordinate_polynomial F a b hunit e
  have harg : (p : ℤ_[p]) ^ e ∣ (x - a) - (x₀ - a) := by
    simpa only [sub_sub_sub_cancel_right] using h
  apply reduction_eq_iff.mp
  rw [← hP x y hx hy hroot, ← hP x₀ y₀ hx₀ hy₀ hroot₀]
  exact reduction_eq_iff.mpr (harg.trans (sub_dvd_eval_sub (x - a) (x₀ - a) P))

end SmoothDiskCongruence
