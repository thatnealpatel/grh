module

public import Lemmas.PrimeCubeShellMoment
import all Lemmas.PrimePairShellMoment
import all Lemmas.ProductLaurentMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Flagged measure on a continuous prime-cube shell

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:52–66` (discovery pin `4160d1ef`).
Owning check session: `01a20ca9-0415-7de3-a7c2-ad7d2c76dee0`.

This is the finite Markov step of (2) for the polynomial of coalesced balanced keys.
It uses the strict frequency cutoff on the continuous shell; it does not estimate
label multiplicities, take an asymptotic, or count sample nodes.
-/

open MeasureTheory

namespace Masullo.PrimeCubeShellTail

open LaurentCircleMoment (uniformCircle)
open PrimeCubeShellMoment (primeFlow integral_shellKernel_mul_moment_eq)
open PrimePairShellMoment (shellKernel quarter_le_sinc_sq integrable_shellKernel)
open ProductLaurentMoment (monomial phaseFactor supportSize continuous_monomial
  integral_norm_laurent_sum_pow_le_of_support_le)

variable {ι : Type*} [Fintype ι]

private theorem quarter_le_shellKernel {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Set.Icc t (5 * t / 4)) : 1 / 4 ≤ shellKernel t (9 * t / 8) u := by
  apply quarter_le_sinc_sq
  apply abs_le.mpr
  have hden : 0 < 2 * t := by positivity
  exact ⟨(le_div_iff₀ hden).mpr (by linarith [hu.1]),
    (div_le_iff₀ hden).mpr (by linarith [hu.2])⟩

private theorem norm_monomial (v : ι → Fin 3) (z : ι → Circle) : ‖monomial v z‖ = 1 := by
  rw [monomial, norm_prod]
  apply Finset.prod_eq_one
  intro i _
  unfold phaseFactor
  split_ifs <;> simp

/-- For `F` the finite prime-flow Laurent sum and `B` its support-weighted squared
coefficient sum, the Lebesgue measure of `‖F‖ ≥ η` on `[t, 5t/4]` is at most
`8πt (B/η²)^m`. The absolute threshold includes equality, and the coefficients
may be arbitrary complex numbers. -/
public theorem volume_shell_superlevel_le {p : ι → ℕ} {X t η : ℝ} {m R : ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (hpX : ∀ i, (p i : ℝ) ≤ X)
    (hX : 1 ≤ X) (hm : 1 ≤ m) (ht : X ^ (m * R) < t) (hη : 0 < η)
    (S : Finset (ι → Fin 3)) (c : (ι → Fin 3) → ℂ)
    (hsize : ∀ v ∈ S, supportSize v = R)
    (hbalance : ∀ v ∈ S,
      (Finset.univ.filter fun i ↦ v i = 1).card = (Finset.univ.filter fun i ↦ v i = 2).card) :
    volume {u : ℝ | u ∈ Set.Icc t (5 * t / 4) ∧ η ≤ ‖∑ v ∈ S, c v * monomial v (primeFlow p u)‖} ≤
      ENNReal.ofReal (8 * Real.pi * t * (((4 * (m : ℝ) - 2) ^ R * ∑ v ∈ S, ‖c v‖ ^ 2) / η ^ 2) ^ m) := by
  let F (u : ℝ) := ∑ v ∈ S, c v * monomial v (primeFlow p u)
  let B := (4 * (m : ℝ) - 2) ^ R * ∑ v ∈ S, ‖c v‖ ^ 2
  let E := {u : ℝ | u ∈ Set.Icc t (5 * t / 4) ∧ η ≤ ‖F u‖}
  let K := shellKernel t (9 * t / 8)
  let G (u : ℝ) := K u * ‖F u‖ ^ (2 * m)
  let a := η ^ (2 * m) / 4
  change volume E ≤ ENNReal.ofReal (8 * Real.pi * t * (B / η ^ 2) ^ m)
  have ht₀ : 0 < t := (pow_pos (zero_lt_one.trans_le hX) _).trans ht
  have ha : 0 < a := by dsimp [a]; positivity
  have hK₀ (u : ℝ) : 0 ≤ K u := sq_nonneg _
  have hG₀ (u : ℝ) : 0 ≤ G u := mul_nonneg (hK₀ u) (pow_nonneg (norm_nonneg _) _)
  have htorus :
      (∫ z : ι → Circle, ‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)
        ∂Measure.pi (fun _ : ι ↦ uniformCircle)) ≤ B ^ m :=
    integral_norm_laurent_sum_pow_le_of_support_le hm S c fun v hv _ ↦ (hsize v hv).le
  have hmoment : (∫ u, G u) ≤ 2 * Real.pi * t * B ^ m := by
    have htransfer := integral_shellKernel_mul_moment_eq hp hinj hpX hX hm ht S c hsize hbalance
    exact htransfer.le.trans (mul_le_mul_of_nonneg_left htorus (by positivity))
  have hflow : Continuous (primeFlow p) :=
    continuous_pi fun i ↦ Circle.exp.continuous.comp (continuous_id.mul_const _)
  have hF : Continuous F :=
    continuous_finsetSum _ fun v _ ↦ continuous_const.mul ((continuous_monomial v).comp hflow)
  have hFbound (u : ℝ) : ‖F u‖ ≤ ∑ v ∈ S, ‖c v‖ := by
    simpa only [F, norm_mul, norm_monomial, mul_one] using
      (norm_sum_le S (fun v ↦ c v * monomial v (primeFlow p u)))
  have hG : Integrable G := by
    apply (integrable_shellKernel ht₀ _).mul_bdd (c := (∑ v ∈ S, ‖c v‖) ^ (2 * m))
      (hF.norm.pow (2 * m)).aestronglyMeasurable
    filter_upwards with u
    change ‖‖F u‖ ^ (2 * m)‖ ≤ _
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFbound u) _
  have hthreshold : E ⊆ {u : ℝ | ENNReal.ofReal a ≤ ENNReal.ofReal (G u)} := by
    intro u hu
    change u ∈ Set.Icc t (5 * t / 4) ∧ η ≤ ‖F u‖ at hu
    apply ENNReal.ofReal_le_ofReal
    calc
      a = (1 / 4 : ℝ) * η ^ (2 * m) := by dsimp [a]; ring
      _ ≤ G u := mul_le_mul (quarter_le_shellKernel ht₀ hu.1)
        (pow_le_pow_left₀ hη.le hu.2 _) (pow_nonneg hη.le _) (hK₀ u)
  calc
    volume E ≤ volume {u : ℝ | ENNReal.ofReal a ≤ ENNReal.ofReal (G u)} := measure_mono hthreshold
    _ ≤ (∫⁻ u, ENNReal.ofReal (G u)) / ENNReal.ofReal a :=
      meas_ge_le_lintegral_div hG.aemeasurable.ennreal_ofReal
        (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ u, G u) / a) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hG₀),
        ENNReal.ofReal_div_of_pos ha]
    _ ≤ ENNReal.ofReal ((2 * Real.pi * t * B ^ m) / a) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hmoment ha.le)
    _ = _ := by
      congr 1
      dsimp only [a]
      rw [pow_mul, div_pow, div_div_eq_mul_div]
      ring

end Masullo.PrimeCubeShellTail
