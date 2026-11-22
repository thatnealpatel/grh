module

public import Lemmas.FiniteHeckeEulerBounds
public import Theorems.FiniteHeckeRightLine
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

/-!
# Logarithmic differentiation of the finite Hecke Euler product

Masullo expands the inverse finite Euler factor of (3.2.1.1), p. 122, in
(B.4.2.7), p. 615. We check the sign and the positive-power indexing by
ordinary differentiation and a geometric series. Lemma 3.2.1.1, p. 123,
states compact-uniform product convergence. For the finite part of
(B.4.2.5)–(6), convergence just on the integration line would not justify
complex differentiation. The project proves local uniform product
convergence and nonvanishing on `Re s > 1` via
`finiteHeckeEulerFactor_hasProdLocallyUniformlyOn` and
`finiteHeckeEulerProduct_ne_zero`, using the ideal count and the same
majorant as for integration. The resulting identity is
for the finite product, not a completed or continued Hecke L-function.
-/

open Complex Filter IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

/-- Masullo's local expansion (B.4.2.7) follows on `Re s > 0` from
`q_v > 1` and a geometric series beginning at the first power. -/
public theorem finiteHeckeEulerFactor_logDeriv {z : Places → ℂ} (v : Places)
    (hz : ‖z v‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    finiteHeckeEulerFactor z v s ≠ 0 ∧ DifferentiableAt ℂ (finiteHeckeEulerFactor z v) s ∧
    HasSum (fun k : ℕ ↦ finiteHeckeTerm z s (v, k)) (-logDeriv (finiteHeckeEulerFactor z v) s) := by
  let l : ℂ := Real.log (finitePlaceNorm v)
  let w := finiteHeckeMonomial z v s
  have hden : 1 - w ≠ 0 := finiteHecke_denom_ne_zero hz hs
  have hD := ((hasDerivAt_finiteHeckeMonomial z v s).const_sub 1).fun_inv hden
  refine ⟨inv_ne_zero hden, hD.differentiableAt, ?_⟩
  have hlog : -logDeriv (finiteHeckeEulerFactor z v) s = l * w * (1 - w)⁻¹ := by
    rw [logDeriv_apply]
    change -(deriv (fun t ↦ (1 - finiteHeckeMonomial z v t)⁻¹) s / (1 - w)⁻¹) = _
    rw [hD.deriv]
    change -(-(-(-l * w)) / (1 - w) ^ 2 / (1 - w)⁻¹) = _
    field_simp
  rw [hlog]
  refine ((hasSum_geometric_of_norm_lt_one (norm_finiteHeckeMonomial_lt_one hz hs)).mul_left
    (l * w)).congr_fun fun k ↦ ?_
  unfold finiteHeckeTerm
  dsimp only [w, l, finiteHeckeMonomial]
  rw [mul_assoc, mul_assoc (↑(Real.log (finitePlaceNorm v)) : ℂ), ← pow_succ', mul_pow,
    ← Complex.exp_nat_mul]
  congr 3
  ring

/-- The finite Euler product, without Archimedean factors (3.2.1.7). -/
@[expose] public noncomputable def finiteHeckeEulerProduct (z : Places → ℂ) (s : ℂ) : ℂ :=
  ∏' v, finiteHeckeEulerFactor z v s

/-- Finite-part logarithmic differentiation in (B.4.2.5)–(7).
The summation is over places and positive powers in one absolutely
convergent series, as supplied by `finiteHecke_right_line_majorant`. -/
public theorem finiteHeckeEulerProduct_logDeriv {z : Places → ℂ} (hz : ∀ v, ‖z v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeEulerProduct z s ≠ 0 ∧ DifferentiableAt ℂ (finiteHeckeEulerProduct z) s ∧
    HasSum (finiteHeckeTerm z s) (-logDeriv (finiteHeckeEulerProduct z) s) := by
  let U : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hloc (v : Places) {t : ℂ} (ht : 0 < t.re) := finiteHeckeEulerFactor_logDeriv v (hz v) ht
  have hd (v : Places) : DifferentiableOn ℂ (finiteHeckeEulerFactor z v) U := fun t ht ↦
    (hloc v (zero_lt_one.trans ht)).2.1.differentiableWithinAt
  have hunif := finiteHeckeEulerFactor_hasProdLocallyUniformlyOn hz
  have hnonzero := finiteHeckeEulerProduct_ne_zero hz hs
  have hdiff := hunif.differentiableOn (.of_forall fun F ↦ by
    simpa only [Finset.prod_fn] using (DifferentiableOn.finsetProd (fun v _ ↦ hd v))) hopen
  refine ⟨hnonzero, (hdiff s hs).differentiableAt (hopen.mem_nhds hs), ?_⟩
  obtain ⟨c, hbound⟩ := finiteHecke_right_line_majorant (K := K) hs
  have hsum : Summable (finiteHeckeTerm z s) := c.of_norm_bounded (hbound z hz s le_rfl)
  have hlocal (v : Places) : (∑' k, finiteHeckeTerm z s (v, k)) =
      -logDeriv (finiteHeckeEulerFactor z v) s := (hloc v (zero_lt_one.trans hs)).2.2.tsum_eq
  have hlog : Summable (fun v ↦ logDeriv (finiteHeckeEulerFactor z v) s) := by
    simpa only [hlocal, neg_neg] using hsum.prod.neg
  have heq := logDeriv_tprod_eq_tsum hopen hs (fun v ↦ (hloc v (zero_lt_one.trans hs)).1)
    hd hlog hunif.multipliableLocallyUniformlyOn hnonzero
  change HasSum (finiteHeckeTerm z s) (-logDeriv (fun t ↦ ∏' v, finiteHeckeEulerFactor z v t) s)
  rw [heq, ← tsum_neg, hsum.hasSum_iff, hsum.tsum_prod]
  simp only [hlocal]

end Masullo
