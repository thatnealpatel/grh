module

public import Lemmas.SignedBlockIntervalMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Disclosed-event moment interpolation

Source: `069b23dd:.godel/bob/replacement-frequency-lists.md:7–25`, at source pin
`bb055047`. Owning check session: `01a209a4-4028-76c1-a295-487f5bedcbac`.
The common angular kernel is `K_{80,t}` from `isolated-tuple-hits.md:29` at
that pin. The two-block price is `twoHitMass_le_four_moments` (`8fd18679`),
which uses the disclosed counting argument of `d8953343`.

This file proves the finite-order Hölder step in the proof of (1), including
the displayed ratio on line 23, and applies it to the actual fixed-mask
source mass. Both gates, `|ν| ≤ 2π/t` and `|ν'| ≤ 2π/t`, are unchanged in
`TwoHits`. The list sees only disclosed labels; the replacement witness may
read the whole source. The diagonal estimate, origin lower bound,
full-to-separated comparison, and union over masks needed to finish (1) are
not proved here. The note **uses** (1) (line 27) to rule out pairing a fixed
fraction of `M` by changing half the starts with disclosure `β = γ/3` and lists
of at most `t^(δ_{γ/3} - ε)` intervals, for fixed `0 < ε < δ_{γ/3}`. The donor
splice on line 31 reuses the two-block calculation. Neither application is
an absolute deletion bound at detection scale or a bound on all far-support
partners.
-/

open MeasureTheory

namespace Masullo.DisclosedMomentInterpolation

open DisclosedReplacementList SignedBlockIntervalMoment

variable {α : Type*} [Fintype α]

private theorem integrable_density {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) (j : ℕ) :
    Integrable (fun u ↦ sincKernel t u * ‖char P labels u‖ ^ j) := by
  have hc : Continuous (char P labels) := by
    unfold char phase
    fun_prop
  refine (integrable_sincKernel ht).mul_bdd (c := 1) (hc.norm.pow j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ ?_)
  have hchar : ‖char P labels u‖ ≤ 1 := calc
    _ ≤ ∑ p, ‖(P.weight p : ℂ) * phase (u * labels p)‖ := norm_sum_le _ _
    _ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re, Complex.norm_real,
        abs_of_nonneg (P.nonneg _), P.total]
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_one₀ (norm_nonneg _) hchar

private theorem moment_nonneg {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) (j : ℕ) :
    0 ≤ moment (sincKernel t) P labels j :=
  integral_nonneg fun u ↦ mul_nonneg (sincKernel_nonneg ht u) (pow_nonneg (norm_nonneg _) _)

/-- Hölder applied to powers of the densities themselves, so it needs no
positivity of their integrals and no change of the underlying measure. -/
private theorem integral_rpow_mul_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hf₀ : ∀ u, 0 ≤ f u) (hg₀ : ∀ u, 0 ≤ g u) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫ u, f u ^ a * g u ^ b) ≤ (∫ u, f u) ^ a * (∫ u, g u) ^ b := by
  have hconj : Real.HolderConjugate a⁻¹ b⁻¹ :=
    ⟨by simpa only [inv_inv, inv_one] using hab, inv_pos.mpr ha, inv_pos.mpr hb⟩
  have cancel_power {h : ℝ → ℝ} (hn : ∀ u, 0 ≤ h u) {w : ℝ} (hw : 0 < w) (u : ℝ) :
      (h u ^ w) ^ w⁻¹ = h u := by
    rw [← Real.rpow_mul (hn u), mul_inv_cancel₀ hw.ne', Real.rpow_one]
  have hLp {h : ℝ → ℝ} (hi : Integrable h) (hn : ∀ u, 0 ≤ h u) {w : ℝ} (hw : 0 < w) :
      MemLp (fun u ↦ h u ^ w) (ENNReal.ofReal w⁻¹) := by
    have hm : AEStronglyMeasurable (fun u ↦ h u ^ w) volume :=
      (hi.aestronglyMeasurable.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
    have hw' := inv_pos.mpr hw
    refine (integrable_norm_rpow_iff hm (by simp [hw]) (by simp)).1 ?_
    rw [ENNReal.toReal_ofReal hw'.le]
    refine hi.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    change h u = ‖h u ^ w‖ ^ w⁻¹
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn u) _), cancel_power hn hw]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall fun u ↦ Real.rpow_nonneg (hf₀ u) a)
    (Filter.Eventually.of_forall fun u ↦ Real.rpow_nonneg (hg₀ u) b)
    (hLp hf hf₀ ha) (hLp hg hg₀ hb)
  simpa only [one_div, inv_inv, cancel_power hf₀ ha, cancel_power hg₀ hb] using h

/-- The same sinc-square kernel at orders `k`, `m`, and `n` gives finite
log-convex interpolation, with equality at either endpoint. -/
public theorem moment_le_interpolation {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {k m n : ℕ}
    (hkn : k < n) (hkm : k ≤ m) (hmn : m ≤ n) :
    moment (sincKernel t) P labels m ≤
      moment (sincKernel t) P labels k ^ (((n : ℝ) - m) / ((n : ℝ) - k)) *
      moment (sincKernel t) P labels n ^ (((m : ℝ) - k) / ((n : ℝ) - k)) := by
  have hd : 0 < (n : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hkn)
  rcases eq_or_lt_of_le hkm with rfl | hkm
  · simp [hd.ne']
  rcases eq_or_lt_of_le hmn with rfl | hmn
  · simp [hd.ne']
  let a : ℝ := ((n : ℝ) - m) / ((n : ℝ) - k)
  let b : ℝ := ((m : ℝ) - k) / ((n : ℝ) - k)
  have ha : 0 < a := div_pos (sub_pos.mpr (Nat.cast_lt.mpr hmn)) hd
  have hb : 0 < b := div_pos (sub_pos.mpr (Nat.cast_lt.mpr hkm)) hd
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, sub_add_sub_cancel, div_self hd.ne']
  have hindex : (k : ℝ) * a + (n : ℝ) * b = (m : ℝ) := by
    dsimp [a, b]
    field_simp [hd.ne']
    ring
  let F (j : ℕ) (u : ℝ) := sincKernel t u * ‖char P labels u‖ ^ j
  have hF₀ (j : ℕ) (u : ℝ) : 0 ≤ F j u :=
    mul_nonneg (sincKernel_nonneg ht u) (pow_nonneg (norm_nonneg _) _)
  have hFmul (u : ℝ) : F k u ^ a * F n u ^ b = F m u := by
    have hK := sincKernel_nonneg ht u
    have hC := norm_nonneg (char P labels u)
    dsimp only [F]
    rw [Real.mul_rpow hK (pow_nonneg hC _), Real.mul_rpow hK (pow_nonneg hC _),
      mul_mul_mul_comm, ← Real.rpow_add_of_nonneg hK ha.le hb.le, hab, Real.rpow_one,
      ← Real.rpow_natCast _ k, ← Real.rpow_natCast _ n, ← Real.rpow_mul hC, ← Real.rpow_mul hC,
      ← Real.rpow_add_of_nonneg hC (by positivity) (by positivity), hindex, Real.rpow_natCast]
  change (∫ u, F m u) ≤ (∫ u, F k u) ^ a * (∫ u, F n u) ^ b
  simpa only [hFmul] using integral_rpow_mul_le (f := F k) (g := F n)
    (integrable_density ht P labels k) (integrable_density ht P labels n) (hF₀ k) (hF₀ n)
    ha hb hab

private theorem moment_mul_le_interpolation {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {k n r v e : ℕ} (hkn : k < n)
    (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n) (hsize : r + v + e = n) :
    moment (sincKernel t) P labels r * moment (sincKernel t) P labels v ≤
      moment (sincKernel t) P labels k ^ (((n : ℝ) + e) / ((n : ℝ) - k)) *
      moment (sincKernel t) P labels n ^ (((n : ℝ) - 2 * k - e) / ((n : ℝ) - k)) := by
  let U := moment (sincKernel t) P labels
  let a (j : ℕ) : ℝ := ((n : ℝ) - j) / ((n : ℝ) - k)
  let b (j : ℕ) : ℝ := ((j : ℝ) - k) / ((n : ℝ) - k)
  have hd : 0 < (n : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hkn)
  have ha {j : ℕ} (hj : j ≤ n) : 0 ≤ a j :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hj)) hd.le
  have hb {j : ℕ} (hj : k ≤ j) : 0 ≤ b j :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hj)) hd.le
  have hUk : 0 ≤ U k := moment_nonneg ht P labels k
  have hUn : 0 ≤ U n := moment_nonneg ht P labels n
  have hsize' : (r : ℝ) + v + e = (n : ℝ) := by exact_mod_cast hsize
  have hA : a r + a v = ((n : ℝ) + e) / ((n : ℝ) - k) := by
    dsimp [a]
    rw [← add_div]
    congr 1
    linarith
  have hB : b r + b v = ((n : ℝ) - 2 * k - e) / ((n : ℝ) - k) := by
    dsimp [b]
    rw [← add_div]
    congr 1
    linarith
  calc
    U r * U v ≤ (U k ^ a r * U n ^ b r) * (U k ^ a v * U n ^ b v) :=
      mul_le_mul (moment_le_interpolation ht P labels hkn hkr hrn)
        (moment_le_interpolation ht P labels hkn hkv hvn) (moment_nonneg ht P labels v)
        (mul_nonneg (Real.rpow_nonneg hUk _) (Real.rpow_nonneg hUn _))
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add_of_nonneg hUk (ha hrn) (ha hvn),
        ← Real.rpow_add_of_nonneg hUn (hb hkr) (hb hkv), hA, hB]

/-- The ratio `U_r U_v / U_n` on line 23 of the source. Only this normalized
form needs strict positivity of `U_n`. -/
public theorem moment_mul_div_le_interpolation {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {k n r v e : ℕ} (hkn : k < n)
    (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n) (hsize : r + v + e = n)
    (hUn : 0 < moment (sincKernel t) P labels n) :
    (moment (sincKernel t) P labels r * moment (sincKernel t) P labels v) /
      moment (sincKernel t) P labels n ≤
        moment (sincKernel t) P labels k ^ (((n : ℝ) + e) / ((n : ℝ) - k)) *
        moment (sincKernel t) P labels n ^ (-((k : ℝ) + e) / ((n : ℝ) - k)) := by
  have hd : 0 < (n : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hkn)
  have hexp : (((n : ℝ) - 2 * k - e) / ((n : ℝ) - k)) - 1 =
      -((k : ℝ) + e) / ((n : ℝ) - k) := by
    field_simp [hd.ne']
    ring
  refine (div_le_div_of_nonneg_right
    (moment_mul_le_interpolation ht P labels hkn hkr hrn hkv hvn hsize) hUn.le).trans_eq ?_
  rw [mul_div_assoc, ← hexp, Real.rpow_sub hUn, Real.rpow_one]

/-- The actual two-hit mass for a fixed mask is bounded by the endpoint
moments with real exponents. Neither endpoint moment is assumed positive. -/
public theorem twoHitMass_le_interpolated_moments {Z : Type*} [Fintype Z]
    {t : ℝ} (ht : 0 < t) (Pz : FiniteWeightLaw Z) (P : FiniteWeightLaw α)
    (labels : α → ℝ) {r v : ℕ} (removedSign : Fin r → Bool)
    (retainedSourceSign retainedTargetSign : Fin v → Bool)
    (sourceDisclosed targetDisclosed : Z → ℝ) (D : Z → Finset ℝ)
    (admissible : Z → (Fin v → α) → (Fin r → α) → ℝ → Prop) {N : ℕ}
    (hcard : ∀ z, (D z).card ≤ N) {k n e : ℕ} (hkn : k < n)
    (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n) (hsize : r + v + e = n) :
    twoHitMass t Pz (iid P v) (iid P r) sourceDisclosed targetDisclosed
      (signedSum labels retainedSourceSign) (signedSum labels retainedTargetSign)
      (signedSum labels removedSign) D admissible ≤
        4 * (N : ℝ) * moment (sincKernel t) P labels k ^ (((n : ℝ) + e) / ((n : ℝ) - k)) *
          moment (sincKernel t) P labels n ^ (((n : ℝ) - 2 * k - e) / ((n : ℝ) - k)) := by
  have hmass := twoHitMass_le_four_moments ht Pz P labels removedSign retainedSourceSign
    retainedTargetSign sourceDisclosed targetDisclosed D admissible hcard
  have hprod := moment_mul_le_interpolation ht P labels hkn hkr hrn hkv hvn hsize
  exact hmass.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * (N : ℝ)))

end Masullo.DisclosedMomentInterpolation
