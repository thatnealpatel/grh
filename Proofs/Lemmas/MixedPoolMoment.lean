module

public import Lemmas.DisclosedMomentInterpolation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Three-block moment bound for a fixed minority mask

Source: `23e865ff:.godel/bob/net-pool-supply.md:20–32` (especially line 28).
Owning check session: `01a209ce-61c0-7258-9ef8-09cad8ad12db`.

Reindex the original iid source slots as the minority positions of copy 1 and
copy 2, then the majority positions of each copy. In the application `N = 2n`,
`P.weight p = w_p/A`, and `labels p = log(1 + d/p)` on the finite set of starts.
All signs are fixed, including any orientation of a whole copy (which preserves
its symmetric source window).
The minority gate is `0 < |W| ≤ 4π/t`. Exposing its labels fixes the minority
contribution in each copy, hence the center of each remaining `2π/t` window.
The two conditional interval masses multiply by the iid slot law; the three
hit events themselves need not be independent.

The next use in the source (line 32) is to sum this fixed-mask bound over masks
and orientations against the original source weight. Here we prove only the
three-hit mass estimate and its finite-order interpolation, not the implication
from a competing split, the mask union, or the comparison with arithmetic
central mass. No estimate for the entire mixed debit is asserted.
-/

open scoped BigOperators

namespace Masullo.MixedPoolMoment

open DisclosedReplacementList SignedBlockIntervalMoment

variable {α : Type*} [Fintype α]

/-- The two copy windows include their respective contributions from `z`,
while the extra window tests the signed sum of the entire minority block. -/
@[expose] public def ThreeHits (t : ℝ) (labels : α → ℝ) {m₁ m₂ r v : ℕ}
    (σ₁ : Fin m₁ → Bool) (σ₂ : Fin m₂ → Bool) (σr : Fin r → Bool) (σv : Fin v → Bool)
    (z : Fin (m₁ + m₂) → α) (x : Fin r → α) (y : Fin v → α) : Prop :=
  let W := signedSum labels (Fin.append σ₁ σ₂) z
  let W₁ := signedSum labels σ₁ (z ∘ Fin.castAdd m₂)
  let W₂ := signedSum labels σ₂ (z ∘ Fin.natAdd m₁)
  (0 < |W| ∧ |W| ≤ 4 * Real.pi / t) ∧
    |signedSum labels σr x + W₁| ≤ 2 * Real.pi / t ∧
    |signedSum labels σv y + W₂| ≤ 2 * Real.pi / t

/-- Source mass under the original iid law on `N` slots. The fixed mask
ordering `e` lists the two minority pieces followed by the two majority blocks. -/
@[expose] public noncomputable def threeHitMass (t : ℝ) (P : FiniteWeightLaw α)
    (labels : α → ℝ) {m₁ m₂ r v N : ℕ} (e : Fin (m₁ + m₂ + r + v) ≃ Fin N)
    (σ₁ : Fin m₁ → Bool) (σ₂ : Fin m₂ → Bool) (σr : Fin r → Bool) (σv : Fin v → Bool) : ℝ :=
  (iid P N).mass fun a ↦
    let p := (Fin.appendEquiv (m₁ + m₂ + r) v).symm (a ∘ e)
    let q := (Fin.appendEquiv (m₁ + m₂) r).symm p.1
    ThreeHits t labels σ₁ σ₂ σr σv q.1 q.2 p.2

private theorem iid_mass_reindex (P : FiniteWeightLaw α) {d N : ℕ} (e : Fin d ≃ Fin N)
    (hit : (Fin d → α) → Prop) :
    (iid P N).mass (fun a ↦ hit (a ∘ e)) = (iid P d).mass hit := by
  classical
  unfold FiniteWeightLaw.mass
  apply Fintype.sum_equiv (Equiv.piCongrLeft' (fun _ : Fin N ↦ α) e.symm)
  intro a
  change (if hit (a ∘ e) then (∏ j, P.weight (a j)) else 0) =
    (if hit (a ∘ e) then (∏ j, P.weight (a (e j))) else 0)
  rw [e.prod_comp (fun j ↦ P.weight (a j))]

private theorem iid_weight_append (P : FiniteWeightLaw α) {d s : ℕ}
    (a : Fin d → α) (b : Fin s → α) :
    (iid P (d + s)).weight (Fin.append a b) = (iid P d).weight a * (iid P s).weight b := by
  simp only [iid, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

private noncomputable def gatedWeight (P : FiniteWeightLaw α) (p : α → Prop) (a : α) : ℝ := by
  classical
  exact if p a then P.weight a else 0

/-- Sum over the exposed minority labels, with no division by their mass.
For each exposure the two remaining sums factor under the original iid law. -/
private theorem iid_mass_blocks (P : FiniteWeightLaw α) {m r v : ℕ}
    (g : (Fin m → α) → Prop) (p : (Fin m → α) → (Fin r → α) → Prop)
    (q : (Fin m → α) → (Fin v → α) → Prop) :
    (iid P (m + r + v)).mass (fun a ↦
      let b := (Fin.appendEquiv (m + r) v).symm a
      let c := (Fin.appendEquiv m r).symm b.1
      g c.1 ∧ p c.1 c.2 ∧ q c.1 b.2) =
    ∑ z, gatedWeight (iid P m) g z * ((iid P r).mass (p z) * (iid P v).mass (q z)) := by
  classical
  let e : ((Fin m → α) × (Fin r → α)) × (Fin v → α) ≃ (Fin (m + r + v) → α) :=
    ((Fin.appendEquiv m r).prodCongr (Equiv.refl _)).trans (Fin.appendEquiv (m + r) v)
  unfold FiniteWeightLaw.mass
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    Equiv.symm_apply_apply]
  change (if g z ∧ p z x ∧ q z y then
      (iid P (m + r + v)).weight (Fin.append (Fin.append z x) y) else 0) = _
  rw [iid_weight_append, iid_weight_append]
  by_cases hg : g z <;> by_cases hp : p z x <;> by_cases hq : q z y <;>
    simp [gatedWeight, hg, hp, hq, mul_assoc]

private theorem mass_nonneg (P : FiniteWeightLaw α) (p : α → Prop) : 0 ≤ P.mass p := by
  classical
  exact Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact P.nonneg x
    · exact le_rfl

private theorem mass_mono (P : FiniteWeightLaw α) {p q : α → Prop}
    (hpq : ∀ a, p a → q a) : P.mass p ≤ P.mass q := by
  classical
  unfold FiniteWeightLaw.mass
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hp : p a
  · simp [hp, hpq a hp]
  · by_cases hq : q a <;> simp [hp, hq, P.nonneg a]

private theorem moment_nonneg {t : ℝ} (ht : 0 < t) (P : FiniteWeightLaw α)
    (labels : α → ℝ) (j : ℕ) : 0 ≤ moment (sincKernel t) P labels j :=
  MeasureTheory.integral_nonneg fun u ↦
    mul_nonneg (sincKernel_nonneg ht u) (pow_nonneg (norm_nonneg _) _)

/-- Fixed-mask source mass: all three gates together cost at most `8 U_m U_r U_v`
for `m = m₁ + m₂`, with no moment positivity assumption. -/
public theorem threeHitMass_le_eight_moments {t : ℝ} (ht : 0 < t) (P : FiniteWeightLaw α)
    (labels : α → ℝ) {m₁ m₂ r v N : ℕ} (e : Fin (m₁ + m₂ + r + v) ≃ Fin N)
    (σ₁ : Fin m₁ → Bool) (σ₂ : Fin m₂ → Bool) (σr : Fin r → Bool) (σv : Fin v → Bool) :
    threeHitMass t P labels e σ₁ σ₂ σr σv ≤
      8 * moment (sincKernel t) P labels (m₁ + m₂) * moment (sincKernel t) P labels r *
        moment (sincKernel t) P labels v := by
  classical
  let U := moment (sincKernel t) P labels
  let W := signedSum labels (Fin.append σ₁ σ₂)
  let g (z : Fin (m₁ + m₂) → α) := 0 < |W z| ∧ |W z| ≤ 4 * Real.pi / t
  let p (z : Fin (m₁ + m₂) → α) (x : Fin r → α) :=
    |signedSum labels σr x + signedSum labels σ₁ (z ∘ Fin.castAdd m₂)| ≤ 2 * Real.pi / t
  let q (z : Fin (m₁ + m₂) → α) (y : Fin v → α) :=
    |signedSum labels σv y + signedSum labels σ₂ (z ∘ Fin.natAdd m₁)| ≤ 2 * Real.pi / t
  have h4 : 4 * Real.pi / t ≤ 40 / t :=
    (div_le_div_iff_of_pos_right ht).2 (by linarith [Real.pi_lt_four])
  have h2 : 2 * Real.pi / t ≤ 40 / t :=
    (div_le_div_iff_of_pos_right ht).2 (by linarith [Real.pi_lt_four])
  have hg : (iid P (m₁ + m₂)).mass g ≤ 2 * U (m₁ + m₂) := calc
    _ ≤ (iid P (m₁ + m₂)).mass (fun z ↦ |W z - 0| ≤ 4 * Real.pi / t) :=
      mass_mono _ (fun z hz ↦ by simpa only [sub_zero] using hz.2)
    _ ≤ _ := intervalMass_le_two_moment ht P labels (Fin.append σ₁ σ₂) 0 _ h4
  have hp (z : Fin (m₁ + m₂) → α) : (iid P r).mass (p z) ≤ 2 * U r := by
    simpa only [p, sub_neg_eq_add] using intervalMass_le_two_moment ht P labels σr
      (-signedSum labels σ₁ (z ∘ Fin.castAdd m₂)) _ h2
  have hq (z : Fin (m₁ + m₂) → α) : (iid P v).mass (q z) ≤ 2 * U v := by
    simpa only [q, sub_neg_eq_add] using intervalMass_le_two_moment ht P labels σv
      (-signedSum labels σ₂ (z ∘ Fin.natAdd m₁)) _ h2
  have hr₀ : 0 ≤ 2 * U r := mul_nonneg (by norm_num) (moment_nonneg ht P labels r)
  have hv₀ : 0 ≤ 2 * U v := mul_nonneg (by norm_num) (moment_nonneg ht P labels v)
  calc
    _ = ∑ z, gatedWeight (iid P (m₁ + m₂)) g z *
        ((iid P r).mass (p z) * (iid P v).mass (q z)) := by
      have h := iid_mass_reindex P e (fun a ↦
        let p := (Fin.appendEquiv (m₁ + m₂ + r) v).symm a
        let q := (Fin.appendEquiv (m₁ + m₂) r).symm p.1
        ThreeHits t labels σ₁ σ₂ σr σv q.1 q.2 p.2)
      exact h.trans (iid_mass_blocks P g p q)
    _ ≤ ∑ z, gatedWeight (iid P (m₁ + m₂)) g z * (2 * U r * (2 * U v)) := by
      refine Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left
        (mul_le_mul (hp z) (hq z) (mass_nonneg _ _) hr₀) ?_
      unfold gatedWeight
      split_ifs
      · exact (iid P (m₁ + m₂)).nonneg z
      · exact le_rfl
    _ = (iid P (m₁ + m₂)).mass g * (2 * U r * (2 * U v)) := by
      rw [FiniteWeightLaw.mass, Finset.sum_mul]
      rfl
    _ ≤ (2 * U (m₁ + m₂)) * (2 * U r * (2 * U v)) :=
      mul_le_mul_of_nonneg_right hg (mul_nonneg hr₀ hv₀)
    _ = _ := by change _ = 8 * U (m₁ + m₂) * U r * U v; ring

private theorem moment_mul_mul_le_interpolation {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {k n m r v : ℕ} (hkn : k < n)
    (hkm : k ≤ m) (hmn : m ≤ n) (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n)
    (hsize : m + r + v = 2 * n) :
    moment (sincKernel t) P labels m * moment (sincKernel t) P labels r *
        moment (sincKernel t) P labels v ≤
      moment (sincKernel t) P labels k ^ ((n : ℝ) / ((n : ℝ) - k)) *
        moment (sincKernel t) P labels n ^ ((2 * (n : ℝ) - 3 * k) / ((n : ℝ) - k)) := by
  let U := moment (sincKernel t) P labels
  let a (j : ℕ) : ℝ := ((n : ℝ) - j) / ((n : ℝ) - k)
  let b (j : ℕ) : ℝ := ((j : ℝ) - k) / ((n : ℝ) - k)
  have hd : 0 < (n : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hkn)
  have ha {j : ℕ} (hj : j ≤ n) : 0 ≤ a j :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hj)) hd.le
  have hb {j : ℕ} (hj : k ≤ j) : 0 ≤ b j :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hj)) hd.le
  have hsize' : (m : ℝ) + r + v = 2 * (n : ℝ) := by exact_mod_cast hsize
  have hA : a m + a r + a v = (n : ℝ) / ((n : ℝ) - k) := by
    dsimp [a]
    rw [← add_div, ← add_div]
    congr 1
    linarith
  have hB : b m + b r + b v = (2 * (n : ℝ) - 3 * k) / ((n : ℝ) - k) := by
    dsimp [b]
    rw [← add_div, ← add_div]
    congr 1
    linarith
  have hU (j : ℕ) : 0 ≤ U j := moment_nonneg ht P labels j
  let bound (j : ℕ) := U k ^ a j * U n ^ b j
  have hbound (j : ℕ) : 0 ≤ bound j :=
    mul_nonneg (Real.rpow_nonneg (hU k) _) (Real.rpow_nonneg (hU n) _)
  have hI {j : ℕ} (hkj : k ≤ j) (hjn : j ≤ n) : U j ≤ bound j :=
    DisclosedMomentInterpolation.moment_le_interpolation ht P labels hkn hkj hjn
  calc
    U m * U r * U v ≤ bound m * bound r * bound v :=
      mul_le_mul (mul_le_mul (hI hkm hmn) (hI hkr hrn) (hU r) (hbound m))
        (hI hkv hvn) (hU v) (mul_nonneg (hbound m) (hbound r))
    _ = (U k ^ a m * U k ^ a r * U k ^ a v) * (U n ^ b m * U n ^ b r * U n ^ b v) := by
      dsimp [bound]
      ring
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg (hU k) (ha hmn) (ha hrn),
        ← Real.rpow_add_of_nonneg (hU k) (add_nonneg (ha hmn) (ha hrn)) (ha hvn),
        ← Real.rpow_add_of_nonneg (hU n) (hb hkm) (hb hkr),
        ← Real.rpow_add_of_nonneg (hU n) (add_nonneg (hb hkm) (hb hkr)) (hb hkv), hA, hB]

/-- Combine the three interval prices by Hölder at the same endpoint orders.
The numerator of the exponent of `U_n` is `2n - 3k`: the sum of the three
orders minus `k` for each block. This bound does not require `U_n > 0`. -/
public theorem threeHitMass_le_interpolated_moments {t : ℝ} (ht : 0 < t) (P : FiniteWeightLaw α)
    (labels : α → ℝ) {m₁ m₂ r v N : ℕ} (e : Fin (m₁ + m₂ + r + v) ≃ Fin N)
    (σ₁ : Fin m₁ → Bool) (σ₂ : Fin m₂ → Bool) (σr : Fin r → Bool) (σv : Fin v → Bool)
    {k n : ℕ} (hkn : k < n) (hkm : k ≤ m₁ + m₂) (hmn : m₁ + m₂ ≤ n)
    (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n)
    (hsize : m₁ + m₂ + r + v = 2 * n) :
    threeHitMass t P labels e σ₁ σ₂ σr σv ≤
      8 * moment (sincKernel t) P labels k ^ ((n : ℝ) / ((n : ℝ) - k)) *
        moment (sincKernel t) P labels n ^ ((2 * (n : ℝ) - 3 * k) / ((n : ℝ) - k)) := by
  refine (threeHitMass_le_eight_moments ht P labels e σ₁ σ₂ σr σv).trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (moment_mul_mul_le_interpolation ht P labels hkn hkm hmn hkr hrn hkv hvn hsize)
    (by norm_num : (0 : ℝ) ≤ 8)

/-- The fixed-mask bound relative to `U_n²`, with exponent `-k/(n-k)` on `U_n`. -/
public theorem threeHitMass_div_sq_le_interpolated_moments {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {m₁ m₂ r v N : ℕ}
    (e : Fin (m₁ + m₂ + r + v) ≃ Fin N)
    (σ₁ : Fin m₁ → Bool) (σ₂ : Fin m₂ → Bool) (σr : Fin r → Bool) (σv : Fin v → Bool)
    {k n : ℕ} (hkn : k < n) (hkm : k ≤ m₁ + m₂) (hmn : m₁ + m₂ ≤ n)
    (hkr : k ≤ r) (hrn : r ≤ n) (hkv : k ≤ v) (hvn : v ≤ n)
    (hsize : m₁ + m₂ + r + v = 2 * n) (hUn : 0 < moment (sincKernel t) P labels n) :
    threeHitMass t P labels e σ₁ σ₂ σr σv / (moment (sincKernel t) P labels n) ^ 2 ≤
      8 * moment (sincKernel t) P labels k ^ ((n : ℝ) / ((n : ℝ) - k)) *
        moment (sincKernel t) P labels n ^ (-(k : ℝ) / ((n : ℝ) - k)) := by
  have hd : 0 < (n : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hkn)
  have hexp : ((2 * (n : ℝ) - 3 * k) / ((n : ℝ) - k)) - 2 = -(k : ℝ) / ((n : ℝ) - k) := by
    field_simp [hd.ne']
    ring
  refine (div_le_div_of_nonneg_right
    (threeHitMass_le_interpolated_moments ht P labels e σ₁ σ₂ σr σv
      hkn hkm hmn hkr hrn hkv hvn hsize) (sq_nonneg _)).trans_eq ?_
  rw [mul_div_assoc, ← hexp, Real.rpow_sub hUn, Real.rpow_ofNat]

end Masullo.MixedPoolMoment
