module

public import Lemmas.PrimePairShellMoment
public import Mathlib.Data.Finset.Lattice.Fold
import all Lemmas.PrimePairShellMoment
import Lemmas.CenteredHeightMesh
import Lemmas.OrderedPrimeTupleDiagonal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A prime-pair shell moment on every translated mesh

Source: `554d2c81:.godel/bob/centered-height-mesh.md:9–17`, the short moment
used to price the omitted sample points. Owning check session:
`01a209f7-85a2-71df-a0cc-7987e51e67d1`.

For the frozen prime-pair polynomial, the even moment of order `2m` has
frequencies of modulus at most `mΩ`, where `Ω` is the diameter of the
start frequencies. Exact sampling applies to each *untruncated* translated
sinc-square majorant at angular period at least `mΩ + 1/T`, including equality.
Positivity then bounds the inclusive shell sum, in the strict short product
spacing range `X^(2m) < T`, with the continuous diagonal's normalization.
The origin is any real number. No quadrature for a shell or a thresholded
weight is asserted.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Masullo.SampledPrimePairShell

open PrimePairShellMoment
open SignedBlockIntervalMoment (phase)

/-- The maximum minus the minimum start frequency, defined as zero for an empty pool. -/
@[expose] public noncomputable def frequencyDiameter (S : Finset ℕ) (d : ℕ) : ℝ :=
  let ω (p : ℕ) := Real.log ((↑(p + d) : ℝ) / p)
  if h : S.Nonempty then S.sup' h ω - S.inf' h ω else 0

private theorem abs_frequency_sub_le_diameter {S : Finset ℕ} (d : ℕ) {p q : ℕ}
    (hp : p ∈ S) (hq : q ∈ S) :
    |Real.log ((↑(p + d) : ℝ) / p) - Real.log ((↑(q + d) : ℝ) / q)| ≤
      frequencyDiameter S d := by
  let ω (r : ℕ) := Real.log ((↑(r + d) : ℝ) / r)
  have hS : S.Nonempty := ⟨p, hp⟩
  change |ω p - ω q| ≤ (if h : S.Nonempty then S.sup' h ω - S.inf' h ω else 0)
  rw [dite_eq_left hS]
  exact abs_sub_le_iff.mpr
    ⟨sub_le_sub (Finset.le_sup' ω hp) (Finset.inf'_le ω hq),
     sub_le_sub (Finset.le_sup' ω hq) (Finset.inf'_le ω hp)⟩

private theorem abs_tupleFreq_sub_le {S : Finset ℕ} {m d : ℕ} {a b : Fin m → ℕ}
    (ha : a ∈ tuples S m) (hb : b ∈ tuples S m) :
    |tupleFreq d a - tupleFreq d b| ≤ (m : ℝ) * frequencyDiameter S d := by
  let ω (p : ℕ) := Real.log ((↑(p + d) : ℝ) / p)
  change |(∑ i, ω (a i)) - ∑ i, ω (b i)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin m, |ω (a i) - ω (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, frequencyDiameter S d :=
      Finset.sum_le_sum fun i _ ↦ abs_frequency_sub_le_diameter d
        (Fintype.mem_piFinset.mp ha i) (Fintype.mem_piFinset.mp hb i)
    _ = _ := by simp

private theorem sample_majorant {T Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ)
    (S : Finset ℕ) (d m : ℕ) (w : ℕ → ℝ) (χ : ℕ → ℂ)
    (hmesh : (m : ℝ) * frequencyDiameter S d + 1 / T ≤ 2 * Real.pi / Δ) (b c : ℝ) :
    let F (u : ℝ) := shellKernel T c u * ‖primePairSum S d w χ u‖ ^ (2 * m)
    Summable (fun j : ℤ ↦ F (b + (j : ℝ) * Δ)) ∧
      Δ * (∑' j : ℤ, F (b + (j : ℝ) * Δ)) = ∫ u, F u := by
  classical
  let F (u : ℝ) := shellKernel T c u * ‖primePairSum S d w χ u‖ ^ (2 * m)
  let t := 2 * Real.pi * T
  -- In the no-alias coordinate `v`, the shell center `c` moves to the kernel center `t`.
  let k := c - t
  let A := tuples S m ×ˢ tuples S m
  let ν (ab : (Fin m → ℕ) × (Fin m → ℕ)) := tupleFreq d ab.1 - tupleFreq d ab.2
  let C (ab : (Fin m → ℕ) × (Fin m → ℕ)) :=
    (tupleCoeff w χ ab.1 * conj (tupleCoeff w χ ab.2)) * phase (k * ν ab)
  let g (v : ℝ) := (CenteredHeightMesh.kernel t v : ℂ) *
    CenteredHeightMesh.expPolynomial A C ν v
  have ht : 0 < t := by dsimp [t]; positivity
  have hν (ab) (hab : ab ∈ A) : |ν ab| ≤ (m : ℝ) * frequencyDiameter S d := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact abs_tupleFreq_sub_le ha hb
  have hradius : 2 * Real.pi / t = 1 / T := by
    dsimp only [t]
    field_simp [Real.pi_ne_zero, hT.ne']
  have hno := CenteredHeightMesh.no_alias A C ν ht hΔ hν
    (by rwa [hradius] : (m : ℝ) * frequencyDiameter S d + 2 * Real.pi / t ≤
      CenteredHeightMesh.angularPeriod Δ) (b - k)
  have hpoly (v : ℝ) : (↑(‖primePairSum S d w χ (v + k)‖ ^ (2 * m)) : ℂ) =
      CenteredHeightMesh.expPolynomial A C ν v := by
    rw [moment_expansion, CenteredHeightMesh.expPolynomial]
    apply Finset.sum_congr rfl
    intro ab _
    change _ * phase ((v + k) * ν ab) = C ab * phase (v * ν ab)
    rw [add_mul]
    simp only [C, phase, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  have hkernel (v : ℝ) : shellKernel T c (v + k) = t * CenteredHeightMesh.kernel t v := by
    have harg : (v + k - c) / (2 * T) = Real.pi * (v / t - 1) := by
      dsimp only [k, t]
      field_simp [Real.pi_ne_zero, hT.ne']
      ring
    rw [shellKernel, CenteredHeightMesh.kernel, harg, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  have hF (v : ℝ) : (F (v + k) : ℂ) = (t : ℂ) * g v := by
    dsimp only [F, g]
    rw [Complex.ofReal_mul, hpoly, hkernel, Complex.ofReal_mul, mul_assoc]
  have hgrid (j : ℤ) : (F (b + (j : ℝ) * Δ) : ℂ) = (t : ℂ) * g (b - k + (j : ℝ) * Δ) := by
    have hshift : b - k + (j : ℝ) * Δ + k = b + (j : ℝ) * Δ := by ring
    rw [← hshift, hF]
  have hnorm (j : ℤ) : F (b + (j : ℝ) * Δ) = ‖(t : ℂ)‖ * ‖g (b - k + (j : ℝ) * Δ)‖ := by
    have h : 0 ≤ F (b + (j : ℝ) * Δ) := by unfold F shellKernel; positivity
    calc
      _ = ‖(F (b + (j : ℝ) * Δ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg h]
      _ = _ := by rw [hgrid, norm_mul]
  change Summable (fun j : ℤ ↦ F (b + (j : ℝ) * Δ)) ∧
    Δ * (∑' j : ℤ, F (b + (j : ℝ) * Δ)) = ∫ u, F u
  refine ⟨?_, ?_⟩
  · simpa only [hnorm] using
      (CenteredHeightMesh.summable_norm_samples A C ν ht hΔ (b - k)).mul_left ‖(t : ℂ)‖
  · apply Complex.ofReal_injective
    calc
      _ = (Δ : ℂ) * (∑' j : ℤ, (F (b + (j : ℝ) * Δ) : ℂ)) := by
        rw [Complex.ofReal_mul, Complex.ofReal_tsum]
      _ = (t : ℂ) * ((Δ : ℂ) * (∑' j : ℤ, g (b - k + (j : ℝ) * Δ))) := by
        simp_rw [hgrid, tsum_mul_left]
        ring
      _ = (t : ℂ) * ∫ v, g v := congrArg ((t : ℂ) * ·) hno
      _ = ∫ v, (F (v + k) : ℂ) := by simp_rw [hF, integral_const_mul]
      _ = _ := (integral_add_right_eq_self (fun v ↦ (F v : ℂ)) k).trans
        (integral_ofReal (𝕜 := ℂ))

private theorem quarter_le_shellKernels {T u : ℝ} (hT : 0 < T)
    (hu : T ≤ |u| ∧ |u| ≤ 2 * T) :
    1 / 4 ≤ shellKernel T (3 * T / 2) u + shellKernel T (-(3 * T / 2)) u := by
  let c := 3 * T / 2
  have hpos (v : ℝ) (hv : T ≤ v ∧ v ≤ 2 * T) : 1 / 4 ≤ shellKernel T c v := by
    apply quarter_le_sinc_sq
    have hden : 0 < 2 * T := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    exact abs_le.mpr ⟨by dsimp [c]; linarith [hv.1], by dsimp [c]; linarith [hv.2]⟩
  change 1 / 4 ≤ shellKernel T c u + shellKernel T (-c) u
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    exact (hpos u hu).trans (le_add_of_nonneg_right (sq_nonneg _))
  · rw [abs_of_nonpos h] at hu
    have hreflect : shellKernel T (-c) u = shellKernel T c (-u) := by
      rw [shellKernel, shellKernel, show (u - -c) / (2 * T) = -((-u - c) / (2 * T)) by ring,
        Real.sinc_neg]
    rw [hreflect]
    exact (hpos (-u) hu).trans (le_add_of_nonneg_left (sq_nonneg _))

/-- The `Δ`-weighted short moment on the inclusive shell of an arbitrary real translate.
The untruncated majorants are sampled exactly; their continuous permutation diagonal
bounds the truncated sum. -/
public theorem tsum_shell_moment_le {S : Finset ℕ} {d m : ℕ} {X T Δ : ℝ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X) (hT : 0 < T)
    (hshort : X ^ (2 * m) < T) (w : ℕ → ℝ) (χ : ℕ → ℂ) (hχ : ∀ p ∈ S, ‖χ p‖ = 1)
    (hΔ : 0 < Δ) (hmesh : (m : ℝ) * frequencyDiameter S d + 1 / T ≤ 2 * Real.pi / Δ)
    (b : ℝ) :
    Δ * (∑' j : ℤ, if T ≤ |b + (j : ℝ) * Δ| ∧ |b + (j : ℝ) * Δ| ≤ 2 * T then
      ‖primePairSum S d w χ (b + (j : ℝ) * Δ)‖ ^ (2 * m) else 0) ≤
      16 * Real.pi * T * (m.factorial : ℝ) * (∑ p ∈ S, w p ^ 2) ^ m := by
  let c := 3 * T / 2
  let x (j : ℤ) := b + (j : ℝ) * Δ
  let f (u : ℝ) := ‖primePairSum S d w χ u‖ ^ (2 * m)
  let F (a u : ℝ) := shellKernel T a u * f u
  let H (j : ℤ) := if T ≤ |x j| ∧ |x j| ≤ 2 * T then f (x j) else 0
  have hpos := sample_majorant hT hΔ S d m w χ hmesh b c
  have hneg := sample_majorant hT hΔ S d m w χ hmesh b (-c)
  have hf (u : ℝ) : 0 ≤ f u := pow_nonneg (norm_nonneg _) _
  have hF (a u : ℝ) : 0 ≤ F a u := mul_nonneg (sq_nonneg _) (hf u)
  have hH (j : ℤ) : 0 ≤ H j := by
    dsimp only [H]
    split
    · exact hf _
    · exact le_rfl
  have hdom (j : ℤ) : H j ≤ 4 * (F c (x j) + F (-c) (x j)) := by
    dsimp only [H]
    split
    next hj =>
      have h := mul_le_mul_of_nonneg_right (quarter_le_shellKernels hT hj) (hf (x j))
      rw [add_mul] at h
      dsimp only [F, c]
      linarith only [h]
    next _ => exact mul_nonneg (by norm_num) (add_nonneg (hF _ _) (hF _ _))
  have hsum : Summable (fun j ↦ 4 * (F c (x j) + F (-c) (x j))) :=
    (hpos.1.add hneg.1).mul_left 4
  change Δ * (∑' j, H j) ≤ _
  calc
    _ ≤ Δ * (∑' j, 4 * (F c (x j) + F (-c) (x j))) :=
      mul_le_mul_of_nonneg_left ((hsum.of_nonneg_of_le hH hdom).tsum_le_tsum hdom hsum) hΔ.le
    _ = 4 * ((Δ * (∑' j, F c (x j))) + Δ * (∑' j, F (-c) (x j))) := by
      rw [tsum_mul_left, hpos.1.tsum_add hneg.1]
      ring
    _ = 4 * ((∫ u, F c u) + ∫ u, F (-c) u) := by rw [hpos.2, hneg.2]
    _ ≤ _ := by
      dsimp only [F, f]
      rw [integral_shellKernel_mul_moment_eq hd hprime hcap hX hT hshort w χ hχ c,
        integral_shellKernel_mul_moment_eq hd hprime hcap hX hT hshort w χ hχ (-c)]
      have h := mul_le_mul_of_nonneg_left (OrderedPrimeTupleDiagonal.zeroMass_le hd hprime m w)
        (show 0 ≤ 2 * Real.pi * T by positivity)
      calc
        _ ≤ 4 * (_ + _) := mul_le_mul_of_nonneg_left (add_le_add h h) (by norm_num)
        _ = _ := by ring

end Masullo.SampledPrimePairShell
