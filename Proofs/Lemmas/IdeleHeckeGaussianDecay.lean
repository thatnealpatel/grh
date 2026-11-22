module

public import Theorems.IdeleHeckeGaussian
import all Lemmas.IdeleStageNormCoordinates
import all Theorems.ComplexGaussianMellin
import all Theorems.RealGaussianMellin

/-! # Coordinate decay of the corrected idelic Hecke Gaussian

In the proof of Theorem 2.2.3.4(1), PDF pp. 83–84, Masullo uses
(2.2.3.8) to bound the tensor sum by its Archimedean part on a lattice,
then uses Schwartz decay in the Archimedean supremum norm. Here we prove
the pointwise bounds needed for this step for the fixed Gaussian of
Definition 3.4.3.2, PDF p. 152, (3.4.3.3)–(9). The existing opposite
angular weight changes the complex monomial by conjugation, which
preserves its norm. The ramified finite factor has norm one on its
support by unitarity. The estimates below do not address the lattice
sum or its uniformity on class representatives. The manuscript reading
is provisional (Markdown and numbered PDF layout).
-/

open IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion
open scoped Classical

namespace Masullo

private theorem exists_pow_mul_gaussian_le (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → r ^ m * Real.exp (-(c * r ^ 2)) ≤ C := by
  have hB : 0 ≤ (m.factorial : ℝ) / c ^ m := by positivity
  refine ⟨1 + (m.factorial : ℝ) / c ^ m, by linarith, ?_⟩
  intro r hr
  have ht : 0 ≤ c * r ^ 2 := mul_nonneg hc.le (sq_nonneg r)
  by_cases h : r ≤ 1
  · calc
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ hr h) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
        (Real.exp_nonneg _) zero_le_one
      _ ≤ 1 + (m.factorial : ℝ) / c ^ m := by linarith
  · have hrs : r ≤ r ^ 2 := by
      simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left (le_of_not_ge h) hr
    have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hcp : 0 < c ^ m := pow_pos hc m
    have hseries := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (c * r ^ 2) ht m)
    have hexp : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
    calc
      r ^ m * Real.exp (-(c * r ^ 2)) ≤ (r ^ 2) ^ m * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrs _) (Real.exp_nonneg _)
      _ ≤ (m.factorial : ℝ) / c ^ m := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp hcp]
        simpa only [mul_pow, mul_comm] using hseries
      _ ≤ 1 + (m.factorial : ℝ) / c ^ m := by linarith

private theorem norm_realZetaGaussian_formula (b : ℕ) (x : ℝ) :
    ‖realZetaGaussian b x‖ = ‖x‖ ^ b * Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  rw [realZetaGaussian, Complex.norm_mul, norm_pow, Complex.norm_real, ← Complex.ofReal_neg,
    Complex.norm_exp_ofReal, Real.norm_eq_abs, sq_abs]

private theorem norm_complexZetaGaussian_formula (n : ℤ) (z : ℂ) :
    ‖complexZetaGaussian n z‖ =
      (1 / (2 * Real.pi)) * ‖z‖ ^ (if 0 ≤ n then n.toNat else n.natAbs) *
        Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) := by
  have h : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  unfold complexZetaGaussian
  split_ifs <;>
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h,
      norm_pow, Complex.norm_conj, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]

private theorem exists_scaled_pow_mul_gaussian_le (a : ℝ) (ha : 0 < a)
    (c : ℝ) (hc : 0 < c) (m p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      (a * r ^ m * Real.exp (-(c * r ^ 2))) * r ^ p ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_pow_mul_gaussian_le c hc (m + p)
  refine ⟨a * C, mul_pos ha hC, fun r hr ↦ ?_⟩
  calc
    _ = a * (r ^ (m + p) * Real.exp (-(c * r ^ 2))) := by rw [pow_add]; ring
    _ ≤ a * C := mul_le_mul_of_nonneg_left (h r hr) ha.le

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v

variable (χ : HeckeCharacter (𝓞 K) K)

/-- Unramified indicators and ramified inverse-character indicators are bounded by one. -/
public theorem norm_finiteHeckeGaussian_le_one
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) (v : V) (u : (F v)ˣ) :
    ‖finiteHeckeGaussian χ v u‖ ≤ 1 := by
  unfold finiteHeckeGaussian
  split
  · split <;> simp
  · rw [Set.indicator_apply]
    split
    · have hu : ‖χ.restrict v (u : F v)‖ = 1 := by
        rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
        exact hχ _
      simp only [norm_inv, hu, inv_one, le_refl]
    · simp

variable (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- Every natural power of the completion radius times the local Gaussian is bounded. -/
public theorem exists_archimedeanHeckeGaussian_norm_mul_pow_le
    (v : InfinitePlace K) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : v.Completionˣ,
      ‖archimedeanHeckeGaussian χ hχ v u‖ * ‖u.val‖ ^ p ≤ C := by
  by_cases hv : v.IsReal
  · let b := (realCompletionGaussianPair χ hχ hv).choose
    obtain ⟨C, hC, h⟩ := exists_scaled_pow_mul_gaussian_le 1 one_pos Real.pi Real.pi_pos b p
    refine ⟨C, hC, fun u ↦ ?_⟩
    have hn : ‖extensionEmbeddingOfIsReal hv u.val‖ = ‖u.val‖ :=
      (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _
    rw [archimedeanHeckeGaussian, dite_eq_left hv, norm_realZetaGaussian_formula, hn]
    simpa only [one_mul] using h ‖u.val‖ (norm_nonneg _)
  · let n := (complexCompletionGaussianPair χ hχ (InfinitePlace.not_isReal_iff_isComplex.mp hv)).choose
    obtain ⟨C, hC, h⟩ := exists_scaled_pow_mul_gaussian_le (1 / (2 * Real.pi)) (by positivity)
      (2 * Real.pi) (by positivity) (if 0 ≤ n then n.toNat else n.natAbs) p
    refine ⟨C, hC, fun u ↦ ?_⟩
    have hn : ‖extensionEmbedding v u.val‖ = ‖u.val‖ :=
      (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _
    rw [archimedeanHeckeGaussian, dite_eq_right hv, norm_complexZetaGaussian_formula, hn]
    exact h ‖u.val‖ (norm_nonneg _)

/-- The fixed tensor on actual ideles is bounded after multiplication by any
power of any Archimedean coordinate radius, with one constant for all places. -/
public theorem exists_ideleHeckeGaussian_norm_mul_pow_le (T : Finset V) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : I) (v : InfinitePlace K),
      ‖ideleHeckeGaussian χ hχ T g‖ * ‖g.val.1 v‖ ^ p ≤ C := by
  choose C0 hC0 h0 using fun v : InfinitePlace K ↦
    exists_archimedeanHeckeGaussian_norm_mul_pow_le χ hχ v 0
  choose Cp hCp hp using fun v : InfinitePlace K ↦
    exists_archimedeanHeckeGaussian_norm_mul_pow_le χ hχ v p
  let C (w : InfinitePlace K) := max (C0 w) (Cp w)
  refine ⟨∏ w, C w, Finset.prod_pos (fun w _ ↦ (hC0 w).trans_le (le_max_left _ _)), ?_⟩
  intro g v
  let A (w : InfinitePlace K) := ‖archimedeanHeckeGaussian χ hχ w (ideleInfiniteCoordinates K g w)‖
  have hA (w : InfinitePlace K) : A w ≤ C w :=
    (by simpa only [pow_zero, mul_one] using h0 w (ideleInfiniteCoordinates K g w) :
      A w ≤ C0 w).trans (le_max_left _ _)
  have hv : A v * ‖g.val.1 v‖ ^ p ≤ C v :=
    (hp v (ideleInfiniteCoordinates K g v)).trans (le_max_right _ _)
  have hproduct : (∏ w, A w) * ‖g.val.1 v‖ ^ p ≤ ∏ w, C w := by
    rw [← Finset.mul_prod_erase _ A (Finset.mem_univ v), ← Finset.mul_prod_erase _ C (Finset.mem_univ v)]
    calc
      _ = (A v * ‖g.val.1 v‖ ^ p) * ∏ w ∈ Finset.univ.erase v, A w := by ring
      _ ≤ _ := mul_le_mul hv (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun w _ ↦ hA w))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) ((hC0 v).le.trans (le_max_left _ _))
  unfold ideleHeckeGaussian ideleZetaTest
  split
  · rw [Complex.norm_mul, norm_prod, norm_prod]
    refine le_trans ?_ hproduct
    have hfinite : (∏ w ∈ T, ‖finiteHeckeGaussian χ w (ideleFiniteCoordinate K g w)‖) ≤ 1 := by
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
        (fun w _ ↦ norm_finiteHeckeGaussian_le_one χ hχ w _)
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hfinite) (pow_nonneg (norm_nonneg _) _)
  · simpa only [norm_zero, zero_mul] using
      (Finset.prod_nonneg fun w _ ↦ (hC0 w).le.trans (le_max_left _ _) : 0 ≤ ∏ w, C w)

end Masullo
