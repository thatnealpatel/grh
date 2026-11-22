module

public import Theorems.IdeleClassGaussianSupport
public import Theorems.IdeleScalarLogSection
import Lemmas.IdeleScalarArchimedeanBound
import Mathlib.Algebra.Module.ZLattice.Summable

/-! # Uniform large-norm decay of principal sums

Theorem 2.2.3.4(1), (2.2.3.4), PDF p. 83, bounds the principal sum
by absolute values and then by a fixed Archimedean lattice sum,
(2.2.3.8)–(13), pp. 83–84. Prove the estimate using just a finite
support bound (integrality after a fixed finite dilation) and
coordinatewise Archimedean decay. The dilation acts only on the compact
cover in the denominator argument, so the norm threshold of the sampled
ideles remains one. Use `ideleScalarLogSection` with ordinary dilation
`t^(1/[K:ℚ])` (Lemma A.2.2.4, PDF p. 547) instead of `s_{F,δ}`
((A.2.2.11), p. 547). Use inverse bounds on the Archimedean unit
coordinates and choose the decay exponent to absorb this ordinary
coordinate scaling, rather than using (2.2.3.10) as printed. Source
reading: Provisional Markdown and numbered PDF layout.
-/

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I₁" => ideleNormOne (K := K)
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "σ" => ideleScalarLogSection (K := K)
local notation "Λ" => mixedEmbedding.integerLattice K

/-- Absolute principal-series decay from two pointwise bounds: Nonzero values
require integral finite coordinates after multiplication by the fixed
idele `c`, and every power of each infinite radius gives a bounded weight.
The argument of `f` is not translated by `c`. -/
public theorem idele_periodization_rapidDecay_of_support (f : I → ℂ) (c : I)
    (hfinite : ∀ g : I, f g ≠ 0 → ∀ v : V, ‖(c * g).val.2 v‖ ≤ 1)
    (harch : ∀ p : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ (g : I) (v : InfinitePlace K),
      ‖f g‖ * ‖g.val.1 v‖ ^ p ≤ A) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : I, 1 ≤ ideleNorm g →
      (Summable fun a : Kˣ ↦ ‖f (d a * g)‖) ∧
      (∑' a : Kˣ, ‖f (d a * g)‖) ≤ C * ideleNorm g ^ (-(N : ℤ)) := by
  classical
  let D := Module.finrank ℚ K
  let p := max (Module.finrank ℤ Λ + 1) (D * N)
  have hp : Module.finrank ℤ Λ < p := (Nat.lt_succ_self _).trans_le (le_max_left ..)
  have hpD : (D : ℝ) * N ≤ (p : ℝ) := by exact_mod_cast le_max_right (Module.finrank ℤ Λ + 1) (D * N)
  have hD : 0 < (D : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  obtain ⟨B, hB, hcover⟩ := exists_compact_cover_ideleClassNormOne (K := K)
  let translate (b : I₁) : I := c * (b : I)
  have ht : Continuous translate := continuous_const.mul continuous_subtype_val
  obtain ⟨m, hm, hden⟩ := exists_uniform_denominator_of_isCompact _ (hB.image ht)
  obtain ⟨l, hl, hlower⟩ := exists_infinite_coordinate_ge_scaled_mixedEmbedding hB hm
  obtain ⟨A, hA, hbound⟩ := harch p
  let W (z : Λ) := (‖z‖ ^ p)⁻¹
  have hW : Summable W := by
    have hp' : (Module.finrank ℤ Λ : ℝ) < p := by exact_mod_cast hp
    simpa only [W, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast] using
      (ZLattice.summable_norm_rpow (L := Λ) (-(p : ℝ)) (neg_lt_neg hp'))
  have hW₀ (z : Λ) : 0 ≤ W z := by dsimp [W]; positivity
  refine ⟨(A / l ^ p) * ((∑' z : Λ, W z) + 1), ?_, ?_⟩
  · have hsum : 0 ≤ ∑' z : Λ, W z := tsum_nonneg hW₀
    positivity
  intro g hg
  -- Pass to a representative `σ x * b` of the same class, with `b ∈ B`.
  let x := ideleLogNorm g
  have hx : 0 ≤ x.toAdd := by rw [ideleLogNorm_apply]; exact Real.log_nonneg hg
  have hnorm : ideleNorm g = Real.exp x.toAdd := by rw [ideleLogNorm_apply, Real.exp_log (zero_lt_one.trans_le hg)]
  let b₀ : I₁ := ⟨(σ x)⁻¹ * g, by
    rw [mem_ideleNormOne, map_mul, map_inv, ideleNorm_ideleScalarLogSection, ← hnorm]
    exact inv_mul_cancel₀ (zero_lt_one.trans_le hg).ne'⟩
  obtain ⟨b, hb, hq⟩ := (mem_image _ _ _).mp (show q₁ b₀ ∈ q₁ '' B from hcover.symm ▸ mem_univ _)
  obtain ⟨u, hu⟩ := (ideleClassQuotientNormOne_eq_iff b b₀).mp hq
  have hgu : g = d u * (σ x * (b : I)) := by
    have hu' : d u * (b : I) = (σ x)⁻¹ * g := by
      simpa only [Subgroup.coe_mul, coe_idelePrincipalNormOne] using congrArg Subtype.val hu
    calc
      g = σ x * ((σ x)⁻¹ * g) := by group
      _ = d u * (σ x * (b : I)) := by rw [← hu']; ac_rfl
  let F (a : Kˣ) := ‖f (d a * σ x * (b : I))‖
  -- The contributing indices inject into a fixed integer lattice.
  have hmem (a : support F) : mixedEmbedding K ((m : K) * ((a : Kˣ) : K)) ∈ Λ := by
    obtain ⟨y, hy⟩ := hden (translate b) (mem_image_of_mem _ hb) a (fun v ↦ by
      have hn := hfinite _ (norm_ne_zero_iff.mp a.property) v
      change ‖c.val.2 v * (((d (a : Kˣ)).val.2 v * (σ x).val.2 v) * (b : I).val.2 v)‖ ≤ 1 at hn
      change ‖(d (a : Kˣ)).val.2 v * (c.val.2 v * (b : I).val.2 v)‖ ≤ 1
      simpa only [ideleScalarLogSection_finite, mul_one, mul_left_comm] using hn)
    exact ⟨y, congrArg (mixedEmbedding K) hy⟩
  let e (a : support F) : Λ := ⟨mixedEmbedding K ((m : K) * ((a : Kˣ) : K)), hmem a⟩
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : Function.Injective e := by
    intro a a' h
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hmK (mixedEmbedding_injective K (congrArg Subtype.val h))
  -- Use the coordinate of sufficiently large radius to bound each summand.
  let Q := (A / l ^ p) * Real.exp (-(N : ℝ) * x.toAdd)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hmajor (a : support F) : F a ≤ Q * W (e a) := by
    obtain ⟨v, hv⟩ := hlower b hb x a
    have hz : 0 < ‖e a‖ := by
      apply norm_pos_iff.mpr
      intro h
      have hh : mixedEmbedding K ((m : K) * ((a : Kˣ) : K)) = 0 := congrArg Subtype.val h
      exact mul_ne_zero hmK (Units.ne_zero (a : Kˣ)) (mixedEmbedding_injective K (hh.trans (map_zero _).symm))
    have hρ : Real.exp ((N : ℝ) * x.toAdd) ≤ (Real.exp (x.toAdd / (D : ℝ))) ^ p := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hpD (div_nonneg hx hD.le)
      convert h using 1
      rw [show (D : ℝ) * N * (x.toAdd / (D : ℝ)) = (N : ℝ) * x.toAdd by field_simp]
    have H : F a * ((l ^ p * Real.exp ((N : ℝ) * x.toAdd)) * ‖e a‖ ^ p) ≤ A := calc
      _ ≤ F a * ((l ^ p * (Real.exp (x.toAdd / (D : ℝ))) ^ p) * ‖e a‖ ^ p) := by
        gcongr
      _ = F a * (l * Real.exp (x.toAdd / (D : ℝ)) * ‖e a‖) ^ p := by simp only [mul_pow]
      _ ≤ F a * ‖(d (a : Kˣ) * σ x * (b : I)).val.1 v‖ ^ p := by
        gcongr
        exact hv
      _ ≤ A := hbound _ v
    calc
      F a ≤ A / ((l ^ p * Real.exp ((N : ℝ) * x.toAdd)) * ‖e a‖ ^ p) :=
        (le_div_iff₀ (by positivity)).mpr H
      _ = Q * W (e a) := by simp only [div_eq_mul_inv, mul_inv, Q, W, neg_mul, Real.exp_neg]; ring
  have hsG : Summable (fun z : Λ ↦ Q * W z) := hW.mul_left _
  have hs : Summable (fun a : support F ↦ F a) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hmajor (hsG.comp_injective he)
  have hsF : Summable F := (hasSum_subtype_support.mp hs.hasSum).summable
  have hbnd : (∑' a : Kˣ, F a) ≤ Q * (∑' z : Λ, W z) := by
    rw [← tsum_subtype_support, ← tsum_mul_left]
    exact hs.tsum_le_tsum_of_inj e he (fun z _ ↦ mul_nonneg hQ.le (hW₀ z)) hmajor hsG
  let E := Equiv.mulRight u
  have hE (a : Kˣ) : ‖f (d a * g)‖ = F (E a) := by
    rw [hgu]
    change ‖f (d a * (d u * (σ x * (b : I))))‖ = ‖f (d (a * u) * σ x * (b : I))‖
    rw [map_mul]
    simp only [mul_assoc]
  change (Summable fun a : Kˣ ↦ ‖f (d a * g)‖) ∧
    (∑' a : Kˣ, ‖f (d a * g)‖) ≤ _
  simp_rw [hE]
  refine ⟨E.summable_iff.mpr hsF, ?_⟩
  rw [E.tsum_eq]
  have hrad : ideleNorm g ^ (-(N : ℤ)) = Real.exp (-(N : ℝ) * x.toAdd) := by
    rw [hnorm, zpow_neg, zpow_natCast, ← Real.exp_nat_mul, neg_mul, Real.exp_neg]
  rw [hrad]
  refine hbnd.trans ?_
  dsimp [Q]
  calc
    _ = (A / l ^ p) * (∑' z : Λ, W z) * Real.exp (-(N : ℝ) * x.toAdd) := by ring
    _ ≤ _ := by gcongr; exact le_add_of_nonneg_right zero_le_one

end Masullo
