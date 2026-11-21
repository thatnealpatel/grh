module

public import Theorems.RationalAdeleLFDilationDeriv
public import Theorems.RationalAdeleClassThetaInversion
import Lemmas.RationalAdeleBoxMajorant
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Differentiating rational theta series

On a compact log-scale interval a box majorant for `Df` controls the
sample derivatives. A separate majorant for `f` at the base point gives
absolute convergence of the original series there.
-/

open NumberField Set
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "σ" => fun t : ℝ ↦ rationalIdeleLogSection (Multiplicative.ofAdd t)
local notation "D" => rationalAdeleLFDilationDeriv

/-- Every rational LF test admits a finite box expansion. -/
public theorem exists_rationalAdeleLF_eq_boxSum (f : E) :
    ∃ (n : ℕ) (b : Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ))
      (a : Fin ((L n) ^ 2) → A) (g : Fin ((L n) ^ 2) → J),
      f.toUnion.val = rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  obtain ⟨a, g, hbox⟩ :=
    exists_rationalAdeleStageCoordinates_symm_eq_boxSum (rationalAdeleFactorialLevel_pos n)
  refine ⟨n, rationalAdeleLFRead n f, a, g, ?_⟩
  conv_lhs => rw [← rationalAdeleLFAssembly_read n f hn]
  rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val, hbox]

private theorem norm_sample_majorant (f : E) {K : Set J} (hK : IsCompact K) :
    ∃ u : ℚˣ → ℝ, Summable u ∧ ∀ q k, k ∈ K → ‖f.toUnion.val ((ιˣ q * k : J) : A)‖ ≤ u q := by
  obtain ⟨_, b, a, g, hf⟩ := exists_rationalAdeleLF_eq_boxSum f
  have hK' : IsCompact ((fun k : J ↦ (k, (0 : A))) '' K) :=
    hK.image (continuous_id.prodMk continuous_const)
  obtain ⟨u, hu, hb⟩ :=
    exists_rationalAdeleBoxSum_orbit_majorant Finset.univ (fun _ ↦ 1) b a g hK'
  refine ⟨u, hu, fun q k hk ↦ ?_⟩
  have h := hb q (k, 0) (mem_image_of_mem _ hk)
  have hq : ((ιˣ q * k : J) : A) = (k : A) * algebraMap ℚ A (q : ℚ) := by
    change algebraMap ℚ A (q : ℚ) * (k : A) = _
    exact mul_comm _ _
  simpa only [rationalAdeleOrbitTerm, add_zero, hf, hq] using h

private theorem hasDerivAt_sample (f : E) (k : J) (q : ℚˣ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f.toUnion.val ((ιˣ q * (σ t * k) : J) : A))
      ((D f).toUnion.val ((ιˣ q * (σ s * k) : J) : A)) s := by
  have h := (hasDerivAt_rationalAdeleLF_logDilation f ((ιˣ q * (σ s * k) : J) : A)).scomp_of_eq s
    ((hasDerivAt_id s).sub_const s) (sub_self s).symm
  have he (t : ℝ) : (σ (t - s) : A) * ((ιˣ q * (σ s * k) : J) : A) =
      ((ιˣ q * (σ t * k) : J) : A) := by
    rw [← Units.val_mul, mul_left_comm, ← mul_assoc (σ (t - s))]
    have hadd : σ (t - s) * σ s = σ t := by
      rw [← map_mul]
      exact congrArg rationalIdeleLogSection (congrArg Multiplicative.ofAdd (sub_add_cancel t s))
    rw [hadd]
  simpa only [Function.comp_def, id_eq, one_smul, he] using h

/-- The derivative on ideles is obtained by summing the differentiated samples. -/
public theorem hasDerivAt_rationalAdeleTheta_logDilation (f : E) (k : J) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ rationalAdeleTheta f.toUnion.val (σ t * k))
      (rationalAdeleTheta (D f).toUnion.val (σ s * k)) s := by
  let orbit (t : ℝ) : J := σ t * k
  have horbit : Continuous orbit := (map_continuous rationalIdeleLogSection).mul continuous_const
  obtain ⟨u, hu, hb⟩ := norm_sample_majorant (D f)
    (isCompact_Icc.image (f := orbit) horbit : IsCompact (orbit '' Icc (s - 1) (s + 1)))
  obtain ⟨v, hv, hvb⟩ := norm_sample_majorant f (isCompact_singleton (x := orbit s))
  have hs : s ∈ Ioo (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun q t _ ↦ hasDerivAt_sample f k q t) _ hs _ hs
  · exact fun q t ht ↦ hb q (orbit t) (mem_image_of_mem _ (Ioo_subset_Icc_self ht))
  · exact Summable.of_norm_bounded hv fun q ↦ hvb q (orbit s) (mem_singleton _)

end Masullo
