module

public import Theorems.RationalAdeleBoxFourier
import Lemmas.RationalIdeleReal
import Lemmas.ScaledPoisson

/-! # Lattice convergence for rational adelic boxes -/

open NumberField IsDedekindDomain Set Topology
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → Cq)
local notation "ι" => algebraMap ℚ A
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

private theorem unramified_mul_finite_unit (b : 𝓢(ℝ, ℂ)) (h : J)
    (hh : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((h : A).2 v) = 1)
    (ht : rationalIdeleReal h ≠ 0) (z : A) :
    rationalAdeleUnramified b ((h : A) * z) =
      rationalAdeleUnramified (dilateSchwartz b (rationalIdeleReal h) ht) z := by
  have hmem : (h : A) * z ∈ rationalIntegralAdeles ↔ z ∈ rationalIntegralAdeles := by
    change (∀ v : HeightOneSpectrum (𝓞 ℚ), (h : A).2 v * z.2 v ∈ v.adicCompletionIntegers ℚ) ↔
      (∀ v : HeightOneSpectrum (𝓞 ℚ), z.2 v ∈ v.adicCompletionIntegers ℚ)
    simp only [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hh, one_mul]
  by_cases hz : z ∈ rationalIntegralAdeles
  · simp only [rationalAdeleUnramified, indicator_of_mem hz, indicator_of_mem (hmem.mpr hz),
      dilateSchwartz_apply, rationalAdeleReal_apply]
    congr 1
    exact map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _
  · simp only [rationalAdeleUnramified, indicator_of_notMem hz,
      indicator_of_notMem (mt hmem.mp hz)]

/-- After principal normalization, absorb the remaining real scale into the
Schwartz factor. Finite units leave the integral-finite support unchanged. -/
private theorem unramified_idele_mul (b : 𝓢(ℝ, ℂ)) (g : J) :
    ∃ (r : ℚˣ) (c : 𝓢(ℝ, ℂ)), ∀ z : A,
      rationalAdeleUnramified b ((g : A) * z) = rationalAdeleUnramified c (ι (r : ℚ) * z) := by
  obtain ⟨r, hreal, hfin⟩ := exists_rational_principal_mul_norm_section g
  let h := ιˣ r * g
  have ht : rationalIdeleReal h ≠ 0 := by
    rw [hreal]
    exact (ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g)).ne'
  refine ⟨r⁻¹, dilateSchwartz b (rationalIdeleReal h) ht, fun z ↦ ?_⟩
  rw [← unramified_mul_finite_unit b h hfin ht]
  congr 1
  change (g : A) * z = (ι (r : ℚ) * (g : A)) * (ι ((r⁻¹ : ℚˣ) : ℚ) * z)
  rw [mul_mul_mul_comm, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    map_one, one_mul]

private noncomputable def diagonalParam : ℚ ≃ rationalDiagonal :=
  Equiv.ofBijective (fun q ↦ (⟨ι q, ⟨q, rfl⟩⟩ : rationalDiagonal))
    ⟨fun _ _ h ↦ AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrArg Subtype.val h),
      fun ⟨_, ⟨q, hq⟩⟩ ↦ ⟨q, Subtype.ext hq⟩⟩

private theorem diagonalParam_apply (q : ℚ) : (diagonalParam q : A) = ι q := rfl

private noncomputable def diagonalScale (r : ℚˣ) : Equiv.Perm rationalDiagonal :=
  (diagonalParam.symm.trans (Equiv.mulLeft₀ (r : ℚ) r.ne_zero)).trans diagonalParam

private theorem diagonalScale_apply (r : ℚˣ) (d : rationalDiagonal) :
    (diagonalScale r d : A) = ι (r : ℚ) * (d : A) := by
  obtain ⟨q, rfl⟩ := diagonalParam.surjective d
  simp only [diagonalScale, Equiv.trans_apply, Equiv.symm_apply_apply, diagonalParam_apply]
  exact map_mul ι _ _

private theorem box_diagonal_reindex (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) :
    ∃ (r : ℚˣ) (c : 𝓢(ℝ, ℂ)), ∀ (x : A) (d : rationalDiagonal),
      rationalAdeleBox b a g (x + (d : A)) =
        rationalAdeleUnramified c (ι (r : ℚ) * (x - a) + (diagonalScale r d : A)) := by
  obtain ⟨r, c, h⟩ := unramified_idele_mul b g⁻¹
  refine ⟨r, c, fun x d ↦ ?_⟩
  rw [rationalAdeleBox, h, diagonalScale_apply, ← mul_add]
  congr 2
  abel

/-- The rational diagonal translates of a box are absolutely summable at every adele. -/
public theorem summable_norm_rationalAdeleBox_add (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (x : A) :
    Summable (fun d : rationalDiagonal ↦ ‖rationalAdeleBox b a g (x + (d : A))‖) := by
  obtain ⟨r, c, h⟩ := box_diagonal_reindex b a g
  simpa only [h, Function.comp_def] using
    (diagonalScale r).summable_iff.mpr
      (summable_norm_rationalAdeleUnramified_add c (ι (r : ℚ) * (x - a)))

/-- The box periodization is continuous on the rational adele class group. -/
public theorem continuous_rationalAdeleComplexPeriodization_box (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) :
    Continuous (rationalAdeleComplexPeriodization (rationalAdeleBox b a g)) := by
  obtain ⟨r, c, h⟩ := box_diagonal_reindex b a g
  apply (QuotientAddGroup.isQuotientMap_mk rationalDiagonal).continuous_iff.mpr
  have he (x : A) : rationalAdeleComplexPeriodization (rationalAdeleBox b a g) (π x) =
      rationalAdeleComplexPeriodization (rationalAdeleUnramified c) (π (ι (r : ℚ) * (x - a))) := by
    simp only [rationalAdeleComplexPeriodization_mk, h]
    exact (diagonalScale r).tsum_eq
      (fun d ↦ rationalAdeleUnramified c (ι (r : ℚ) * (x - a) + (d : A)))
  have hc : Continuous (fun x : A ↦ ι (r : ℚ) * (x - a)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  have hcont := (continuous_rationalAdeleComplexPeriodization_unramified c).comp
    (QuotientAddGroup.continuous_mk.comp hc)
  simpa only [Function.comp_def, he] using hcont

/-- The unramified tensor sampled along a dilated rational diagonal is
absolutely summable, including the sample at zero. -/
public theorem summable_norm_rationalAdeleUnramified_mul_diagonal (b : 𝓢(ℝ, ℂ)) (g : J) :
    Summable (fun q : ℚ ↦ ‖rationalAdeleUnramified b ((g : A) * ι q)‖) := by
  obtain ⟨r, c, h⟩ := unramified_idele_mul b g
  have hs := (diagonalScale r).summable_iff.mpr
    (summable_norm_rationalAdeleUnramified_add c 0)
  have hq := diagonalParam.summable_iff.mpr hs
  simpa only [Function.comp_def, zero_add, diagonalScale_apply, diagonalParam_apply, h] using hq

end Masullo
