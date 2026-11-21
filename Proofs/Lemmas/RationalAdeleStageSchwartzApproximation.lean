module

public import Lemmas.RationalAdeleStageNorm
import Lemmas.RationalAdeleStageLpApproximation
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space

/-! # Replacing sampled profiles by Schwartz functions

Sample on a finite quotient stage, then spend the remaining error budget
on smooth compactly supported approximations to the real profiles.
-/

open NumberField MeasureTheory
open scoped ENNReal InnerProductSpace SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar
local notation "S" => 𝓢(ℝ, ℂ)

set_option linter.concreteInstances false

private theorem integral_norm_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  let u := hf.toLp f
  calc
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := integral_congr_ae ((hf.coeFn_toLp).symm.mono fun x h ↦ by rw [h])
    _ = RCLike.re (⟪u, u⟫_ℂ) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
      simp only [inner_self_eq_norm_sq]
    _ = _ := by rw [inner_self_eq_norm_sq, Lp.norm_toLp]

variable [MeasurableSpace A] [BorelSpace A]

/-- A continuous compactly supported adelic function is approximable in
normalized `L²` by Schwartz profiles assembled on one positive stage. -/
public theorem exists_rationalAdeleSchwartzStage_L2_approx {f : A → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∃ g : rationalAdeleSchwartzStage M,
      MemLp g.val 2 μA ∧ eLpNorm (f - g.val) 2 μA < ε := by
  obtain ⟨δ, hδ, hadd⟩ := exists_Lp_half ℂ μA 2 hε.ne'
  let η := min δ 1
  have hη : 0 < η := lt_min hδ (by simp)
  have hηfin : η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  obtain ⟨_, M, hM, hb, _, hsample⟩ := exists_rationalAdeleStage_L2_sample hc hs hδ
  let b (j : Fin (M ^ 2)) (t : ℝ) := f (rationalAdeleAt t (rationalAdeleStageRepresentative M j))
  let d : ℝ := η.toReal / M
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : 0 < d := div_pos (ENNReal.toReal_pos hη.ne' hηfin) hMreal
  have hbLp (j : Fin (M ^ 2)) : MemLp (b j) 2 volume :=
    (hb j).1.memLp_of_hasCompactSupport (hb j).2
  have hreal (j : Fin (M ^ 2)) : ∃ c : S, eLpNorm (b j - (c : ℝ → ℂ)) 2 volume ≤ ENNReal.ofReal d := by
    obtain ⟨c, hcs, hcd, he⟩ := (hbLp j).exist_eLpNorm_sub_le (by simp) (by simp) hd
    exact ⟨hcs.toSchwartzMap hcd, he⟩
  choose c hclose using hreal
  let g := (rationalAdeleStageCoordinates hM).symm c
  let v : Fin (M ^ 2) → ℝ → ℂ := b - fun j ↦ (c j : ℝ → ℂ)
  have hv (j : Fin (M ^ 2)) : MemLp (v j) 2 volume := (hbLp j).sub ((c j).memLp 2 volume)
  have hg : g.val = rationalAdeleAssembleProfiles M (fun j ↦ c j) :=
    rationalAdeleStageCoordinates_symm_eq_assembleProfiles hM c
  have hgLp : MemLp g.val 2 μA := by
    rw [hg]
    exact (rationalAdeleAssembleProfiles_norm_sq hM _ (fun j ↦ (c j).memLp 2 volume)).1
  obtain ⟨hvA, hsq⟩ := rationalAdeleAssembleProfiles_norm_sq hM v hv
  have hsum : (∑ j, ∫ t, ‖v j t‖ ^ 2) ≤ η.toReal ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin (M ^ 2), d ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [integral_norm_sq_eq_eLpNorm_sq (hv j)]
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg
          ((ENNReal.le_ofReal_iff_toReal_le (hv j).eLpNorm_ne_top hd.le).1 (hclose j)) _
      _ = η.toReal ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, d]
        field_simp [hMreal.ne']
  have herror : eLpNorm (rationalAdeleAssembleProfiles M v) 2 μA ≤ η := by
    apply (ENNReal.toReal_le_toReal hvA.eLpNorm_ne_top hηfin).mp
    have hsq' : (eLpNorm (rationalAdeleAssembleProfiles M v) 2 μA).toReal ^ 2 ≤ η.toReal ^ 2 := by
      rw [← integral_norm_sq_eq_eLpNorm_sq hvA, hsq]
      have hpos : 0 ≤ (∑ j, ∫ t, ‖v j t‖ ^ 2) := by positivity
      have hw : (M : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hM)
      exact (mul_le_of_le_one_left hpos hw).trans hsum
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (rationalAdeleAssembleProfiles M v) 2 μA),
      ENNReal.toReal_nonneg (a := η)]
  refine ⟨M, hM, g, hgLp, ?_⟩
  let u := rationalAdeleAssembleProfiles M b
  have huv : rationalAdeleAssembleProfiles M v = u - g.val := by
    simpa only [u, v, hg] using rationalAdeleAssembleProfiles_sub M b (fun j ↦ c j)
  have he : f - g.val = (f - u) + (u - g.val) := by abel
  rw [he]
  exact hadd _ _ hsample.le ((huv ▸ herror).trans (min_le_left _ _))

end Masullo
