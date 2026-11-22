module

public import Mathlib.Topology.Metrizable.Uniformity
public import Theorems.RadialWeightedSchwartzStage
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Endpoint estimates for the radial weighted Schwartz stage

Masullo's Lemma D.3.2.3(1) (pp. 801–802) uses the two half-lines to control
intermediate weights by endpoint weights. This is the radial case of the stage
topology argument in Examples D.3.3.4–5 (pp. 805–806), used in Theorem
D.3.3.7(2) (pp. 806, 810).
-/

open Set Filter Topology
open scoped BigOperators ContDiff SchwartzMap Uniformity

namespace Masullo

private theorem logStageWeight_sub_mul (a c x : ℝ) :
    logStageWeight (c - a) x * logStageWeight a x = logStageWeight c x := by
  simp only [logStageWeight, ← Complex.ofReal_mul, ← Real.exp_add, sub_mul, sub_add_cancel]

private theorem coord_eq_weight_mul {I : Set ℝ} (F : logWeightedStage I) (a c : I) :
    (F.1 c : ℝ → ℂ) = fun x ↦ logStageWeight (c - a) x * F.1 a x := by
  obtain ⟨f, hf⟩ := F.property
  rw [← hf]
  funext x
  simp only [logWeightedProfileMap_apply, ← mul_assoc, logStageWeight_sub_mul]

private theorem contDiff_logStageWeight (d : ℝ) : ContDiff ℝ ∞ (logStageWeight d) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

private theorem iteratedDeriv_logStageWeight (n : ℕ) (d : ℝ) :
    iteratedDeriv n (logStageWeight d) = fun x ↦ ((d : ℂ) ^ n) * logStageWeight d x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (logStageWeight d) ((d : ℂ) * logStageWeight d x) x := by
      have hd : HasDerivAt (fun y : ℝ ↦ d * y) d x := by
        simpa using (hasDerivAt_id x).const_mul d
      change HasDerivAt (fun y ↦ (Real.exp (d * y) : ℂ))
        ((d : ℂ) * (Real.exp (d * x) : ℂ)) x
      rw [mul_comm]
      exact_mod_cast hd.exp.ofReal_comp
    rw [(h.const_mul ((d : ℂ) ^ n)).deriv, pow_succ, mul_assoc]

private theorem weightedDeriv_le_of_mul_nonpos (d : ℝ) (f : 𝓢(ℝ, ℂ)) (k n : ℕ) (x : ℝ)
    (hx : d * x ≤ 0) :
    |x| ^ k * ‖iteratedDeriv n (fun t ↦ logStageWeight d t * f t) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |d| ^ j *
        SchwartzMap.seminorm ℂ k (n - j) f := by
  rw [iteratedDeriv_fun_mul ((contDiff_logStageWeight d).contDiffAt.of_le (by exact_mod_cast le_top))
    (f.contDiffAt n)]
  simp only [iteratedDeriv_logStageWeight]
  have hW : ‖logStageWeight d x‖ ≤ 1 := by
    simpa only [logStageWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using Real.exp_le_one_iff.2 hx
  calc
    _ ≤ |x| ^ k * ∑ j ∈ Finset.range (n + 1),
        ‖(n.choose j : ℂ) * ((d : ℂ) ^ j * logStageWeight d x) * iteratedDeriv (n - j) f x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ = (n.choose j : ℝ) * |d| ^ j *
            (‖logStageWeight d x‖ * (|x| ^ k * ‖iteratedDeriv (n - j) f x‖)) := by ring
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ 1 * (|x| ^ k * ‖iteratedDeriv (n - j) f x‖) := by gcongr
            _ ≤ _ := by simpa only [one_mul] using f.le_seminorm' ℂ k (n - j) x

/-- Every weighted Schwartz seminorm at an intermediate weight is controlled by finitely many
seminorms at the two bracketing weights. The coefficients do not depend on the profile. -/
public theorem logWeightedStage_seminorm_le_endpoints {I : Set ℝ} {a c b : I}
    (hac : a ≤ c) (hcb : c ≤ b) (k n : ℕ) (F : logWeightedStage I) :
    SchwartzMap.seminorm ℂ k n (F.1 c) ≤
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |(c : ℝ) - a| ^ j *
        SchwartzMap.seminorm ℂ k (n - j) (F.1 a)) +
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |(c : ℝ) - b| ^ j *
        SchwartzMap.seminorm ℂ k (n - j) (F.1 b)) := by
  apply (F.1 c).seminorm_le_bound' ℂ k n (by positivity)
  intro x
  rcases le_total x 0 with hx | hx
  · have h := weightedDeriv_le_of_mul_nonpos ((c : ℝ) - a) (F.1 a) k n x
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hac) hx)
    rw [← coord_eq_weight_mul F a c] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have h := weightedDeriv_le_of_mul_nonpos ((c : ℝ) - b) (F.1 b) k n x
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcb) hx)
    rw [← coord_eq_weight_mul F b c] at h
    exact h.trans (le_add_of_nonneg_left (by positivity))

/-- Restricting to weights that bracket every original weight recovers the whole stage
uniformity, not only its points. -/
public theorem isUniformEmbedding_logWeightedStage_restrict {I : Set ℝ} {J : Set I}
    (hJ : ∀ c : I, ∃ a b : J, a.1 ≤ c ∧ c ≤ b.1) :
    IsUniformEmbedding (fun (F : logWeightedStage I) (j : J) ↦ F.1 j.1) := by
  let r : logWeightedStage I →+ (J → 𝓢(ℝ, ℂ)) :=
    { toFun := fun F j ↦ F.1 j.1
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let : IsUniformAddGroup (logWeightedStage I) :=
    IsUniformInducing.isUniformAddGroup (logWeightedStage I).subtype.toAddMonoidHom ⟨rfl⟩
  change IsUniformEmbedding r
  apply IsUniformInducing.isUniformEmbedding
  apply AddMonoidHom.isUniformInducing_of_isInducing
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · have hr : Continuous r := continuous_pi fun j ↦
      (continuous_apply j.1).comp continuous_subtype_val
    exact tendsto_iff_comap.mp (by simpa only [map_zero] using hr.tendsto 0)
  · let L := comap r (𝓝 0)
    change Tendsto id L (𝓝 0)
    have hL : Tendsto r L (𝓝 0) := tendsto_iff_comap.mpr le_rfl
    rw [IsInducing.subtypeVal.tendsto_nhds_iff]
    apply tendsto_pi_nhds.2
    intro c
    obtain ⟨a, b, hac, hcb⟩ := hJ c
    refine (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _ |>.2 ?_
    rintro ⟨k, n⟩ ε hε
    let B (j : J) (U : J → 𝓢(ℝ, ℂ)) : ℝ :=
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |(c : ℝ) - (j.1 : ℝ)| ^ i *
        SchwartzMap.seminorm ℂ k (n - i) (U j)
    have hB (j : J) : Continuous (B j) := by
      refine continuous_finsetSum _ fun i _ ↦ continuous_const.mul ?_
      exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n - i)).comp
        (continuous_apply j)
    have hzero (j : J) : B j 0 = 0 := by simp [B]
    have ht : Tendsto (fun F ↦ B a (r F) + B b (r F)) L (𝓝 0) := by
      simpa only [hzero, add_zero, Function.comp_def] using (((hB a).tendsto 0).comp hL).add
        (((hB b).tendsto 0).comp hL)
    filter_upwards [ht.eventually_lt_const hε] with F hF
    simpa only [SchwartzMap.schwartzSeminormFamily_apply, Function.comp_apply, id_eq,
      Submodule.coe_zero, Pi.zero_apply, sub_zero] using
        (logWeightedStage_seminorm_le_endpoints hac hcb k n F).trans_lt hF

/-- A dense set of weights suffices for bracketing after adjoining the attained extrema.
This also works for disconnected, empty, and singleton weight sets. -/
private theorem exists_countable_bracketing_weights (I : Set ℝ) :
    ∃ J : Set I, J.Countable ∧ ∀ c : I, ∃ a b : J, a.1 ≤ c ∧ c ≤ b.1 := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (α := I)
  let lo : Set I := {c | ∀ a : I, c ≤ a}
  let hi : Set I := {c | ∀ a : I, a ≤ c}
  have hlo : lo.Subsingleton := fun _ hx _ hy ↦ le_antisymm (hx _) (hy _)
  have hhi : hi.Subsingleton := fun _ hx _ hy ↦ le_antisymm (hy _) (hx _)
  let J := D ∪ lo ∪ hi
  refine ⟨J, (hDc.union hlo.countable).union hhi.countable, fun c ↦ ?_⟩
  have hl : ∃ a : J, a.1 ≤ c := by
    by_cases hc : c ∈ lo
    · exact ⟨⟨c, Or.inl (Or.inr hc)⟩, le_rfl⟩
    · have hn : {a : I | (a : ℝ) < (c : ℝ)}.Nonempty := by
        simp only [lo, mem_ofPred_eq, not_forall, not_le] at hc
        exact hc
      obtain ⟨a, haD, ha⟩ := hD.exists_mem_open
        (isOpen_lt continuous_subtype_val continuous_const) hn
      exact ⟨⟨a, Or.inl (Or.inl haD)⟩, ha.le⟩
  have hu : ∃ b : J, c ≤ b.1 := by
    by_cases hc : c ∈ hi
    · exact ⟨⟨c, Or.inr hc⟩, le_rfl⟩
    · have hn : {b : I | (c : ℝ) < (b : ℝ)}.Nonempty := by
        simp only [hi, mem_ofPred_eq, not_forall, not_le] at hc
        exact hc
      obtain ⟨b, hbD, hb⟩ := hD.exists_mem_open
        (isOpen_lt continuous_const continuous_subtype_val) hn
      exact ⟨⟨b, Or.inl (Or.inl hbD)⟩, hb.le⟩
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  exact ⟨a, b, ha, hb⟩

/-- The actual radial stage embeds as a closed subspace of a countable product of
Schwartz spaces by restriction of the original weighted-map coordinates. -/
public theorem exists_countable_logWeightedStage_closedEmbedding {I : Set ℝ} (hI : I.Nonempty) :
    ∃ J : Set I, J.Countable ∧
      IsClosedEmbedding (fun (F : logWeightedStage I) (j : J) ↦ F.1 j.1) := by
  let := completeSpace_logWeightedStage hI
  obtain ⟨J, hJc, hJ⟩ := exists_countable_bracketing_weights I
  exact ⟨J, hJc, (isUniformEmbedding_logWeightedStage_restrict hJ).isClosedEmbedding⟩

/-- The original stage uniformity is countably generated, so it is metrizable without
changing the uniformity used in `completeSpace_logWeightedStage`. -/
public theorem uniformity_logWeightedStage_isCountablyGenerated (I : Set ℝ) :
    (𝓤 (logWeightedStage I)).IsCountablyGenerated := by
  obtain ⟨J, hJc, hJ⟩ := exists_countable_bracketing_weights I
  let := hJc.to_subtype
  let : (𝓤 𝓢(ℝ, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  rw [← (isUniformEmbedding_logWeightedStage_restrict hJ).toIsUniformInducing.comap_uniformity]
  infer_instance

/-- The radial stage is metrizable in its all-weight Schwartz topology. -/
public theorem metrizableSpace_logWeightedStage (I : Set ℝ) :
    TopologicalSpace.MetrizableSpace (logWeightedStage I) := by
  let := uniformity_logWeightedStage_isCountablyGenerated I
  exact UniformSpace.metrizableSpace

/-- The radial complex stage is locally convex over the underlying real field. -/
public theorem locallyConvexSpace_logWeightedStage (I : Set ℝ) :
    LocallyConvexSpace ℝ (logWeightedStage I) := by
  change LocallyConvexSpace ℝ ((logWeightedStage I).restrictScalars ℝ)
  infer_instance

end Masullo
