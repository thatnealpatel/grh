module

public import Lemmas.IdeleClassTraceLocal
public import Theorems.RationalRadialStripTrace
import all Lemmas.RationalLocalAdditiveModulus
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Local geometric terms for rational radial tests

On a single-place idele class, the idelic norm is the local norm. At a
finite place the rational different is trivial, so the two Haar measures
both give the integral units mass one. At the real place the completion
coordinate carries half of full Haar to half of full Haar, with both signs
retained. Positive compact log support makes the physical and symmetric
log cutoffs agree on the nonzero integrand for all sufficiently small radii.
-/

open Filter IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion ℚ v
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "radial(" F ")" => (fun c : C ↦ F (Real.log (ideleClassNorm c)))

/-- The finite local term of a rational log-norm profile, with the actual
finite-completion Haar measure. The equality of expressions does not need
support or smoothness assumptions. -/
public theorem finiteTraceTerm_rationalRadial (v : V) (F : ℝ → ℂ) :
    finiteTraceTerm v radial(F) = rationalRadialFiniteTerm v F := by
  let : MeasurableSpace K[v]ˣ := borel _
  let : BorelSpace K[v]ˣ := ⟨rfl⟩
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := Ideal.absNorm_eq_one_iff.mp (by
    rw [absNorm_differentIdeal ℚ, NumberField.discr_rat]; rfl)
  have hmass : finiteCompletionMultiplicativeHaar v (range (finiteCompletionUnitInclusion ℚ v)) = 1 := by
    rw [finiteCompletionMultiplicativeHaar_unitMass]
    simp [hd]
  have hhaar : finiteCompletionMultiplicativeHaar v = rationalLocalMultiplicativeHaar v := by
    symm
    apply rationalLocalMultiplicativeHaar_eq
    exact hmass
  unfold finiteTraceTerm rationalRadialFiniteTerm
  dsimp only
  rw [measureReal_def, hmass, ENNReal.toReal_one, div_one, prime_absNorm, hhaar]
  simp only [finiteTraceKernel, ideleClassNorm_ofAdicCompletion, rationalLocalRadialKernel,
    Real.sqrt_eq_rpow]

local notation "w" => Rat.infinitePlace
local notation "hw" => Rat.isReal_infinitePlace
local notation "L" => Rat.infinitePlace.Completion
local notation "half" => (1 / 2 : ℝ≥0∞)

private noncomputable def realUnitsEquiv : Lˣ ≃ₜ* ℝˣ :=
  Units.mapContinuousMulEquiv
    { (ringEquivRealOfIsReal hw).toMulEquiv with
      continuous_toFun := (isometryEquivRealOfIsReal hw).continuous
      continuous_invFun := (isometryEquivRealOfIsReal hw).symm.continuous }

private theorem norm_eq_abs_realCoordinate (x : L) :
    ‖x‖ = |extensionEmbeddingOfIsReal hw x| :=
  ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x).symm

private theorem ideleClassNorm_realUnits (u : Lˣ) :
    ideleClassNorm (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w u) = |(realUnitsEquiv u : ℝ)| := by
  rw [IdeleClassGroup.ofCompletion, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    ideleClassNorm_mk, ideleNorm_apply,
    AdeleRing.norm_apply_of_isUnit (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ w u).isUnit]
  change (∏ v : InfinitePlace ℚ, ‖InfiniteAdeleRing.ofCompletion w (u : L) v‖ ^ v.mult) *
    (∏ᶠ v : V, ‖(1 : K[v])‖) = _
  let := Classical.decEq (InfinitePlace ℚ)
  rw [Fintype.prod_subsingleton _ w, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  simp only [norm_one, finprod_one, mul_one]
  change ‖Pi.mulSingle w (u : L) w‖ = _
  rw [Pi.mulSingle_eq_same]
  exact norm_eq_abs_realCoordinate (u : L)

noncomputable section RealPlace

local instance : MeasurableSpace Lˣ := borel _
local instance : BorelSpace Lˣ := ⟨rfl⟩

private theorem realUnitsEquiv_map_halfHaar :
    (half • realCompletionHaar hw).map realUnitsEquiv = half • realMultiplicativeHaar := by
  have hmeas : Measurable (realUnitsEquiv : Lˣ → ℝˣ) := realUnitsEquiv.continuous.measurable
  rw [Measure.map_smul _ hmeas.aemeasurable]
  congr 1
  let j : MeasurableEmbedding (Units.val : ℝˣ → ℝ) :=
    Units.isOpenEmbedding_val.measurableEmbedding
  apply j.map_injective
  rw [Measure.map_map j.measurable hmeas]
  change (realCompletionHaar hw).map (fun u : Lˣ ↦ extensionEmbeddingOfIsReal hw u.val) = _
  rw [realCompletionHaar_map, map_realMultiplicativeHaar_val, restrict_compl_singleton]

private noncomputable def displacementCutoff (F : ℝ → ℂ) (ε : ℝ) : ℂ :=
  ∫ y in {y : ℝˣ | ε ≤ |1 - (y : ℝ)|}, realLogProfileHaarKernel F y
    ∂(half • realMultiplicativeHaar)

private theorem displacementCutoff_eventuallyEq {F : ℝ → ℂ} (hc : HasCompactSupport F)
    (ht : tsupport F ⊆ Ioi 0) :
    displacementCutoff F =ᶠ[𝓝[>] 0] rationalRadialRealCutoff F := by
  have hgap : ∃ δ > 0, tsupport F ⊆ Ici δ := by
    rcases (tsupport F).eq_empty_or_nonempty with h | h
    · exact ⟨1, zero_lt_one, by rw [h]; exact empty_subset _⟩
    · obtain ⟨δ, hδ, hmin⟩ := hc.exists_isLeast h
      exact ⟨δ, ht hδ, hmin⟩
  obtain ⟨δ, hδ, hgap⟩ := hgap
  have hexp : 0 < Real.exp δ - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hδ)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hexp)] with ε hε
  have hkeep (y : ℝˣ) (hy : realLogProfileHaarKernel F y ≠ 0) :
      ε ≤ |1 - (y : ℝ)| ∧ ε ≤ |Real.log (|(y : ℝ)|)| := by
    have hF : F (Real.log |(y : ℝ)|) ≠ 0 := by
      intro hz
      exact hy (by rw [realLogProfileHaarKernel, hz, zero_mul, zero_div])
    have hlog : δ ≤ Real.log |(y : ℝ)| := hgap (subset_tsupport F hF)
    have hy' := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (abs_pos.mpr y.ne_zero)] at hy'
    have hdist : |(y : ℝ)| - 1 ≤ |1 - (y : ℝ)| := by
      simpa [abs_sub_comm (y : ℝ) 1] using abs_sub_abs_le_abs_sub (y : ℝ) 1
    exact ⟨(hε.2.le.trans (min_le_right _ _)).trans ((sub_le_sub_right hy' 1).trans hdist),
      (hε.2.le.trans (min_le_left _ _)).trans (hlog.trans (le_abs_self _))⟩
  unfold displacementCutoff rationalRadialRealCutoff
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ not_not.mp (fun h ↦ hy (hkeep y h).1)),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ not_not.mp (fun h ↦ hy (hkeep y h).2))]

/-- For positive compact log support the local real trace condition is exactly
convergence of the symmetric log cutoff to the same value from the right. -/
public theorem hasArchimedeanTraceValue_rationalRadial_iff {F : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (ht : tsupport F ⊆ Ioi 0) (R : ℂ) :
    HasArchimedeanTraceValue w radial(F) R ↔
      Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 R) := by
  have hj : MeasurableEmbedding (realUnitsEquiv : Lˣ → ℝˣ) :=
    realUnitsEquiv.toHomeomorph.measurableEmbedding
  have hdisp (u : Lˣ) : ‖1 - (u : L)‖ = |1 - (realUnitsEquiv u : ℝ)| := by
    rw [norm_eq_abs_realCoordinate, map_sub, map_one]
    rfl
  have hker : (fun u : Lˣ ↦ radial(F) (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w u) *
      (Real.sqrt ‖(u : L)‖ : ℂ) / (‖1 - (u : L)‖ : ℂ)) =
      realLogProfileHaarKernel F ∘ realUnitsEquiv := by
    funext u
    simp only [Function.comp_apply, ideleClassNorm_realUnits, norm_eq_abs_realCoordinate, hdisp,
      realLogProfileHaarKernel, Real.sqrt_eq_rpow]
    rfl
  have hset (ε : ℝ) : {u : Lˣ | ε ≤ ‖1 - (u : L)‖} =
      realUnitsEquiv ⁻¹' {y : ℝˣ | ε ≤ |1 - (y : ℝ)|} := by
    ext u
    change (ε ≤ ‖1 - (u : L)‖) ↔ (ε ≤ |1 - (realUnitsEquiv u : ℝ)|)
    rw [hdisp]
  have hint (ε : ℝ) (hε : 0 < ε) : IntegrableOn (realLogProfileHaarKernel F ∘ realUnitsEquiv)
      {u : Lˣ | ε ≤ ‖1 - (u : L)‖} (half • realCompletionHaar hw) := by
    rw [hset, ← hj.integrableOn_map_iff, realUnitsEquiv_map_halfHaar]
    exact (real_log_profile_haar_cutoff hf hc hε).2.1
  have hcut : (fun ε : ℝ ↦ ∫ u in {u : Lˣ | ε ≤ ‖1 - (u : L)‖},
      realLogProfileHaarKernel F (realUnitsEquiv u) ∂(half • realCompletionHaar hw)) =
      displacementCutoff F := by
    funext ε
    rw [hset, displacementCutoff, ← realUnitsEquiv_map_halfHaar, hj.setIntegral_map]
  unfold HasArchimedeanTraceValue
  dsimp only
  simp only [dite_eq_left hw, Rat.isReal_infinitePlace.mult_eq_one, pow_one, hker]
  rw [and_iff_right hint]
  change Tendsto (fun ε : ℝ ↦ ∫ u in {u : Lˣ | ε ≤ ‖1 - (u : L)‖},
      realLogProfileHaarKernel F (realUnitsEquiv u) ∂(half • realCompletionHaar hw)) _ _ ↔ _
  rw [hcut]
  exact tendsto_congr' (displacementCutoff_eventuallyEq hc ht)

end RealPlace

end Masullo
