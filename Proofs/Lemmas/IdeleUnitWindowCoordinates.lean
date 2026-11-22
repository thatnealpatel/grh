module

public import Lemmas.IdeleUnitWindow
public import Lemmas.LogVolume
public import Theorems.ArchimedeanHaarCoordinates

/-! # Coordinates of the split integral-finite unit window

At the omitted place the radial section multiplies by a positive scalar.
It changes the total weighted log but leaves the retained logs and all
angles unchanged. The finite components remain in the integral units.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open InfinitePlace.Completion (extensionEmbedding extensionEmbeddingOfIsReal
  extensionEmbeddingOfIsReal_apply)
open NumberField.Units.dirichletUnitTheorem (logSpace w₀)
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "L" => Multiplicative ℝ
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)

/-- The Archimedean factor of the split window: norm log in `J`, retained
logs in the regulator box, and angles in the torsion slice. -/
@[expose] public noncomputable def archimedeanUnitWindowStrip (v : InfinitePlace K) (J : Set L) :
    Set ((w : InfinitePlace K) → w.Completionˣ) :=
  (fun u ↦ ((∑ w, (w.mult : ℝ) * Real.log ‖(u w).val‖),
    (fun w : {w : InfinitePlace K // w ≠ W} ↦ (w.val.mult : ℝ) * Real.log ‖(u w.val).val‖),
    fun w ↦ archimedeanAngle w (u w))) ⁻¹'
    ((Multiplicative.ofAdd ⁻¹' J) ×ˢ archimedeanUnitDomainCoordinates v)

private theorem ideleLogSection_mem_finiteUnits (x : L) : ideleLogSection W x ∈ ideleFiniteUnits := by
  rw [mem_ideleFiniteUnits]
  intro w
  rw [ideleLogSection_finite, map_one]

private theorem split_infinite_embedding (x : L) (g : I₁) (w : InfinitePlace K) :
    extensionEmbedding w (ideleInfiniteUnitCoordinates K (σ (x, g)) w).val =
      (if w = W then (Real.exp (x.toAdd / ((w₀ : InfinitePlace K).mult : ℝ)) : ℂ) else 1) *
        extensionEmbedding w (ideleInfiniteUnitCoordinates K (g : I) w).val := by
  rw [ideleLogSplit_apply]
  change extensionEmbedding w (((ideleLogSection W x : I) : A).1 w * ((g : I) : A).1 w) = _
  rw [map_mul, ideleLogSection_infinite]
  rfl

private theorem split_retained (x : L) (g : I₁) (w : {w : InfinitePlace K // w ≠ W}) :
    ideleInfiniteUnitCoordinates K (σ (x, g)) w.val = ideleInfiniteUnitCoordinates K (g : I) w.val := by
  apply Units.ext
  apply (extensionEmbedding w.val).injective
  rw [split_infinite_embedding, ite_eq_right w.property, one_mul]

omit [NumberField K] in
private theorem angle_eq_of_pos_scale (w : InfinitePlace K) (a b : w.Completionˣ)
    {r : ℝ} (hr : 0 < r)
    (h : extensionEmbedding w a.val = (r : ℂ) * extensionEmbedding w b.val) :
    archimedeanAngle w a = archimedeanAngle w b := by
  let P (c : AngularChart w.Completionˣ) : Prop := c.coord a = c.coord b
  change P (archimedeanAngularChart w)
  by_cases hw : w.IsReal
  · rw [archimedeanAngularChart, dite_eq_left hw]
    have hreal : extensionEmbeddingOfIsReal hw a.val = r * extensionEmbeddingOfIsReal hw b.val := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_mul, extensionEmbeddingOfIsReal_apply, extensionEmbeddingOfIsReal_apply]
      exact h
    dsimp only [P, AngularChart.coord]
    simp only [hreal, mul_pos_iff_of_pos_left hr]
  · rw [archimedeanAngularChart, dite_eq_right hw]
    dsimp only [P, AngularChart.coord]
    rw [h, Complex.arg_real_mul _ hr]

private theorem split_angles (x : L) (g : I₁) (w : InfinitePlace K) :
    archimedeanAngle w (ideleInfiniteUnitCoordinates K (σ (x, g)) w) =
      archimedeanAngle w (ideleInfiniteUnitCoordinates K (g : I) w) := by
  by_cases hw : w = W
  · apply angle_eq_of_pos_scale w _ _ (Real.exp_pos (x.toAdd / ((w₀ : InfinitePlace K).mult : ℝ)))
    simpa only [ite_eq_left hw] using split_infinite_embedding x g w
  · rw [split_retained x g ⟨w, hw⟩]

private theorem logNorm_eq_sum (a : I) (ha : a ∈ ideleFiniteUnits) :
    (ideleLogNorm a).toAdd = ∑ w : InfinitePlace K,
      (w.mult : ℝ) * Real.log ‖(ideleInfiniteUnitCoordinates K a w).val‖ := by
  rw [ideleLogNorm_apply, ideleNorm_of_mem_ideleFiniteUnits ha, Real.log_prod]
  · exact Finset.sum_congr rfl fun w _ ↦ Real.log_pow _ _
  · exact fun w _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (ideleInfiniteUnitCoordinates K a w).ne_zero)

/-- The image of the actual idelic splitting is the integral-finite rectangle
of the Archimedean strip. In particular its preimage in any finite stage
is the Archimedean strip times integral units, not full active factors. -/
public theorem image_ideleLogSplit_unitWindow (v : InfinitePlace K) (J : Set L) :
    σ '' (J ×ˢ ideleUnitWindow v) = ideleUnitRectangle K (archimedeanUnitWindowStrip v J) := by
  apply (Set.eq_preimage_iff_image_eq (σ).bijective).mp
  ext p
  rcases p with ⟨x, g⟩
  have hfin : σ (x, g) ∈ ideleFiniteUnits ↔ (g : I) ∈ ideleFiniteUnits := by
    rw [ideleLogSplit_apply]
    exact ideleFiniteUnits.mul_mem_cancel_left (ideleLogSection_mem_finiteUnits x)
  have hfin' : (∀ w : HeightOneSpectrum (𝓞 K),
      (σ (x, g) : A).2 w ∈ w.adicCompletionIntegers K ∧
      (↑((σ (x, g))⁻¹) : A).2 w ∈ w.adicCompletionIntegers K) ↔ σ (x, g) ∈ ideleFiniteUnits := by
    change _ ↔ σ (x, g) ∈ (ideleFiniteUnits (K := K) : Set I)
    rw [← range_ideleFiniteStageEmbedding_empty, range_ideleFiniteStageEmbedding]
    simp
  change (x ∈ J ∧ (g : I) ∈ ideleFiniteUnits ∧ ideleInfinitePart (g : I) ∈ _) ↔
    (ideleInfiniteUnitCoordinates K (σ (x, g)) ∈ archimedeanUnitWindowStrip v J ∧ _)
  rw [hfin', hfin]
  by_cases hg : (g : I) ∈ ideleFiniteUnits
  · let a : archimedeanNormOne (K := K) :=
      ⟨ideleInfinitePart (g : I), ideleInfinitePart_mem_archimedeanNormOne g hg⟩
    have ha : ideleInfinitePart (g : I) ∈
        ((↑) : archimedeanNormOne (K := K) → (InfiniteAdeleRing K)ˣ) '' archimedeanUnitDomain v ↔
        a ∈ archimedeanUnitDomain v := by
      change (a : (InfiniteAdeleRing K)ˣ) ∈ _ ↔ _
      exact Subtype.val_injective.mem_set_image
    have hlocal (w : InfinitePlace K) :
        ContinuousMulEquiv.piUnits (a : (InfiniteAdeleRing K)ˣ) w =
          ideleInfiniteUnitCoordinates K (g : I) w := by
      apply Units.ext
      exact congrFun (ideleInfinitePart_val (g : I)) w
    have hlogs : (fun w : {w : InfinitePlace K // w ≠ W} ↦
        (w.val.mult : ℝ) * Real.log ‖(ideleInfiniteUnitCoordinates K (σ (x, g)) w.val).val‖) =
        archimedeanDroppedLog a := by
      funext w
      rw [split_retained x g w, archimedeanDroppedLog_apply]
      change (w.val.mult : ℝ) * Real.log ‖(ideleInfiniteUnitCoordinates K (g : I) w.val).val‖ =
        (w.val.mult : ℝ) * Real.log ‖(ideleInfinitePart (g : I)).val w.val‖
      rw [ideleInfinitePart_val]
      rfl
    have hang : (fun w ↦ archimedeanAngle w (ideleInfiniteUnitCoordinates K (σ (x, g)) w)) =
        fun w ↦ archimedeanAngle w (ContinuousMulEquiv.piUnits (a : (InfiniteAdeleRing K)ˣ) w) := by
      funext w
      rw [hlocal, split_angles]
    have hx : ideleLogNorm (σ (x, g)) = x := by
      have hg1 : ideleLogNorm (g : I) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [ideleLogNorm_apply, (mem_ideleNormOne _).mp g.property, Real.log_one]
        rfl
      rw [ideleLogSplit_apply, map_mul, ideleLogNorm_section, hg1, mul_one]
    rw [ha, mem_archimedeanUnitDomain_iff_coordinates, archimedeanUnitWindowStrip,
      mem_preimage, mem_prod, ← logNorm_eq_sum _ (hfin.mpr hg), hx, hlogs, hang]
    simp [hg]
  · simp [hg]

private theorem measurableSet_archimedeanUnitDomainCoordinates (v : InfinitePlace K) :
    MeasurableSet (archimedeanUnitDomainCoordinates v) :=
  (measurableSet_regulatorBox K).prod (measurableSet_archimedeanAngularTorsionSlice v)

section Haar

variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
  [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]

/-- The Archimedean strip in completion-unit coordinates is Borel. -/
public theorem measurableSet_archimedeanUnitWindowStrip (v : InfinitePlace K) {J : Set L}
    (hJ : MeasurableSet J) : MeasurableSet (archimedeanUnitWindowStrip v J) :=
  ((hJ.preimage measurable_ofAdd).prod (measurableSet_archimedeanUnitDomainCoordinates v)).preimage
    (measurePreserving_archimedeanHaarCoordinates K).measurable

/-- Separation of the log coordinate contributes Lebesgue mass with no
extra weight, while the retained factors give the mass of `E₀`. -/
public theorem measure_archimedeanUnitWindowStrip (v : InfinitePlace K) {J : Set L}
    (hJ : MeasurableSet J) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    (Measure.pi fun w : InfinitePlace K ↦ archimedeanCompletionHaar w)
        (archimedeanUnitWindowStrip v J) =
      logVolume J * ((volume : Measure (logSpace K)).prod ω) (archimedeanUnitDomainCoordinates v) := by
  intro ω
  rw [archimedeanUnitWindowStrip]
  rw [(measurePreserving_archimedeanHaarCoordinates K).measure_preimage
    (((hJ.preimage measurable_ofAdd).prod (measurableSet_archimedeanUnitDomainCoordinates v)).nullMeasurableSet),
    Measure.prod_prod, ← map_toAdd_logVolume, Measure.map_apply measurable_toAdd
      (hJ.preimage measurable_ofAdd)]
  rfl

end Haar

end Masullo
