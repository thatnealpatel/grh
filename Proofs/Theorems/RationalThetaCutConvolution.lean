module

public import Theorems.RationalThetaBandClosure
public import Theorems.RationalThetaCutBand
public import Theorems.RationalThetaPrimeMask
public import Theorems.RationalThetaConvolutionProjection
public import Lemmas.WeightedLogConvolution
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Cut ranges after projected log convolution

The band is on the additive Fourier transform of the real Schwartz test.
The convolution, by contrast, acts on the raw theta profile in log norm.
The cutoff is applied last, after both projections.
-/

open NumberField MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- The pointwise range equality with an actual finite prime-unit mask on
adelic tests, evaluated on the positive norm section. -/
public theorem rationalTheta_primeMasked_cutBand_image_eq (p : Nat.Primes) {Y Λ : ℝ}
    (hY : 0 < Y) (hΛ : 0 < Λ) :
    (fun (c : 𝓢(ℝ, ℂ)) (t : Ioc (0 : ℝ) Λ) ↦ ∑' q : ℚˣ,
      rationalAdelePrimeMasked p c
        ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q *
          rationalIdeleLogSection (Multiplicative.ofAdd (Real.log t)) : IdeleGroup (𝓞 ℚ) ℚ) :
          AdeleRing (𝓞 ℚ) ℚ)) '' rationalThetaBandInput (Y / (p : ℝ)) =
      (fun (b : 𝓢(ℝ, ℂ)) (t : Ioc (0 : ℝ) Λ) ↦ rationalTheta b t) '' rationalThetaBandInput Y := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  rw [← rationalTheta_cutBand_image_eq hp hY hΛ]
  apply congrArg (· '' rationalThetaBandInput (Y / (p : ℝ)))
  funext c t
  exact (rationalTheta_eq_primeMasked_idele_sum p c t.property.1).2

private noncomputable abbrev H := Lp ℂ 2 (volume : Measure ℝ)

/-- Position multiplication in the weight-conjugated log coordinate. This
commutes with multiplication by the weight, not in general with convolution. -/
public noncomputable def rationalThetaLogMultiplier {ρ : ℝ → ℂ} (hρ : MemLp ρ ⊤ volume)
    (u : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (hρ.mul (Lp.memLp u) (r := 2)).toLp _

private theorem logCut_eq_of_ae {ρ : ℝ → ℂ} (hρ : MemLp ρ ⊤ volume) {u v : H}
    (h : ∀ᵐ x, ρ x ≠ 0 → u x = v x) : rationalThetaLogMultiplier hρ u = rationalThetaLogMultiplier hρ v := by
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [h] with x hx
  change ρ x * u x = ρ x * v x
  by_cases h0 : ρ x = 0
  · simp [h0]
  · rw [hx h0]

/-- A lower bound on the kernel support determines exactly how far above
an upper observation cutoff the two input profiles must agree. -/
public theorem logConvolution_eq_of_agree_below {f u v : ℝ → ℂ} {a R : ℝ}
    (hf : Function.support f ⊆ Ici a) (huv : EqOn u v (Iic (R - a)))
    {x : ℝ} (hx : x ≤ R) :
    (∫ y, f y * u (x - y)) = ∫ y, f y * v (x - y) := by
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : f y = 0
  · simp [hy]
  · rw [huv (show x - y ∈ Iic (R - a) from sub_le_sub hx (hf hy))]

private theorem unweight_ae {s : ℝ} {u : H} {v : ℝ → ℂ}
    (hu : ⇑u =ᵐ[volume] fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) * v x)
    (x : ℝ) : ∀ᵐ y : ℝ, u (x - y) / (symmetricStripWeightRoot 0 s (x - y) : ℂ) = v (x - y) := by
  have h := ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hu)
  filter_upwards [h] with y hy
  change u (x - y) = _ * v (x - y) at hy
  rw [hy, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (symmetricStripWeightRoot_pos ..).ne')]

private noncomputable abbrev fullSpace {s : ℝ} (hs : 0 ≤ s) :=
  rationalThetaWeightedEvenImage 0 hs (le_refl 0) univ

private noncomputable abbrev bandSpace {s : ℝ} (hs : 0 ≤ s) (Y : ℝ) :=
  rationalThetaWeightedEvenImage 0 hs (le_refl 0) {ξ | |ξ| ≤ Y}

private noncomputable abbrev bandVector {s Y : ℝ} (hs : 0 ≤ s) {b : 𝓢(ℝ, ℂ)}
    (hb : b ∈ rationalThetaBandInput Y) :=
  rationalThetaWeightedLog 0 hs (le_refl 0) ⟨b, hb.2.1, hb.2.2.1⟩

private theorem bandVector_mem {s Y : ℝ} (hs : 0 ≤ s) {b : 𝓢(ℝ, ℂ)}
    (hb : b ∈ rationalThetaBandInput Y) : bandVector hs hb ∈ bandSpace hs Y := by
  exact rationalThetaWeightedLog_mem_evenImage 0 hs (le_refl 0) _ _ hb.1
    (fun ξ hξ ↦ hb.2.2.2 ξ (lt_of_not_ge hξ))

private theorem thetaVector_ae {s : ℝ} (hs : 0 ≤ s) (b : RationalThetaInput) :
    ⇑(rationalThetaWeightedLog 0 hs (le_refl 0) b) =ᵐ[volume]
      fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) * rationalTheta b.val (Real.exp x) := by
  simpa only [rationalThetaWeightedLog, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    using (memLp_rationalTheta_weighted b 0 0 s hs (le_refl 0)).coeFn_toLp

private theorem isClosed_invariant_of_generators {s : ℝ} (hs : 0 ≤ s) (A : H →L[ℂ] H)
    (hg : ∀ b : RationalThetaInput, Function.Even (⇑b.val) →
      A (rationalThetaWeightedLog 0 hs (le_refl 0) b) ∈ fullSpace hs) :
    ∀ u ∈ fullSpace hs, A u ∈ fullSpace hs := by
  intro u hu
  have he : (fullSpace hs : Set H) ⊆ A ⁻¹' (fullSpace hs : Set H) := by
    conv_lhs => rw [coe_rationalThetaWeightedEvenImage]
    exact closure_minimal (by rintro _ ⟨b, hb, rfl⟩; exact hg b hb.1)
      ((fullSpace hs).isClosed.preimage A.continuous)
  exact he hu

/-- On a genuine input, ambient bounded convolution is the Bochner integral
of weighted theta profiles of dilated inputs. -/
public theorem weightedLogConvolution_theta_eq {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (b : RationalThetaInput) :
    weightedLogConvolution hs hf hcf (rationalThetaWeightedLog 0 hs (le_refl 0) b) =
      rationalThetaWeightedLogConvolution hs f b := by
  apply Lp.ext
  refine (weightedLogConvolution_ae hs hf hcf _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (rationalThetaWeightedLogConvolution_ae hs f b hf hcf).symm
  filter_upwards with x
  apply congrArg (_ * ·)
  apply integral_congr_ae
  filter_upwards [unweight_ae (thetaVector_ae hs b) x] with y hy
  rw [hy]

/-- Bounded raw convolution preserves the entire closed even theta image,
not only the generating set. -/
public theorem weightedLogConvolution_mem_thetaClosure {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) {u : Lp ℂ 2 (volume : Measure ℝ)}
    (hu : u ∈ rationalThetaWeightedEvenImage 0 hs (le_refl 0) univ) :
    weightedLogConvolution hs hf hcf u ∈ rationalThetaWeightedEvenImage 0 hs (le_refl 0) univ := by
  apply isClosed_invariant_of_generators hs (weightedLogConvolution hs hf hcf) _ u hu
  intro b hb
  rw [weightedLogConvolution_theta_eq hs hf hcf b]
  exact rationalThetaWeightedLogConvolution_mem_evenImage hs f b hb

/-- Exact equality of cut output ranges, with the band projection applied
first, raw log convolution second, and the full theta projection third.
`R` is the upper log cutoff. If the kernel is supported above `a`, the
backward telescope need only cover positive norms through `exp (R - a)`.
No uniform lift as `R` varies, or equality of traces, is asserted. -/
public theorem rationalTheta_projected_cutBand_image_eq {s Y p R a : ℝ} (hs : 0 ≤ s)
    (hp : 1 < p) (hY : 0 < Y) {f ρ : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (ha : Function.support f ⊆ Ici a)
    (hρ : MemLp ρ ⊤ volume) (hR : Function.support ρ ⊆ Iic R) :
    let Q := (rationalThetaWeightedEvenImage 0 hs (le_refl 0) {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
    let P := (rationalThetaWeightedEvenImage 0 hs (le_refl 0) univ).toSubmodule.starProjection
    let T := fun u ↦ rationalThetaLogMultiplier hρ (P (weightedLogConvolution hs hf hcf (Q u)))
    let J := fun b : rationalThetaBandInput Y ↦ rationalThetaWeightedLog 0 hs (le_refl 0)
      ⟨b.val, b.property.2.1, b.property.2.2.1⟩
    range (fun b ↦ T (J b)) = range (fun c : rationalThetaBandInput (Y / p) ↦
      T (J ⟨c.val - dilateSchwartz c.val p (zero_lt_one.trans hp).ne',
        (rationalTheta_cutBand_difference hp hY c.property).1⟩)) := by
  have hA : ∀ b : RationalThetaInput, Function.Even (⇑b.val) →
      ⇑((fullSpace hs).toSubmodule.starProjection
        (weightedLogConvolution hs hf hcf (rationalThetaWeightedLog 0 hs (le_refl 0) b)))
        =ᵐ[volume] fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) *
          ∫ y, f y * rationalTheta b.val (Real.exp (x - y)) := by
    intro b hb
    rw [weightedLogConvolution_theta_eq hs hf hcf b]
    exact rationalThetaWeightedLogConvolution_starProjection_ae hs f b hb hf hcf
  dsimp only
  apply Subset.antisymm
  · rintro _ ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨c, hc, he⟩ := rationalTheta_cutBand_preimage hp hY (Real.exp_pos (R - a)) hb
    refine ⟨⟨c, hc⟩, ?_⟩
    have hd := rationalTheta_cutBand_difference hp hY hc
    dsimp only
    rw [Submodule.starProjection_eq_self_iff.mpr (bandVector_mem hs hd.1),
      Submodule.starProjection_eq_self_iff.mpr (bandVector_mem hs hb)]
    apply logCut_eq_of_ae hρ
    filter_upwards [hA ⟨_, hd.1.2.1, hd.1.2.2.1⟩ hd.1.1,
      hA ⟨b, hb.2.1, hb.2.2.1⟩ hb.1] with x h1 h2
    intro hx
    rw [h1, h2]
    apply congrArg (_ * ·)
    apply logConvolution_eq_of_agree_below (u := fun z ↦ rationalTheta
      (c - dilateSchwartz c p (zero_lt_one.trans hp).ne') (Real.exp z))
      (v := fun z ↦ rationalTheta b (Real.exp z)) ha _ (hR hx)
    intro z hz
    exact (hd.2 _ (Real.exp_pos z)).trans (he _ (Real.exp_pos _) (Real.exp_le_exp.mpr hz))
  · rintro _ ⟨c, rfl⟩
    exact ⟨⟨_, (rationalTheta_cutBand_difference hp hY c.property).1⟩, rfl⟩


end Masullo
