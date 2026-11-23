module

public import Lemmas.FloorGridMeanKernel
public import Lemmas.FloorGridPhysical
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Local splitting of the floor-grid trace pairing

Removing the half-weight from each absorbed `L²` vector gives a locally integrable
physical profile. The bump and the outer cutoff localize the two legs, so the mean
profile need not be globally square integrable.
-/

open MeasureTheory
open scoped ContDiff

namespace Masullo

noncomputable section

/-- Undo the weight absorbed into the unweighted real `L²(dx)` vector. -/
@[expose] public def floorGridPhysicalProfile (a : ℝ) (v : Lp ℝ 2 (volume : Measure ℝ))
    (x : ℝ) : ℝ :=
  v x / (Real.exp (a * |x|) * (1 + x ^ 2))

/-- Remove the mean exponential kernel from a physical leg. -/
@[expose] public def floorGridCenteredProfile (a : ℝ) (v : Lp ℝ 2 (volume : Measure ℝ))
    (c x : ℝ) : ℝ :=
  floorGridPhysicalProfile a v x - c * floorGridMeanKernel x

/-- The ordinary diagonal of the local trace pairing, with both legs unabsorbed. -/
@[expose] public def floorGridFullPair (a : ℝ) (ρ b : ℝ → ℝ)
    (v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ :=
  ∫ x, ρ x * floorGridMeanWeight a x * floorGridPhysicalProfile a v x *
    (∫ z, deriv b z * floorGridPhysicalProfile a v (x - z))

/-- The two mixed terms and the centered–centered term of the local trace pairing. -/
@[expose] public def floorGridCenteredPair (a : ℝ) (ρ b : ℝ → ℝ)
    (v : Lp ℝ 2 (volume : Measure ℝ)) (c : ℝ) : ℝ :=
  let m := fun x ↦ c * floorGridMeanKernel x
  let r := floorGridCenteredProfile a v c
  ∫ x, (ρ x * floorGridMeanWeight a x * m x * (∫ z, deriv b z * r (x - z))) +
    (ρ x * floorGridMeanWeight a x * r x * (∫ z, deriv b z * m (x - z))) +
    (ρ x * floorGridMeanWeight a x * r x * (∫ z, deriv b z * r (x - z)))

/-- The physical leg of a column is its floor factor times the mean kernel. -/
public theorem floorGridPhysicalProfile_column_ae (a : ℝ) (ha : a < 1 / 2) (j k : ℕ) :
    floorGridPhysicalProfile a (floorGridColumn a ha j k) =ᵐ[volume]
      fun x ↦ floorGridMeanKernel x * ((⌊(k : ℝ) * floorGridPhase j x⌋ : ℤ) : ℝ) := by
  filter_upwards [floorGridColumn_ae a ha j k] with x hx
  have h : Real.exp (a * |x|) * (1 + x ^ 2) ≠ 0 := by positivity
  rw [floorGridPhysicalProfile, hx, floorGridEnvelope, floorGridMeanKernel, div_eq_iff h]
  ring

/-- An unabsorbed `L²` vector is locally integrable, regardless of the sign of `a`. -/
public theorem locallyIntegrable_floorGridPhysicalProfile (a : ℝ)
    (v : Lp ℝ 2 (volume : Measure ℝ)) : LocallyIntegrable (floorGridPhysicalProfile a v) := by
  have hw : Continuous (fun x : ℝ ↦ (Real.exp (a * |x|) * (1 + x ^ 2))⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity)
  change LocallyIntegrable (fun x ↦ v x / (Real.exp (a * |x|) * (1 + x ^ 2)))
  simp_rw [div_eq_mul_inv]
  exact ((Lp.memLp v).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)).mul_continuous hw

private theorem continuous_floorGridMeanProfile (c : ℝ) :
    Continuous (fun x ↦ c * floorGridMeanKernel x) := by
  unfold floorGridMeanKernel
  fun_prop

/-- At every translated argument, the compactly supported differentiated bump can
be paired with any locally integrable physical leg. -/
public theorem integrable_floorGridInner {b p : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) (hp : LocallyIntegrable p) (x : ℝ) :
    Integrable (fun z ↦ deriv b z * p (x - z)) :=
  (hcb.deriv.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
    hb.continuous_deriv_one hp x).integrable

/-- The outer integral is absolutely convergent for any two locally integrable legs.
The inner convolution is continuous, so it acts as part of the compact outer test. -/
public theorem integrable_floorGridPairIntegrand (a : ℝ) {ρ b p q : ℝ → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) (hp : LocallyIntegrable p) (hq : LocallyIntegrable q) :
    Integrable (fun x ↦ ρ x * floorGridMeanWeight a x * p x *
      (∫ z, deriv b z * q (x - z))) := by
  have hw : Continuous (floorGridMeanWeight a) := by unfold floorGridMeanWeight; fun_prop
  have hconv : Continuous (fun x ↦ ∫ z, deriv b z * q (x - z)) :=
    hcb.deriv.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
      hb.continuous_deriv_one hq
  refine (hp.integrable_smul_left_of_hasCompactSupport ((hρ.mul hw).mul hconv)
    hcρ.mul_right.mul_right).congr (ae_of_all _ fun x ↦ ?_)
  change (ρ x * floorGridMeanWeight a x * (∫ z, deriv b z * q (x - z))) * p x = _
  exact mul_right_comm ..

/-- The physical pairing may be computed with any a.e. equal physical representative.
In particular the inner integral is unchanged for every outer argument. -/
public theorem floorGridFullPair_congr (a : ℝ) (ρ b : ℝ → ℝ)
    {v : Lp ℝ 2 (volume : Measure ℝ)} {p : ℝ → ℝ}
    (hp : floorGridPhysicalProfile a v =ᵐ[volume] p) :
    floorGridFullPair a ρ b v =
      ∫ x, ρ x * floorGridMeanWeight a x * p x * (∫ z, deriv b z * p (x - z)) := by
  unfold floorGridFullPair
  apply integral_congr_ae
  filter_upwards [hp] with x hx
  rw [hx]
  congr 1
  apply integral_congr_ae
  have hshift := (volume.measurePreserving_sub_left x).quasiMeasurePreserving
  filter_upwards [hp.comp_tendsto hshift.tendsto_ae] with z hz
  exact congrArg (deriv b z * ·) hz

/-- The full local diagonal is exactly its mean–mean term plus the three terms
with a centered leg. All integrability follows from the test hypotheses and `v ∈ L²`. -/
public theorem floorGridFullPair_split (a : ℝ) {ρ b : ℝ → ℝ}
    (v : Lp ℝ 2 (volume : Measure ℝ)) (c : ℝ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) :
    floorGridFullPair a ρ b v = floorGridMeanPair a ρ b c + floorGridCenteredPair a ρ b v c := by
  let p := floorGridPhysicalProfile a v
  let m := fun x ↦ c * floorGridMeanKernel x
  let r := floorGridCenteredProfile a v c
  let J (f : ℝ → ℝ) (x : ℝ) := ∫ z, deriv b z * f (x - z)
  let K (f g : ℝ → ℝ) (x : ℝ) := ρ x * floorGridMeanWeight a x * f x * J g x
  have hm : LocallyIntegrable m := (continuous_floorGridMeanProfile c).locallyIntegrable
  have hr : LocallyIntegrable r := (locallyIntegrable_floorGridPhysicalProfile a v).sub hm
  have hi {f g : ℝ → ℝ} (hf : LocallyIntegrable f) (hg : LocallyIntegrable g) :
      Integrable (K f g) := integrable_floorGridPairIntegrand a hρ hcρ hb hcb hf hg
  have hleg (x : ℝ) : p x = m x + r x := by
    dsimp [p, m, r, floorGridCenteredProfile]
    ring
  have hJ (x : ℝ) : J p x = J m x + J r x := by
    change (∫ z, deriv b z * p (x - z)) =
      (∫ z, deriv b z * m (x - z)) + ∫ z, deriv b z * r (x - z)
    rw [← integral_add (integrable_floorGridInner hb hcb hm x)
      (integrable_floorGridInner hb hcb hr x)]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      dsimp only
      rw [hleg, mul_add]
  have hcenter : Integrable (fun x ↦ (K m r x + K r m x) + K r r x) :=
    ((hi hm hr).add (hi hr hm)).add (hi hr hr)
  change (∫ x, K p p x) = (∫ x, K m m x) +
    ∫ x, (K m r x + K r m x) + K r r x
  rw [← integral_add (hi hm hm) hcenter]
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ by
    dsimp only [K]
    rw [hleg x, hJ x]
    ring

end

end Masullo
