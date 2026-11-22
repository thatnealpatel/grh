module

public import Theorems.RationalThetaBand
import Lemmas.ScaledPoisson

/-!
# Exact finite-band theta ranges on a bounded norm window

On the rational unramified real section, the even two-moment theta profiles
with band bound `Y`, restricted to `0 < t ≤ Λ`, are exactly the restrictions
of the differences `Θ_c(t) - Θ_c(p*t)` from inputs with band bound `Y/p`.
The preimage is a finite backward telescope: the remainder moves below the
band's lower norm edge uniformly on the window. This is a pointwise range
identity on the window, not an identity for profiles on all positive norms
or a statement about their closures.
-/

open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Even real-line Schwartz inputs with both zero modes removed and with
Fourier transform vanishing outside `[-Y, Y]`. -/
@[expose] public def rationalThetaBandInput (Y : ℝ) : Set 𝓢(ℝ, ℂ) :=
  {b | Function.Even b ∧ b 0 = 0 ∧ (𝓕 b) 0 = 0 ∧
    ∀ ξ : ℝ, Y < |ξ| → (𝓕 b) ξ = 0}

private theorem bandInput_mono {X Y : ℝ} (hXY : X ≤ Y) :
    rationalThetaBandInput X ⊆ rationalThetaBandInput Y := by
  rintro b ⟨he, h₀, hF₀, hband⟩
  exact ⟨he, h₀, hF₀, fun ξ hξ ↦ hband ξ (hXY.trans_lt hξ)⟩

private theorem bandInput_sub {Y : ℝ} {b c : 𝓢(ℝ, ℂ)}
    (hb : b ∈ rationalThetaBandInput Y) (hc : c ∈ rationalThetaBandInput Y) :
    b - c ∈ rationalThetaBandInput Y := by
  rcases hb with ⟨hbe, hb₀, hFb₀, hbband⟩
  rcases hc with ⟨hce, hc₀, hFc₀, hcband⟩
  refine ⟨fun x ↦ ?_, ?_, ?_, fun ξ hξ ↦ ?_⟩
  · simp only [_root_.sub_apply, hbe x, hce x]
  · simp [_root_.sub_apply, hb₀, hc₀]
  · simp [FourierTransform.fourier_sub, _root_.sub_apply, hFb₀, hFc₀]
  · simp [FourierTransform.fourier_sub, _root_.sub_apply, hbband ξ hξ, hcband ξ hξ]

private theorem bandInput_dilate {Y a : ℝ} {b : 𝓢(ℝ, ℂ)}
    (hb : b ∈ rationalThetaBandInput Y) (ha : 0 < a) :
    dilateSchwartz b a ha.ne' ∈ rationalThetaBandInput (a * Y) := by
  rcases hb with ⟨he, h₀, hF₀, hband⟩
  refine ⟨fun x ↦ ?_, ?_, ?_, fun ξ hξ ↦ ?_⟩
  · simpa only [dilateSchwartz_apply, mul_neg] using he (a * x)
  · simp [dilateSchwartz_apply, h₀]
  · simp [fourier_dilateSchwartz _ ha, hF₀]
  · rw [fourier_dilateSchwartz _ ha, hband, smul_zero]
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha), ← div_eq_inv_mul]
    exact (lt_div_iff₀ ha).mpr (by simpa only [mul_comm Y a] using hξ)

private theorem rationalTheta_sub (b c : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) :
    rationalTheta (b - c) t = rationalTheta b t - rationalTheta c t := by
  have hs (a : 𝓢(ℝ, ℂ)) :=
    (summable_norm_schwartz_int_mul a ht).of_norm.subtype (fun n : ℤ ↦ n ≠ 0)
  exact (hs b).tsum_sub (hs c)

private theorem rationalTheta_dilate (b : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    rationalTheta (dilateSchwartz b a ha) t = rationalTheta b (a * t) := by
  simp only [rationalTheta, dilateSchwartz_apply, mul_assoc]

/-- The negative sum of the first `n` inverse dilates, built by recursion. -/
private noncomputable def cutBandPartialPreimage (b : 𝓢(ℝ, ℂ)) {p : ℝ} (hp : 0 < p) :
    ℕ → 𝓢(ℝ, ℂ)
  | 0 => 0
  | n + 1 => dilateSchwartz (cutBandPartialPreimage b hp n - b) p⁻¹ (inv_pos.mpr hp).ne'

private theorem cutBandPartialPreimage_telescope (b : 𝓢(ℝ, ℂ)) {p : ℝ} (hp : 0 < p)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    rationalTheta (cutBandPartialPreimage b hp n) t -
        rationalTheta (cutBandPartialPreimage b hp n) (p * t) =
      rationalTheta b t - rationalTheta b (p⁻¹ ^ n * t) := by
  have hstep (n : ℕ) (s : ℝ) (hs : 0 < s) :
      rationalTheta (cutBandPartialPreimage b hp (n + 1)) s =
        rationalTheta (cutBandPartialPreimage b hp n) (p⁻¹ * s) -
          rationalTheta b (p⁻¹ * s) := by
    rw [cutBandPartialPreimage, rationalTheta_dilate,
      rationalTheta_sub _ _ (mul_pos (inv_pos.mpr hp) hs).ne']
  have hscale (s : ℝ) : p⁻¹ * (p * s) = s := by
    rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  induction n generalizing t with
  | zero => simp [cutBandPartialPreimage, rationalTheta]
  | succ n ih =>
    have h := ih (mul_pos (inv_pos.mpr hp) ht)
    rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at h
    rw [hstep n t ht, hstep n (p * t) (mul_pos hp ht), hscale, pow_succ, mul_assoc,
      sub_sub_sub_comm, h]
    abel

/-- A single narrower-band input realizes a given theta profile by a dilation
difference throughout the window `0 < t ≤ Λ`, including the upper endpoint. -/
public theorem rationalTheta_cutBand_preimage {p Y Λ : ℝ} (hp : 1 < p) (hY : 0 < Y)
    (_hΛ : 0 < Λ) {b : 𝓢(ℝ, ℂ)} (hb : b ∈ rationalThetaBandInput Y) :
    ∃ c ∈ rationalThetaBandInput (Y / p), ∀ t : ℝ, 0 < t → t ≤ Λ →
      rationalTheta c t - rationalTheta c (p * t) = rationalTheta b t := by
  have hp₀ := zero_lt_one.trans hp
  have hnarrow : Y / p ≤ Y := div_le_self hY.le hp.le
  have hpre (n : ℕ) : cutBandPartialPreimage b hp₀ n ∈ rationalThetaBandInput (Y / p) := by
    induction n with
    | zero => simp [cutBandPartialPreimage, rationalThetaBandInput, Function.Even]
    | succ n ih =>
      rw [cutBandPartialPreimage, div_eq_inv_mul]
      exact bandInput_dilate (bandInput_sub (bandInput_mono hnarrow ih) hb) (inv_pos.mpr hp₀)
  -- The strict inequality makes the Poisson remainder vanish even at `t = Λ`.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Y * Λ) hp
  refine ⟨cutBandPartialPreimage b hp₀ n, hpre n, fun t ht htΛ ↦ ?_⟩
  rcases hb with ⟨_, hb₀, hFb₀, hband⟩
  have hedge : Y < (p⁻¹ ^ n * t)⁻¹ := by
    rw [inv_pow, ← div_eq_inv_mul, inv_div, lt_div_iff₀ ht]
    exact (mul_le_mul_of_nonneg_left htΛ hY.le).trans_lt hn
  rw [cutBandPartialPreimage_telescope b hp₀ n ht,
    rationalTheta_eq_zero_of_inv_gt_band b hb₀ hFb₀ hband
      (mul_pos (pow_pos (inv_pos.mpr hp₀) n) ht) hedge, sub_zero]

/-- The Schwartz difference of a narrower-band input and its positive dilate is
in the wider band. It realizes the theta difference at every positive scale,
without any window restriction. -/
public theorem rationalTheta_cutBand_difference {p Y : ℝ} (hp : 1 < p) (hY : 0 < Y)
    {c : 𝓢(ℝ, ℂ)} (hc : c ∈ rationalThetaBandInput (Y / p)) :
    let d := c - dilateSchwartz c p (zero_lt_one.trans hp).ne'
    d ∈ rationalThetaBandInput Y ∧ ∀ t : ℝ, 0 < t →
      rationalTheta d t = rationalTheta c t - rationalTheta c (p * t) := by
  have hp₀ := zero_lt_one.trans hp
  have hd := bandInput_dilate hc hp₀
  rw [mul_comm p, div_mul_cancel₀ _ hp₀.ne'] at hd
  refine ⟨bandInput_sub (bandInput_mono (div_le_self hY.le hp.le) hc) hd, fun t ht ↦ ?_⟩
  rw [rationalTheta_sub _ _ ht.ne', rationalTheta_dilate]

/-- Equality of pointwise profile sets on the positive norm window. No closure
is taken: the two sides are actual restrictions of the indicated profiles. -/
public theorem rationalTheta_cutBand_image_eq {p Y Λ : ℝ} (hp : 1 < p) (hY : 0 < Y)
    (hΛ : 0 < Λ) :
    (fun (c : 𝓢(ℝ, ℂ)) (t : Set.Ioc (0 : ℝ) Λ) ↦
        rationalTheta c t - rationalTheta c (p * t)) '' rationalThetaBandInput (Y / p) =
      (fun (b : 𝓢(ℝ, ℂ)) (t : Set.Ioc (0 : ℝ) Λ) ↦
        rationalTheta b t) '' rationalThetaBandInput Y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hd, h⟩ := rationalTheta_cutBand_difference hp hY hc
    exact ⟨_, hd, funext fun t ↦ h t t.property.1⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, h⟩ := rationalTheta_cutBand_preimage hp hY hΛ hb
    exact ⟨c, hc, funext fun t ↦ h t t.property.1 t.property.2⟩

end Masullo
