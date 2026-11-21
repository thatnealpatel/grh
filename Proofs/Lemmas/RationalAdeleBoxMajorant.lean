module

public import Theorems.RationalAdeleBoxSumPoisson
import Lemmas.RationalIdeleUnitWindow
import Mathlib.Analysis.PSeries

/-! # Local summable bounds for rational adelic orbit samples -/

open NumberField IsDedekindDomain Set Topology Filter
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "ι" => algebraMap ℚ A
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

private theorem exists_schwartz_scaled_lattice_majorant (b : 𝓢(ℝ, ℂ)) {d B : ℝ}
    (hd : 0 < d) :
    ∃ u : ℤ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
      ∀ (n : ℤ) (t x : ℝ), d ≤ |t| → |x| ≤ B → ‖b (t * ((n : ℝ) + x))‖ ≤ u n := by
  let C₀ := SchwartzMap.seminorm ℝ 0 0 b
  let C₂ := SchwartzMap.seminorm ℝ 2 0 b
  let C := C₀ + 2 * (d⁻¹ ^ 2 * C₂ + B ^ 2 * C₀)
  have hc₀ : 0 ≤ C₀ := apply_nonneg _ _
  have hc₂ : 0 ≤ C₂ := apply_nonneg _ _
  have hc : 0 ≤ C := by dsimp [C]; positivity
  let u : ℤ → ℝ := fun n ↦ C / (1 + |(n : ℝ)| ^ 2)
  have hu (n : ℤ) : 0 ≤ u n := by dsimp [u]; positivity
  refine ⟨u, ?_, hu, ?_⟩
  · apply Summable.of_norm_bounded_eventually
      ((Real.summable_abs_int_rpow (b := 2) one_lt_two).mul_left C)
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
    have hn' : 0 < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    rw [Real.norm_of_nonneg (hu n), Real.rpow_neg (abs_nonneg _) 2,
      Real.rpow_two, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hc (by positivity) (by linarith)
  · intro n t x ht hx
    let y := t * ((n : ℝ) + x)
    have h₀ : ‖b y‖ ≤ C₀ := by simpa [C₀] using b.le_seminorm ℝ 0 0 y
    have h₂ : |y| ^ 2 * ‖b y‖ ≤ C₂ := by
      simpa [C₂, Real.norm_eq_abs] using b.le_seminorm ℝ 2 0 y
    have hxy : |(n : ℝ) + x| ≤ d⁻¹ * |y| := by
      rw [← div_eq_inv_mul, le_div_iff₀ hd, mul_comm, show |y| = |t| * |(n : ℝ) + x| by
        exact abs_mul _ _]
      exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have hn : |(n : ℝ)| ≤ d⁻¹ * |y| + B := by
      calc
        |(n : ℝ)| = |((n : ℝ) + x) - x| := by rw [add_sub_cancel_right]
        _ ≤ |(n : ℝ) + x| + |x| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((n : ℝ) + x) (-x)
        _ ≤ _ := add_le_add hxy hx
    have hsq : |(n : ℝ)| ^ 2 ≤ 2 * (d⁻¹ ^ 2 * |y| ^ 2 + B ^ 2) := by
      have := pow_le_pow_left₀ (abs_nonneg (n : ℝ)) hn 2
      nlinarith [sq_nonneg (d⁻¹ * |y| - B)]
    change ‖b y‖ ≤ u n
    apply (le_div_iff₀ (by positivity : 0 < 1 + |(n : ℝ)| ^ 2)).mpr
    calc
      ‖b y‖ * (1 + |(n : ℝ)| ^ 2) ≤ ‖b y‖ * (1 + 2 * (d⁻¹ ^ 2 * |y| ^ 2 + B ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hsq _) (norm_nonneg _)
      _ = ‖b y‖ + 2 * (d⁻¹ ^ 2 * (|y| ^ 2 * ‖b y‖) + B ^ 2 * ‖b y‖) := by ring
      _ ≤ C := by
        exact add_le_add h₀ (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left h₂ (sq_nonneg _))
            (mul_le_mul_of_nonneg_left h₀ (sq_nonneg _))) (by norm_num))

private theorem real_mul (x y : A) :
    rationalAdeleReal (x * y) = rationalAdeleReal x * rationalAdeleReal y := by
  simp only [rationalAdeleReal_apply]
  exact map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

private theorem real_add (x y : A) :
    rationalAdeleReal (x + y) = rationalAdeleReal x + rationalAdeleReal y := by
  simp only [rationalAdeleReal_apply]
  exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

private theorem integral_mul_iff (h : J) (hh : h ∈ rationalIdeleUnitWindow) (x : A) :
    (h : A) * x ∈ rationalIntegralAdeles ↔ x ∈ rationalIntegralAdeles := by
  change (∀ v : HeightOneSpectrum (𝓞 ℚ), (h : A).2 v * x.2 v ∈ v.adicCompletionIntegers ℚ) ↔
    (∀ v : HeightOneSpectrum (𝓞 ℚ), x.2 v ∈ v.adicCompletionIntegers ℚ)
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hh, one_mul]

/-- On a neighborhood of each pair `(k₀, x₀)`, the rational orbit samples of one
box have a summable majorant independent of both parameters. -/
public theorem exists_rationalAdeleBox_orbit_majorant (b : 𝓢(ℝ, ℂ)) (a : A) (g : J)
    (p₀ : J × A) :
    ∃ U ∈ 𝓝 p₀, ∃ u : ℚ → ℝ, Summable u ∧
      ∀ q p, p ∈ U → ‖rationalAdeleBox b a g ((p.1 : A) * (ι q + p.2))‖ ≤ u q := by
  classical
  obtain ⟨r, hr, hfin⟩ := exists_rational_principal_mul_norm_section (g⁻¹ * p₀.1)
  let h : J × A → J := fun p ↦ ιˣ r * (g⁻¹ * p.1)
  let a' : A := (↑(g⁻¹) : A) * a
  let z : J × A → A := fun p ↦ ι (↑r⁻¹ : ℚ) * p.2 - (↑((h p)⁻¹) : A) * a'
  have hcont : Continuous h := continuous_const.mul (continuous_const.mul continuous_fst)
  have hzcont : Continuous z := (continuous_const.mul continuous_snd).sub
    ((Units.continuous_val.comp hcont.inv).mul continuous_const)
  obtain ⟨q₀, hq₀⟩ := exists_rational_sub_mem_integral (z p₀)
  let w : J × A → A := fun p ↦ z p - ι q₀
  have hwcont : Continuous w := hzcont.sub continuous_const
  have hpos' : 0 < rationalIdeleReal (h p₀) := by
    dsimp only [h]
    rw [hr, ← ideleClassNorm_mk]
    exact ideleClassNorm_pos _
  have hpos : 0 < rationalAdeleReal (h p₀ : A) := by
    rwa [rationalAdeleReal_apply]
  let d := rationalAdeleReal (h p₀ : A) / 2
  let B := |rationalAdeleReal (w p₀)| + 1
  have hd : 0 < d := half_pos hpos
  have hU : ∀ᶠ p in 𝓝 p₀, h p ∈ rationalIdeleUnitWindow ∧ w p ∈ rationalIntegralAdeles ∧
      d < rationalAdeleReal (h p : A) ∧ |rationalAdeleReal (w p)| < B := by
    have hwindow : h p₀ ∈ rationalIdeleUnitWindow :=
      mem_rationalIdeleUnitWindow_of_finiteValuation_eq_one hpos' hfin
    have h1 : ∀ᶠ p in 𝓝 p₀, h p ∈ rationalIdeleUnitWindow := hcont.continuousAt (isOpen_rationalIdeleUnitWindow.mem_nhds hwindow)
    have h2 : ∀ᶠ p in 𝓝 p₀, w p ∈ rationalIntegralAdeles := hwcont.continuousAt (isOpen_rationalIntegralAdeles.mem_nhds hq₀)
    have h3 : ∀ᶠ p in 𝓝 p₀, d < rationalAdeleReal (h p : A) := ((continuous_rationalAdeleReal.comp Units.continuous_val).comp hcont).continuousAt
      (Ioi_mem_nhds (half_lt_self hpos))
    have h4 : ∀ᶠ p in 𝓝 p₀, |rationalAdeleReal (w p)| < B := (continuous_rationalAdeleReal.comp hwcont).abs.continuousAt
      (Iio_mem_nhds (lt_add_one (|rationalAdeleReal (w p₀)|)))
    exact h1.and (h2.and (h3.and h4))
  obtain ⟨v, hv, hv₀, hvb⟩ := exists_schwartz_scaled_lattice_majorant b hd (B := B)
  let idx : ℤ → ℚ := fun n ↦ (r : ℚ) * ((n : ℚ) - q₀)
  let u : ℚ → ℝ := fun q ↦ if q ∈ range idx then v (Function.invFun idx q) else 0
  have hi : Function.Injective idx := by
    intro m n hmn
    have he : (m : ℚ) - q₀ = (n : ℚ) - q₀ := mul_left_cancel₀ r.ne_zero hmn
    exact Int.cast_injective (sub_left_inj.mp he)
  have hui (n : ℤ) : u (idx n) = v n := by
    dsimp only [u]
    rw [ite_eq_left (mem_range_self n), Function.leftInverse_invFun hi n]
  have hu : Summable u := (hi.summable_iff (by
    intro q hq
    exact ite_eq_right hq)).mp (by simpa only [Function.comp_def, hui] using hv)
  have hu₀ (q : ℚ) : 0 ≤ u q := by
    dsimp [u]
    split_ifs <;> first | exact hv₀ _ | rfl
  refine ⟨_, hU, u, hu, ?_⟩
  rintro q p ⟨hp, hwp, hdp, hBp⟩
  let y : A := ι (q / (r : ℚ) + q₀) + w p
  have hy : (↑(g⁻¹) : A) * ((p.1 : A) * (ι q + p.2) - a) = (h p : A) * y := by
    have hh : (h p : A) = ι (r : ℚ) * ((↑(g⁻¹) : A) * (p.1 : A)) := rfl
    have hrr : ι (r : ℚ) * ι (↑r⁻¹ : ℚ) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    have hy' : y = ι (↑r⁻¹ : ℚ) * (ι q + p.2) - (↑((h p)⁻¹) : A) * a' := by
      simp only [y, w, z, div_eq_mul_inv, map_add, map_mul, Units.val_inv_eq_inv_val]
      ring
    have hs : (h p : A) * ι (↑r⁻¹ : ℚ) = (↑(g⁻¹) : A) * (p.1 : A) := by
      rw [hh, mul_right_comm, hrr, one_mul]
    rw [hy', mul_sub, mul_sub, ← mul_assoc (h p : A) _ a', Units.mul_inv, one_mul,
      ← mul_assoc (h p : A), hs, mul_assoc]
  rw [rationalAdeleBox, hy, rationalAdeleUnramified]
  by_cases hyi : y ∈ rationalIntegralAdeles
  · rw [indicator_of_mem ((integral_mul_iff _ hp _).mpr hyi)]
    have hyq : ι (q / (r : ℚ) + q₀) ∈ rationalIntegralAdeles := by
      simpa only [y, add_sub_cancel_right] using rationalIntegralAdeles.sub_mem hyi hwp
    obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff _).mp hyq
    have hqn : q = idx n := by
      dsimp [idx]
      rw [← hn, add_sub_cancel_right, mul_comm, div_mul_cancel₀ _ r.ne_zero]
    rw [hqn, hui, real_mul, real_add, rationalAdeleReal_algebraMap, hn, Rat.cast_intCast]
    apply hvb _ _ _ (hdp.le.trans (le_abs_self _)) hBp.le
  · rw [indicator_of_notMem (mt (integral_mul_iff _ hp _).mp hyi), norm_zero]
    exact hu₀ q


/-- The terms of the rational orbit series, indexed by nonzero rationals. -/
@[expose] public noncomputable def rationalAdeleOrbitTerm (f : A → ℂ) (q : ℚˣ) (p : J × A) : ℂ :=
  f ((p.1 : A) * (ι (q : ℚ) + p.2))

private def HasOrbitMajorant (f : A → ℂ) (U : Set (J × A)) : Prop :=
  ∃ u : ℚˣ → ℝ, Summable u ∧ ∀ q p, p ∈ U → ‖rationalAdeleOrbitTerm f q p‖ ≤ u q

private theorem hasOrbitMajorant_mono {f : A → ℂ} {U V : Set (J × A)}
    (h : HasOrbitMajorant f V) (hUV : U ⊆ V) : HasOrbitMajorant f U := by
  obtain ⟨u, hu, hub⟩ := h
  exact ⟨u, hu, fun q p hp ↦ hub q p (hUV hp)⟩

private theorem hasOrbitMajorant_add {f g : A → ℂ} {U : Set (J × A)}
    (h : HasOrbitMajorant f U) (h' : HasOrbitMajorant g U) : HasOrbitMajorant (f + g) U := by
  obtain ⟨u, hu, hub⟩ := h
  obtain ⟨v, hv, hvb⟩ := h'
  exact ⟨_, hu.add hv, fun q p hp ↦ (norm_add_le _ _).trans (add_le_add (hub q p hp) (hvb q p hp))⟩

private theorem hasOrbitMajorant_const_mul {f : A → ℂ} {U : Set (J × A)} (c : ℂ)
    (h : HasOrbitMajorant f U) : HasOrbitMajorant (fun x ↦ c * f x) U := by
  obtain ⟨u, hu, hub⟩ := h
  refine ⟨_, hu.mul_left ‖c‖, fun q p hp ↦ ?_⟩
  rw [rationalAdeleOrbitTerm, norm_mul]
  exact mul_le_mul_of_nonneg_left (hub q p hp) (norm_nonneg _)

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- A finite box sum has a summable bound on a neighborhood of each orbit parameter. -/
public theorem exists_rationalAdeleBoxSum_orbit_local_majorant (p₀ : J × A) :
    ∃ U ∈ 𝓝 p₀, ∃ u : ℚˣ → ℝ, Summable u ∧
      ∀ q p, p ∈ U → ‖rationalAdeleOrbitTerm f q p‖ ≤ u q := by
  change ∃ U ∈ 𝓝 p₀, HasOrbitMajorant f U
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨univ, univ_mem, 0, summable_zero, by simp [rationalAdeleOrbitTerm, rationalAdeleBoxSum]⟩
  | insert i t hi ih =>
    obtain ⟨U, hU, u, hu, hub⟩ := exists_rationalAdeleBox_orbit_majorant (b i) (a i) (g i) p₀
    have hbox : HasOrbitMajorant (rationalAdeleBox (b i) (a i) (g i)) U :=
      ⟨_, hu.comp_injective Units.val_injective, fun q p hp ↦ hub q p hp⟩
    obtain ⟨V, hV, hVB⟩ := ih
    refine ⟨U ∩ V, inter_mem hU hV, ?_⟩
    have h := hasOrbitMajorant_add
      (hasOrbitMajorant_const_mul (c i) (hasOrbitMajorant_mono hbox inter_subset_left))
      (hasOrbitMajorant_mono hVB inter_subset_right)
    convert h using 1
    funext x
    simp only [rationalAdeleBoxSum, Finset.sum_insert hi, Pi.add_apply]

/-- A single summable bound controls the nonzero rational samples of `f` on
any compact set of dilation and shift pairs. -/
public theorem exists_rationalAdeleBoxSum_orbit_majorant {K : Set (J × A)} (hK : IsCompact K) :
    ∃ u : ℚˣ → ℝ, Summable u ∧ ∀ q p, p ∈ K → ‖rationalAdeleOrbitTerm f q p‖ ≤ u q := by
  change HasOrbitMajorant f K
  refine hK.induction_on ⟨0, summable_zero, by simp⟩ (fun _ _ hUV hV ↦
    hasOrbitMajorant_mono hV hUV) ?_ ?_
  · intro U V hU hV
    obtain ⟨u, hu, hub⟩ := hU
    obtain ⟨v, hv, hvb⟩ := hV
    refine ⟨_, hu.abs.add hv.abs, fun q p hp ↦ ?_⟩
    rcases hp with hp | hp
    · exact (hub q p hp).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact (hvb q p hp).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
  · intro p _
    obtain ⟨U, hU, hB⟩ := exists_rationalAdeleBoxSum_orbit_local_majorant s c b a g p
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hB⟩

end Masullo
