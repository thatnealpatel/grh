module

public import Lemmas.IdeleClassStripDivisor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Linarith

/-! # The radial zero sum of the completed trivial Hecke character

Reindex the absolute zero family of (B.4.2.2) by the norm powers in
(12.5.1.3). A width greater than `1/2` includes even possible zeros
on the two boundary lines of the critical strip. No normalization of
the Mellin pairing or trace identity is asserted.
-/

open Filter NumberField
open scoped Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

private theorem normPower_order {L : ℂ → ℂ} (hL : Meromorphic L)
    (hEuler : ∀ s : ℂ, 1 < s.re → L s =
      completedHeckeEulerProduct (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) s) (s : ℂ) :
    ideleClassHeckeOrder (ideleClassNormPower (K := K) s) = meromorphicOrderAt L s := by
  rw [ideleClassHeckeOrder_eq _ hL, ideleClassNormExponent_normPower]
  intro z hz
  simpa only [ideleClassHeckeBase_normPower] using hEuler z hz

/-- Transport an unordered weighted zero sum of the entire numerator from the
trivial-character explicit formula to the full strip index. Weights on other
norm-one characters must vanish, not the characters' zero divisors. -/
public theorem hasSum_trivialHeckeStrip_iff {L H : ℂ → ℂ} (hL : Meromorphic L)
    (hEuler : ∀ s : ℂ, 1 < s.re → L s =
      completedHeckeEulerProduct (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (hzeros : ∀ z, H z = 0 → z ≠ 0 ∧ z ≠ 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1)
    {a : ℝ} (ha : 1 / 2 < a) (W : HeckeCharacter (𝓞 K) K → ℂ)
    (hW : ∀ χ, (∃ c : ideleClassNormOne (K := K), χ (c : _) ≠ 1) → W χ = 0) {b : ℂ} :
    HasSum (fun z : OpenStripHeckeZero K a ↦ (z.order : ℂ) * W z.character) b ↔
      HasSum (fun z : {s : ℂ // H s = 0} ↦
        (analyticOrderNatAt H z.val : ℂ) * W (ideleClassNormPower z.val)) b := by
  classical
  let q := fun s : ℂ ↦ (s - 1) * s
  have hq (s : ℂ) : AnalyticAt ℂ q s := by dsimp [q]; fun_prop
  have hprod (s : ℂ) : H =ᶠ[𝓝[≠] s] q * L := by
    have avoid (t : ℂ) : ∀ᶠ w in 𝓝[≠] s, w ≠ t := by
      by_cases h : s = t
      · subst t; exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin h
    filter_upwards [avoid 0, avoid 1] with w hw₀ hw₁ using hclear w hw₀ hw₁
  have h₁ : H 1 ≠ 0 := fun h ↦ (hzeros 1 h).2.1 rfl
  have hnat (s : ℂ) : (analyticOrderNatAt H s : ℕ∞) = analyticOrderAt H s :=
    Nat.cast_analyticOrderNatAt fun he ↦ h₁ (congrFun
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hH.analyticAt).mp he) 1)
  have hord (z : {s : ℂ // H s = 0}) : meromorphicOrderAt L z.val =
      ((analyticOrderNatAt H z.val : ℤ) : WithTop ℤ) := by
    obtain ⟨h₀, h₁, _⟩ := hzeros _ z.property
    have hu : q z.val ≠ 0 := mul_ne_zero (sub_ne_zero.mpr h₁) h₀
    rw [← meromorphicOrderAt_mul_of_ne_zero (hq z.val) hu, ← meromorphicOrderAt_congr (hprod z.val),
      (hH.analyticAt _).meromorphicOrderAt_eq, ← hnat, ENat.map_natCast]
  let S := {z : OpenStripHeckeZero K a | ∀ c : ideleClassNormOne (K := K), z.character (c : _) = 1}
  let f (z : {s : ℂ // H s = 0}) : S :=
    ⟨⟨ideleClassNormPower z.val, by
        rw [ideleClassNormExponent_normPower, abs_lt]
        obtain ⟨_, _, h₀, h₁⟩ := hzeros _ z.property
        constructor <;> linarith,
      ⟨analyticOrderNatAt H z.val, Nat.pos_of_ne_zero (fun h ↦
        (hH.analyticAt _).analyticOrderAt_ne_zero.mpr z.property (by simp [← hnat z.val, h])),
        (normPower_order hL hEuler _).trans (hord z)⟩⟩, ideleClassNormPower_on_normOne _⟩
  have hinj : Function.Injective f := fun z w h ↦ Subtype.ext (by
    have h' := congrArg (fun u : S ↦ ideleClassNormExponent u.val.character) h
    simpa [f] using h')
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨s, hs, _⟩ := ideleClassNormPower_existsUnique z.val.character z.property
    have hpos : 0 < meromorphicOrderAt L s := by
      rw [← normPower_order hL hEuler, ← hs, z.val.heckeOrder_eq]
      exact_mod_cast z.val.order_pos
    have hz : H s = 0 := by
      by_contra h
      have hp := hpos.trans_le (le_add_of_nonneg_left (hq s).meromorphicOrderAt_nonneg)
      rw [← meromorphicOrderAt_mul (hq s).meromorphicAt (hL s), ← meromorphicOrderAt_congr (hprod s),
        (hH.analyticAt s).meromorphicOrderAt_eq, (hH.analyticAt s).analyticOrderAt_eq_zero.mpr h] at hp
      simp at hp
    exact ⟨⟨s, hz⟩, Subtype.ext (OpenStripHeckeZero.character_injective hs.symm)⟩
  have horder (z) : (f z).val.order = analyticOrderNatAt H z.val := by
    have h := (f z).val.heckeOrder_eq
    change ideleClassHeckeOrder (ideleClassNormPower z.val) = _ at h
    rw [normPower_order hL hEuler, hord] at h
    exact_mod_cast h.symm
  have hsupp : Function.support (fun z : OpenStripHeckeZero K a ↦ (z.order : ℂ) * W z.character) ⊆ S := by
    intro z hz c
    by_contra hn
    exact hz (by simp [hW _ ⟨c, hn⟩])
  rw [← hasSum_subtype_iff_of_support_subset hsupp, ← (Equiv.ofBijective f ⟨hinj, hsurj⟩).hasSum_iff]
  change HasSum (fun z ↦ ((f z).val.order : ℂ) * W (ideleClassNormPower z.val)) b ↔ _
  simp only [horder]

end Masullo
