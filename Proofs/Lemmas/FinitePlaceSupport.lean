module

public import Lemmas.SinglePlaceNorm

/-!
# Finite-place restrictions of idele-class tests

The product formula descends the adelic norm to the idele class group (Masullo,
Appendix A.1.3). In the proof of Theorem 12.5.1.1, the test vanishes on the
norm-one subgroup and has support in a band about norm one. The discreteness
of the finite-place norm then kills the individual local test restriction at
each place whose residue norm exceeds that band. This is a project lemma for
the linear local terms, not a proof of the manuscript's orbital trace limit.
-/

open NumberField IsDedekindDomain
open scoped BigOperators

namespace Masullo

open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The adelic norm as a multiplicative map on the idele group. -/
public noncomputable def ideleNorm : IdeleGroup (𝓞 K) K →* ℝ where
  toFun x := ‖(x : AdeleRing (𝓞 K) K)‖
  map_one' := by
    change ‖(1 : AdeleRing (𝓞 K) K)‖ = 1
    rw [AdeleRing.norm_apply_of_isUnit isUnit_one]
    change (∏ v : InfinitePlace K, ‖(1 : v.Completion)‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖) = 1
    simp only [norm_one, one_pow, Finset.prod_const_one, finprod_one, one_mul]
  map_mul' x y := by
    rw [AdeleRing.norm_apply_of_isUnit (x * y).isUnit,
      AdeleRing.norm_apply_of_isUnit x.isUnit, AdeleRing.norm_apply_of_isUnit y.isUnit]
    change
      (∏ v : InfinitePlace K, ‖(x : AdeleRing (𝓞 K) K).1 v *
        (y : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : AdeleRing (𝓞 K) K).2 v *
        (y : AdeleRing (𝓞 K) K).2 v‖) = _
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
    let snd : AdeleRing (𝓞 K) K →* IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
      MonoidHom.snd _ _
    have hfin (z : IdeleGroup (𝓞 K) K) :
        (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(z : AdeleRing (𝓞 K) K).2 v‖).HasFiniteMulSupport :=
      NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (Units.map snd z)
    rw [finprod_mul_distrib (hfin x) (hfin y)]
    ac_rfl

/-- The product formula makes the norm well-defined on idele classes. -/
public noncomputable def ideleClassNorm : IdeleClassGroup (𝓞 K) K →* ℝ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) ideleNorm (by
    intro x hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
    apply MonoidHom.mem_ker.mpr
    change ‖algebraMap K (AdeleRing (𝓞 K) K) (u : K)‖ = 1
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero u.ne_zero)

/-- The norm on idele classes restricts to the given local norm at a finite place. -/
public theorem ideleClassNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleClassNorm (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      ‖(u : v.adicCompletion K)‖ := by
  rw [ideleClassNorm, IdeleClassGroup.ofAdicCompletion, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  exact norm_idele_ofAdicCompletion v u

/-- At a finite place the nonzero local norms are integer powers of the ideal norm. -/
private theorem localNorm_eq_zpow (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ∃ n : ℤ, ‖(u : v.adicCompletion K)‖ = (v.asIdeal.absNorm : ℝ) ^ n := by
  let w : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have h : w (u : v.adicCompletion K) ≠ 0 := w.ne_zero_iff.mpr u.ne_zero
  refine ⟨WithZero.log (w (u : v.adicCompletion K)), ?_⟩
  rw [FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v) h,
    NNReal.coe_zpow, NNReal.coe_natCast]

/-- For a place of ideal norm greater than `T`, the indicated test restricts to zero. -/
public theorem finitePlaceRestriction_eq_zero (v : HeightOneSpectrum (𝓞 K)) (T : ℝ)
    (hT : 1 < T) (hq : T < (v.asIdeal.absNorm : ℝ))
    (φ : IdeleClassGroup (𝓞 K) K → ℂ)
    (hband : ∀ g, φ g ≠ 0 → T⁻¹ < ideleClassNorm g ∧ ideleClassNorm g < T)
    (hunit : ∀ g, ideleClassNorm g = 1 → φ g = 0)
    (u : (v.adicCompletion K)ˣ) :
    φ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) = 0 := by
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u
  let q : ℝ := v.asIdeal.absNorm
  change φ g = 0
  change T < q at hq
  have hq₁ : 1 ≤ q := (hT.trans hq).le
  obtain ⟨n, hn⟩ := localNorm_eq_zpow v u
  have hn' : ideleClassNorm g = q ^ n := (ideleClassNorm_ofAdicCompletion v u).trans hn
  obtain hneg | heq | hpos := lt_trichotomy n 0
  · by_contra hφ
    have hlow := (hband g hφ).1
    have hsmall : q ^ n ≤ q⁻¹ := by
      rw [← zpow_neg_one]
      exact zpow_le_zpow_right₀ hq₁ (by omega)
    have hinv : q⁻¹ < T⁻¹ :=
      (inv_lt_inv₀ (zero_lt_one.trans (hT.trans hq)) (zero_lt_one.trans hT)).mpr hq
    exact (not_lt_of_ge ((hn'.le.trans hsmall).trans hinv.le)) hlow
  · exact hunit g (by simpa only [heq, zpow_zero] using hn')
  · by_contra hφ
    have hupp := (hband g hφ).2
    have hlarge : q ≤ q ^ n := by
      conv_lhs => rw [← zpow_one q]
      exact zpow_le_zpow_right₀ hq₁ (by omega)
    exact (not_lt_of_ge (hq.le.trans (hlarge.trans hn'.ge))) hupp

end Masullo
