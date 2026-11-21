module

public import Lemmas.SinglePlaceNorm
public import Mathlib.Topology.Algebra.Support

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Order.Compact

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

private theorem hasFiniteMulSupport_finiteNorm (x : IdeleGroup (𝓞 K) K) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : AdeleRing (𝓞 K) K).2 v‖).HasFiniteMulSupport := by
  let snd : AdeleRing (𝓞 K) K →* IsDedekindDomain.FiniteAdeleRing (𝓞 K) K := MonoidHom.snd _ _
  exact NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (Units.map snd x)

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
    rw [finprod_mul_distrib (hasFiniteMulSupport_finiteNorm x) (hasFiniteMulSupport_finiteNorm y)]
    ac_rfl

public theorem ideleNorm_apply (a : IdeleGroup (𝓞 K) K) :
    ideleNorm a = ‖(a : AdeleRing (𝓞 K) K)‖ := by
  unfold ideleNorm
  rfl

/-- The idelic norm is continuous for the topology on units (Appendix A.1.3.3). -/
public theorem continuous_ideleNorm : Continuous (ideleNorm (K := K)) := by
  let integral : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    {a | ∀ v, a v ∈ v.adicCompletionIntegers K}
  have hopen : IsOpen integral :=
    RestrictedProduct.isOpen_forall_mem (fun _ ↦ Valued.isOpen_valuationSubring _)
  let value : IdeleGroup (𝓞 K) K → AdeleRing (𝓞 K) K := (↑)
  have hval : Continuous value := Units.continuous_val
  have hinv : Continuous (fun x ↦ value x⁻¹) := Units.continuous_coe_inv
  let U : Set (IdeleGroup (𝓞 K) K) :=
    {x | (value x).2 ∈ integral ∧ (value x⁻¹).2 ∈ integral}
  have hU : IsOpen U := (hopen.preimage hval.snd).inter (hopen.preimage hinv.snd)
  have hOne : (1 : IdeleGroup (𝓞 K) K) ∈ U := by
    have hone : ∀ v : HeightOneSpectrum (𝓞 K), (1 : v.adicCompletion K) ∈
        v.adicCompletionIntegers K := fun _ ↦ one_mem _
    exact ⟨hone, hone⟩
  let arch (x : IdeleGroup (𝓞 K) K) : ℝ := ∏ v : InfinitePlace K, ‖(value x).1 v‖ ^ v.mult
  have hArch : Continuous arch :=
    continuous_finsetProd _ (fun v _ ↦ ((continuous_apply v).comp hval.fst).norm.pow v.mult)
  -- On this identity neighborhood the finite-place factors are all one.
  apply continuous_of_continuousAt_one ideleNorm (hArch.continuousAt.congr ?_)
  filter_upwards [hU.mem_nhds hOne] with x hx
  change (∀ v, (value x).2 v ∈ v.adicCompletionIntegers K) ∧
    (∀ v, (value x⁻¹).2 v ∈ v.adicCompletionIntegers K) at hx
  have hlocal (v : HeightOneSpectrum (𝓞 K)) : ‖(value x).2 v‖ = 1 := by
    have norm_le_one {a : v.adicCompletion K} (ha : a ∈ v.adicCompletionIntegers K) : ‖a‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr
        ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp ha)
    have ha := norm_le_one (hx.1 v)
    have hb := norm_le_one (hx.2 v)
    have hab : (value x).2 v * (value x⁻¹).2 v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 K) K ↦ a.2 v) x.val_inv
    have hnorm : ‖(value x).2 v‖ * ‖(value x⁻¹).2 v‖ = 1 := by
      rw [← norm_mul, hab, norm_one]
    exact ha.antisymm (calc
      1 = ‖(value x).2 v‖ * ‖(value x⁻¹).2 v‖ := hnorm.symm
      _ ≤ ‖(value x).2 v‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = ‖(value x).2 v‖ := mul_one _)
  change arch x = ‖value x‖
  rw [AdeleRing.norm_apply_of_isUnit x.isUnit]
  change arch x = arch x * ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(value x).2 v‖
  simp only [hlocal, finprod_one, mul_one]

/-- The product formula makes the norm well-defined on idele classes. -/
public noncomputable def ideleClassNorm : IdeleClassGroup (𝓞 K) K →* ℝ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) ideleNorm (by
    intro x hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
    apply MonoidHom.mem_ker.mpr
    change ‖algebraMap K (AdeleRing (𝓞 K) K) (u : K)‖ = 1
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero u.ne_zero)

public theorem ideleClassNorm_mk (a : IdeleGroup (𝓞 K) K) :
    ideleClassNorm (QuotientGroup.mk a) = ideleNorm a := by
  unfold ideleClassNorm
  rfl

/-- The descended norm is continuous in the quotient topology (Appendix A.1.3.4). -/
public theorem continuous_ideleClassNorm : Continuous (ideleClassNorm (K := K)) := by
  apply (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 K) K)).continuous_iff.mpr
  exact continuous_ideleNorm

/-- The descended norm takes values in the positive reals. -/
public theorem ideleClassNorm_pos (g : IdeleClassGroup (𝓞 K) K) : 0 < ideleClassNorm g := by
  induction g using QuotientGroup.induction_on with
  | _ x =>
    change 0 < ‖(x : AdeleRing (𝓞 K) K)‖
    rw [AdeleRing.norm_apply_of_isUnit x.isUnit]
    obtain ⟨hArch, hFin, _⟩ := AdeleRing.isUnit_iff.mp x.isUnit
    apply mul_pos
    · exact Finset.prod_pos (fun v _ ↦ pow_pos (norm_pos_iff.mpr (hArch v)) _)
    · rw [finprod_eq_prod _ (hasFiniteMulSupport_finiteNorm x)]
      exact Finset.prod_pos (fun v _ ↦ norm_pos_iff.mpr (hFin v))

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

/-- The norm of the topological support of a compactly supported test lies in a
strict band `(T⁻¹, T)` about one. -/
public theorem exists_ideleClassNorm_band_of_hasCompactSupport
    (φ : IdeleClassGroup (𝓞 K) K → ℂ) (hφ : HasCompactSupport φ) :
    ∃ T : ℝ, 1 < T ∧ ∀ g ∈ tsupport φ, ideleClassNorm g ∈ Set.Ioo T⁻¹ T := by
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨lo, _, hlo⟩ := hφ.exists_isMinOn hne continuous_ideleClassNorm.continuousOn
    obtain ⟨hi, _, hhi⟩ := hφ.exists_isMaxOn hne continuous_ideleClassNorm.continuousOn
    obtain ⟨T, hT⟩ := exists_gt (max 1 (max (ideleClassNorm lo)⁻¹ (ideleClassNorm hi)))
    have hT₁ : 1 < T := (le_max_left _ _).trans_lt hT
    have hTlo : (ideleClassNorm lo)⁻¹ < T :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hT)
    have hThi : ideleClassNorm hi < T :=
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hT)
    refine ⟨T, hT₁, fun g hg ↦ ⟨?_, (hhi hg).trans_lt hThi⟩⟩
    exact ((inv_lt_comm₀ (zero_lt_one.trans hT₁) (ideleClassNorm_pos lo)).mpr hTlo).trans_le
      (hlo hg)
  · refine ⟨2, by norm_num, ?_⟩
    simp [Set.not_nonempty_iff_eq_empty.mp hne]

/-- A compactly supported test vanishing on the norm-one subgroup restricts to
zero on the entire multiplicative group at every finite place outside a finite set. -/
public theorem exists_finitePlaceRestriction_eq_zero_of_hasCompactSupport
    (φ : IdeleClassGroup (𝓞 K) K → ℂ) (hφ : HasCompactSupport φ)
    (hunit : ∀ g, ideleClassNorm g = 1 → φ g = 0) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ v, v ∉ S →
      ∀ u : (v.adicCompletion K)ˣ, φ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) = 0 := by
  obtain ⟨T, hT, hband⟩ := exists_ideleClassNorm_band_of_hasCompactSupport φ hφ
  refine ⟨{v | v.asIdeal.absNorm ≤ ⌈T⌉₊},
    Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le _, ?_⟩
  intro v hv u
  have hq : ⌈T⌉₊ < v.asIdeal.absNorm := lt_of_not_ge hv
  exact finitePlaceRestriction_eq_zero v T hT ((Nat.le_ceil T).trans_lt (Nat.cast_lt.mpr hq))
    φ (fun g hg ↦ hband g (subset_tsupport φ hg)) hunit u

end Masullo
