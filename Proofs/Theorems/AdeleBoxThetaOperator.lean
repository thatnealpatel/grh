module

public import Lemmas.AdeleBoxDilation
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Lemmas.FiniteAdeleDenominators
import Lemmas.IdeleCompactDenominators
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! # Global theta on the adelic box span

For Masullo's §1.1.4 (p. 12), this constructs the sum in (2.2.3.1) on the
accepted number-field box span. A compact set of ideles gives a single lattice
majorant for each translated-box tensor. The sum descends to continuous functions
on the idele class group. No source LF topology or kernel-quotient topology is
constructed here.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace InfinitePlace.Completion Set
open scoped Classical Masullo Pointwise SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "j[" v "]" => algebraMap (𝓞 K) L[v]
local notation "Λ" => mixedEmbedding.integerLattice K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

private theorem box_clearer (a : F) (g : Fˣ) :
    ∃ c : I, ∀ h : I, h.val.2 ∈ finiteAdeleBox a g → ∀ v : V, ‖(c * h).val.2 v‖ ≤ 1 := by
  obtain ⟨r, hr, hra⟩ := exists_finiteAdele_clearDenominator a
  obtain ⟨s, hs, hsg⟩ := exists_finiteAdele_clearDenominator (g : F)
  -- Clear both the translate and the scale using the product of their denominators.
  let c := d (Units.mk0 (algebraMap (𝓞 K) K (r * s))
    (by simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (mul_ne_zero hr hs)))
  refine ⟨c, fun h hh v ↦ ?_⟩
  have hav : j[v] r * a v ∈ O[v] := hra v
  have hgv : j[v] s * (g : F) v ∈ O[v] := hsg v
  have hint (t : 𝓞 K) : j[v] t ∈ O[v] := by
    change Valued.v (j[v] t) ≤ 1
    change Valued.v ((algebraMap (𝓞 K) K t : K) : L[v]) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  rcases hh v with ⟨_, ⟨t, ht, rfl⟩, heq⟩
  change a v + (g : F) v * t = h.val.2 v at heq
  apply Valued.toNormedField.norm_le_one_iff.mpr
  change (j[v] (r * s) * h.val.2 v) ∈ O[v]
  rw [← heq, map_mul, mul_add]
  have ha' : j[v] r * j[v] s * a v = j[v] s * (j[v] r * a v) := by ac_rfl
  have hg' : j[v] r * j[v] s * ((g : F) v * t) = (j[v] r * (j[v] s * (g : F) v)) * t := by ac_rfl
  rw [ha', hg']
  exact (O[v]).toSubring.add_mem ((O[v]).toSubring.mul_mem (hint s) hav)
    ((O[v]).toSubring.mul_mem ((O[v]).toSubring.mul_mem (hint r) hgv) ht)

private theorem norm_le_archEuclidean (x : InfiniteAdeleRing K) (v : InfinitePlace K) :
    ‖x v‖ ≤ ‖(archimedeanEuclideanToAdele K).symm x‖ := by
  let y := (archimedeanEuclideanToAdele K).symm x
  have heq : mixedEmbedding.euclidean.toMixed K y = InfiniteAdeleRing.ringEquiv_mixedSpace K x :=
    archimedeanEuclideanToAdele_symm_mixed K x
  by_cases hv : v.IsReal
  · let w : {v : InfinitePlace K // v.IsReal} := ⟨v, hv⟩
    have hw : y.fst w = extensionEmbeddingOfIsReal hv (x v) :=
      congrArg (fun z : mixedEmbedding.mixedSpace K ↦ z.1 w) heq
    rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v), ← hw]
    exact (PiLp.norm_apply_le y.fst w).trans (WithLp.norm_fst_le _ y)
  · let w : {v : InfinitePlace K // v.IsComplex} := ⟨v, not_isReal_iff_isComplex.mp hv⟩
    have hw : y.snd w = extensionEmbedding v (x v) :=
      congrArg (fun z : mixedEmbedding.mixedSpace K ↦ z.2 w) heq
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v), ← hw]
    exact (PiLp.norm_apply_le y.snd w).trans (WithLp.norm_snd_le _ y)

private theorem compact_arch_lower {B : Set I} (hB : IsCompact B) :
    ∃ r : ℝ, 0 < r ∧ ∀ h ∈ B, ∀ v : InfinitePlace K, r ≤ ‖h.val.1 v‖ := by
  have hcont (v : InfinitePlace K) : Continuous (fun h : I ↦ ‖(h⁻¹).val.1 v‖) :=
    ((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val.comp continuous_inv))).norm
  have hlocal (v : InfinitePlace K) : ∃ M : ℝ, ∀ h ∈ B, ‖(h⁻¹).val.1 v‖ ≤ M := by
    obtain ⟨M, hM⟩ := hB.bddAbove_image (hcont v).continuousOn
    exact ⟨M, fun h hh ↦ hM ⟨h, hh, rfl⟩⟩
  choose M hM using hlocal
  obtain ⟨U, hU⟩ := (Set.finite_range M).bddAbove
  let C := max 1 U
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left 1 U)
  refine ⟨1 / C, one_div_pos.mpr hC, fun h hh v ↦ (div_le_iff₀ hC).mpr ?_⟩
  have hi : ‖(h⁻¹).val.1 v‖ ≤ C :=
    (hM v h hh).trans ((hU (Set.mem_range_self v)).trans (le_max_right 1 U))
  have hmul : h.val.1 v * (h⁻¹).val.1 v = 1 := congrArg (fun z : A ↦ z.1 v) h.mul_inv
  calc
    1 = ‖h.val.1 v‖ * ‖(h⁻¹).val.1 v‖ := by rw [← norm_mul, hmul, norm_one]
    _ ≤ ‖h.val.1 v‖ * C := mul_le_mul_of_nonneg_left hi (norm_nonneg _)

private theorem arch_lower {B : Set I} (hB : IsCompact B) {m : ℕ} (hm : 0 < m) :
    ∃ l : ℝ, 0 < l ∧ ∀ h ∈ B, ∀ b : Kˣ,
      l * ‖mixedEmbedding K ((m : K) * (b : K))‖ ≤
        ‖(archimedeanEuclideanToAdele K).symm ((d b * h).val.1)‖ := by
  obtain ⟨r, hr, hcoord⟩ := compact_arch_lower hB
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨r / m, div_pos hr hmR, fun h hh b ↦ ?_⟩
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun v : InfinitePlace K ↦ mixedEmbedding.normAtPlace v (mixedEmbedding K ((m : K) * b.val)))
  rw [hv, mixedEmbedding.normAtPlace_apply, map_mul, v.map_natCast]
  have hd : ‖(d b).val.1 v‖ = v (b : K) := by
    change ‖algebraMap K v.Completion (b : K)‖ = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, AbsoluteValue.Completion.norm_coe]
    rfl
  calc
    r / m * ((m : ℝ) * v (b : K)) = v (b : K) * r := by field_simp [hmR.ne']
    _ ≤ v (b : K) * ‖h.val.1 v‖ := mul_le_mul_of_nonneg_left (hcoord h hh v) (apply_nonneg v _)
    _ = ‖(d b * h).val.1 v‖ := by
      change v (b : K) * ‖h.val.1 v‖ = ‖(d b).val.1 v * h.val.1 v‖
      rw [norm_mul, hd]
    _ ≤ _ := norm_le_archEuclidean _ _

private theorem compact_major_box (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) {B : Set I}
    (hB : IsCompact B) : ∃ M : Kˣ → ℝ, Summable M ∧ ∀ b h, h ∈ B →
      ‖adeleBoxTensor φ a g ((d b * h).val)‖ ≤ M b := by
  obtain ⟨c, hc⟩ := box_clearer a g
  let translate (h : I) : I := c * h
  obtain ⟨m, hm, hden⟩ := exists_uniform_denominator_of_isCompact _
    (hB.image (show Continuous translate from continuous_const.mul continuous_id))
  obtain ⟨l, hl, hlower⟩ := arch_lower hB hm
  let p := Module.finrank ℤ Λ + 1
  have hp : (Module.finrank ℤ Λ : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_succ_self _
  obtain ⟨D, hD, hdecay⟩ := φ.decay p 0
  -- A common support for the series on all of B, not the support at one h.
  let S : Set Kˣ := {b | (m : K) * (b : K) ∈ range (algebraMap (𝓞 K) K)}
  let e (b : S) : Λ := ⟨mixedEmbedding K ((m : K) * ((b : Kˣ) : K)), by
    obtain ⟨y, hy⟩ := b.property
    exact ⟨y, congrArg (mixedEmbedding K) hy⟩⟩
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : Function.Injective e := by
    intro b b' hb
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hmK (mixedEmbedding_injective K (congrArg Subtype.val hb))
  let W (z : Λ) := (D / l ^ p) * (‖z‖ ^ p)⁻¹
  have hW : Summable W := by
    apply Summable.mul_left
    simpa only [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast] using
      (ZLattice.summable_norm_rpow (L := Λ) (-(p : ℝ)) (neg_lt_neg hp))
  -- Extend the majorant by zero to keep the full index type Kˣ.
  let M (b : Kˣ) := if hb : b ∈ S then W (e ⟨b, hb⟩) else 0
  have hMs : Summable M := by
    rw [← summable_subtype_and_compl (s := S)]
    exact ⟨(hW.comp_injective he).congr (fun b ↦ by simp [M, b.property]),
      summable_zero.congr (fun b ↦ by
        have hb : (b : Kˣ) ∉ S := b.property
        simp [M, hb])⟩
  refine ⟨M, hMs, fun b h hh ↦ ?_⟩
  have hM₀ : 0 ≤ M b := by dsimp [M]; split <;> positivity
  by_cases hbox : (d b * h).val.2 ∈ finiteAdeleBox a g
  · have hb : b ∈ S := hden (translate h) (mem_image_of_mem _ hh) b (fun v ↦ by
      rw [show d b * translate h = c * (d b * h) by dsimp [translate]; ac_rfl]
      exact hc _ hbox v)
    rw [adeleBoxTensor, indicator_of_mem hbox, mul_one]
    let x := (archimedeanEuclideanToAdele K).symm ((d b * h).val.1)
    let z := e ⟨b, hb⟩
    have hz : 0 < ‖z‖ := by
      apply norm_pos_iff.mpr
      intro hz₀
      have hh₀ : mixedEmbedding K ((m : K) * (b : K)) = 0 := congrArg Subtype.val hz₀
      exact mul_ne_zero hmK b.ne_zero (mixedEmbedding_injective K (hh₀.trans (map_zero _).symm))
    have hle : ‖φ x‖ * (l * ‖z‖) ^ p ≤ D := calc
      _ ≤ ‖φ x‖ * ‖x‖ ^ p := by gcongr; exact hlower h hh b
      _ ≤ D := by simpa [mul_comm] using hdecay x
    change ‖φ x‖ ≤ M b
    rw [show M b = W z by simp [M, hb, z], show W z = D / (l * ‖z‖) ^ p by
      change D / l ^ p * (‖z‖ ^ p)⁻¹ = D / (l * ‖z‖) ^ p
      rw [mul_pow]
      field_simp [hl.ne', hz.ne']]
    exact (le_div_iff₀ (by positivity)).mpr hle
  · rw [adeleBoxTensor, indicator_of_notMem hbox, mul_zero, norm_zero]
    exact hM₀

/-- One summable majorant holds for the full principal series on a compact set
of ideles. The majorant depends on the test and compact set, not on the idele. -/
public theorem exists_adeleBoxPrincipalMajorant {f : A → ℂ} (hf : f ∈ adeleBoxSpan K)
    {B : Set I} (hB : IsCompact B) :
    ∃ M : Kˣ → ℝ, Summable M ∧ ∀ b h, h ∈ B → ‖f (d b * h).val‖ ≤ M b := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, a, g, rfl⟩ := hf
    exact compact_major_box φ a g hB
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add f g _ _ ihf ihg =>
    obtain ⟨M, hM, hMf⟩ := ihf
    obtain ⟨N, hN, hNg⟩ := ihg
    exact ⟨fun b ↦ M b + N b, hM.add hN, fun b h hh ↦
      (norm_add_le (f (d b * h).val) (g (d b * h).val)).trans
        (add_le_add (hMf b h hh) (hNg b h hh))⟩
  | smul c f _ ih =>
    obtain ⟨M, hM, hMf⟩ := ih
    refine ⟨fun b ↦ ‖c‖ * M b, hM.mul_left _, fun b h hh ↦ ?_⟩
    change ‖c • f (d b * h).val‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hMf b h hh) (norm_nonneg _)

/-- The complex principal subsums converge uniformly on every compact set. -/
public theorem hasSumUniformlyOn_adeleBoxPrincipal {f : A → ℂ} (hf : f ∈ adeleBoxSpan K)
    {B : Set I} (hB : IsCompact B) :
    HasSumUniformlyOn (fun b : Kˣ ↦ fun h : I ↦ f (d b * h).val)
      (fun h : I ↦ ∑' b : Kˣ, f (d b * h).val) B := by
  obtain ⟨M, hM, hMle⟩ := exists_adeleBoxPrincipalMajorant hf hB
  exact .of_norm_le_summable hM hMle

/-- Uniform convergence of the absolute principal series on every compact set
in the units topology, with finite subsums indexed by `Finset Kˣ`. -/
public theorem hasSumUniformlyOn_adeleBoxPrincipal_norm {f : A → ℂ} (hf : f ∈ adeleBoxSpan K)
    {B : Set I} (hB : IsCompact B) :
    HasSumUniformlyOn (fun b : Kˣ ↦ fun h : I ↦ ‖f (d b * h).val‖)
      (fun h : I ↦ ∑' b : Kˣ, ‖f (d b * h).val‖) B := by
  obtain ⟨M, hM, hMle⟩ := exists_adeleBoxPrincipalMajorant hf hB
  exact .of_norm_le_summable hM (fun b h hh ↦ by
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hMle b h hh)

/-- The full principal series is absolutely summable at each idele. -/
public theorem summable_norm_adeleBoxPrincipal {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (h : I) :
    Summable fun b : Kˣ ↦ ‖f (d b * h).val‖ := by
  obtain ⟨M, hM, hMle⟩ := exists_adeleBoxPrincipalMajorant hf (isCompact_singleton (x := h))
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun b ↦ hMle b h (mem_singleton h)) hM

private theorem summable_adeleBoxPrincipal {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (h : I) :
    Summable fun b : Kˣ ↦ f (d b * h).val := (summable_norm_adeleBoxPrincipal hf h).of_norm

private theorem isClopen_finiteAdeleBox (a : F) (g : Fˣ) : IsClopen (finiteAdeleBox a g) := by
  let S : Set F := {z | ∀ v : V, z v ∈ O[v]}
  have hs : IsClopen S := by
    constructor
    · rw [show S = ⋂ v : V, (fun z : F ↦ z v) ⁻¹' (O[v] : Set L[v]) by
        ext z; simp [S]]
      exact isClosed_iInter fun v ↦ (Valued.isClosed_integer _).preimage
        (RestrictedProduct.continuous_eval v)
    · exact RestrictedProduct.isOpen_forall_mem (fun v : V ↦ Valued.isOpen_valuationSubring L[v])
  let T (z : F) : F := (g⁻¹ : Fˣ).val * (z - a)
  have hT : Continuous T := continuous_const.mul (continuous_id.sub continuous_const)
  have heq : finiteAdeleBox a g = T ⁻¹' S := by
    ext z
    change (∀ v : V, z v ∈ (a v + ·) '' (g.val v • (O[v] : Set L[v]))) ↔
      ∀ v : V, g.inv v * (z v - a v) ∈ O[v]
    refine forall_congr' fun v ↦ ?_
    have hi : g.inv v * g.val v = 1 := congrArg (fun x : F ↦ x v) g.inv_val
    have hg : g.val v * g.inv v = 1 := congrArg (fun x : F ↦ x v) g.val_inv
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, heq⟩
      change a v + g.val v * t = z v at heq
      rwa [← heq, add_sub_cancel_left, ← mul_assoc, hi, one_mul]
    · intro hx
      refine ⟨_, ⟨_, hx, rfl⟩, ?_⟩
      change a v + g.val v * (g.inv v * (z v - a v)) = z v
      rw [← mul_assoc, hg, one_mul, add_sub_cancel]
  rw [heq]
  exact hs.preimage hT

private theorem continuous_adeleBoxTest {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, a, g, rfl⟩ := hf
    exact (φ.continuous.comp ((archimedeanEuclideanToAdele K).symm.continuous.comp
      continuous_fst)).mul (((isClopen_finiteAdeleBox a g).continuous_indicator
        (continuous_const (y := (1 : ℂ)))).comp continuous_snd)
  | zero => exact continuous_const
  | add _ _ _ _ ihf ihg => exact ihf.add ihg
  | smul c _ _ ih => exact continuous_const.smul ih

private theorem continuous_adeleBoxPrincipalSum {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) :
    Continuous fun h : I ↦ ∑' b : Kˣ, f (d b * h).val := by
  rw [continuous_iff_continuousAt]
  intro h
  obtain ⟨B, hB, hBh⟩ := exists_compact_mem_nhds h
  obtain ⟨M, hM, hMle⟩ := exists_adeleBoxPrincipalMajorant hf hB
  have hsum : ContinuousOn (fun h : I ↦ ∑' b : Kˣ, f (d b * h).val) B :=
    continuousOn_tsum (fun b ↦ ((continuous_adeleBoxTest hf).comp
      (Units.continuous_val.comp (continuous_const.mul continuous_id))).continuousOn) hM hMle
  exact (hsum h (mem_of_mem_nhds hBh)).continuousAt hBh

/-- Principal multiplication changes only the enumeration of the full series. -/
public theorem adeleBoxPrincipalSum_invariant {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (u : Kˣ) (h : I) :
    (∑' b : Kˣ, f (d b * (d u * h)).val) = ∑' b : Kˣ, f (d b * h).val := by
  let E := Equiv.mulRight u
  have hs := (summable_adeleBoxPrincipal hf h).hasSum
  refine ((E.hasSum_iff.mpr hs).congr_fun ?_).tsum_eq
  intro b
  change f (d b * (d u * h)).val = f (d (b * u) * h).val
  rw [map_mul, mul_assoc]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "P" => IdeleGroup.principalSubgroup (𝓞 K) K

private def adeleBoxThetaMap (f : adeleBoxSpan K) : C(C, ℂ) := by
  let T (h : I) := ∑' b : Kˣ, (f : A → ℂ) (d b * h).val
  have heq (g h : I) (hgh : QuotientGroup.mk g = (QuotientGroup.mk h : C)) : T g = T h := by
    have hp : g / h ∈ P := QuotientGroup.eq_iff_div_mem.mp hgh
    obtain ⟨u, hu⟩ := hp
    have hg : d u * h = g := eq_div_iff_mul_eq'.mp hu
    have hinv := adeleBoxPrincipalSum_invariant f.property u h
    change T (d u * h) = T h at hinv
    simpa only [hg] using hinv
  refine ⟨Quotient.lift T (fun _ _ h ↦ heq _ _ (Quotient.sound h)), ?_⟩
  exact QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    (continuous_adeleBoxPrincipalSum f.property)

private theorem adeleBoxThetaMap_mk (f : adeleBoxSpan K) (h : I) :
    adeleBoxThetaMap f (QuotientGroup.mk h : C) = ∑' b : Kˣ, (f : A → ℂ) (d b * h).val := rfl

/-- The global principal theta operator on the number-field adelic box span.
Its values are continuous on the actual idele class group. This is a linear
map, not a continuity assertion in a topology on the source span. -/
public def adeleBoxThetaLinear : adeleBoxSpan K →ₗ[ℂ] C(C, ℂ) where
  toFun := adeleBoxThetaMap
  map_add' f g := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [ContinuousMap.add_apply, adeleBoxThetaMap_mk]
    exact (summable_adeleBoxPrincipal f.property h).tsum_add
      (summable_adeleBoxPrincipal g.property h)
  map_smul' c f := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [ContinuousMap.smul_apply, adeleBoxThetaMap_mk, RingHom.id_apply]
    exact (summable_adeleBoxPrincipal f.property h).tsum_const_smul c

/-- Evaluation on an idele representative uses the convergent series over all `Kˣ`. -/
public theorem adeleBoxThetaLinear_apply (f : adeleBoxSpan K) (h : I) :
    adeleBoxThetaLinear f (QuotientGroup.mk h : C) =
      ∑' b : Kˣ, (f : A → ℂ) (d b * h).val := adeleBoxThetaMap_mk f h

end

end Masullo
