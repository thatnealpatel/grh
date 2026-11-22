module

public import Theorems.FiniteHeckeAbsoluteZeta
public import Theorems.IdeleFiniteStageExhaustion
public import Theorems.IdeleFiniteStageIntegral

/-! # The raw idelic zeta integral above one

Masullo uses the global absolute product in (3.2.2.6), p. 126, and asserts
(3.4.1.6) for `Re s > 1` in the proof of Theorem 3.4.1.1, pp. 143–144.
Footnote 3 asks for the justification of the initial identities. For the
raw density of (3.2.2.1), p. 124, we use the exact restrictions of
(A.3.2.5), p. 560, and the grouped Archimedean factor of (3.4.1.2), p. 143.
The repair bounds the positive stage masses before passing to the complex
Euler product. The fixed local integrals retain their actual Haar masses;
we do not assert the printed modified factors, continuation, or integrability
for the full Schwartz–Bruhat class. Readings are provisional (Markdown and
numbered PDF layout).
-/

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical Masullo

namespace Masullo

private theorem prod_stage_eq {V M : Type*} [CommMonoid M]
    (T S : Finset V) (hTS : T ⊆ S) (f b : V → M)
    (h : ∀ v ∉ T, f v = b v) (hb : ∀ v ∈ T, b v = 1) :
    (∏ v ∈ S, f v) = (∏ v ∈ T, f v) * (∏ v ∈ S, b v) := by
  have hd : (∏ v ∈ S \ T, f v) = ∏ v ∈ S \ T, b v :=
    Finset.prod_congr rfl fun v hv ↦ h v (Finset.mem_sdiff.mp hv).2
  have hp : (∏ v ∈ S \ T, b v) = ∏ v ∈ S, b v :=
    Finset.prod_subset Finset.sdiff_subset fun v hv hn ↦
      hb v (by by_contra ht; exact hn (Finset.mem_sdiff.mpr ⟨hv, ht⟩))
  rw [← Finset.prod_sdiff hTS, hd, hp, mul_comm]

private theorem prod_tail_union {V M : Type*} [CommMonoid M]
    (T S : Finset V) (b : V → M) (hb : ∀ v ∈ T, b v = 1) :
    (∏ v ∈ T ∪ S, b v) = ∏ v ∈ S, b v :=
  (Finset.prod_subset Finset.subset_union_right fun v hv hn ↦
    hb v ((Finset.mem_union.mp hv).resolve_right hn)).symm

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "U" S => range (ideleFiniteStageEmbedding K S)
set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace K) → v.Completionˣ)

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [mf : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [mu : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [bf : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [bu : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  (μa : (v : InfinitePlace K) → Measure v.Completionˣ)
  (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)ˣ)
  [ha : ∀ v, (μa v).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]

/-- On `Re s > 1`, the raw upstairs integral and its absolute mass factor
into the grouped Archimedean term, the unchanged local integrals on `T`,
and the respective Euler tails off `T`. Here `T` contains the test exceptions,
ramification, and all places whose integer units do not have mass one. -/
public theorem ideleZetaIntegral_rightHalfPlane (E T : Finset V) (hET : E ⊆ T)
    (hT : ∀ v ∉ T, finiteCompletionUnitMass K μf v = 1)
    (μ : Measure I) (hμ : ∀ S : Finset V, T ⊆ S →
      μ.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S)
    (χ : HeckeCharacter (𝓞 K) K) (hu : ∀ v ∉ T, χ.IsUnramifiedAt v)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (s : ℂ) (hs : 1 < s.re) (arch : A → ℂ) (f : (v : V) → (F v)ˣ → ℂ) :
    let g (a : I) := ideleZetaTest K E arch f a *
      χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) *
      (‖(a : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s
    let aInf (x : A) := arch x *
      (∏ v : InfinitePlace K, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x v))) *
      ((∏ v : InfinitePlace K, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s
    let aFin (v : V) (x : (F v)ˣ) := ideleFiniteTest K E f v x *
      χ.restrict v (x : F v) * (‖(x : F v)‖ : ℂ) ^ s
    let z (v : V) := if v ∈ T then 0 else finiteHeckeCoefficient χ v
    let b (v : V) := if v ∈ T then 1 else finiteHeckeRealEulerFactor v s.re
    Integrable aInf (Measure.pi μa) → (∀ v ∈ T, Integrable (aFin v) (μf v)) →
      Integrable g μ ∧
      (∫ x, g x ∂μ) = (∫ x, aInf x ∂Measure.pi μa) * (∏ v ∈ T, ∫ x, aFin v x ∂μf v) *
        finiteHeckeEulerProduct z s ∧
      (∫ x, ‖g x‖ ∂μ) = (∫ x, ‖aInf x‖ ∂Measure.pi μa) *
        (∏ v ∈ T, ∫ x, ‖aFin v x‖ ∂μf v) * (∏' v, b v) := by
  intro g aInf aFin z b hA hF
  let c (v : V) := finiteHeckeEulerFactor z v s
  let C := (∫ x, aInf x ∂Measure.pi μa) * (∏ v ∈ T, ∫ x, aFin v x ∂μf v)
  let B := (∫ x, ‖aInf x‖ ∂Measure.pi μa) * (∏ v ∈ T, ∫ x, ‖aFin v x‖ ∂μf v)
  have hb (v) (hv : v ∈ T) : b v = 1 := ite_eq_left hv
  have hc (v) (hv : v ∈ T) : c v = 1 := by simp [c, z, hv, finiteHeckeEulerFactor, finiteHeckeMonomial]
  -- At a good place, use the local computation on the full completion units,
  -- with the standard integral-ring indicator, not an integral-unit restriction.
  have hloc (v : V) (hv : v ∉ T) : Integrable (aFin v) (μf v) ∧
      (∫ x, aFin v x ∂μf v) = c v ∧ (∫ x, ‖aFin v x‖ ∂μf v) = b v := by
    have hm : μf v (finiteLocalUnitSet v) = 1 := by
      rw [finiteLocalUnitSet_eq_range]
      exact hT v hv
    have hmr : (μf v).real (finiteLocalUnitSet v) = 1 := by simp [Measure.real, hm]
    have hmf : μf v (finiteLocalUnitSet v) ≠ ⊤ := by simp [hm]
    have hE : v ∉ E := fun h ↦ hv (hET h)
    have he : aFin v = {x : (F v)ˣ | ‖(x : F v)‖ ≤ 1}.indicator
        (fun x ↦ χ.restrict v (x : F v) * (‖(x : F v)‖ : ℂ) ^ s) := by
      funext x
      by_cases hx : ‖(x : F v)‖ ≤ 1 <;>
        simp only [aFin, ideleFiniteTest, ite_eq_right hE, Set.indicator_apply, Set.mem_ofPred_eq,
          hx, ite_true, ite_false, one_mul, zero_mul]
    rw [he]
    obtain ⟨hi, hval⟩ := finiteHeckeLocalZeta_unramified χ hχ v (μf v) hmf (hu v hv)
      (s := s) (zero_lt_one.trans hs)
    have hn := (finiteHeckeLocalZeta_norm χ hχ v (μf v) hmf (s := s) (zero_lt_one.trans hs)).2
    exact ⟨hi, by simpa [c, z, hv, hmr, finiteHeckeEulerFactor, finiteHeckeMonomial] using hval,
      by simpa [b, hv, hmr] using hn⟩
  -- Split the stage formulas into the fixed local integrals and the two tails.
  have hstage (S : Finset V) (hTS : T ⊆ S) : IntegrableOn g (U S) μ ∧
      (∫ x in U S, g x ∂μ) = C * (∏ v ∈ S, c v) ∧
      (∫ x in U S, ‖g x‖ ∂μ) = B * (∏ v ∈ S, b v) := by
    have hFi (v : V) : Integrable (aFin v) (μf v) := by
      by_cases hv : v ∈ T
      · exact hF v hv
      · exact (hloc v hv).1
    obtain ⟨hi, hv, hn⟩ := ideleFiniteStage_zetaIntegral K μa μf E S (hET.trans hTS)
      (fun v hv ↦ hT v (fun h ↦ hv (hTS h))) μ (hμ S hTS) χ
      (fun v hv ↦ hu v (fun h ↦ hv (hTS h))) s arch f hA (fun v ↦ hFi v)
    change (∫ x in U S, g x ∂μ) =
      (∫ x, aInf x ∂Measure.pi μa) * (∏ v : {v // v ∈ S}, ∫ x, aFin v x ∂μf v) at hv
    change (∫ x in U S, ‖g x‖ ∂μ) =
      (∫ x, ‖aInf x‖ ∂Measure.pi μa) * (∏ v : {v // v ∈ S}, ∫ x, ‖aFin v x‖ ∂μf v) at hn
    have hp := Finset.prod_coe_sort (s := S) (f := fun v : V ↦ ∫ x, aFin v x ∂μf v)
    have hpNorm := Finset.prod_coe_sort (s := S) (f := fun v : V ↦ ∫ x, ‖aFin v x‖ ∂μf v)
    refine ⟨hi, ?_, ?_⟩
    · rw [hv, hp, prod_stage_eq T S hTS _ c (fun v h ↦ (hloc v h).2.1) hc, ← mul_assoc]
    · rw [hn, hpNorm, prod_stage_eq T S hTS _ b (fun v h ↦ (hloc v h).2.2) hb, ← mul_assoc]
  -- The positive tail gives the uniform absolute bound needed for exhaustion.
  obtain ⟨hpb, hbound⟩ := finiteHeckeRealEulerTail_hasProd T hs
  have hB : 0 ≤ B := mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
    (Finset.prod_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
  obtain ⟨hi, _, hlim, hlimNorm⟩ := ideleFiniteStage_exhaust K T μ g (B * ∏' v, b v)
    (fun S hTS ↦ (hstage S hTS).1) (fun S hTS ↦ by
      rw [(hstage S hTS).2.2]
      exact mul_le_mul_of_nonneg_left (hbound S) hB)
  -- Both Euler limits are for finite sets ordered by inclusion, with one
  -- padded at T, so they use the same net as the stage exhaustion.
  have hz (v : V) : ‖z v‖ ≤ 1 := by
    by_cases hv : v ∈ T
    · simp [z, hv]
    · simpa [z, hv] using norm_finiteHeckeCoefficient_le_one χ hχ v
  have hpc := (finiteHeckeEulerFactor_hasProdLocallyUniformlyOn hz).hasProd (x := s) hs
  have heq (S : Finset V) : (∫ x in U (T ∪ S), g x ∂μ) = C * (∏ v ∈ S, c v) := by
    rw [(hstage (T ∪ S) Finset.subset_union_left).2.1, prod_tail_union T S c hc]
  have heqNorm (S : Finset V) : (∫ x in U (T ∪ S), ‖g x‖ ∂μ) = B * (∏ v ∈ S, b v) := by
    rw [(hstage (T ∪ S) Finset.subset_union_left).2.2, prod_tail_union T S b hb]
  refine ⟨hi, tendsto_nhds_unique hlim ?_, tendsto_nhds_unique hlimNorm ?_⟩
  · have hp : Tendsto (fun S : Finset V ↦ ∏ v ∈ S, c v) atTop
        (𝓝 (finiteHeckeEulerProduct z s)) := hpc
    simpa only [heq] using hp.const_mul C
  · have hp : Tendsto (fun S : Finset V ↦ ∏ v ∈ S, b v) atTop (𝓝 (∏' v, b v)) := hpb
    simpa only [heqNorm] using hp.const_mul B

end Masullo
